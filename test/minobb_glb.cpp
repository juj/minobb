// test/minobb_glb.cpp
//
// Usage: minobb_glb <file.glb> [max_points]
//
// Opens the GLB file given in argv[1], collects the POSITION vertices of
// every primitive in the scene, transforms them into scene (world) space
// using the glTF node graph, computes the convex hull and the minimum-volume
// OBB with minobb(), and prints both as a JSON document to stdout.
//
// max_points (optional, 0 = no cap): the hull is O(n^2) and the OBB search
// O(E^3), so on very large meshes the input may be reduced to at most
// max_points with a deterministic uniform world-space grid (one point per
// occupied cell). The reported "vertices" count is the number of points
// actually used.
//
// Only dependencies: the C++ standard library and minobb.{h,cpp}.

#include "minobb.h"

#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <unordered_set>
#include <vector>

// ---------------------------------------------------------------------------
// Minimal JSON parser (just enough for glTF JSON chunks).
// ---------------------------------------------------------------------------

struct JsonValue
{
	enum Type { NUL, BOOL, NUMBER, STRING, ARRAY, OBJECT } type = NUL;
	bool b = false;
	double num = 0.0;
	std::string str;
	std::vector<JsonValue> arr;
	std::vector<std::pair<std::string, JsonValue>> obj;

	const JsonValue *Find(const char *key) const
	{
		if (type != OBJECT) return nullptr;
		for (const auto &kv : obj)
			if (kv.first == key) return &kv.second;
		return nullptr;
	}
};

struct JsonParser
{
	const char *s;
	int i = 0;
	bool ok = true;

	explicit JsonParser(const char *data) : s(data) {}

	static void SkipWs(JsonParser &p)
	{
		while (p.s[p.i] == ' ' || p.s[p.i] == '\t' || p.s[p.i] == '\n' || p.s[p.i] == '\r')
			p.i++;
	}

	static char Peek(JsonParser &p)
	{
		SkipWs(p);
		return p.s[p.i];
	}

	static bool Consume(JsonParser &p, char c)
	{
		if (Peek(p) == c) { p.i++; return true; }
		p.ok = false;
		return false;
	}

	static std::string ParseStringToken(JsonParser &p)
	{
		if (Peek(p) != '"') { p.ok = false; return ""; }
		p.i++;
		std::string out;
		while (p.s[p.i])
		{
			char c = p.s[p.i++];
			if (c == '"') return out;
			if (c == '\\')
			{
				char e = p.s[p.i++];
				switch (e)
				{
				case '"': out += '"'; break;
				case '\\': out += '\\'; break;
				case '/': out += '/'; break;
				case 'b': out += '\b'; break;
				case 'f': out += '\f'; break;
				case 'n': out += '\n'; break;
				case 'r': out += '\r'; break;
				case 't': out += '\t'; break;
				case 'u':
				{
					// Encode as a placeholder; glTF keys/strings we care about are ASCII.
					int code = 0;
					for (int k = 0; k < 4; k++)
					{
						char h = p.s[p.i++];
						code = code * 16 + (h <= '9' ? h - '0' : tolower(h) - 'a' + 10);
					}
					if (code < 128) out += (char)code;
					break;
				}
				default: p.ok = false; break;
				}
			}
			else out += c;
		}
		p.ok = false;
		return "";
	}

	static double ParseNumber(JsonParser &p)
	{
		SkipWs(p);
		const char *start = p.s + p.i;
		static const std::string kNumChars = "+-0123456789.eE";
		while (p.s[p.i] && kNumChars.find(p.s[p.i]) != std::string::npos)
			p.i++;
		return strtod(start, nullptr);
	}

	static JsonValue ParseValue(JsonParser &p)
	{
		JsonValue v;
		char c = Peek(p);
		if (c == '"')
		{
			v.type = JsonValue::STRING;
			v.str = ParseStringToken(p);
		}
		else if (c == '{')
		{
			v.type = JsonValue::OBJECT;
			p.i++;
			if (Peek(p) == '}') { p.i++; return v; }
			for (;;)
			{
				std::string key = ParseStringToken(p);
				if (!Consume(p, ':')) return v;
				JsonValue child = ParseValue(p);
				v.obj.emplace_back(std::move(key), std::move(child));
				char sep = Peek(p);
				if (sep == ',') { p.i++; continue; }
				if (sep == '}') { p.i++; break; }
				p.ok = false;
				break;
			}
		}
		else if (c == '[')
		{
			v.type = JsonValue::ARRAY;
			p.i++;
			if (Peek(p) == ']') { p.i++; return v; }
			for (;;)
			{
				v.arr.push_back(ParseValue(p));
				char sep = Peek(p);
				if (sep == ',') { p.i++; continue; }
				if (sep == ']') { p.i++; break; }
				p.ok = false;
				break;
			}
		}
		else if (c == 't')
		{
			if (strncmp(p.s + p.i, "true", 4) == 0) { p.i += 4; v.type = JsonValue::BOOL; v.b = true; }
			else p.ok = false;
		}
		else if (c == 'f')
		{
			if (strncmp(p.s + p.i, "false", 5) == 0) { p.i += 5; v.type = JsonValue::BOOL; v.b = false; }
			else p.ok = false;
		}
		else if (c == 'n')
		{
			if (strncmp(p.s + p.i, "null", 4) == 0) { p.i += 4; v.type = JsonValue::NUL; }
			else p.ok = false;
		}
		else
		{
			v.type = JsonValue::NUMBER;
			v.num = ParseNumber(p);
		}
		return v;
	}
};

// Reduces a world-space point list to at most `max_points` using a uniform
// grid (the first point of each occupied cell is kept). Deterministic.
// max_points == 0 disables subsampling.
static void SubsampleGrid(std::vector<float> &pts, size_t max_points)
{
	const size_t n = pts.size() / 3;
	if (max_points == 0 || n <= max_points)
		return;

	vec3 mn(pts[0], pts[1], pts[2]), mx(mn);
	for (size_t i = 0; i < n; i++)
	{
		const vec3 p(pts[3 * i], pts[3 * i + 1], pts[3 * i + 2]);
		mn.x = std::min(mn.x, p.x); mn.y = std::min(mn.y, p.y); mn.z = std::min(mn.z, p.z);
		mx.x = std::max(mx.x, p.x); mx.y = std::max(mx.y, p.y); mx.z = std::max(mx.z, p.z);
	}
	float sx = mx.x - mn.x, sy = mx.y - mn.y, sz = mx.z - mn.z;
	if (sx < 0) sx = 0;
	if (sy < 0) sy = 0;
	if (sz < 0) sz = 0;

	// Number of cells per axis so that k^3 is about max_points (<= n here).
	int k = (int)std::ceil(std::cbrt((double)max_points));
	if (k < 1) k = 1;

	std::unordered_set<size_t> used;
	used.reserve(max_points * 2);
	std::vector<float> out;
	out.reserve(std::min(n, max_points * 3));
	for (size_t i = 0; i < n; i++)
	{
		const float x = pts[3 * i], y = pts[3 * i + 1], z = pts[3 * i + 2];
		int ix = sx > 0 ? (int)((x - mn.x) / sx * k) : 0;
		int iy = sy > 0 ? (int)((y - mn.y) / sy * k) : 0;
		int iz = sz > 0 ? (int)((z - mn.z) / sz * k) : 0;
		if (ix >= k) ix = k - 1;
		if (iy >= k) iy = k - 1;
		if (iz >= k) iz = k - 1;
		const size_t cell = ((size_t)(size_t)ix * k + (size_t)iy) * k + (size_t)iz;
		if (used.insert(cell).second)
			out.insert(out.end(), pts.begin() + 3 * i, pts.begin() + 3 * i + 3);
	}
	pts.swap(out);
}

// ---------------------------------------------------------------------------
// 4x4 matrices (column-major, glTF convention) and node-graph traversal.
// ---------------------------------------------------------------------------

struct Mat4
{
	float m[16];
};

static Mat4 Mat4Identity()
{
	Mat4 r;
	memset(r.m, 0, sizeof r.m);
	r.m[0] = r.m[5] = r.m[10] = r.m[15] = 1.f;
	return r;
}

// Returns a * b (b is applied first, then a).
static Mat4 Mat4Multiply(const Mat4 &a, const Mat4 &b)
{
	Mat4 r;
	for (int c = 0; c < 4; c++)
		for (int row = 0; row < 4; row++)
		{
			float s = 0.f;
			for (int k = 0; k < 4; k++)
				s += a.m[k * 4 + row] * b.m[c * 4 + k];
			r.m[c * 4 + row] = s;
		}
	return r;
}

static void Mat4TransformPoint(const Mat4 &mat, const vec3 &p, vec3 &o)
{
	o.x = mat.m[0] * p.x + mat.m[4] * p.y + mat.m[8] * p.z + mat.m[12];
	o.y = mat.m[1] * p.x + mat.m[5] * p.y + mat.m[9] * p.z + mat.m[13];
	o.z = mat.m[2] * p.x + mat.m[6] * p.y + mat.m[10] * p.z + mat.m[14];
}

// Local transform of a glTF node: explicit "matrix" if present, otherwise
// composed from translation / rotation (quaternion) / scale (TRS).
static Mat4 Mat4FromNode(const JsonValue &node)
{
	const JsonValue *jmat = node.Find("matrix");
	if (jmat && jmat->type == JsonValue::ARRAY && jmat->arr.size() == 16)
	{
		Mat4 r;
		for (int k = 0; k < 16; k++)
			r.m[k] = (float)jmat->arr[k].num;
		return r;
	}

	float tx = 0, ty = 0, tz = 0;
	float qx = 0, qy = 0, qz = 0, qw = 1;
	float sx = 1, sy = 1, sz = 1;
	if (const JsonValue *t = node.Find("translation"))
		if (t->type == JsonValue::ARRAY && t->arr.size() == 3)
		{
			tx = (float)t->arr[0].num;
			ty = (float)t->arr[1].num;
			tz = (float)t->arr[2].num;
		}
	if (const JsonValue *q = node.Find("rotation"))
		if (q->type == JsonValue::ARRAY && q->arr.size() == 4)
		{
			qx = (float)q->arr[0].num;
			qy = (float)q->arr[1].num;
			qz = (float)q->arr[2].num;
			qw = (float)q->arr[3].num;
		}
	if (const JsonValue *s = node.Find("scale"))
		if (s->type == JsonValue::ARRAY && s->arr.size() == 3)
		{
			sx = (float)s->arr[0].num;
			sy = (float)s->arr[1].num;
			sz = (float)s->arr[2].num;
		}

	// Rotation matrix rows from the quaternion (glTF spec).
	const float xx = qx * qx, yy = qy * qy, zz = qz * qz;
	const float xy = qx * qy, xz = qx * qz, yz = qy * qz;
	const float xw = qx * qw, yw = qy * qw, zw = qz * qw;
	// Column-major result: m[col*4+row].
	Mat4 r = Mat4Identity();
	r.m[0] = sx * (1 - 2 * (yy + zz));
	r.m[1] = sx * (2 * (xy - zw));
	r.m[2] = sx * (2 * (xz + yw));
	r.m[4] = sy * (2 * (xy + zw));
	r.m[5] = sy * (1 - 2 * (xx + zz));
	r.m[6] = sy * (2 * (yz - xw));
	r.m[8] = sz * (2 * (xz - yw));
	r.m[9] = sz * (2 * (yz + xw));
	r.m[10] = sz * (1 - 2 * (xx + yy));
	r.m[12] = tx;
	r.m[13] = ty;
	r.m[14] = tz;
	return r;
}

// ---------------------------------------------------------------------------
// GLB loading: collect world-space POSITION vertices of the whole scene.
// ---------------------------------------------------------------------------

static bool ReadEntireFile(const char *path, std::vector<char> &out)
{
	FILE *f = fopen(path, "rb");
	if (!f) return false;
	if (fseek(f, 0, SEEK_END) != 0) { fclose(f); return false; }
	long size = ftell(f);
	if (size < 0) { fclose(f); return false; }
	fseek(f, 0, SEEK_SET);
	out.resize((size_t)size);
	bool ok = size == 0 || fread(out.data(), 1, (size_t)size, f) == (size_t)size;
	fclose(f);
	return ok;
}

// Reads one VEC3 vertex at index `vi` of a POSITION accessor. The vertex
// stride comes from the buffer view's byteStride (or is tightly packed).
static bool ReadVertex3(const std::vector<char> &bin, const JsonValue &acc,
	const JsonValue &bv, size_t vi, vec3 &out)
{
	const JsonValue *j_count = acc.Find("count");
	const JsonValue *j_ct = acc.Find("componentType");
	const JsonValue *j_off = acc.Find("byteOffset");
	int count = j_count ? (int)j_count->num : 0;
	int component_type = j_ct ? (int)j_ct->num : 0;
	size_t acc_byte_offset = j_off ? (size_t)j_off->num : 0;
	if ((int)vi >= count) return false;

	const JsonValue *j_bvoff = bv.Find("byteOffset");
	const JsonValue *j_stride = bv.Find("byteStride");
	size_t bv_byte_offset = j_bvoff ? (size_t)j_bvoff->num : 0;

	size_t comp_size = 0;
	switch (component_type)
	{
	case 5126: comp_size = 4; break; // FLOAT
	case 5125: comp_size = 4; break; // UNSIGNED_INT
	case 5123: comp_size = 2; break; // UNSIGNED_SHORT
	case 5121: comp_size = 1; break; // UNSIGNED_BYTE
	case 5122: comp_size = 2; break; // SHORT
	case 5120: comp_size = 1; break; // BYTE
	default:
		fprintf(stderr, "error: unsupported componentType %d\n", component_type);
		return false;
	}
	const size_t vertex_stride = j_stride ? (size_t)j_stride->num : 3 * comp_size;
	const uint8_t *data = (const uint8_t *)bin.data() + bv_byte_offset + acc_byte_offset + vi * vertex_stride;
	if (data + 3 * comp_size > (const uint8_t *)bin.data() + bin.size())
	{
		fprintf(stderr, "error: vertex data out of range\n");
		return false;
	}

	float v[3];
	for (int k = 0; k < 3; k++)
	{
		const uint8_t *p = data + (size_t)k * comp_size;
		switch (component_type)
		{
		case 5126: { float f; memcpy(&f, p, 4); v[k] = f; break; }
		case 5125: { uint32_t u; memcpy(&u, p, 4); v[k] = (float)u; break; }
		case 5123: { uint16_t u; memcpy(&u, p, 2); v[k] = (float)u; break; }
		case 5121: v[k] = (float)*p; break;
		case 5122: { int16_t s; memcpy(&s, p, 2); v[k] = (float)s; break; }
		case 5120: { int8_t s; memcpy(&s, p, 1); v[k] = (float)s; break; }
		default: return false;
		}
	}
	out = vec3(v[0], v[1], v[2]);
	return true;
}

// Collects the POSITION vertices of every primitive referenced by the scene
// graph, transformed by the accumulated node transforms into scene (world)
// space. `pts` is filled with tightly packed float triples (12-byte stride).
static bool ExtractWorldPoints(const std::vector<char> &bin, const JsonValue &json,
	std::vector<float> &pts)
{
	const JsonValue *accessors = json.Find("accessors");
	const JsonValue *buffer_views = json.Find("bufferViews");
	const JsonValue *meshes = json.Find("meshes");
	const JsonValue *nodes = json.Find("nodes");
	const JsonValue *scenes = json.Find("scenes"); // optional
	const JsonValue *buffers = json.Find("buffers");
	if ((!accessors || accessors->type != JsonValue::ARRAY) ||
		(!buffer_views || buffer_views->type != JsonValue::ARRAY) ||
		(!meshes || meshes->type != JsonValue::ARRAY) ||
		(!nodes || nodes->type != JsonValue::ARRAY) ||
		(scenes && scenes->type != JsonValue::ARRAY) ||
		(!buffers || buffers->type != JsonValue::ARRAY) ||
		buffers->arr.empty() || buffers->arr[0].Find("uri") != nullptr)
	{
		fprintf(stderr, "error: unsupported or missing glTF sections "
			"(only BIN-chunk buffer 0 is supported)\n");
		return false;
	}

	const size_t n_nodes = nodes->arr.size();

	// Per-node local transforms.
	std::vector<Mat4> node_mat(n_nodes);
	for (size_t i = 0; i < n_nodes; i++)
		node_mat[i] = Mat4FromNode(nodes->arr[i]);

	// World transforms: BFS from every scene's root nodes. If "scenes" is
	// omitted, the default scene implicitly contains all nodes (glTF spec).
	std::vector<Mat4> world(n_nodes);
	std::vector<char> visited(n_nodes, 0);
	std::vector<int> queue;
	auto enqueue_root = [&](int i) {
		if (i < 0 || (size_t)i >= n_nodes || visited[i]) return;
		visited[i] = 1;
		world[i] = node_mat[i];
		queue.push_back(i);
	};
	if (scenes)
	{
		for (const JsonValue &scene : scenes->arr)
		{
			const JsonValue *roots = scene.Find("nodes");
			if (!roots) continue;
			for (const JsonValue &root : roots->arr)
				enqueue_root((int)root.num);
		}
	}
	else
	{
		// Default scene: the top-level nodes (not a child of any other node).
		std::vector<char> is_child(n_nodes, 0);
		for (size_t i = 0; i < n_nodes; i++)
		{
			const JsonValue *children = nodes->arr[i].Find("children");
			if (!children) continue;
			for (const JsonValue &child : children->arr)
			{
				int j = (int)child.num;
				if (j >= 0 && (size_t)j < n_nodes)
					is_child[j] = 1;
			}
		}
		for (size_t i = 0; i < n_nodes; i++)
			if (!is_child[i])
				enqueue_root((int)i);
	}
	for (size_t qi = 0; qi < queue.size(); qi++)
	{
		int i = queue[qi];
		const JsonValue *children = nodes->arr[i].Find("children");
		if (!children) continue;
		for (const JsonValue &child : children->arr)
		{
			int j = (int)child.num;
			if (j < 0 || (size_t)j >= n_nodes || visited[j]) continue;
			visited[j] = 1;
			world[j] = Mat4Multiply(world[i], node_mat[j]);
			queue.push_back(j);
		}
	}

	// Collect and transform the vertices.
	pts.clear();
	for (size_t i = 0; i < n_nodes; i++)
	{
		if (!visited[i]) continue;
		const JsonValue *j_mesh = nodes->arr[i].Find("mesh");
		if (!j_mesh) continue;
		int mesh_idx = (int)j_mesh->num;
		if (mesh_idx < 0 || (size_t)mesh_idx >= meshes->arr.size())
		{
			fprintf(stderr, "error: mesh %d not found\n", mesh_idx);
			return false;
		}
		const JsonValue &mesh = meshes->arr[mesh_idx];
		const JsonValue *prims = mesh.Find("primitives");
		if (!prims) continue;
		for (const JsonValue &prim : prims->arr)
		{
			const JsonValue *attrs = prim.Find("attributes");
			if (!attrs) continue;
			const JsonValue *pos = attrs->Find("POSITION");
			if (!pos || pos->type != JsonValue::NUMBER) continue;
			int accessor_idx = (int)pos->num;
			if (accessor_idx < 0 || (size_t)accessor_idx >= accessors->arr.size())
			{
				fprintf(stderr, "error: accessor %d not found\n", accessor_idx);
				return false;
			}
			const JsonValue &acc = accessors->arr[accessor_idx];
			const JsonValue *type = acc.Find("type");
			if (!type || type->str != "VEC3")
			{
				fprintf(stderr, "error: POSITION accessor type must be VEC3\n");
				return false;
			}
			const JsonValue *j_bv = acc.Find("bufferView");
			int buffer_view_idx = j_bv ? (int)j_bv->num : -1;
			if (buffer_view_idx < 0 || (size_t)buffer_view_idx >= buffer_views->arr.size())
			{
				fprintf(stderr, "error: bufferView %d not found\n", buffer_view_idx);
				return false;
			}
			const JsonValue &bv = buffer_views->arr[buffer_view_idx];
			const JsonValue *j_buf = bv.Find("buffer");
			if (!j_buf || (int)j_buf->num != 0)
			{
				fprintf(stderr, "error: only BIN-chunk buffer 0 is supported\n");
				return false;
			}

			const JsonValue *j_count = acc.Find("count");
			int count = j_count ? (int)j_count->num : 0;
			pts.reserve(pts.size() + (size_t)count * 3);
			for (int vi = 0; vi < count; vi++)
			{
				vec3 p, w;
				if (!ReadVertex3(bin, acc, bv, (size_t)vi, p)) return false;
				Mat4TransformPoint(world[i], p, w);
				pts.push_back(w.x);
				pts.push_back(w.y);
				pts.push_back(w.z);
			}
		}
	}
	if (pts.empty())
	{
		fprintf(stderr, "error: no POSITION vertices found in the scene\n");
		return false;
	}
	return true;
}

int main(int argc, char **argv)
{
	if (argc < 2)
	{
		fprintf(stderr, "usage: %s <file.glb> [max_points]\n", argv[0]);
		return 1;
	}
	const size_t max_points = (argc >= 3) ? strtoull(argv[2], nullptr, 10) : 0;

	std::vector<char> glb;
	if (!ReadEntireFile(argv[1], glb))
	{
		fprintf(stderr, "error: cannot read %s\n", argv[1]);
		return 1;
	}

	// Parse the GLB container: 12-byte header, then length-prefixed chunks.
	static const uint32_t kMagic = 0x46546C67;      // "glTF"
	static const uint32_t kChunkJson = 0x4E4F534A;  // "JSON"
	static const uint32_t kChunkBin = 0x004E4942;   // "BIN\0"

	if (glb.size() < 12 || memcmp(glb.data(), &kMagic, 4) != 0)
	{
		fprintf(stderr, "error: not a GLB file\n");
		return 1;
	}
	uint32_t version, total_length;
	memcpy(&version, glb.data() + 4, 4);
	memcpy(&total_length, glb.data() + 8, 4);
	if (version < 2)
	{
		fprintf(stderr, "error: unsupported GLB version %u\n", version);
		return 1;
	}
	if (total_length != glb.size())
	{
		fprintf(stderr, "error: GLB header length %u does not match file size %zu\n",
			total_length, glb.size());
		return 1;
	}

	// The BIN chunk becomes buffer 0; JSON is parsed separately.
	const char *bin_data = nullptr;
	size_t bin_size = 0;
	std::string json_str;

	size_t offset = 12;
	while (offset + 8 <= glb.size())
	{
		uint32_t chunk_length, chunk_type;
		memcpy(&chunk_length, glb.data() + offset, 4);
		memcpy(&chunk_type, glb.data() + offset + 4, 4);
		offset += 8;
		if (offset + chunk_length > glb.size())
		{
			fprintf(stderr, "error: truncated GLB chunk\n");
			return 1;
		}
		if (chunk_type == kChunkJson)
		{
			json_str.assign(glb.data() + offset, chunk_length);
		}
		else if (chunk_type == kChunkBin)
		{
			bin_data = glb.data() + offset;
			bin_size = chunk_length;
		}
		offset += chunk_length;
	}
	(void)bin_size;

	if (json_str.empty())
	{
		fprintf(stderr, "error: no JSON chunk\n");
		return 1;
	}
	if (!bin_data)
	{
		fprintf(stderr, "error: no BIN chunk (embedded buffers not supported)\n");
		return 1;
	}

	// Parse the JSON and extract positions (rebased onto the BIN chunk,
	// since glTF buffer 0 offsets are relative to the start of the BIN data).
	JsonParser parser(json_str.c_str());
	JsonValue json = JsonParser::ParseValue(parser);
	if (!parser.ok)
	{
		fprintf(stderr, "error: failed to parse GLB JSON chunk\n");
		return 1;
	}

	std::vector<float> pts;
	// The BIN chunk is glTF buffer 0.
	std::vector<char> bin_view(bin_data, bin_data + bin_size);
	if (!ExtractWorldPoints(bin_view, json, pts))
		return 1;

	const int total_pts = (int)(pts.size() / 3);
	SubsampleGrid(pts, max_points);

	int num_pts = (int)(pts.size() / 3);
	fprintf(stderr, "info: %d world-space points\n", total_pts);
	if (num_pts < total_pts)
		fprintf(stderr, "info: subsampled to %d points (uniform grid, max_points=%zu)\n",
			num_pts, max_points);

	// Compute the convex hull and the minimum-volume OBB.
	auto t0 = std::chrono::steady_clock::now();
	Hull3 hull = convex_hull(pts.data(), num_pts, 12);
	auto t1 = std::chrono::steady_clock::now();
	OBB obb = minobb(pts.data(), num_pts, 12);
	auto t2 = std::chrono::steady_clock::now();
	fprintf(stderr, "info: hull: %zu verts, %zu faces (%.2fs)\n",
		hull.v.size(), hull.f.size(),
		std::chrono::duration<double>(t1 - t0).count());
	fprintf(stderr, "info: obb: volume %g (%.2fs)\n",
		obb.Volume(), std::chrono::duration<double>(t2 - t1).count());

	// Print the results as a single JSON document.
	printf("{\n");
	printf("  \"vertices\": %d,\n", num_pts);
	if (num_pts < total_pts)
		printf("  \"subsampled_from\": %d,\n", total_pts);

	printf("  \"hull\": {\n");
	printf("    \"degenerate\": %s,\n", hull.IsDegenerate() ? "true" : "false");
	printf("    \"vertices\": [");
	for (size_t i = 0; i < hull.v.size(); i++)
		printf("%s\n      [%.9g, %.9g, %.9g]", i ? "," : "", hull.v[i].x, hull.v[i].y, hull.v[i].z);
	printf(hull.v.empty() ? "],\n" : "\n    ],\n");
	printf("    \"faces\": [");
	for (size_t i = 0; i < hull.f.size(); i++)
	{
		const std::vector<int> &face = hull.f[i];
		printf("%s\n      [", i ? "," : "");
		for (size_t j = 0; j < face.size(); j++)
			printf("%d%s", face[j], j + 1 < face.size() ? ", " : "");
		printf("]");
	}
	printf(hull.f.empty() ? "]\n" : "\n    ]\n");
	printf("  },\n");

	printf("  \"obb\": {\n");
	printf("    \"degenerate\": %s,\n", obb.IsDegenerate() ? "true" : "false");
	printf("    \"center\": [%.9g, %.9g, %.9g],\n", obb.pos.x, obb.pos.y, obb.pos.z);
	printf("    \"half_extents\": [%.9g, %.9g, %.9g],\n", obb.r.x, obb.r.y, obb.r.z);
	printf("    \"size\": [%.9g, %.9g, %.9g],\n", 2.f * obb.r.x, 2.f * obb.r.y, 2.f * obb.r.z);
	printf("    \"axes\": [");
	for (int i = 0; i < 3; i++)
		printf("%s\n      [%.9g, %.9g, %.9g]", i ? "," : "", obb.axis[i].x, obb.axis[i].y, obb.axis[i].z);
	printf("\n    ],\n");
	printf("    \"volume\": %.9g\n", obb.Volume());
	printf("  }\n");
	printf("}\n");

	return 0;
}
