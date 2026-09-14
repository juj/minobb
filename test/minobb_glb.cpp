// test/minobb_glb.cpp
//
// Usage: minobb_glb <file.glb>
//
// Opens the GLB file given in argv[1], extracts the vertex positions of the
// first primitive that has a POSITION attribute, computes the minimum-volume
// OBB with minobb(), and prints the OBB parameters (center, half extents,
// orthonormal axes, size, volume) to stdout.
//
// Only dependencies: the C++ standard library and minobb.{h,cpp}.

#include "minobb.h"

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
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

// ---------------------------------------------------------------------------
// GLB loading: extract vertex positions of the first POSITION attribute.
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

// Copies the POSITION vertex data of the given GLB into `pts` as tightly
// packed float triples (12-byte stride). Returns false on error.
static bool ExtractPositions(const std::vector<char> &glb, const JsonValue &json,
	std::vector<float> &pts)
{
	// Find the first primitive with a POSITION attribute, to get its accessor index.
	int accessor_idx = -1;
	const JsonValue *meshes = json.Find("meshes");
	if (meshes && meshes->type == JsonValue::ARRAY)
	{
		for (const JsonValue &mesh : meshes->arr)
		{
			const JsonValue *prims = mesh.Find("primitives");
			if (!prims) continue;
			for (const JsonValue &prim : prims->arr)
			{
				const JsonValue *attrs = prim.Find("attributes");
				if (!attrs) continue;
				const JsonValue *pos = attrs->Find("POSITION");
				if (pos && pos->type == JsonValue::NUMBER)
				{
					accessor_idx = (int)pos->num;
					break;
				}
			}
			if (accessor_idx >= 0) break;
		}
	}
	if (accessor_idx < 0)
	{
		fprintf(stderr, "error: no primitive with a POSITION attribute found\n");
		return false;
	}

	// Look up the accessor.
	const JsonValue *accessors = json.Find("accessors");
	if (!accessors || accessors->type != JsonValue::ARRAY ||
		accessor_idx >= (int)accessors->arr.size())
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
	const JsonValue *j_count = acc.Find("count");
	const JsonValue *j_ct = acc.Find("componentType");
	const JsonValue *j_bv = acc.Find("bufferView");
	const JsonValue *j_off = acc.Find("byteOffset");
	int count = j_count ? (int)j_count->num : 0;
	int component_type = j_ct ? (int)j_ct->num : 0;
	int buffer_view_idx = j_bv ? (int)j_bv->num : 0;
	int acc_byte_offset = j_off ? (int)j_off->num : 0;
	if (count <= 0)
	{
		fprintf(stderr, "error: POSITION accessor has count %d\n", count);
		return false;
	}

	// Look up the buffer view.
	const JsonValue *buffer_views = json.Find("bufferViews");
	if (!buffer_views || buffer_views->type != JsonValue::ARRAY ||
		buffer_view_idx >= (int)buffer_views->arr.size())
	{
		fprintf(stderr, "error: bufferView %d not found\n", buffer_view_idx);
		return false;
	}
	const JsonValue &bv = buffer_views->arr[buffer_view_idx];
	const JsonValue *j_buf = bv.Find("buffer");
	const JsonValue *j_bvoff = bv.Find("byteOffset");
	int buffer_idx = j_buf ? (int)j_buf->num : 0;
	int bv_byte_offset = j_bvoff ? (int)j_bvoff->num : 0;

	// Buffer 0 must be the GLB BIN chunk (embedded data: URIs are not supported).
	const JsonValue *buffers = json.Find("buffers");
	if (!buffers || buffers->type != JsonValue::ARRAY || buffer_idx >= (int)buffers->arr.size() ||
		buffers->arr[buffer_idx].Find("uri") != nullptr)
	{
		fprintf(stderr, "error: only BIN-chunk buffer 0 is supported\n");
		return false;
	}

	size_t data_offset = (size_t)(bv_byte_offset + acc_byte_offset);
	size_t n_elems = (size_t)count * 3;
	pts.resize(n_elems);

	const uint8_t *data = (const uint8_t *)glb.data();
	switch (component_type)
	{
	case 5126: // FLOAT
	{
		if (data_offset + n_elems * 4 > glb.size()) { fprintf(stderr, "error: data out of range\n"); return false; }
		memcpy(pts.data(), data + data_offset, n_elems * 4);
		break;
	}
	case 5125: // UNSIGNED_INT
	{
		if (data_offset + n_elems * 4 > glb.size()) { fprintf(stderr, "error: data out of range\n"); return false; }
		const uint32_t *src = (const uint32_t *)(data + data_offset);
		for (size_t k = 0; k < n_elems; k++) pts[k] = (float)src[k];
		break;
	}
	case 5123: // UNSIGNED_SHORT
	{
		if (data_offset + n_elems * 2 > glb.size()) { fprintf(stderr, "error: data out of range\n"); return false; }
		const uint16_t *src = (const uint16_t *)(data + data_offset);
		for (size_t k = 0; k < n_elems; k++) pts[k] = (float)src[k];
		break;
	}
	case 5121: // UNSIGNED_BYTE
	{
		if (data_offset + n_elems > glb.size()) { fprintf(stderr, "error: data out of range\n"); return false; }
		for (size_t k = 0; k < n_elems; k++) pts[k] = (float)data[data_offset + k];
		break;
	}
	default:
		fprintf(stderr, "error: unsupported componentType %d\n", component_type);
		return false;
	}
	return true;
}

int main(int argc, char **argv)
{
	if (argc < 2)
	{
		fprintf(stderr, "usage: %s <file.glb>\n", argv[0]);
		return 1;
	}

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
	// Run the extractor against a view of the BIN chunk.
	std::vector<char> bin_view(bin_data, bin_data + bin_size);
	if (!ExtractPositions(bin_view, json, pts))
		return 1;

	int num_pts = (int)(pts.size() / 3);

	// Compute the convex hull and the minimum-volume OBB.
	Hull3 hull = convex_hull(pts.data(), num_pts, 12);
	OBB obb = minobb(pts.data(), num_pts, 12);

	// Print the results as a single JSON document.
	printf("{\n");
	printf("  \"vertices\": %d,\n", num_pts);

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
