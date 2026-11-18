// glb.cpp
//
// See glb.h. The file may come from anywhere, so nothing in it is trusted:
// every index and byte range is checked before use.

#define _CRT_SECURE_NO_WARNINGS

#include "glb.h"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

namespace
{

struct Json
{
	enum Type { Null, Bool, Number, String, Array, Object } type = Null;
	double num = 0;                // Number or Bool value.
	std::string str;               // String value.
	std::vector<Json> items;       // Array elements, or Object values...
	std::vector<std::string> keys; // ...and their keys.

	// Member and element access. Anything that does not exist reads as Null.
	const Json &operator[](const char *key) const
	{
		for (size_t i = 0; i < keys.size(); ++i)
			if (keys[i] == key) return items[i];
		return null();
	}
	const Json &at(long long i) const { return type == Array && i >= 0 && i < (long long)items.size() ? items[i] : null(); }
	static const Json &null() { static const Json j; return j; }

	// The value as a non-negative integer (an index, count or offset; clamped to 9e15), or `def` if it is not one.
	long long uint(long long def = -1) const { return type == Number && num >= 0 ? (long long)std::min(num, 9e15) : def; }
	double number(double def) const { return type == Number ? num : def; }
};

// Recursive descent JSON parser over NUL-terminated text.
struct Parser
{
	const char *s;
	bool ok = true;
	int depth = 0;

	char peek()
	{
		while (*s == ' ' || *s == '\t' || *s == '\n' || *s == '\r') ++s;
		return *s;
	}
	bool eat(char c) { return peek() == c ? ++s, true : false; }

	std::string string()
	{
		std::string out;
		ok = ok && eat('"');
		for (; ok && *s != '"'; ++s)
		{
			if (*s == '\\' && *++s == 'u') // Escapes are only decoded as far as glTF needs.
			{
				char hex[5] = {};
				strncpy(hex, s + 1, 4);
				s += strlen(hex);
				out += (char)std::min(strtol(hex, nullptr, 16), 127L);
			}
			else if (*s) out += *s;
			else ok = false;
		}
		if (ok) ++s;
		return out;
	}

	Json value()
	{
		Json v;
		const char c = peek(), close = c == '{' ? '}' : ']';
		if (++depth > 200) ok = false;
		else if (c == '{' || c == '[')
		{
			++s;
			v.type = c == '{' ? Json::Object : Json::Array;
			while (ok && peek() != close)
			{
				if (c == '{')
				{
					v.keys.push_back(string());
					ok = ok && eat(':');
				}
				v.items.push_back(value());
				ok = ok && (eat(',') || peek() == close);
			}
			ok = ok && eat(close);
		}
		else if (c == '"') { v.type = Json::String; v.str = string(); }
		else if (!strncmp(s, "true", 4)) { v.type = Json::Bool; v.num = 1; s += 4; }
		else if (!strncmp(s, "false", 5)) { v.type = Json::Bool; s += 5; }
		else if (!strncmp(s, "null", 4)) s += 4;
		else
		{
			char *end;
			v.type = Json::Number;
			v.num = strtod(s, &end);
			ok = ok && end != s;
			s = end;
		}
		--depth;
		return v;
	}
};

bool read_file(const std::string &path, std::string &out)
{
	FILE *f = fopen(path.c_str(), "rb");
	if (!f) return false;
	char chunk[65536];
	for (size_t n; (n = fread(chunk, 1, sizeof chunk, f)) > 0;) out.append(chunk, n);
	fclose(f);
	return true;
}

std::string base64_decode(const char *s)
{
	std::string out;
	for (unsigned acc = 0, bits = 0; *s; ++s)
	{
		const char *digits = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
		const char *d = strchr(digits, *s);
		if (!d) continue; // Padding.
		acc = acc << 6 | (unsigned)(d - digits);
		if ((bits += 6) >= 8) out += (char)(acc >> (bits -= 8));
	}
	return out;
}

// An affine transform: the upper 3x4 part of a column-major 4x4 matrix.
struct Mat { double m[12]; };

Mat operator*(const Mat &a, const Mat &b)
{
	Mat r;
	for (int c = 0; c < 4; ++c)
		for (int i = 0; i < 3; ++i)
			r.m[c * 3 + i] = a.m[i] * b.m[c * 3] + a.m[3 + i] * b.m[c * 3 + 1] + a.m[6 + i] * b.m[c * 3 + 2]
				+ (c == 3 ? a.m[9 + i] : 0);
	return r;
}

// The local transform of a node: either a matrix, or a translation * rotation * scale.
Mat node_transform(const Json &node)
{
	const Json &matrix = node["matrix"], &t = node["translation"], &r = node["rotation"], &s = node["scale"];
	Mat m;
	if (matrix.items.size() == 16)
	{
		for (int i = 0; i < 12; ++i) m.m[i] = matrix.at(i / 3 * 4 + i % 3).number(0);
		return m;
	}
	const bool rotated = r.items.size() == 4;
	const double x = rotated ? r.at(0).number(0) : 0, y = rotated ? r.at(1).number(0) : 0;
	const double z = rotated ? r.at(2).number(0) : 0, w = rotated ? r.at(3).number(1) : 1;
	const double rotation[9] = {
		1 - 2 * (y * y + z * z), 2 * (x * y + z * w), 2 * (x * z - y * w),
		2 * (x * y - z * w), 1 - 2 * (x * x + z * z), 2 * (y * z + x * w),
		2 * (x * z + y * w), 2 * (y * z - x * w), 1 - 2 * (x * x + y * y) };
	for (int i = 0; i < 9; ++i) m.m[i] = rotation[i] * (s.items.size() == 3 ? s.at(i / 3).number(1) : 1);
	for (int i = 0; i < 3; ++i) m.m[9 + i] = t.items.size() == 3 ? t.at(i).number(0) : 0;
	return m;
}

template<typename T> double load(const char *p, double normalize)
{
	T v;
	memcpy(&v, p, sizeof v);
	return normalize ? std::max(v / normalize, -1.0) : (double)v;
}

// Decodes one accessor component of the given glTF componentType.
double component(const char *p, long long type, bool normalized)
{
	switch (type)
	{
	case 5120: return load<int8_t>(p, normalized ? 127 : 0);
	case 5121: return load<uint8_t>(p, normalized ? 255 : 0);
	case 5122: return load<int16_t>(p, normalized ? 32767 : 0);
	case 5123: return load<uint16_t>(p, normalized ? 65535 : 0);
	case 5125: return load<uint32_t>(p, 0);
	default: return load<float>(p, 0);
	}
}

// The elements of an accessor: `count` of them, each with a fixed number of components of one type.
struct Elements
{
	const char *data = nullptr;
	size_t count = 0, stride = 0, size = 0; // (size: the bytes of a component.)
	long long type = 0;                     // The glTF componentType.
	bool normalized = false;

	double get(size_t element, int k) const { return component(data + element * stride + k * size, type, normalized); }
};

enum AccessorStatus { Missing, Unsupported, OutOfBounds, Ok };

// Looks up the accessor of the given index and element type ("VEC3", "VEC4" or "MAT4"), and checks that all
// of its data is inside its buffer.
AccessorStatus read_accessor(const Json &root, const std::vector<std::string> &buffers, const Json &index, const char *type, Elements &e)
{
	const Json &accessor = root["accessors"].at(index.uint());
	if (accessor.type == Json::Null) return Missing;
	const Json &view = root["bufferViews"].at(accessor["bufferView"].uint());
	if (accessor["type"].str != type || view.type == Json::Null || accessor["sparse"].type != Json::Null) return Unsupported;

	const long long buffer = view["buffer"].uint();
	e.type = accessor["componentType"].uint();
	e.size = e.type == 5120 || e.type == 5121 ? 1 : e.type == 5122 || e.type == 5123 ? 2 : 4;
	e.count = (size_t)accessor["count"].uint(0);
	const size_t elementSize = (type[0] == 'M' ? 16 : type[3] - '0') * e.size;
	e.stride = std::max((size_t)view["byteStride"].uint(0), elementSize);
	const size_t offset = (size_t)view["byteOffset"].uint(0) + (size_t)accessor["byteOffset"].uint(0);
	const size_t available = buffer >= 0 && buffer < (long long)buffers.size() ? buffers[buffer].size() : 0;
	if (e.count && (available < elementSize || offset > available - elementSize
		|| e.count - 1 > (available - elementSize - offset) / e.stride))
		return OutOfBounds;
	e.data = e.count ? buffers[buffer].data() + offset : nullptr;
	e.normalized = accessor["normalized"].num != 0;
	return Ok;
}

} // ~namespace

bool glb_read_positions(const char *path, std::vector<float> &pts, std::string &error)
{
	auto fail = [&](const std::string &message) { error = message; return false; };

	// A .glb is a 12 byte header followed by chunks: the JSON text, and the binary
	// data of the first buffer. Anything else is taken to be the JSON text of a .gltf.
	std::string file, text, bin;
	if (!read_file(path, file)) return fail("cannot read the file");
	if (file.compare(0, 4, "glTF") != 0) text.swap(file);
	for (size_t pos = 12; pos + 8 <= file.size();)
	{
		uint32_t size, type;
		memcpy(&size, &file[pos], 4);
		memcpy(&type, &file[pos + 4], 4);
		pos += 8;
		if (size > file.size() - pos) return fail("truncated GLB chunk");
		if (type == 0x4E4F534A) text.assign(file, pos, size); // "JSON"
		if (type == 0x004E4942) bin.assign(file, pos, size);  // "BIN"
		pos += size;
	}

	Parser parser = { text.c_str() };
	const Json root = parser.value();
	if (!parser.ok || root.type != Json::Object) return fail("malformed glTF JSON");

	// Load the buffers.
	std::vector<std::string> buffers(root["buffers"].items.size());
	for (size_t i = 0; i < buffers.size(); ++i)
	{
		std::string uri = root["buffers"].at(i)["uri"].str, dir = path;
		if (root["buffers"].at(i)["uri"].type != Json::String) buffers[i].swap(bin);
		else if (uri.compare(0, 5, "data:") == 0) buffers[i] = base64_decode(uri.c_str() + std::min(uri.find(','), uri.size()));
		else
		{
			for (size_t j = 0; j + 2 < uri.size(); ++j) // Percent-decode.
				if (uri[j] == '%') uri.replace(j, 3, 1, (char)strtol(uri.substr(j + 1, 2).c_str(), nullptr, 16));
			dir.erase(dir.find_last_of("/\\") + 1);
			if (!read_file(dir + uri, buffers[i])) return fail("cannot read the buffer " + uri);
		}
	}

	// The roots of the default scene; in a file without scenes, the nodes that have no parent.
	const Json &nodes = root["nodes"], &scenes = root["scenes"];
	std::vector<char> visited(nodes.items.size(), 0);
	std::vector<std::pair<long long, Mat>> stack;
	const Mat identity = { { 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0 } };
	for (const Json &node : nodes.items)
		for (const Json &child : node["children"].items)
			if (nodes.at(child.uint()).type == Json::Object) visited[child.uint()] = 1;

	// The world transform of every node, for the joints of the skins: a walk over the whole hierarchy, from
	// the nodes that have no parent.
	std::vector<Mat> world(nodes.items.size(), identity);
	for (size_t i = 0; i < visited.size(); ++i)
		if (!visited[i]) stack.push_back({ (long long)i, identity });
	std::vector<char> placed(nodes.items.size(), 0);
	while (!stack.empty())
	{
		const long long index = stack.back().first;
		const Json &node = nodes.at(index);
		if (node.type != Json::Object || placed[index]) { stack.pop_back(); continue; }
		placed[index] = 1;
		world[index] = stack.back().second * node_transform(node);
		stack.pop_back();
		for (const Json &child : node["children"].items) stack.push_back({ child.uint(), world[index] });
	}

	for (size_t i = 0; i < visited.size(); ++i)
		if (scenes.items.empty() && !visited[i]) stack.push_back({ (long long)i, identity });
	for (const Json &node : scenes.at(root["scene"].uint(0))["nodes"].items) stack.push_back({ node.uint(), identity });
	visited.assign(visited.size(), 0);

	// Traverse the node hierarchy, collecting the positions of the meshes on the way.
	std::vector<Mat> jointMatrices;
	std::vector<Elements> joints, weights;
	while (!stack.empty())
	{
		const long long index = stack.back().first;
		const Json &node = nodes.at(index);
		if (node.type != Json::Object || visited[index]) { stack.pop_back(); continue; }
		visited[index] = 1;
		const Mat nodeToWorld = stack.back().second * node_transform(node);
		stack.pop_back();
		for (const Json &child : node["children"].items) stack.push_back({ child.uint(), nodeToWorld });

		// The mesh of a node with a skin is posed by the joints of the skin: each vertex goes where its joints
		// take it, by the transform of the joint node times the inverse bind matrix of the joint, weighted by
		// the weights of the vertex. (The transform of the node itself does not apply to such a mesh.) The
		// joints are where the nodes of the file have them: animations are not applied.
		const Json &skin = root["skins"].at(node["skin"].uint());
		jointMatrices.clear();
		if (skin.type == Json::Object)
		{
			Elements inverseBind;
			const AccessorStatus status = read_accessor(root, buffers, skin["inverseBindMatrices"], "MAT4", inverseBind);
			if (status == Unsupported || status == OutOfBounds || (status == Ok && inverseBind.type != 5126))
				return fail("unsupported inverse bind matrices of a skin");
			for (size_t j = 0; j < skin["joints"].items.size(); ++j)
			{
				const long long joint = skin["joints"].at((long long)j).uint();
				Mat bind = identity;
				if (status == Ok && j < inverseBind.count)
					for (int k = 0; k < 12; ++k) bind.m[k] = inverseBind.get(j, k / 3 * 4 + k % 3);
				jointMatrices.push_back((joint >= 0 && joint < (long long)world.size() ? world[joint] : identity) * bind);
			}
		}

		for (const Json &primitive : root["meshes"].at(node["mesh"].uint())["primitives"].items)
		{
			Elements positions;
			const AccessorStatus status = read_accessor(root, buffers, primitive["attributes"]["POSITION"], "VEC3", positions);
			if (status == Missing) continue;
			if (status == Unsupported) return fail("unsupported POSITION accessor (sparse or compressed data?)");
			if (status == OutOfBounds) return fail("POSITION data is out of the bounds of its buffer");

			// The joints and weights of the vertices: four of each per set, in the attributes JOINTS_0 and
			// WEIGHTS_0, JOINTS_1 and WEIGHTS_1, and so on.
			joints.clear();
			weights.clear();
			for (int set = 0; !jointMatrices.empty(); ++set)
			{
				Elements j, w;
				const AccessorStatus haveJoints = read_accessor(root, buffers, primitive["attributes"][("JOINTS_" + std::to_string(set)).c_str()], "VEC4", j);
				const AccessorStatus haveWeights = read_accessor(root, buffers, primitive["attributes"][("WEIGHTS_" + std::to_string(set)).c_str()], "VEC4", w);
				if (haveJoints == Missing || haveWeights == Missing) break;
				if (haveJoints != Ok || haveWeights != Ok || j.count < positions.count || w.count < positions.count)
					return fail("unsupported JOINTS or WEIGHTS accessor");
				joints.push_back(j);
				weights.push_back(w);
			}

			for (size_t i = 0; i < positions.count; ++i)
			{
				const double v[3] = { positions.get(i, 0), positions.get(i, 1), positions.get(i, 2) };
				double p[3] = { 0, 0, 0 }, total = 0;
				for (size_t set = 0; set < joints.size(); ++set)
					for (int k = 0; k < 4; ++k)
					{
						const double weight = weights[set].get(i, k), joint = joints[set].get(i, k);
						if (!(weight > 0) || !(joint < (double)jointMatrices.size())) continue;
						const Mat &m = jointMatrices[(size_t)joint];
						for (int c = 0; c < 3; ++c) p[c] += weight * (m.m[c] * v[0] + m.m[3 + c] * v[1] + m.m[6 + c] * v[2] + m.m[9 + c]);
						total += weight;
					}
				// (The weights of a vertex are to add up to one. Where they do not, they are scaled to; and a
				// vertex with no weight at all stays with the node, like the vertices of a mesh without a skin.)
				for (int c = 0; c < 3; ++c)
					pts.push_back((float)(total > 0 ? p[c] / total
						: nodeToWorld.m[c] * v[0] + nodeToWorld.m[3 + c] * v[1] + nodeToWorld.m[6 + c] * v[2] + nodeToWorld.m[9 + c]));
			}
		}
	}
	return true;
}
