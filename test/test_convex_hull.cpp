// test/test_convex_hull.cpp
//
// Usage: test_convex_hull <file.glb | file.gltf | @name> [max_sample_points]
//        test_convex_hull --list
//
// Computes the convex hull of the vertex positions of a glTF file, or of the
// built-in synthetic point set @name (--list prints their names), verifies
// it, and prints the hull and the verdict as a JSON document to stdout. The
// JSON also carries up to max_sample_points (default 20000) of the input
// points, for visualization.
//
// The verification is exact, and independent of convex_hull.cpp: orientation
// tests that floating point cannot settle are decided with integer arithmetic
// on the float bit patterns. A (solid) hull passes iff
//   - its vertices are distinct input points,
//   - its faces are strictly convex planar polygons that form a closed
//     manifold, with no two adjacent faces coplanar,
//   - no input point is above the plane of any face,
// i.e. iff it is the convex hull of the input, with exactly its true vertices
// and facets.
//
// Exit status: 0 = the hull is correct, 1 = it is not, 2 = no input points.

#include "convex_hull.h"
#include "glb.h"

#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdarg>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>

typedef std::vector<vec3> Points;

// ---------------------------------------------------------------------------
// Exact orientation predicates.
// ---------------------------------------------------------------------------

// A fixed size two's complement integer, wide enough for the 3x3 determinants below.
struct Int
{
	enum { N = 28 };
	uint32_t w[N];

	Int() { memset(w, 0, sizeof w); }
	Int(float f) : Int() // The value of f * 2^149, which is an integer.
	{
		uint32_t u;
		memcpy(&u, &f, 4);
		const int exponent = (u >> 23) & 255, shift = exponent ? exponent - 1 : 0;
		const uint64_t mantissa = (uint64_t)((u & 0x7FFFFF) | (exponent ? 0x800000 : 0)) << (shift % 32);
		w[shift / 32] = (uint32_t)mantissa;
		w[shift / 32 + 1] = (uint32_t)(mantissa >> 32);
		if (u >> 31) *this = Int() - *this;
	}
	Int operator-(const Int &b) const
	{
		Int r;
		int64_t carry = 0;
		for (int i = 0; i < N; ++i)
		{
			carry += (int64_t)w[i] - b.w[i];
			r.w[i] = (uint32_t)carry;
			carry >>= 32;
		}
		return r;
	}
	Int operator+(const Int &b) const { return *this - (Int() - b); }
	Int operator*(const Int &b) const
	{
		Int r;
		for (int i = 0; i < N; ++i)
		{
			uint64_t carry = 0;
			for (int j = 0; w[i] && i + j < N; ++j)
			{
				carry += (uint64_t)w[i] * b.w[j] + r.w[i + j];
				r.w[i + j] = (uint32_t)carry;
				carry >>= 32;
			}
		}
		return r;
	}
	int sign() const
	{
		if (w[N - 1] >> 31) return -1;
		for (int i = 0; i < N; ++i)
			if (w[i]) return 1;
		return 0;
	}
};

// The sign of det[b-a, c-a] of the points projected along coordinate axis k:
// positive iff a, b, c wind counterclockwise about +k.
static int orient2d(int k, const vec3 &a, const vec3 &b, const vec3 &c)
{
	const int u = (k + 1) % 3, v = (k + 2) % 3;
	const double l = ((double)b[u] - a[u]) * ((double)c[v] - a[v]), r = ((double)b[v] - a[v]) * ((double)c[u] - a[u]);
	if (fabs(l - r) > 1e-14 * (fabs(l) + fabs(r))) return l > r ? 1 : -1; // Decided by a wide margin.
	if (l == 0 && r == 0) return 0;
	const Int au(a[u]), av(a[v]);
	return ((Int(b[u]) - au) * (Int(c[v]) - av) - (Int(b[v]) - av) * (Int(c[u]) - au)).sign();
}

// The sign of det[b-a, c-a, d-a]: positive iff d is above the plane of a, b,
// c, i.e. on the side from which a, b, c are seen winding counterclockwise.
static int orient3d(const vec3 &a, const vec3 &b, const vec3 &c, const vec3 &d)
{
	double det = 0, mag = 0;
	for (int k = 0, k1 = 1, k2 = 2; k < 3; k1 = k2, k2 = k++)
	{
		const double l = ((double)b[k1] - a[k1]) * ((double)c[k2] - a[k2]);
		const double r = ((double)b[k2] - a[k2]) * ((double)c[k1] - a[k1]);
		det += (l - r) * ((double)d[k] - a[k]);
		mag += (fabs(l) + fabs(r)) * fabs((double)d[k] - a[k]);
	}
	if (fabs(det) > 1e-14 * mag) return det > 0 ? 1 : -1; // Decided by a wide margin.
	if (mag == 0) return 0;
	Int u[3], v[3], w[3];
	for (int k = 0; k < 3; ++k)
	{
		u[k] = Int(b[k]) - Int(a[k]);
		v[k] = Int(c[k]) - Int(a[k]);
		w[k] = Int(d[k]) - Int(a[k]);
	}
	const Int x = u[1] * v[2] - u[2] * v[1], y = u[2] * v[0] - u[0] * v[2], z = u[0] * v[1] - u[1] * v[0];
	return (x * w[0] + y * w[1] + z * w[2]).sign();
}

static bool lex_less(const vec3 &a, const vec3 &b)
{
	return a.x != b.x ? a.x < b.x : a.y != b.y ? a.y < b.y : a.z < b.z;
}

// ---------------------------------------------------------------------------
// Verification.
// ---------------------------------------------------------------------------

// A bounding box tree of points, for finding the points on the upper side of a plane.
struct Tree
{
	struct Node { double lo[3], hi[3]; int begin, end, skip; };
	Points p;
	std::vector<Node> nodes;

	explicit Tree(const Points &points) : p(points) { if (!p.empty()) build(0, (int)p.size()); }

	void build(int begin, int end)
	{
		const size_t id = nodes.size();
		Node n = { { 0, 0, 0 }, { 0, 0, 0 }, begin, end, 0 };
		int widest = 0;
		for (int k = 0; k < 3; ++k)
		{
			n.lo[k] = n.hi[k] = p[begin][k];
			for (int i = begin; i < end; ++i)
			{
				n.lo[k] = std::min(n.lo[k], (double)p[i][k]);
				n.hi[k] = std::max(n.hi[k], (double)p[i][k]);
			}
			if (n.hi[k] - n.lo[k] > n.hi[widest] - n.lo[widest]) widest = k;
		}
		nodes.push_back(n);
		if (end - begin > 16)
		{
			const int mid = (begin + end) / 2;
			std::nth_element(p.begin() + begin, p.begin() + mid, p.begin() + end,
				[widest](const vec3 &a, const vec3 &b) { return a[widest] < b[widest]; });
			build(begin, mid);
			build(mid, end);
		}
		nodes[id].skip = (int)nodes.size();
	}

	// Calls visit(q) for (at least) all points q with n.(q - a) >= -margin.
	template<typename Visit> void above(const double n[3], const vec3 &a, double margin, Visit visit) const
	{
		for (int i = 0; i < (int)nodes.size();)
		{
			const Node &node = nodes[i];
			double h = 0;
			for (int k = 0; k < 3; ++k) h += std::max(n[k] * (node.lo[k] - a[k]), n[k] * (node.hi[k] - a[k]));
			if (h < -margin) { i = node.skip; continue; }
			if (node.skip == ++i)
				for (int j = node.begin; j < node.end; ++j) visit(p[j]);
		}
	}
};

static std::string format(const char *fmt, ...)
{
	char text[512];
	va_list args;
	va_start(args, fmt);
	vsnprintf(text, sizeof text, fmt, args);
	va_end(args);
	return text;
}

#define CHECK(condition, ...) do { if (!(condition)) return format(__VA_ARGS__); } while (0)

// Verifies a hull that claims the points to be coplanar, collinear, or all the same.
static std::string verify_degenerate(const Points &pts, const Hull3 &hull)
{
	const Points &v = hull.v;
	const int V = (int)v.size();
	CHECK(hull.f.size() == (V >= 3 ? 1u : 0u), "a degenerate hull of %d vertices has %d faces", V, (int)hull.f.size());
	CHECK(V > 0 || pts.empty(), "the hull is empty");
	if (V == 1)
		for (const vec3 &p : pts) CHECK(p == v[0], "the hull is a single point, the input is not");
	if (V == 2)
	{
		const vec3 &lo = v[lex_less(v[1], v[0])], &hi = v[lex_less(v[0], v[1])];
		for (const vec3 &p : pts)
		{
			for (int k = 0; k < 3; ++k)
				CHECK(orient2d(k, lo, hi, p) == 0, "the hull is a segment, but the input is not collinear");
			CHECK(!lex_less(p, lo) && !lex_less(hi, p), "an input point is outside of the segment");
		}
	}
	if (V < 3) return "";

	// A polygon: it must be strictly convex, and all points must be in its plane, on the inner side of its edges.
	const std::vector<int> &f = hull.f[0];
	CHECK((int)f.size() == V, "the polygon has %d corners for %d vertices", (int)f.size(), V);
	int k = 0, ccw = 0;
	for (; k < 3 && !ccw; k += !ccw) ccw = orient2d(k, v[f[0]], v[f[1]], v[f[2]]);
	CHECK(ccw, "the polygon is not strictly convex");
	for (int i = 0; i < V; ++i)
	{
		const vec3 &a = v[f[i]], &b = v[f[(i + 1) % V]];
		CHECK(orient2d(k, a, b, v[f[(i + 2) % V]]) == ccw, "the polygon is not strictly convex");
		for (const vec3 &p : pts) CHECK(orient2d(k, a, b, p) != -ccw, "an input point is outside of the polygon");
	}
	for (const vec3 &p : pts)
		CHECK(orient3d(v[f[0]], v[f[1]], v[f[2]], p) == 0, "the hull is flat, but the input is not coplanar");
	return "";
}

// Returns an empty string if `hull` is the convex hull of `pts`, else the reason why it is not.
static std::string verify(const Points &pts, const Hull3 &hull)
{
	const Points &v = hull.v;
	const int V = (int)v.size(), F = (int)hull.f.size();

	// The vertices are distinct input points.
	typedef std::array<uint32_t, 3> Bits;
	auto bits = [](const vec3 &p) { Bits b; memcpy(&b, &p, sizeof b); return b; };
	std::vector<Bits> input;
	for (const vec3 &p : pts) input.push_back(bits(p));
	std::sort(input.begin(), input.end());
	for (int i = 0; i < V; ++i)
		CHECK(std::binary_search(input.begin(), input.end(), bits(v[i])), "vertex %d is not an input point", i);
	Points sorted = v;
	std::sort(sorted.begin(), sorted.end(), lex_less);
	for (int i = 1; i < V; ++i) CHECK(!(sorted[i - 1] == sorted[i]), "the hull has duplicate vertices");

	// The faces are polygons over the vertices, each of which is used.
	std::vector<char> used(V, 0);
	for (int i = 0; i < F; ++i)
	{
		CHECK(hull.f[i].size() >= 3, "face %d has %d vertices", i, (int)hull.f[i].size());
		for (int j : hull.f[i])
		{
			CHECK(j >= 0 && j < V, "face %d refers to vertex %d of %d", i, j, V);
			used[j] = 1;
		}
	}
	for (int i = 0; i < V && F; ++i) CHECK(used[i], "vertex %d is not used by any face", i);
	if (hull.degenerate) return verify_degenerate(pts, hull);

	// The faces form a closed manifold: each directed edge exists once, and so does its opposite.
	struct Edge { uint64_t key; int face, pos; };
	auto before = [](const Edge &a, const Edge &b) { return a.key < b.key; };
	std::vector<Edge> edges;
	for (int i = 0; i < F; ++i)
		for (int j = 0, n = (int)hull.f[i].size(); j < n; ++j)
			edges.push_back({ (uint64_t)hull.f[i][j] << 32 | (uint32_t)hull.f[i][(j + 1) % n], i, j });
	std::sort(edges.begin(), edges.end(), before);
	for (size_t i = 1; i < edges.size(); ++i)
		CHECK(edges[i - 1].key != edges[i].key, "edge %d->%d is used by several faces",
			(int)(edges[i].key >> 32), (int)edges[i].key);
	const int euler = V - (int)edges.size() / 2 + F;
	CHECK(euler == 2, "Euler characteristic V-E+F is %d instead of 2", euler);

	double lo[3], hi[3];
	for (int k = 0; k < 3; ++k)
	{
		lo[k] = hi[k] = pts[0][k];
		for (const vec3 &p : pts)
		{
			lo[k] = std::min(lo[k], (double)p[k]);
			hi[k] = std::max(hi[k], (double)p[k]);
		}
	}
	const Tree tree(pts);
	for (int i = 0; i < F; ++i)
	{
		const std::vector<int> &f = hull.f[i];
		const int n = (int)f.size();
		const vec3 &a = v[f[0]], &b = v[f[1]], &c = v[f[2]];
		for (int j = 0; j < n; ++j)
		{
			// The face across each edge bends strictly down from the plane of this face...
			const Edge opposite = { (uint64_t)f[(j + 1) % n] << 32 | (uint32_t)f[j], 0, 0 };
			const auto e = std::lower_bound(edges.begin(), edges.end(), opposite, before);
			CHECK(e != edges.end() && e->key == opposite.key, "edge %d->%d of face %d has no opposite edge",
				f[j], f[(j + 1) % n], i);
			const vec3 &below = v[hull.f[e->face][(e->pos + 2) % hull.f[e->face].size()]];
			CHECK(orient3d(a, b, c, below) < 0, "faces %d and %d are coplanar, or meet at a concave edge", i, e->face);
			// ...in which this face is a strictly convex polygon.
			CHECK(orient3d(a, b, c, v[f[j]]) == 0, "face %d is not planar", i);
			CHECK(orient3d(v[f[j]], v[f[(j + 1) % n]], v[f[(j + 2) % n]], below) < 0, "face %d is not strictly convex", i);
		}

		// No input point is above the plane of the face. The tree prunes the points that are below it
		// by more than a (generous) bound for the rounding errors of evaluating the plane equation.
		double normal[3], margin = 0;
		for (int k = 0, k1 = 1, k2 = 2; k < 3; k1 = k2, k2 = k++)
		{
			const double l = ((double)b[k1] - a[k1]) * ((double)c[k2] - a[k2]);
			const double r = ((double)b[k2] - a[k2]) * ((double)c[k1] - a[k1]);
			normal[k] = l - r;
			margin += 1e-13 * (fabs(l) + fabs(r)) * std::max(a[k] - lo[k], hi[k] - a[k]);
		}
		int outside = 0;
		tree.above(normal, a, margin, [&](const vec3 &p) { outside += orient3d(a, b, c, p) > 0; });
		CHECK(!outside, "%d input points are outside of face %d", outside, i);
	}
	return "";
}

// ---------------------------------------------------------------------------
// Synthetic point sets: the degenerate and numerically nasty cases.
// ---------------------------------------------------------------------------

static float rnd() // Uniform in [0, 1).
{
	static uint32_t state = 1;
	state = state * 1664525u + 1013904223u;
	return (float)(state >> 8) / 16777216.f;
}

static vec3 rnd_in_ball()
{
	for (;;)
	{
		const vec3 p{ 2 * rnd() - 1, 2 * rnd() - 1, 2 * rnd() - 1 }; // (Braces: evaluated left to right.)
		if (p.x * p.x + p.y * p.y + p.z * p.z <= 1) return p;
	}
}

// The points (i, j, k) * scale + offset of the integer lattice [0, n]^3, rotated if `rotate` is set.
static Points lattice(int n, float scale = 1, float offset = 0, bool rotate = false)
{
	Points p;
	for (int i = 0; i <= n; ++i)
		for (int j = 0; j <= n; ++j)
			for (int k = 0; k <= n; ++k)
			{
				const vec3 q((float)i * scale + offset, (float)j * scale + offset, (float)k * scale + offset);
				const vec3 r(0.36f * q.x + 0.48f * q.y - 0.8f * q.z, -0.8f * q.x + 0.6f * q.y, 0.48f * q.x + 0.64f * q.y + 0.6f * q.z);
				p.push_back(rotate ? r : q);
			}
	return p;
}

// A small random point set that is degenerate in one of several ways.
static Points degenerate_points(int kind)
{
	Points p;
	const int range = 1 + (int)(rnd() * 6);
	auto r = [range] { return (float)((int)(rnd() * (float)(2 * range + 1)) - range); }; // An integer in [-range, range].
	for (int n = 1 + (int)(rnd() * (kind == 7 ? 300 : 40)); n > 0; --n)
	{
		vec3 q{ r(), r(), r() }; // Kind 0: a small lattice. The others:
		switch (kind)
		{
		case 1: q *= 0.1f; break;                                              // A lattice with rounding noise.
		case 2: q.z = (float)(rnd() < 0.5f); break;                            // Two parallel planes.
		case 3: q.z = -q.x - q.y + (float)(rnd() < 0.1f); break;               // Mostly on a tilted plane.
		case 4: q += vec3(1e7f, -3e6f, 16777216.f); break;                     // Far from the origin.
		case 5: for (int k = 0; k < 3; ++k) q[k] = ldexpf(q[k], (int)(rnd() * 240) - 140); break; // Wild magnitudes.
		case 6: q = vec3(q.x * 1.4e-45f, q.y * 1.4e-45f, q.z * 1e-38f); break; // Denormals.
		case 7: q.x += rnd() < 0.25f ? 1e-7f * q.y : 0; q.z = 3 * q.x + (rnd() < 0.25f ? q.z : 0); q.y = 2 * q.x; break; // Mostly collinear.
		}
		p.push_back(q);
	}
	return p;
}

struct Synthetic { const char *name; Points (*make)(); };

static const Synthetic synthetic[] = {
	{ "fuzz", [] { // 20000 small degenerate point sets: yields the first one whose hull is wrong, or else the last one.
		Points p;
		for (int i = 0; i < 20000; ++i)
		{
			p = degenerate_points(i % 8);
			if (!verify(p, convex_hull(&p[0].x, (int)p.size(), sizeof(vec3))).empty()) break;
		}
		return p; } },
	{ "tetrahedron", [] { return Points{ { 0, 0, 0 }, { 1, 0, 0 }, { 0, 1, 0 }, { 0, 0, 1 } }; } },
	{ "cube", [] { return lattice(1); } },
	// Lattices: nearly all points are exactly coplanar and collinear with several others.
	{ "grid", [] { return lattice(16); } },
	{ "grid_tenths", [] { return lattice(16, 0.1f); } },
	{ "grid_rotated", [] { return lattice(16, 1, 0, true); } },
	{ "grid_far_away", [] { return lattice(16, 1, 1e7f); } },
	{ "grid_denormal", [] { return lattice(6, 1.4e-45f); } },
	{ "grid_huge", [] { return lattice(6, 5e37f); } },
	{ "grid_duplicated", [] {
		Points p;
		for (int i = 0; i < 1000; ++i)
			for (const vec3 &q : lattice(1)) p.push_back(q);
		return p; } },
	{ "octahedron", [] { // Lattice points with |x| + |y| + |z| <= 12: the faces are not axis aligned.
		Points p;
		for (const vec3 &q : lattice(24, 1, -12))
			if (fabsf(q.x) + fabsf(q.y) + fabsf(q.z) <= 12) p.push_back(q);
		return p; } },
	{ "slab", [] { // A grid of points alternating between just above and just below the plane z = 0.
		Points p;
		for (int i = 0; i < 40; ++i)
			for (int j = 0; j < 40; ++j) p.push_back(vec3((float)i, (float)j, (i + j) % 2 ? 1e-30f : -1e-30f));
		return p; } },
	{ "cylinder", [] { // Two large exactly planar caps.
		Points p;
		for (int i = 0; i < 512; ++i)
		{
			const float angle = (float)(i / 2) * 0.0245437f;
			p.push_back(vec3(cosf(angle), sinf(angle), i % 2 ? 1.f : -1.f));
		}
		return p; } },
	{ "sphere", [] { // All points are hull vertices.
		Points p;
		while (p.size() < 20000)
		{
			const vec3 q = rnd_in_ball();
			const float length = sqrtf(q.x * q.x + q.y * q.y + q.z * q.z);
			if (length > 0.1f) p.push_back(q * (1 / length));
		}
		return p; } },
	{ "ball", [] { Points p; while (p.size() < 200000) p.push_back(rnd_in_ball()); return p; } },
	{ "moment_curve", [] { // A cyclic polytope: all points are vertices, with as many faces between them as possible.
		Points p;
		for (int i = 1; i <= 400; ++i) p.push_back(vec3((float)i, (float)i * (float)i, (float)i * (float)i * (float)i));
		return p; } },
	{ "wide_exponents", [] { // Coordinates of very different magnitudes: their differences are not exact even in doubles.
		Points p;
		while (p.size() < 5000)
		{
			float c[3];
			for (float &x : c)
			{
				const float mantissa = 2 * rnd() - 1;
				x = ldexpf(mantissa, (int)(rnd() * 120) - 60);
			}
			p.push_back(vec3(c[0], c[1], c[2]));
		}
		return p; } },
	{ "needle", [] { // Nearly collinear.
		Points p;
		while (p.size() < 5000)
		{
			const float t = rnd();
			p.push_back(vec3{ t + 1e-7f * rnd(), 2 * t + 1e-7f * rnd(), 3 * t + 1e-7f * rnd() });
		}
		return p; } },
	{ "non_finite", [] { // NaNs and infinities are to be ignored.
		Points p = lattice(4);
		for (size_t i = 0; i < p.size(); i += 7) p[i][i % 3] = i % 2 ? NAN : i % 4 ? INFINITY : -INFINITY;
		return p; } },
	// Degenerate hulls.
	{ "planar_axis_aligned", [] { Points p; while (p.size() < 5000) p.push_back(vec3{ rnd(), 0.5f, rnd() }); return p; } },
	{ "planar_tilted", [] { // Exactly on the plane x + y + z = 0.
		Points p;
		for (int i = -20; i <= 20; ++i)
			for (int j = -20; j <= 20; ++j)
				if (abs(i + j) <= 20) p.push_back(vec3((float)i, (float)j, (float)(-i - j)));
		return p; } },
	{ "planar_disc_rotated", [] { // Nearly but not exactly planar: a paper thin solid.
		Points p;
		while (p.size() < 5000)
		{
			const vec3 q = rnd_in_ball();
			p.push_back(vec3(0.36f * q.x + 0.48f * q.y, -0.8f * q.x + 0.6f * q.y, 0.48f * q.x + 0.64f * q.y));
		}
		return p; } },
	{ "triangle", [] {
		return Points{ { 0, 0, 0 }, { 1, 0, 0 }, { 0, 1, 0 }, { 0.25f, 0.25f, 0 }, { 0.5f, 0.5f, 0 }, { 0.5f, 0, 0 } }; } },
	{ "collinear", [] {
		Points p;
		for (int i = -50; i <= 50; ++i)
		{
			const float t = (float)(i * i % 37);
			p.push_back(vec3(t, 2 * t, 3 * t));
		}
		return p; } },
	{ "two_points", [] { return Points{ { 1, 2, 3 }, { -1, 2, 3 }, { 1, 2, 3 } }; } },
	{ "point", [] { return Points(10, vec3(1, 2, 3)); } },
};

// ---------------------------------------------------------------------------

static double seconds()
{
	return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

int main(int argc, char **argv)
{
	const std::string name = argc > 1 ? argv[1] : "";
	const size_t max_sample = argc > 2 ? strtoull(argv[2], nullptr, 10) : 20000;
	if (name.empty() || name == "--list")
	{
		for (const Synthetic &s : synthetic) printf("@%s\n", s.name);
		return 0;
	}

	// Load the input points. The synthetic ones are passed to convex_hull() with a stride and an offset.
	const double t0 = seconds();
	std::vector<float> data;
	std::string error;
	int stride = 3;
	if (name[0] == '@')
	{
		stride = 5;
		for (const Synthetic &s : synthetic)
			if (name.substr(1) == s.name)
				for (const vec3 &p : s.make()) data.insert(data.end(), { 0, p.x, p.y, p.z, 0 });
		if (data.empty()) error = "unknown synthetic point set";
	}
	else if (!glb_read_positions(name.c_str(), data, error)) data.clear();
	else if (data.empty()) error = "the file has no vertex positions";
	const float *xyz = data.data() + (stride == 5);
	const int count = (int)(data.size() / stride);
	Points pts;
	for (int i = 0; i < count; ++i)
	{
		const vec3 p(xyz[i * stride], xyz[i * stride + 1], xyz[i * stride + 2]);
		if (std::isfinite(p.x) && std::isfinite(p.y) && std::isfinite(p.z)) pts.push_back(p);
	}

	const double t1 = seconds();
	const Hull3 hull = convex_hull(xyz, count, stride * (int)sizeof(float));
	const double t2 = seconds();
	if (error.empty()) error = verify(pts, hull);
	const double t3 = seconds();

	// Volume and surface area, relative to the first vertex for accuracy.
	double volume = 0, area = 0;
	for (const std::vector<int> &f : hull.f)
		for (size_t i = 1; i + 1 < f.size(); ++i)
		{
			double a[3], b[3], c[3], n[3];
			for (int k = 0; k < 3; ++k)
			{
				a[k] = (double)hull.v[f[0]][k] - hull.v[0][k];
				b[k] = (double)hull.v[f[i]][k] - hull.v[f[0]][k];
				c[k] = (double)hull.v[f[i + 1]][k] - hull.v[f[0]][k];
			}
			for (int k = 0, k1 = 1, k2 = 2; k < 3; k1 = k2, k2 = k++) n[k] = b[k1] * c[k2] - b[k2] * c[k1];
			volume += (a[0] * n[0] + a[1] * n[1] + a[2] * n[2]) / 6;
			area += sqrt(n[0] * n[0] + n[1] * n[1] + n[2] * n[2]) / 2;
		}

	printf("{\n\"points\": %d,\n\"finite_points\": %d,\n\"ok\": %s,\n\"error\": \"",
		count, (int)pts.size(), error.empty() ? "true" : "false");
	for (char c : error) printf(c == '"' || c == '\\' ? "\\%c" : "%c", (unsigned char)c < 32 ? ' ' : c);
	printf("\",\n\"seconds\": {\"load\": %.6f, \"hull\": %.6f, \"verify\": %.6f},\n", t1 - t0, t2 - t1, t3 - t2);
	printf("\"degenerate\": %s,\n\"volume\": %.9g,\n\"area\": %.9g,\n\"vertices\": [",
		hull.degenerate ? "true" : "false", volume, area);
	for (size_t i = 0; i < hull.v.size(); ++i)
		printf("%s%.9g,%.9g,%.9g", i ? ",\n" : "\n", hull.v[i].x, hull.v[i].y, hull.v[i].z);
	printf("],\n\"faces\": [");
	for (size_t i = 0; i < hull.f.size(); ++i)
	{
		printf(i ? ",\n[" : "\n[");
		for (size_t j = 0; j < hull.f[i].size(); ++j) printf(j ? ",%d" : "%d", hull.f[i][j]);
		printf("]");
	}
	printf("],\n\"sample\": [");
	const size_t step = std::max<size_t>((pts.size() + max_sample - 1) / std::max<size_t>(max_sample, 1), 1);
	for (size_t i = 0; i < pts.size() && max_sample; i += step)
		printf("%s%.9g,%.9g,%.9g", i ? ",\n" : "\n", pts[i].x, pts[i].y, pts[i].z);
	printf("]\n}\n");
	return error.empty() ? 0 : pts.empty() ? 2 : 1;
}
