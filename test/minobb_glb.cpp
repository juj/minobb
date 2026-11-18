// test/minobb_glb.cpp
//
// Usage: minobb_glb <file.glb> [max_points]
//
// Opens the GLB file given in argv[1], collects the POSITION vertices of
// every primitive in the scene, transforms them into scene (world) space
// using the glTF node graph, computes the convex hull, the minimum-volume
// OBB with minobb() (with its default tolerance: the box can be that much
// larger than the minimum) and the minimum enclosing sphere with minsphere(),
// and prints them as a JSON document to stdout.
//
// max_points (optional, 0 = no cap): the input may be reduced to at most
// max_points with a deterministic uniform world-space grid (one point per
// occupied cell). The reported "vertices" count is the number of points
// actually used.
//
// Only dependencies: the C++ standard library, minobb.{h,cpp}, minsphere.{h,cpp},
// convex_hull.{h,cpp} and glb.{h,cpp}.

#define NOMINMAX
#define _CRT_SECURE_NO_WARNINGS

#include "minobb.h"
#include "minsphere.h"
#include "glb.h"
#include <windows.h>
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <unordered_set>
#include <vector>

// ---------------------------------------------------------------------------
// High-resolution timing (Windows QueryPerformanceCounter).
// ---------------------------------------------------------------------------

static double NowSeconds()
{
	static LARGE_INTEGER freq = {};
	if (freq.QuadPart == 0)
		QueryPerformanceFrequency(&freq);
	LARGE_INTEGER cnt;
	QueryPerformanceCounter(&cnt);
	return (double)cnt.QuadPart / (double)freq.QuadPart;
}

// Returns the time that one call of f() takes, in seconds. A call that takes
// less than a few milliseconds is repeated for that long, and the fastest run
// counts; calls that are too fast for the timer are timed in batches.
template<typename F>
static double TimeCall(F f)
{
	double best = INFINITY, total = 0;
	int batch = 1;
	for (int run = 0; run < 64 && total < 0.005; ++run)
	{
		const double t0 = NowSeconds();
		for (int i = 0; i < batch; ++i)
			f();
		const double t = NowSeconds() - t0;
		total += t;
		if (t < 1e-4 && batch < (1 << 20))
			batch *= 4;
		else
			best = std::min(best, t / batch);
	}
	return best;
}

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

int main(int argc, char **argv)
{
	if (argc < 2)
	{
		fprintf(stderr, "usage: %s <file.glb> [max_points]\n", argv[0]);
		return 1;
	}
	const size_t max_points = (argc >= 3) ? strtoull(argv[2], nullptr, 10) : 0;

	// Collect the world space POSITION vertices of the scene.
	double tLoad0 = NowSeconds();
	std::vector<float> pts;
	std::string error;
	if (!glb_read_positions(argv[1], pts, error) || pts.empty())
	{
		fprintf(stderr, "error: %s\n", error.empty() ? "no POSITION vertices found in the scene" : error.c_str());
		return 1;
	}
	fprintf(stderr, "info: load: %.3fs\n", NowSeconds() - tLoad0);

	const int total_pts = (int)(pts.size() / 3);

	// AABB #1: over all original world-space vertices (before any subsampling).
	vec3 aabb_v_min(pts[0], pts[1], pts[2]), aabb_v_max(aabb_v_min);
	for (int i = 0; i < total_pts; i++)
	{
		const vec3 p(pts[3 * i], pts[3 * i + 1], pts[3 * i + 2]);
		aabb_v_min.x = std::min(aabb_v_min.x, p.x);
		aabb_v_min.y = std::min(aabb_v_min.y, p.y);
		aabb_v_min.z = std::min(aabb_v_min.z, p.z);
		aabb_v_max.x = std::max(aabb_v_max.x, p.x);
		aabb_v_max.y = std::max(aabb_v_max.y, p.y);
		aabb_v_max.z = std::max(aabb_v_max.z, p.z);
	}

	SubsampleGrid(pts, max_points);

	int num_pts = (int)(pts.size() / 3);
	fprintf(stderr, "info: %d world-space points\n", total_pts);
	if (num_pts < total_pts)
		fprintf(stderr, "info: subsampled to %d points (uniform grid, max_points=%zu)\n",
			num_pts, max_points);

	// Compute the convex hull, then the minimum-volume OBB from it (two-pass
	// API; timed with QueryPerformanceCounter, the times go into the JSON).
	Hull3 hull;
	OBB obb;
	const double hull_sec = TimeCall([&] { hull = convex_hull(pts.data(), num_pts, 12); });
	const double obb_sec = TimeCall([&] { obb = minobb(hull); });
	fprintf(stderr, "info: hull: %zu verts, %zu faces (%.3fs)\n",
		hull.v.size(), hull.f.size(), hull_sec);
	if (obb.IsDegenerate())
		fprintf(stderr, "info: obb: none, minobb() returned a degenerate box (%.3fs)\n", obb_sec);
	else
		fprintf(stderr, "info: obb: volume %g (%.3fs)\n", obb.Volume(), obb_sec);

	// The minimum enclosing sphere, computed from the points. It does not need
	// the hull: the time of computing it from the vertices of the hull instead
	// (which gives the same sphere) is measured for comparison.
	Sphere sphere, hull_sphere;
	const double sphere_sec = TimeCall([&] { sphere = minsphere(pts.data(), num_pts, 12); });
	const double sphere_hull_sec = TimeCall([&] { hull_sphere = minsphere(hull); });
	if (sphere.IsDegenerate())
		fprintf(stderr, "info: sphere: none, minsphere() returned a degenerate sphere (%.6fs)\n", sphere_sec);
	else
		fprintf(stderr, "info: sphere: radius %g, through %d of the points (%.6fs, from the hull %.6fs)\n",
			sphere.r, sphere.numSupport, sphere_sec, sphere_hull_sec);

	// Print the results as a single JSON document.
	printf("{\n");
	printf("  \"vertices\": %d,\n", num_pts);
	if (num_pts < total_pts)
		printf("  \"subsampled_from\": %d,\n", total_pts);
	printf("  \"timing\": {\n");
	printf("    \"hull_sec\": %.9f,\n", hull_sec);
	printf("    \"obb_sec\": %.9f,\n", obb_sec);
	printf("    \"sphere_sec\": %.9f,\n", sphere_sec);
	printf("    \"sphere_hull_sec\": %.9f\n", sphere_hull_sec);
	printf("  },\n");

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

	// AABB #2: over the convex hull vertices only.
	vec3 aabb_h_min(0.f, 0.f, 0.f), aabb_h_max(0.f, 0.f, 0.f);
	if (!hull.v.empty())
	{
		aabb_h_min = aabb_h_max = hull.v[0];
		for (const vec3 &p : hull.v)
		{
			aabb_h_min.x = std::min(aabb_h_min.x, p.x);
			aabb_h_min.y = std::min(aabb_h_min.y, p.y);
			aabb_h_min.z = std::min(aabb_h_min.z, p.z);
			aabb_h_max.x = std::max(aabb_h_max.x, p.x);
			aabb_h_max.y = std::max(aabb_h_max.y, p.y);
			aabb_h_max.z = std::max(aabb_h_max.z, p.z);
		}
	}
	auto print_aabb = [](const char *name, const vec3 &mn, const vec3 &mx) {
		printf("  \"%s\": {\n", name);
		printf("    \"min\": [%.9g, %.9g, %.9g],\n", mn.x, mn.y, mn.z);
		printf("    \"max\": [%.9g, %.9g, %.9g],\n", mx.x, mx.y, mx.z);
		printf("    \"center\": [%.9g, %.9g, %.9g],\n",
			mn.x + (mx.x - mn.x) * 0.5f, mn.y + (mx.y - mn.y) * 0.5f, mn.z + (mx.z - mn.z) * 0.5f);
		printf("    \"size\": [%.9g, %.9g, %.9g],\n", mx.x - mn.x, mx.y - mn.y, mx.z - mn.z);
		printf("    \"volume\": %.9g\n", (mx.x - mn.x) * (mx.y - mn.y) * (mx.z - mn.z));
		printf("  },\n");
	};
	print_aabb("aabb_vertices", aabb_v_min, aabb_v_max);
	print_aabb("aabb_hull", aabb_h_min, aabb_h_max);

	// A degenerate box (minobb() returned none) has nothing else to print:
	// its size and volume are not valid JSON numbers.
	printf("  \"obb\": {\n");
	if (obb.IsDegenerate())
		printf("    \"degenerate\": true\n");
	else
	{
		printf("    \"degenerate\": false,\n");
		printf("    \"center\": [%.9g, %.9g, %.9g],\n", obb.pos.x, obb.pos.y, obb.pos.z);
		printf("    \"half_extents\": [%.9g, %.9g, %.9g],\n", obb.r.x, obb.r.y, obb.r.z);
		printf("    \"size\": [%.9g, %.9g, %.9g],\n", 2.f * obb.r.x, 2.f * obb.r.y, 2.f * obb.r.z);
		printf("    \"axes\": [");
		for (int i = 0; i < 3; i++)
			printf("%s\n      [%.9g, %.9g, %.9g]", i ? "," : "", obb.axis[i].x, obb.axis[i].y, obb.axis[i].z);
		printf("\n    ],\n");
		printf("    \"volume\": %.9g\n", obb.Volume());
	}
	printf("  },\n");

	// The minimum enclosing sphere, with its support points: the two to four
	// input points that it passes through and that determine it.
	printf("  \"sphere\": {\n");
	if (sphere.IsDegenerate())
		printf("    \"degenerate\": true\n");
	else
	{
		printf("    \"degenerate\": false,\n");
		printf("    \"center\": [%.9g, %.9g, %.9g],\n", sphere.pos.x, sphere.pos.y, sphere.pos.z);
		printf("    \"radius\": %.9g,\n", sphere.r);
		printf("    \"volume\": %.9g,\n", sphere.Volume());
		printf("    \"support\": [");
		for (int i = 0; i < sphere.numSupport; i++)
		{
			const float *p = &pts[3 * (size_t)sphere.support[i]];
			printf("%s\n      [%.9g, %.9g, %.9g]", i ? "," : "", p[0], p[1], p[2]);
		}
		printf("\n    ]\n");
	}
	printf("  }\n");
	printf("}\n");

	return 0;
}
