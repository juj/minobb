// web/calculator.cpp
//
// The WebAssembly side of site/calculator.js, which site/view.html uses to
// compute the convex hull, the minimum-volume OBB and the axis-aligned
// bounding box of a model in the browser. Built with Emscripten by
// build_viewer.py; web/calculator_api.js is the JavaScript side.
//
// The results are the same numbers that test/minobb_glb.cpp prints as JSON,
// computed with the same float arithmetic.

#include "minobb.h"
#include <emscripten.h>
#include <algorithm>
#include <cmath>
#include <vector>

// The layout of the array that calculator_compute() returns. Everything in it
// is a double: the counts and flags are small integers, the coordinates are
// floats. Keep in sync with web/calculator_api.js.
enum
{
	R_NUM_HULL_VERTICES = 0,
	R_NUM_HULL_FACES,
	R_NUM_FACE_INTS,   // Length of the array of calculator_hull_faces().
	R_HULL_DEGENERATE, // 1 if the hull is flat (planar, collinear or a single point).
	R_OBB_DEGENERATE,  // 1 if minobb() returned no box (there were no finite points).
	R_HULL_SEC,
	R_OBB_SEC,
	R_AABB_VERTICES,                  // 13 numbers: min, max, center, size (3 each), volume.
	R_AABB_HULL = R_AABB_VERTICES + 13, // The same of the hull vertices.
	R_OBB = R_AABB_HULL + 13,         // 19 numbers: center, half extents, size, axes (3 x 3), volume.
	R_COUNT = R_OBB + 19
};

static double result[R_COUNT];
static Hull3 hull;
static std::vector<int> hullFaces; // Of each face: the number of its vertices, then their indices.

// Returns the time that one call of f() takes, in seconds. A call that takes
// less than a few milliseconds is repeated for some ten milliseconds, and the
// fastest run counts; calls that are fast are timed in batches. (This is
// TimeCall() of test/minobb_glb.cpp, for a coarser timer: that of a browser
// ticks every 0.1 ms, so a batch has to take milliseconds to be measured.)
template<typename F>
static double TimeCall(F f)
{
	double best = INFINITY, total = 0;
	int batch = 1;
	for (int run = 0; run < 64 && total < 0.01; ++run)
	{
		const double t0 = emscripten_get_now();
		for (int i = 0; i < batch; ++i)
			f();
		const double t = (emscripten_get_now() - t0) * 1e-3;
		total += t;
		if (t < 2e-3 && batch < (1 << 20))
			batch *= 4;
		else
			best = std::min(best, t / batch);
	}
	return best;
}

static void WriteAABB(double *out, const vec3 &mn, const vec3 &mx)
{
	const float values[13] = {
		mn.x, mn.y, mn.z,
		mx.x, mx.y, mx.z,
		mn.x + (mx.x - mn.x) * 0.5f, mn.y + (mx.y - mn.y) * 0.5f, mn.z + (mx.z - mn.z) * 0.5f,
		mx.x - mn.x, mx.y - mn.y, mx.z - mn.z,
		(mx.x - mn.x) * (mx.y - mn.y) * (mx.z - mn.z)
	};
	std::copy(values, values + 13, out);
}

extern "C" {

// Computes the convex hull of the `numPoints` packed xyz float triples at
// `points`, and its minimum-volume OBB to within `tolerance` (see minobb.h).
// Returns an array of R_COUNT doubles, which stays valid until the next call.
EMSCRIPTEN_KEEPALIVE const double *calculator_compute(const float *points, int numPoints, float tolerance)
{
	OBB obb;
	result[R_HULL_SEC] = TimeCall([&] { hull = convex_hull(points, numPoints, 3 * sizeof(float)); });
	result[R_OBB_SEC] = TimeCall([&] { obb = minobb(hull, tolerance); });

	hullFaces.clear();
	for (const std::vector<int> &face : hull.f)
	{
		hullFaces.push_back((int)face.size());
		hullFaces.insert(hullFaces.end(), face.begin(), face.end());
	}
	result[R_NUM_HULL_VERTICES] = (double)hull.v.size();
	result[R_NUM_HULL_FACES] = (double)hull.f.size();
	result[R_NUM_FACE_INTS] = (double)hullFaces.size();
	result[R_HULL_DEGENERATE] = hull.IsDegenerate() ? 1 : 0;
	result[R_OBB_DEGENERATE] = obb.IsDegenerate() ? 1 : 0;

	// The box of all the points. (convex_hull() ignores the points that are
	// not finite, and so does this.)
	bool any = false;
	vec3 mn, mx;
	for (int i = 0; i < numPoints; ++i)
	{
		const vec3 p(points[3 * i], points[3 * i + 1], points[3 * i + 2]);
		if (!std::isfinite(p.x) || !std::isfinite(p.y) || !std::isfinite(p.z))
			continue;
		if (!any)
			mn = mx = p;
		any = true;
		mn.x = std::min(mn.x, p.x); mn.y = std::min(mn.y, p.y); mn.z = std::min(mn.z, p.z);
		mx.x = std::max(mx.x, p.x); mx.y = std::max(mx.y, p.y); mx.z = std::max(mx.z, p.z);
	}
	WriteAABB(result + R_AABB_VERTICES, mn, mx);

	// The box of the hull vertices.
	mn = mx = hull.v.empty() ? vec3() : hull.v[0];
	for (const vec3 &p : hull.v)
	{
		mn.x = std::min(mn.x, p.x); mn.y = std::min(mn.y, p.y); mn.z = std::min(mn.z, p.z);
		mx.x = std::max(mx.x, p.x); mx.y = std::max(mx.y, p.y); mx.z = std::max(mx.z, p.z);
	}
	WriteAABB(result + R_AABB_HULL, mn, mx);

	double *o = result + R_OBB;
	std::fill(o, o + 19, 0.0);
	if (!obb.IsDegenerate())
	{
		const float values[19] = {
			obb.pos.x, obb.pos.y, obb.pos.z,
			obb.r.x, obb.r.y, obb.r.z,
			2.f * obb.r.x, 2.f * obb.r.y, 2.f * obb.r.z,
			obb.axis[0].x, obb.axis[0].y, obb.axis[0].z,
			obb.axis[1].x, obb.axis[1].y, obb.axis[1].z,
			obb.axis[2].x, obb.axis[2].y, obb.axis[2].z,
			obb.Volume()
		};
		std::copy(values, values + 19, o);
	}
	return result;
}

// The vertices of the hull of the last calculator_compute(): packed xyz float triples.
EMSCRIPTEN_KEEPALIVE const float *calculator_hull_vertices()
{
	return hull.v.empty() ? nullptr : &hull.v[0].x;
}

// The faces of the hull of the last calculator_compute(): of each face the
// number of its vertices, followed by their indices (counterclockwise from outside).
EMSCRIPTEN_KEEPALIVE const int *calculator_hull_faces()
{
	return hullFaces.data();
}

}
