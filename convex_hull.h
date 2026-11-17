// convex_hull.h
//
// Exact 3D convex hull of single-precision (f32) point sets, self-contained.
//
// convex_hull() returns the true convex hull of the input floats, not an
// epsilon approximation of it: all geometric decisions are made by predicates
// whose sign is exact (a floating point filter that falls back to exact
// arithmetic when it cannot certify the sign). Hence the result is always a
// valid closed convex polyhedron, whatever the input: coplanar grids, sliver
// triangles, duplicate points, wildly varying magnitudes...

#pragma once

#include <vector>

// A minimal 3-component float vector.
struct vec3
{
	float x, y, z;

	vec3() : x(0.f), y(0.f), z(0.f) {}
	vec3(float _x, float _y, float _z) : x(_x), y(_y), z(_z) {}

	vec3 operator + (const vec3 &b) const { return vec3(x + b.x, y + b.y, z + b.z); }
	vec3 operator - (const vec3 &b) const { return vec3(x - b.x, y - b.y, z - b.z); }
	vec3 operator * (float s) const { return vec3(x * s, y * s, z * s); }
	vec3 operator - () const { return vec3(-x, -y, -z); }
	bool operator == (const vec3 &b) const { return x == b.x && y == b.y && z == b.z; }

	vec3 &operator += (const vec3 &b) { x += b.x; y += b.y; z += b.z; return *this; }
	vec3 &operator -= (const vec3 &b) { x -= b.x; y -= b.y; z -= b.z; return *this; }
	vec3 &operator *= (float s) { x *= s; y *= s; z *= s; return *this; }

	float &operator[](int i) { float *p = &x; return p[i]; }
	float operator[](int i) const { const float *p = &x; return p[i]; }
};

// A convex hull: vertices `v` and convex polygonal faces `f` (indices into
// `v`), wound counterclockwise when seen from outside.
//
// The faces are the actual facets of the hull: exactly coplanar triangles are
// merged into a single polygon, so no two adjacent faces are coplanar and
// every vertex is a true corner (extreme point). For points in general
// position all faces are triangles. Fan-triangulate from f[i][0] if triangles
// are needed.
struct Hull3
{
	std::vector<vec3> v;             // Hull vertices (a subset of the input points, bit for bit).
	std::vector<std::vector<int>> f; // Hull faces, counterclockwise from outside.
	bool degenerate = false;

	// True if the input was planar, collinear, or a single point, i.e. the hull
	// is not a solid polyhedron. In that case v/f hold the lower dimensional
	// hull: a flat convex polygon (its corners + one face listing them), a line
	// segment (two endpoints, no faces), or a single point.
	bool IsDegenerate() const { return degenerate; }
};

// Computes the convex hull of the point set.
//
// `pts` points to an array of `num_pts` xyz point triples in floats.
// `stride_bytes` is the byte stride between consecutive points (e.g. 12 for
// tightly packed floats, or larger if the points are embedded in a struct).
// Non-finite points (NaN/Inf) are ignored, duplicate points are harmless.
//
// The hull is degenerate (IsDegenerate() == true) if the points are exactly
// coplanar or collinear, or there are fewer than 4 distinct points.
//
// Runs in O(n log n) typical time (Quickhull). Thread safe.
Hull3 convex_hull(const float *pts, int num_pts, int stride_bytes);
