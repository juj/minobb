// minobb.h
//
// Minimal-volume oriented bounding box (OBB), self-contained.
//
// Extracted from MathGeoLib's OBB::OptimalEnclosingOBB() (Jylanki 2015,
// "Optimal bounding boxes for non-triangular meshes", section 5).
//
// minobb() computes the (conjectured) minimum-volume OBB enclosing the given
// point set:
//   A) Three edges of the convex hull touch three mutually adjacent faces of the OBB.
//   B) Two edges touch two opposite faces of the OBB, and a third edge touches a
//      face adjacent to the two.
//   C) Two edges touch two faces of the OBB, where one of the OBB's faces is flush
//      with a whole face of the convex hull.
//
// The algorithm computes the exact convex hull of the input points and then
// enumerates the candidate box orientations implied by the contact configurations
// above (the paper's Theorem 7.1: the minimum-volume OBB touches at least three
// edges of the polyhedron, two of which touch two distinct faces of the OBB).
//
// Complexity: O(n^2) convex hull + O(E^3) configuration enumeration in the worst
// case (E = number of convex hull edges, E <= 3n/2). Intended for small to
// medium sized point sets, not for million-point meshes.
//
// Degenerate input (all points in a plane, on a line, or a single point) is
// handled by a 2D rotating-calipers / 1D fallback, producing a flat OBB.

#pragma once

#include <cmath>

// A minimal 3-component float vector.
struct vec3
{
	float x, y, z;

	vec3() : x(0.f), y(0.f), z(0.f) {}
	vec3(float _x, float _y, float _z) : x(_x), y(_y), z(_z) {}

	float Dot(const vec3 &b) const { return x*b.x + y*b.y + z*b.z; }

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

	static float Dot(const vec3 &a, const vec3 &b) { return a.x*b.x + a.y*b.y + a.z*b.z; }
	static vec3 Cross(const vec3 &a, const vec3 &b)
	{
		return vec3(a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x);
	}
};

inline vec3 operator * (float s, const vec3 &v) { return v * s; }
inline float Dot(const vec3 &a, const vec3 &b) { return vec3::Dot(a, b); }
inline vec3 Cross(const vec3 &a, const vec3 &b) { return vec3::Cross(a, b); }

// An oriented bounding box: center `pos`, half-extents `r`, orthonormal axes `axis[0..2]`.
// Same layout/semantics as MathGeoLib's OBB (a point p is inside if all
// components of LocalToOBB(p) = dot(axis[i], p - pos) are within [-r[i], r[i]]).
struct OBB
{
	vec3 pos;     // Center point of the OBB.
	vec3 r;       // Half extents along each axis. A component < 0 marks the OBB as invalid/degenerate.
	vec3 axis[3]; // Orthonormal basis (rows of the LocalToWorld rotation).

	float Volume() const { return (r.x * 2.f) * (r.y * 2.f) * (r.z * 2.f); }

	// True if the OBB is invalid (marker produced when the input is degenerate).
	bool IsDegenerate() const { return r.x < 0.f || r.y < 0.f || r.z < 0.f; }

	// Local space coordinates of a world space point.
	vec3 LocalToWorldInverse(const vec3 &p) const
	{
		vec3 d = p - pos;
		return vec3(vec3::Dot(axis[0], d), vec3::Dot(axis[1], d), vec3::Dot(axis[2], d));
	}

	// Signed distance to the OBB (negative inside).
	float Distance(const vec3 &p) const
	{
		vec3 q = LocalToWorldInverse(p);
		float dx = q.x > r.x ? q.x - r.x : (q.x < -r.x ? -r.x - q.x : 0.f);
		float dy = q.y > r.y ? q.y - r.y : (q.y < -r.y ? -r.y - q.y : 0.f);
		float dz = q.z > r.z ? q.z - r.z : (q.z < -r.z ? -r.z - q.z : 0.f);
		return (dx*dx > 0.f || dy*dy > 0.f || dz*dz > 0.f)
			? (float)std::sqrt((double)dx*dx + (double)dy*dy + (double)dz*dz) : 0.f;
	}
};

// Computes the minimum-volume OBB (conjectured, see Theorem 7.1 of the paper)
// enclosing the point set.
//
// `pts` points to an array of `num_pts` xyz point triples in floats.
// `stride_bytes` is the byte stride between consecutive points (e.g. 12 for
// tightly packed floats, or larger if the points are embedded in a struct).
//
// Returns a degenerate OBB (IsDegenerate() == true) if num_pts < 1.
OBB minobb(float *pts, int num_pts, int stride_bytes);
