// minobb.h
//
// Minimal-volume oriented bounding box (OBB), self-contained.
//
// Extracted from MathGeoLib's OBB::OptimalEnclosingOBB() (Jylanki 2015,
// "Optimal bounding boxes for non-triangular meshes", section 5).
//
// minobb() computes the (conjectured) minimum-volume OBB enclosing the given
// convex hull (and hence the point set the hull was computed from):
//   A) Three edges of the convex hull touch three mutually adjacent faces of the OBB.
//   B) Two edges touch two opposite faces of the OBB, and a third edge touches a
//      face adjacent to the two.
//   C) Two edges touch two faces of the OBB, where one of the OBB's faces is flush
//      with a whole face of the convex hull.
//
// Typical usage is a two-pass run:
//   Hull3 hull = convex_hull(pts, num_pts, stride_bytes); // See convex_hull.h.
//   OBB obb = minobb(hull);
//
// minobb() enumerates the candidate box orientations implied by the contact
// configurations above (the paper's Theorem 7.1: the minimum-volume OBB touches
// at least three edges of the polyhedron, two of which touch two distinct faces
// of the OBB). It only needs the hull vertices and face connectivity: for any
// axis direction the extreme input point is a hull vertex, so the resulting box
// is exact for the full input at a fraction of the cost.
//
// Complexity: O(n log n) typical for the convex hull (convex_hull()) + O(E^3)
// configuration enumeration for minobb() in the worst case (E = number of
// convex hull edges). The input can be large, as long as its hull is small to
// medium sized.
//
// Degenerate input (all points in a plane, on a line, or a single point) is
// handled by a 2D rotating-calipers / 1D fallback, producing a flat OBB.

#pragma once

#include "convex_hull.h" // vec3, Hull3, convex_hull()

// Dot and cross product of two vectors.
float dot(const vec3 &a, const vec3 &b);
vec3 cross(const vec3 &a, const vec3 &b);

// An oriented bounding box: center `pos`, half-extents `r`, orthonormal axes `axis[0..2]`.
// Same layout/semantics as MathGeoLib's OBB (a point p is inside if all
// components of LocalToOBB(p) = dot(axis[i], p - pos) are within [-r[i], r[i]]).
struct OBB
{
	vec3 pos;     // Center point of the OBB.
	vec3 r;       // Half extents along each axis. A component < 0 marks the OBB as invalid/degenerate.
	vec3 axis[3]; // Orthonormal basis (rows of the LocalToWorld rotation).

	// Volume of the OBB.
	float Volume() const;

	// True if the OBB is invalid (marker produced when the input is degenerate).
	bool IsDegenerate() const;

	// Local space coordinates of a world space point.
	vec3 LocalToWorldInverse(const vec3 &p) const;

	// Signed distance to the OBB (negative inside).
	float Distance(const vec3 &p) const;
};

// Computes the minimum-volume OBB (conjectured, see Theorem 7.1 of the paper)
// enclosing the given convex hull (and hence the point set the hull was
// computed from).
//
// `hull` must be the result of convex_hull() for the point set of interest.
// For degenerate (planar/collinear/single-point) hulls a flat OBB is returned
// via a 2D rotating-calipers / 1D fallback. A hull that is flat to the
// precision of single precision floats (thinner than 2e-6 times its size) gets
// the box with the smallest area instead of the smallest volume: at that
// thickness the volume of a box with float axes is rounding noise.
//
// The returned box contains all the vertices of the hull, and its axes are
// orthonormal, both to the precision of floats. (Far away from the origin the
// box center cannot be represented accurately, and the box is then grown by
// the rounding error of its center.)
//
// Returns a degenerate OBB (IsDegenerate() == true) if the hull has no
// vertices, or if it is too large: the search needs E*V bits of working
// memory (E edges, V vertices), and gives up if that is more than 4 GB.
OBB minobb(const Hull3 &hull);
