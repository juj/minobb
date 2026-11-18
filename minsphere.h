// minsphere.h
//
// Minimum enclosing sphere of a 3D point set, self-contained.
//
// Adapted from MathGeoLib's Sphere::OptimalEnclosingSphere().
//
// minsphere() computes the smallest sphere that contains all the given
// points: the points themselves, or the vertices of a convex hull.
//
//   float points[] = { 0,0,0,  4,1,0,  1,3,0,  2,2,5 };
//   Sphere s = minsphere(points, 4, 3 * sizeof(float));
//   // s.pos is the center and s.r the radius.
//
//   Hull3 hull = convex_hull(pts, num_pts, stride_bytes); // See convex_hull.h.
//   Sphere s = minsphere(hull); // The same sphere, from the vertices of the hull.
//
// The smallest sphere around a point set is unique, and it is the smallest
// sphere around the two, three or four of the points that lie on it and hold
// it in place (its support points). minsphere() keeps such a support set and
// the sphere through it, looks for the point that is the farthest outside the
// sphere, and exchanges it into the support set, which makes the sphere
// larger. When no point is outside any more, the sphere is the smallest one.
//
// Complexity: linear in the number of points for the inputs seen in practice.
// Each exchange costs a pass over the points, and some ten are needed, but a
// large point set is first solved for a sample of its points, which leaves
// one or two exchanges for the whole set, and after the first pass most of
// the points are known to be inside the final sphere and are dropped. So the
// points of a typical model are read twice: 15 million vertices take 30 ms on
// one thread of a desktop CPU. (The points that all lie near the sphere, like
// those of a ball, cannot be dropped, and are read some five times.) Memory
// is needed only for the points that are left after the others are dropped.
//
// minsphere() does not need the convex hull: for the points of a model it is
// some twenty times faster to call it on the points than to compute the hull.
// With the hull at hand, the sphere of the hull takes less time still, as it
// has fewer points to look at.

#pragma once

#include "convex_hull.h" // vec3, Hull3

// A sphere: center `pos` and radius `r`. As the result of minsphere(), also
// the points that define the sphere.
struct Sphere
{
	vec3 pos; // Center point of the sphere.
	float r;  // Radius. Negative marks the sphere as invalid/degenerate.

	// The support points: the two to four points that the sphere passes
	// through and that determine it, as indices to the points that were given
	// to minsphere() (for a hull, to its vertices `v`). The smallest sphere
	// around the support points alone is the same sphere. A sphere around a
	// single point has that point here, and an invalid sphere has none.
	int numSupport;
	int support[4];

	Sphere() : r(-1.f), numSupport(0) { support[0] = support[1] = support[2] = support[3] = -1; }

	// Volume of the sphere.
	float Volume() const;

	// True if the sphere is invalid (marker produced when there are no points).
	bool IsDegenerate() const { return !(r >= 0.f); }

	// Signed distance to the surface of the sphere (negative inside).
	float Distance(const vec3 &p) const;

	// True if the point is inside the sphere or on it. (The test is done in
	// double precision, in which the result is exact for all but the points
	// that are within some 1e-15 of the radius from the surface.)
	bool Contains(const vec3 &p) const;
};

// Computes the minimum enclosing sphere of a point set.
//
// `pts` points to an array of `num_pts` xyz point triples in floats.
// `stride_bytes` is the byte stride between consecutive points (e.g. 12 for
// tightly packed floats, or larger if the points are embedded in a struct).
// Non-finite points (NaN/Inf) are ignored, duplicate points are harmless.
//
// The returned sphere contains all the points: |p - pos| <= r holds for each
// point p, with the center and the radius as the floats that they are. Its
// radius is the smallest possible to the precision of floats: what it has
// over the minimum is the rounding of the center and of the radius to floats.
// (Far away from the origin the center cannot be represented accurately, and
// the sphere is then larger by the rounding error of its center.)
//
// There are no tolerances to tune: the result does not depend on the scale of
// the points, and any input is fine. Points on a line or in a plane, and
// points that all lie on one sphere, get their smallest sphere like any
// others.
//
// Returns a degenerate sphere (IsDegenerate() == true) if there are no
// (finite) points. A single point gets a sphere of radius 0.
Sphere minsphere(const float *pts, int num_pts, int stride_bytes);

// Computes the minimum enclosing sphere of a convex hull, which is also that
// of the point set that the hull was computed from: the points that lie on
// the smallest sphere of a point set are vertices of its hull.
//
// `hull` is the result of convex_hull(), degenerate (flat) or not. The
// support points of the sphere are indices to hull.v.
Sphere minsphere(const Hull3 &hull);
