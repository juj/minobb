// minobb.cpp
//
// Self-contained implementation of the minimum-volume OBB algorithm from
// MathGeoLib's OBB::OptimalEnclosingOBB() (Jylanki 2015).
//
// The code is a port of the original with the following simplifications:
//  - MathGeoLib's vec (float4/SSE) is replaced by a plain vec3 float struct.
//  - The convex hull is computed by a simple O(n^2) incremental algorithm
//    instead of MathGeoLib's QuickHull (the hull only needs to be correct, not fast).
//  - The graph-search (flood fill) based extreme vertex / antipodal / sidepodal
//    searches are replaced by exhaustive O(V) linear scans (see the NAIVE_ANTIPODAL_SEARCH
//    and NAIVE_SIDEPODAL_SEARCH variants in the original OBB.cpp, which are
//    documented to be equivalent). This makes the code much simpler at the cost
//    of performance on large inputs.
//  - Spatial traversal orders, search hints, timing instrumentation, logging
//    and validity asserts from the original are removed.
//
// Everything else (the contact-configuration enumeration: categories A, B and C;
// ComputeBasis; AreEdgesCompatibleForOBB; AreCompatibleOpposingEdges;
// IsVertexAntipodalToEdge; the 2D planar fallback with rotating calipers)
// follows the original code as closely as practical.

#include "minobb.h"

#include <vector>
#include <algorithm>
#include <cmath>
#include <cfloat>
#include <cstring>

// ----------------------------------------------------------------------------
// vec3 and OBB implementations
// ----------------------------------------------------------------------------

float dot(const vec3 &a, const vec3 &b) { return a.x*b.x + a.y*b.y + a.z*b.z; }

vec3 cross(const vec3 &a, const vec3 &b)
{
	return vec3(a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x);
}

float OBB::Volume() const
{
	return (r.x * 2.f) * (r.y * 2.f) * (r.z * 2.f);
}

bool OBB::IsDegenerate() const
{
	return r.x < 0.f || r.y < 0.f || r.z < 0.f;
}

vec3 OBB::LocalToWorldInverse(const vec3 &p) const
{
	vec3 d = p - pos;
	return vec3(dot(axis[0], d), dot(axis[1], d), dot(axis[2], d));
}

float OBB::Distance(const vec3 &p) const
{
	vec3 q = LocalToWorldInverse(p);
	float dx = q.x > r.x ? q.x - r.x : (q.x < -r.x ? -r.x - q.x : 0.f);
	float dy = q.y > r.y ? q.y - r.y : (q.y < -r.y ? -r.y - q.y : 0.f);
	float dz = q.z > r.z ? q.z - r.z : (q.z < -r.z ? -r.z - q.z : 0.f);
	return (dx*dx > 0.f || dy*dy > 0.f || dz*dz > 0.f)
		? (float)std::sqrt((double)dx*dx + (double)dy*dy + (double)dz*dz) : 0.f;
}

namespace
{

// ----------------------------------------------------------------------------
// Small math helpers
// ----------------------------------------------------------------------------

// Maximum of the three components (horizontal max).
inline float hmax(const vec3 &v) { return fmaxf(v.x, fmaxf(v.y, v.z)); }
// Same semantics as MathGeoLib's EqualAbs(): |a - b| < epsilon (default 1e-4).
inline bool EqualAbs(float a, float b, float epsilon = 1e-4f) { return fabsf(a - b) < epsilon; }

float LengthSq(const vec3 &v) { return dot(v, v); }

// Normalizes the vector in place, returns the original length.
float Normalize(vec3 &v)
{
	float lenSq = LengthSq(v);
	if (lenSq > 0.f)
	{
		float len = (float)sqrt((double)lenSq);
		float inv = 1.f / len;
		v *= inv;
	}
	return (float)sqrt((double)lenSq);
}

vec3 Normalized(const vec3 &v)
{
	vec3 u = v;
	Normalize(u);
	return u;
}

// A vector perpendicular to this one (this one must not be near-zero).
vec3 Perpendicular(const vec3 &v)
{
	// Choose the smallest magnitude component and cross with the corresponding unit axis.
	const float ax = fabsf(v.x), ay = fabsf(v.y), az = fabsf(v.z);
	vec3 dir = (ax < ay && ax < az) ? vec3(1.f, 0.f, 0.f) :
	           (ay < az)           ? vec3(0.f, 1.f, 0.f) : vec3(0.f, 0.f, 1.f);
	return cross(dir, v);
}

// Computes an orthonormal basis (outU, outV) perpendicular to this vector
// (this vector must be normalized). Same semantics as MathGeoLib's
// vec::PerpendicularBasis().
void PerpendicularBasis(const vec3 &v, vec3 &outU, vec3 &outV)
{
	outU = Normalized(Perpendicular(v));
	outV = Normalized(cross(outU, v));
}

// ----------------------------------------------------------------------------
// 2D point / min-area rectangle (rotating calipers)
// ----------------------------------------------------------------------------

struct float2
{
	float x, y;
	float2() : x(0.f), y(0.f) {}
	float2(float _x, float _y) : x(_x), y(_y) {}
	float2 operator - (const float2 &b) const { return float2(x - b.x, y - b.y); }
	float2 operator - () const { return float2(-x, -y); }
	float Dot(const float2 &b) const { return x*b.x + y*b.y; }
	float PerpDot(const float2 &b) const { return x*b.y - y*b.x; } // 2D cross product
	float2 Normalized() const { float l = (float)sqrt((double)(x*x + y*y)); float inv = l > 0.f ? 1.f/l : 0.f; return float2(x*inv, y*inv); }
	float2 Rotated90CCW() const { return float2(-y, x); }
	float2 Rotated90CW() const { return float2(y, -x); }
};

inline float2 operator - (const float2 *a, const float2 &b) { return *a - b; }

// Computes the convex hull of the points in place (returns it in the first
// n' elements, CCW oriented, no collinear or duplicate points).
// Port of MathGeoLib's float2_ConvexHullInPlace().
int ConvexHull2InPlace(float2 *p, int n)
{
	if (n <= 1) return n > 0 ? n : 0;

	std::sort(p, p + n, [](const float2 &a, const float2 &b)
	{
		return a.x < b.x || (a.x == b.x && a.y < b.y);
	});

	const float eps = 1e-6f;

	if (n == 2)
	{
		float dx = p[1].x - p[0].x, dy = p[1].y - p[0].y;
		return (dx*dx + dy*dy) > eps ? 2 : 1;
	}

	std::vector<float2> hull(2 * (size_t)n);

	// Signed 2D cross product of (b - a) x (c - a).
	auto cross2 = [](const float2 &a, const float2 &b, const float2 &c) -> float
	{
		return (b.x - a.x)*(c.y - a.y) - (b.y - a.y)*(c.x - a.x);
	};

	// Scan left to right for the bottom side.
	hull[0] = p[0];
	hull[1] = p[1];
	int k = 2;
	for (int i = 2; i < n; ++i)
	{
		while (k >= 2 && cross2(hull[k-2], hull[k-1], p[i]) <= 0.f)
			--k; // A clockwise (or collinear) turn, pop.
		hull[k++] = p[i];
	}

	// Come back scanning right to left for the top side.
	const int start = k;
	for (int i = n - 2; i > 0; --i)
	{
		while (k > start && cross2(hull[k-2], hull[k-1], p[i]) <= 0.f)
			--k;
		hull[k++] = p[i];
	}

	// Handle the final (leftmost) point.
	while (k > start && cross2(hull[k-2], hull[k-1], p[0]) <= 0.f)
		--k;

	// Clean up the generated convex hull by erasing duplicate entries.
	int h = 0;
	p[0] = hull[0];
	for (int i = 1; i < k; ++i)
	{
		float dx = hull[i].x - p[h].x, dy = hull[i].y - p[h].y;
		if (dx*dx + dy*dy > eps)
			p[++h] = hull[i];
	}
	while (h > 0)
	{
		float dx = p[h].x - p[0].x, dy = p[h].y - p[0].y;
		if (dx*dx + dy*dy < eps)
			--h;
		else
			break;
	}
	return h + 1;
}

// Computes the minimum area 2D rectangle enclosing the points.
// Port of MathGeoLib's float2::MinAreaRectInPlace() (rotating calipers).
// On output: uDir, vDir are the rectangle axes, [minU,maxU]x[minV,maxV] the
// extents in that frame, center the rectangle center. Returns the area.
float MinAreaRect2D(const float2 *inP, int n, float2 &center, float2 &uDir, float2 &vDir,
	float &minU, float &maxU, float &minV, float &maxV)
{
	if (n <= 0)
		return -1.f;

	std::vector<float2> p(inP, inP + n);
	n = ConvexHull2InPlace(&p[0], n);
	if (n == 1)
	{
		center = p[0];
		uDir = float2(1.f, 0.f);
		vDir = float2(0.f, 1.f);
		minU = maxU = center.x;
		minV = maxV = center.y;
		return 0.f;
	}

	// e[i] point to the antipodal point pairs: e[0] and e[2] are pairs, so are e[1] and e[3].
	float2 *e[4] = { &p[0], &p[0], &p[0], &p[0] };

	// Compute the initial AABB rectangle antipodal points for the rotating calipers method.
	for (int i = 1; i < n; ++i)
	{
		if (p[i].x < e[0]->x) e[0] = &p[i];
		else if (p[i].x > e[2]->x) e[2] = &p[i];
		if (p[i].y < e[1]->y) e[1] = &p[i];
		else if (p[i].y > e[3]->y) e[3] = &p[i];
	}

	// Direction vector of the edge that the currently tested rectangle is in contact with.
	float2 ed = float2(0.f, -1.f);
	float minArea = FLT_MAX;
	const float2 * const pEnd = &p[n];

	#define NEXT_P(ptr) ((ptr) == pEnd ? &p[0] : (ptr) + 1)

	// These track directions the convex hull is pointing towards at each antipodal point.
	float2 d[4];
	d[0] = (NEXT_P(e[0]) - *e[0]).Normalized();
	d[1] = (NEXT_P(e[1]) - *e[1]).Normalized();
	d[2] = (NEXT_P(e[2]) - *e[2]).Normalized();
	d[3] = (NEXT_P(e[3]) - *e[3]).Normalized();

	while (ed.y <= 0.f)
	{
		float cosA0 =  ed.Dot(d[0]);
		float cosA1 =  ed.PerpDot(d[1]);
		float cosA2 = -ed.Dot(d[2]);
		float cosA3 = -ed.PerpDot(d[3]);

		float maxCos = fmaxf(fmaxf(cosA0, cosA1), fmaxf(cosA2, cosA3));
		if (cosA0 >= maxCos)      { ed = d[0];                e[0] = NEXT_P(e[0]); d[0] = (NEXT_P(e[0]) - *e[0]).Normalized(); }
		else if (cosA1 >= maxCos) { ed = d[1].Rotated90CW();  e[1] = NEXT_P(e[1]); d[1] = (NEXT_P(e[1]) - *e[1]).Normalized(); }
		else if (cosA2 >= maxCos) { ed = -d[2];               e[2] = NEXT_P(e[2]); d[2] = (NEXT_P(e[2]) - *e[2]).Normalized(); }
		else                      { ed = d[3].Rotated90CCW(); e[3] = NEXT_P(e[3]); d[3] = (NEXT_P(e[3]) - *e[3]).Normalized(); }

		float minu = ed.PerpDot(*e[0]);
		float maxu = ed.PerpDot(*e[2]);
		float minv = ed.Dot(*e[1]);
		float maxv = ed.Dot(*e[3]);

		float area = fabsf((maxu - minu) * (maxv - minv));
		if (area < minArea)
		{
			vDir = ed;
			minArea = area;
			minU = fminf(minu, maxu);
			maxU = fmaxf(minu, maxu);
			minV = fminf(minv, maxv);
			maxV = fmaxf(minv, maxv);
		}
	}

	uDir = vDir.Rotated90CCW();
	center = float2(0.5f * (uDir.x * (minU + maxU) + vDir.x * (minV + maxV)),
	               0.5f * (uDir.y * (minU + maxU) + vDir.y * (minV + maxV)));

	#undef NEXT_P
	return minArea;
}

// ----------------------------------------------------------------------------
// 3D convex hull (simple incremental algorithm, O(n^2) typical)
// ----------------------------------------------------------------------------

struct Hull3
{
	std::vector<vec3> v;  // Hull vertices.
	std::vector<std::vector<int>> f; // Hull faces (triangles), CCW oriented from outside.

	bool IsDegenerate() const { return v.size() <= 3 || f.empty(); }
};

Hull3 BuildHull3Core(const std::vector<vec3> &ptsIn)
{
	Hull3 hull;

	// Remove exact duplicates.
	std::vector<vec3> pts = ptsIn;
	std::sort(pts.begin(), pts.end(), [](const vec3 &a, const vec3 &b)
	{
		if (a.x != b.x) return a.x < b.x;
		if (a.y != b.y) return a.y < b.y;
		return a.z < b.z;
	});
	pts.erase(std::unique(pts.begin(), pts.end(), [](const vec3 &a, const vec3 &b)
	{
		return a.x == b.x && a.y == b.y && a.z == b.z;
	}), pts.end());
	const int n = (int)pts.size();
	if (n == 0)
		return hull;

	float scale = 1.f;
	for (int i = 0; i < n; ++i)
		scale = fmaxf(scale, hmax(vec3(fabsf(pts[i].x), fabsf(pts[i].y), fabsf(pts[i].z))));

	// Find four affinely independent points to bootstrap with.
	int ia = -1, ib = -1, ic = -1, id = -1;
	for (int i = 0; i < n && ia == -1; ++i)
		for (int j = i + 1; j < n && ia == -1; ++j)
			for (int k = j + 1; k < n && ia == -1; ++k)
			{
				vec3 a = pts[j] - pts[i];
				vec3 b = pts[k] - pts[i];
				float abArea = LengthSq(cross(a, b));
				for (int l = k + 1; l < n && ia == -1; ++l)
				{
					float det = fabsf(dot(cross(a, b), pts[l] - pts[i]));
					// Require a non-degenerate volume relative to the point spread.
					if (det > 1e-10f * scale * (1.f + abArea))
					{
						ia = i; ib = j; ic = k; id = l;
					}
				}
			}

	if (ia == -1)
	{
		// The points are planar (or fewer than 4 unique points): signal degenerate so that
		// the caller falls back to the 2D algorithm.
		hull.v.resize(fminf((int)pts.size(), 3));
		for (int i = 0; i < (int)hull.v.size(); ++i)
			hull.v[i] = pts[i];
		return hull;
	}

	// Bootstrap with the tetrahedron (ia, ib, ic, id).
	hull.v.push_back(pts[ia]);
	hull.v.push_back(pts[ib]);
	hull.v.push_back(pts[ic]);
	hull.v.push_back(pts[id]);

	// Add a face, making sure it is oriented CCW from outside (the normal points away
	// from the interior, i.e. away from the given reference point `ref`).
	auto addFace = [&](int a, int b, int c, int ref)
	{
		vec3 n = cross(hull.v[b] - hull.v[a], hull.v[c] - hull.v[a]);
		if (dot(n, hull.v[ref] - hull.v[a]) > 0.f)
			std::swap(b, c); // Normal points towards the interior, flip.
		hull.f.push_back({ a, b, c });
	};
	addFace(0, 1, 2, 3);
	addFace(0, 1, 3, 2);
	addFace(0, 2, 3, 1);
	addFace(1, 2, 3, 0);

	// Incrementally insert the remaining points.
	for (int i = 0; i < n; ++i)
	{
		if (i == ia || i == ib || i == ic || i == id)
			continue;
		const vec3 &q = pts[i];

		// Find all faces visible from q.
		std::vector<int> visible;
		for (size_t fi = 0; fi < hull.f.size(); ++fi)
		{
			const std::vector<int> &face = hull.f[fi];
			vec3 n = Normalized(cross(hull.v[face[1]] - hull.v[face[0]], hull.v[face[2]] - hull.v[face[0]]));
			// Distance from q to the face plane (positive = outside the hull).
			float dist = dot(n, q - hull.v[face[0]]);
			if (dist > 1e-6f * scale)
				visible.push_back((int)fi);
		}
		if (visible.empty())
			continue; // q is inside (or on) the hull.

		// Collect the horizon: directed edges of the visible region that border a
		// non-visible face.
		struct DirEdge { int a, b; };
		std::vector<DirEdge> visEdges;
		for (int fi : visible)
		{
			const std::vector<int> &face = hull.f[fi];
			visEdges.push_back({ face[0], face[1] });
			visEdges.push_back({ face[1], face[2] });
			visEdges.push_back({ face[2], face[0] });
		}
		std::vector<DirEdge> horizon;
		for (const DirEdge &e : visEdges)
		{
			bool hasReverse = false;
			for (const DirEdge &o : visEdges)
				if (o.a == e.b && o.b == e.a)
					hasReverse = true;
			if (!hasReverse)
				horizon.push_back(e);
		}

		int qIdx = (int)hull.v.size();
		hull.v.push_back(q);

		// Rebuild the faces: keep the non-visible ones, add a new face for each horizon edge.
		std::vector<std::vector<int>> newFaces;
		newFaces.reserve(hull.f.size());
		for (size_t fi = 0; fi < hull.f.size(); ++fi)
		{
			bool vis = false;
			for (int vfi : visible)
				if ((int)fi == vfi) { vis = true; break; }
			if (!vis)
				newFaces.push_back(hull.f[fi]);
		}
		for (const DirEdge &he : horizon)
			newFaces.push_back({ he.a, he.b, qIdx }); // (a, b, q) is outward oriented (horizon runs CCW around the hole).
		hull.f.swap(newFaces);
	}

	// Robustness pass: ensure all face normals point strictly outward. On a valid
	// convex hull every other vertex must lie on or behind the face plane.
	for (size_t fi = 0; fi < hull.f.size(); ++fi)
	{
		std::vector<int> &face = hull.f[fi];
		vec3 n = cross(hull.v[face[1]] - hull.v[face[0]], hull.v[face[2]] - hull.v[face[0]]);
		for (size_t vi = 0; vi < hull.v.size(); ++vi)
		{
			int idx = (int)vi;
			if (idx == face[0] || idx == face[1] || idx == face[2])
				continue;
			if (dot(n, hull.v[idx] - hull.v[face[0]]) > 1e-9f * (1.f + LengthSq(n)) * scale)
			{
				std::swap(face[1], face[2]);
				break;
			}
		}
	}

	// Remove vertices not referenced by any face (points that turned out to be
	// interior during the incremental construction). The original
	// Polyhedron::ConvexHull stores only the actual hull vertices; keeping the
	// interior points around would make the antipodal search below O(E*n) in
	// the input size instead of O(E*V_hull).
	{
		std::vector<unsigned char> used(hull.v.size(), 0);
		for (size_t fi = 0; fi < hull.f.size(); ++fi)
			for (size_t j = 0; j < hull.f[fi].size(); ++j)
				used[hull.f[fi][j]] = 1;
		std::vector<int> remap(hull.v.size(), -1);
		std::vector<vec3> newV;
		newV.reserve(hull.v.size());
		for (size_t i = 0; i < hull.v.size(); ++i)
			if (used[i])
			{
				remap[i] = (int)newV.size();
				newV.push_back(hull.v[i]);
			}
		for (size_t fi = 0; fi < hull.f.size(); ++fi)
			for (size_t j = 0; j < hull.f[fi].size(); ++j)
				hull.f[fi][j] = remap[hull.f[fi][j]];
		hull.v.swap(newV);
	}

	return hull;
}

Hull3 ConvexHull3(const std::vector<vec3> &ptsIn)
{
	// Note: MathGeoLib's Polyhedron::ConvexHull is an incremental algorithm whose
	// exact vertex set for nearly-degenerate inputs is path-dependent (initial
	// tetrahedron from 14 fixed directions + RNG-ordered conflict processing with
	// inPlaneEpsilon = 1e-4). We build the exact hull of the input instead; for
	// well-conditioned point sets (the intended use case) the two agree, and the
	// OBB search below is robust to the extra nearly-coplanar vertices.
	return BuildHull3Core(ptsIn);
}

// ----------------------------------------------------------------------------
// OBB algorithm (ported from OBB.cpp)
// ----------------------------------------------------------------------------

struct Edge
{
	int first, last;
};


OBB FixedOrientationEnclosingOBB(const std::vector<vec3> &points, const vec3 &dir0, const vec3 &dir1);

// Finds the extreme (min and max) points along a direction.
void ExtremePointsAlongDirection(const std::vector<vec3> &points, const vec3 &dir,
	int &idxSmallest, int &idxLargest, float &smallestD, float &largestD)
{
	int n = (int)points.size();
	idxSmallest = idxLargest = 0;
	smallestD = FLT_MAX;
	largestD = -FLT_MAX;
	for (int i = 0; i < n; ++i)
	{
		float d = dot(points[i], dir);
		if (d < smallestD)
		{
			smallestD = d;
			idxSmallest = i;
		}
		if (d > largestD)
		{
			largestD = d;
			idxLargest = i;
		}
	}
}

// Port of SmallestOBBVolumeJiggle().
float SmallestOBBVolumeJiggle(const vec3 &edge_, const std::vector<vec3> &pointArray,
	std::vector<float2> &pts, vec3 &outEdgeA, vec3 &outEdgeB)
{
	vec3 edge = edge_;
	int numTimesNotImproved = 0;
	float bestVolume = FLT_MAX;
	vec3 edgeFirstChoice, edgeSecondChoice;
	const int numPoints = (int)pointArray.size();
	pts.resize(numPoints);
	while (numTimesNotImproved <= 1)
	{
		int e1, e2;
		float dummy1, dummy2;
		ExtremePointsAlongDirection(pointArray, edge, e1, e2, dummy1, dummy2);
		float edgeLength = fabsf(dot(pointArray[e1] - pointArray[e2], edge));

		vec3 u, v;
		PerpendicularBasis(edge, u, v);

		for (int k = 0; k < numPoints; ++k)
			pts[k] = float2(dot(u, pointArray[k]), dot(v, pointArray[k]));

		float2 rectCenter, uDir, vDir;
		float minU = 0.f, maxU = 0.f, minV = 0.f, maxV = 0.f;
		MinAreaRect2D(&pts[0], numPoints, rectCenter, uDir, vDir, minU, maxU, minV, maxV);
		float2 c10 = float2((maxV - minV) * vDir.x, (maxV - minV) * vDir.y);
		float2 c20 = float2((maxU - minU) * uDir.x, (maxU - minU) * uDir.y);

		vec3 edge1BackIn3D = u * c10.x + v * c10.y;
		vec3 edge2BackIn3D = u * c20.x + v * c20.y;

		float volume = (float)sqrt((double)LengthSq(edge1BackIn3D)) *
		               (float)sqrt((double)LengthSq(edge2BackIn3D)) * edgeLength;

		if (volume < bestVolume)
		{
			bestVolume = volume;
			edgeFirstChoice = u * uDir.x + v * uDir.y;
			Normalize(edgeFirstChoice);

			edgeSecondChoice = u * vDir.x + v * vDir.y;
			Normalize(edgeSecondChoice);

			outEdgeA = edge;
			outEdgeB = edge = edgeFirstChoice;
			numTimesNotImproved = 0;
		}
		else
		{
			++numTimesNotImproved;
			edge = edgeSecondChoice;
		}
	}
	return bestVolume;
}

// Port of SmallestOBBVolume2DPlanar() (with a 1D guard for collinear input).
OBB SmallestOBBVolume2DPlanar(const std::vector<vec3> &pointArray)
{
	const int numPoints = (int)pointArray.size();

	// 1D guard: all points collinear (or a single unique point) -> build a flat box
	// along the line through the two most distant points.
	vec3 commonPlaneNormal;
	for (int i = 2; i < numPoints; ++i)
	{
		vec3 normal = cross(pointArray[i] - pointArray[i-2], pointArray[i] - pointArray[i-1]);
		if (Normalize(normal) > 1e-12f)
		{
			if (dot(commonPlaneNormal, normal) >= 0.f)
				commonPlaneNormal += normal;
			else
				commonPlaneNormal -= normal;
			Normalize(commonPlaneNormal);
		}
	}
	if (LengthSq(commonPlaneNormal) < 0.5f)
	{
		// Collinear: find the two most distant points.
		int a = 0, b = 1;
		float bestDist = -1.f;
		for (int i = 0; i < numPoints; ++i)
			for (int j = i + 1; j < numPoints; ++j)
			{
				float d = LengthSq(pointArray[i] - pointArray[j]);
				if (d > bestDist)
				{
					bestDist = d;
					a = i;
					b = j;
				}
			}
		OBB o;
		o.pos = (pointArray[a] + pointArray[b]) * 0.5f;
		o.axis[0] = pointArray[b] - pointArray[a];
		o.axis[0] = Normalized(o.axis[0]);
		PerpendicularBasis(o.axis[0], o.axis[1], o.axis[2]);
		float diameter = (float)sqrt((double)bestDist);
		o.r = vec3(diameter * 0.5f, 0.f, 0.f);
		return o;
	}

	std::vector<float2> pts;
	vec3 edgeA, edgeB;
	SmallestOBBVolumeJiggle(commonPlaneNormal, pointArray, pts, edgeA, edgeB);
	return FixedOrientationEnclosingOBB(pointArray, edgeA, edgeB);
}

// 2D convex hull (monotone chain) of projected points. Returns the hull in
// CCW order without repeating the first point. Collinear points are dropped.
static std::vector<float2> ConvexHull2D(const std::vector<float2> &pts)
{
	int n = (int)pts.size();
	if (n < 3)
		return pts;
	std::vector<float2> s = pts;
	std::sort(s.begin(), s.end(), [](const float2 &a, const float2 &b)
	{
		return a.x < b.x || (a.x == b.x && a.y < b.y);
	});
	std::vector<float2> h;
	h.reserve(2 * n);
	for (int i = 0; i < n; ++i)
	{
		while (h.size() >= 2 && (h[h.size()-1] - h[h.size()-2]).PerpDot(s[i] - h[h.size()-2]) <= 0.f)
			h.pop_back();
		h.push_back(s[i]);
	}
	int lower = (int)h.size();
	for (int i = n - 2; i >= 0; --i)
	{
		while ((int)h.size() > lower && (h[h.size()-1] - h[h.size()-2]).PerpDot(s[i] - h[h.size()-2]) <= 0.f)
			h.pop_back();
		h.push_back(s[i]);
	}
	if (!h.empty())
		h.pop_back();
	return h;
}

// Coarse-to-fine sphere sweep used as a fallback when the category search finds
// no configuration at all. For nearly-planar hulls the numerically coplanar
// faces break the flush-edge structure the category search relies on, and the
// planar 2D fallback (which assumes a truly flat input) is off by tens of
// percent. Given a box axis n1, the optimal box is exact: (range along n1)
// times (minimum-area rectangle of the projection on the plane perpendicular
// to n1). So a dense sweep of n1 plus an exact in-plane min-rectangle gives a
// high-quality box. Only used for small hulls (the cost is ~V^2 per sample).
static OBB CoarseSweepEnclosingOBB(const std::vector<vec3> &pts)
{
	const int V = (int)pts.size();
	OBB empty;
	if (V < 4 || V > 96)
		return empty;

	// Center the points for numerical hygiene.
	vec3 c(0.f, 0.f, 0.f);
	for (int i = 0; i < V; ++i)
		c += pts[i];
	c *= (1.f / (float)V);
	std::vector<vec3> q(V);
	for (int i = 0; i < V; ++i)
		q[i] = pts[i] - c;

	// For direction n1: return the volume of the optimal box with that axis,
	// and the min-rectangle side direction w in the perpendicular plane.
	auto eval = [&](const vec3 &n1, float &vol, vec3 &w)
	{
		vec3 up = fabsf(n1.z) > 0.9f ? vec3(1.f, 0.f, 0.f) : vec3(0.f, 0.f, 1.f);
		vec3 u = Normalized(cross(n1, up));
		vec3 v = cross(n1, u);
		float amin = FLT_MAX, amax = -FLT_MAX;
		std::vector<float2> proj(V);
		for (int i = 0; i < V; ++i)
		{
			float a = dot(q[i], n1);
			if (a < amin) amin = a;
			if (a > amax) amax = a;
			proj[i] = float2(dot(q[i], u), dot(q[i], v));
		}
		std::vector<float2> h = ConvexHull2D(proj);
		int m = (int)h.size();
		if (m < 3)
		{
			vol = 0.f; // Degenerate projection; the caller handles it.
			w = u;
			return;
		}
		float bestArea = FLT_MAX;
		float2 bestE = h[0] - h[1];
		for (int i = 0; i < m; ++i)
		{
			float2 e = (h[(i + 1) % m] - h[i]).Normalized();
			float2 p = e.Rotated90CCW();
			float umn = FLT_MAX, umx = -FLT_MAX, pmn = FLT_MAX, pmx = -FLT_MAX;
			for (int j = 0; j < m; ++j)
			{
				float2 d = h[j] - h[i];
				float uu = d.Dot(e);
				float pp = d.Dot(p);
				if (uu < umn) umn = uu;
				if (uu > umx) umx = uu;
				if (pp < pmn) pmn = pp;
				if (pp > pmx) pmx = pp;
			}
			float area = (umx - umn) * (pmx - pmn);
			if (area < bestArea)
			{
				bestArea = area;
				bestE = e;
			}
		}
		vol = (amax - amin) * bestArea;
		w = u * bestE.x + v * bestE.y;
	};

	// Coarse full-sphere grid (3 degrees), then local tangent-space refinement.
	vec3 bestN = vec3(0.f, 0.f, 1.f);
	float bestVol = -1.f;
	for (int i = 0; i <= 60; ++i)
	{
		float th = (float)i * (3.14159265358979f / 180.f);
		float st = sinf(th), ct = cosf(th);
		for (int j = 0; j < 120; ++j)
		{
			float ph = (float)j * (2.f * 3.14159265358979f / 120.f);
			vec3 n1(st * cosf(ph), st * sinf(ph), ct);
			float vol;
			vec3 w;
			eval(n1, vol, w);
			if (vol > 0.f && (bestVol < 0.f || vol < bestVol))
			{
				bestVol = vol;
				bestN = n1;
			}
		}
	}
	for (int lvl = 0; lvl < 5 && bestVol > 0.f; ++lvl)
	{
		float half = 1.5f * powf(0.1f, (float)lvl); // degrees
		vec3 t1 = Normalized(cross(bestN, fabsf(bestN.z) > 0.9f ? vec3(1.f, 0.f, 0.f) : vec3(0.f, 0.f, 1.f)));
		vec3 t2 = cross(bestN, t1);
		float lv = bestVol;
		vec3 ln = bestN;
		for (int i = -10; i <= 10; ++i)
			for (int j = -10; j <= 10; ++j)
			{
				float a = (float)i * (half * 3.14159265358979f / 180.f);
				float b = (float)j * (half * 3.14159265358979f / 180.f);
				vec3 n1 = Normalized(bestN + t1 * sinf(a) + t2 * sinf(b));
				float vol;
				vec3 w;
				eval(n1, vol, w);
				if (vol > 0.f && vol < lv)
				{
					lv = vol;
					ln = n1;
				}
			}
		bestVol = lv;
		bestN = ln;
	}
	if (bestVol <= 0.f)
		return empty;

	// Build the final box from the best axis: n1 plus the exact min-rectangle
	// side direction, retightened against all input points.
	float vol;
	vec3 w;
	eval(bestN, vol, w);
	return FixedOrientationEnclosingOBB(pts, Normalized(bestN), Normalized(w));
}

// Moves the floating point sign bit from src to dst.
inline void MoveSign(float &dst, float &src)
{
	if (src < 0.f)
	{
		dst = -dst;
		src = -src;
	}
}

// Port of ComputeBasis().
int ComputeBasis(const vec3 &f1a, const vec3 &f1b,
	const vec3 &f2a, const vec3 &f2b,
	const vec3 &f3a, const vec3 &f3b,
	vec3 *n1,
	vec3 *n2,
	vec3 *n3)
{
	const float eps = 1e-4f;
	const float angleEps = 1e-3f;

	{
		vec3 a = f1b;
		vec3 b = f1a - f1b;
		vec3 c = f2b;
		vec3 d = f2a - f2b;
		vec3 e = f3b;
		vec3 f = f3a - f3b;

		float g = dot(a, c)*dot(d, e) - dot(a, d)*dot(c, e);
		float h = dot(a, c)*dot(d, f) - dot(a, d)*dot(c, f);
		float i = dot(b, c)*dot(d, e) - dot(b, d)*dot(c, e);
		float j = dot(b, c)*dot(d, f) - dot(b, d)*dot(c, f);

		float k = g*dot(b, e) - dot(a, e)*i;
		float l = h*dot(b, e) + g*dot(b, f) - dot(a, f)*i - dot(a, e)*j;
		float m = h*dot(b, f) - dot(a, f)*j;

		float s = l*l - 4.f*m*k;

		if (fabsf(m) < 1e-5f || fabsf(s) < 1e-5f)
		{
			// The equation is linear instead.
			float v = -k / l;
			float t = -(g + h*v) / (i + j*v);
			float u = -(dot(c, e) + dot(c, f)*v) / (dot(d, e) + dot(d, f)*v);
			int nSolutions = 0;
			// If we happened to divide by zero above, the following checks handle them.
			if (v >= -eps && t >= -eps && u >= -eps && v <= 1.f + eps && t <= 1.f + eps && u <= 1.f + eps)
			{
				n1[0] = Normalized(a + b*t);
				n2[0] = Normalized(c + d*u);
				n3[0] = Normalized(e + f*v);
				if (fabsf(dot(n1[0], n2[0])) < angleEps
					&& fabsf(dot(n1[0], n3[0])) < angleEps
					&& fabsf(dot(n2[0], n3[0])) < angleEps)
					return 1;
				else
					return 0;
			}
			return nSolutions;
		}

		if (s < 0.f)
			return 0; // Discriminant negative, no solutions for v.

		float sgnL = l < 0.f ? -1.f : 1.f;
		float V1 = -(l + sgnL*(float)sqrt((double)s)) / (2.f*m);
		float V2 = k / (m*V1);

		float T1 = -(g + h*V1) / (i + j*V1);
		float T2 = -(g + h*V2) / (i + j*V2);

		float U1 = -(dot(c, e) + dot(c, f)*V1) / (dot(d, e) + dot(d, f)*V1);
		float U2 = -(dot(c, e) + dot(c, f)*V2) / (dot(d, e) + dot(d, f)*V2);

		int nSolutions = 0;
		if (V1 >= -eps && T1 >= -eps && U1 >= -eps && V1 <= 1.f + eps && T1 <= 1.f + eps && U1 <= 1.f + eps)
		{
			n1[nSolutions] = Normalized(a + b*T1);
			n2[nSolutions] = Normalized(c + d*U1);
			n3[nSolutions] = Normalized(e + f*V1);

			if (fabsf(dot(n1[nSolutions], n2[nSolutions])) < angleEps
				&& fabsf(dot(n1[nSolutions], n3[nSolutions])) < angleEps
				&& fabsf(dot(n2[nSolutions], n3[nSolutions])) < angleEps)
				++nSolutions;
		}
		if (V2 >= -eps && T2 >= -eps && U2 >= -eps && V2 <= 1.f + eps && T2 <= 1.f + eps && U2 <= 1.f + eps)
		{
			n1[nSolutions] = Normalized(a + b*T2);
			n2[nSolutions] = Normalized(c + d*U2);
			n3[nSolutions] = Normalized(e + f*V2);
			if (fabsf(dot(n1[nSolutions], n2[nSolutions])) < angleEps
				&& fabsf(dot(n1[nSolutions], n3[nSolutions])) < angleEps
				&& fabsf(dot(n2[nSolutions], n3[nSolutions])) < angleEps)
				++nSolutions;
		}
		if (s < 1e-4f && nSolutions == 2)
			nSolutions = 1;

		return nSolutions;
	}
}

// Port of AreEdgesCompatibleForOBB().
bool AreEdgesCompatibleForOBB(const vec3 &f1a, const vec3 &f1b, const vec3 &f2a, const vec3 &f2b)
{
	const vec3 f1a_f1b = f1a - f1b;
	const vec3 f2a_f2b = f2a - f2b;
	float a = dot(f1b, f2b);
	float b = dot(f1a_f1b, f2b);
	float c = dot(f2a_f2b, f1b);
	float d = dot(f1a_f1b, f2a_f2b);

	/*
		n1 = f1a*t + f1b*(1-t) = f1b + (f1a-f1b)*t
		n2 = f2a*u + f2b*(1-u) = f2b + (f2a-f2b)*u

		n1.n2 = 0
		a + t*b + u*c + t*u*d = 0

		Does this equation have a solution within t & u \in [0,1]?

		// The function f(t,u) = a + t*b + u*c + t*u*d is continuous and bilinear
		// with respect to t and u, so test the four corners to get the minimum
		// and maximum of the function. If minimum <= 0 and
		// maximum >= 0, we know it must have a zero inside t,u \in [0,1].

		t=0: f(t,u)=a+uc   => min: a, max: a+c
		u=0: f(t,u)=a+tb   => min: a, max: a+b
		t=1: f(t,u)=a+uc + b+ud  => min: a+b, max: a+b+c+d
		u=1: f(t,u)=a+tb + c+td  => min: a+c, max: a+b+c+d
	*/
	float ab = a + b;
	float ac = a + c;
	float abcd = ab + c + d;
	float minVal = fminf(fminf(a, ab), fminf(ac, abcd));
	float maxVal = fmaxf(fmaxf(a, ab), fmaxf(ac, abcd));
	return minVal <= 0.f && maxVal >= 0.f;
}

// Port of AreCompatibleOpposingEdges().
bool AreCompatibleOpposingEdges(const vec3 &f1a, const vec3 &f1b, const vec3 &f2a, const vec3 &f2b, vec3 &outN)
{
	/*
		n1 = f1a*t + f1b*(1-t)
		n2 = f2a*u + f2b*(1-u)
		n1 = -c*n2, where c > 0
		f1a*t - f1b*t + cu*f2a + c*f2b - cu*f2b = -f1b
		c*f2b + t*(f1a-f1b) + cu*(f2a-f2b) = -f1b

		M * v = -f1b, where

		M = [ f2b, (f1a-f1b), (f2a-f2b) ] column vectors
		v = [c, t, cu]
	*/

	const float tooCloseToFaceEpsilon = 1e-4f;

	// Solve the 3x3 system with Cramer's rule.
	const vec3 col0 = f2b;
	const vec3 col1 = f1a - f1b;
	const vec3 col2 = f2a - f2b;
	const vec3 rhs = -f1b;

	float det = dot(col0, cross(col1, col2));
	if (fabsf(det) < 1e-12f)
		return false;

	float c  = dot(rhs,   cross(col1, col2)) / det;
	float t  = dot(col0,  cross(rhs,   col2)) / det;
	float cu = dot(col0,  cross(col1,  rhs))  / det;

	if (c <= 0.f || t < 0.f || t > 1.f)
		return false;
	float u = cu / c;
	if (t < tooCloseToFaceEpsilon || t > 1.f - tooCloseToFaceEpsilon
		|| u < tooCloseToFaceEpsilon || u > 1.f - tooCloseToFaceEpsilon)
		return false;
	if (cu < 0.f || cu > c)
		return false;
	outN = f1b + (f1a - f1b) * t;
	return true;
}

// Port of IsVertexAntipodalToEdge().
bool IsVertexAntipodalToEdge(const std::vector<vec3> &v, int vi, const std::vector<int> &neighbors, const vec3 &f1a, const vec3 &f1b)
{
	float tMin = 0.f;
	float tMax = 1.f;

	vec3 vert = v[vi];
	vec3 f1b_f1a = f1b - f1a;
	for (size_t i = 0; i < neighbors.size(); ++i)
	{
		/* Is an edge and a vertex compatible to be antipodal?

			n1 = f1b + (f1a-f1b)*t
			e { v-vn }

			n1.e <= 0
			(f1b + (f1a-f1b)*t).e <= 0
			t*(f1a-f1b).e <= -f1b.e
			if (f1a-f1b).e > 0:
				t <= -f1b.e / (f1a-f1b).e && t \in [0,1]
				-f1b.e / (f1a-f1b).e >= 0
				f1b.e <= 0
			if (f1a-f1b).e < 0:
				t >= -f1b.e / (f1a-f1b).e && t \in [0,1]
				-f1b.e / (f1a-f1b).e <= 1
				-f1b.e >= (f1a-f1b).e
				f1b.e + (f1a-f1b).e <= 0
			if (f1a-f1b).e == 0:
				0 <= -f1b.e
		*/
		vec3 e = v[neighbors[i]] - vert;
		float s = dot(f1b_f1a, e);
		float n = dot(f1b, e);
		const float epsilon = 1e-4f;
		if (s > epsilon)
			tMax = fminf(tMax, n / s);
		else if (s < -epsilon)
			tMin = fmaxf(tMin, n / s);
		else if (n < -epsilon)
			return false;

		// The interval of possible solutions for t is now degenerate?
		if (tMax - tMin < -5e-2f) // -1e-3f has been seen to be too strict here.
			return false;
	}
	return true;
}

// Port of TestThreeAdjacentFaces().
void TestThreeAdjacentFaces(const vec3 &n1, const vec3 &n2, const vec3 &n3,
	int edgeI, int edgeJ, int edgeK,
	const std::vector<vec3> &hullV, const std::vector<Edge> &edges,
	const std::vector<std::vector<int>> &antipodalPointsForEdge,
	float *minVolume, OBB *minOBB)
{
	// Compute the most extreme points in each direction.
	float maxN1 = dot(n1, hullV[edges[edgeI].first]);
	float maxN2 = dot(n2, hullV[edges[edgeJ].first]);
	float maxN3 = dot(n3, hullV[edges[edgeK].first]);
	auto minAlong = [&](const vec3 &dir, const std::vector<int> &candidates)
	{
		float m = FLT_MAX;
		if (candidates.empty())
		{
			for (const vec3 &p : hullV)
				m = fminf(m, dot(dir, p));
		}
		else
			for (size_t l = 0; l < candidates.size(); ++l)
				m = fminf(m, dot(dir, hullV[candidates[l]]));
		return m;
	};
	float minN1 = minAlong(n1, antipodalPointsForEdge[edgeI]);
	float minN2 = minAlong(n2, antipodalPointsForEdge[edgeJ]);
	float minN3 = minAlong(n3, antipodalPointsForEdge[edgeK]);
	float volume = (maxN1 - minN1) * (maxN2 - minN2) * (maxN3 - minN3);
	if (volume > 0.f && volume < *minVolume)
	{
		minOBB->axis[0] = n1;
		minOBB->axis[1] = n2;
		minOBB->axis[2] = n3;
		minOBB->r = vec3(maxN1 - minN1, maxN2 - minN2, maxN3 - minN3) * 0.5f;
		minOBB->pos = n1 * (minN1 + minOBB->r.x) + n2 * (minN2 + minOBB->r.y) + n3 * (minN3 + minOBB->r.z);
		*minVolume = volume;
	}
}

// Port of OBB::OptimalEnclosingOBB(const Polyhedron &).
// Returns an OBB with IsDegenerate() == true if the input is (near) planar.
OBB OptimalEnclosingOBB3D(const Hull3 &hull)
{
	/* Outline of the algorithm (from the original):
	  0. Compute the convex hull of the point set (done by the caller)
	  1. Compute vertex adjacency data.
	  2. Precompute face normal direction vectors.
	  3. Compute edge adjacency data (the two faces sharing each edge).
	  4. Precompute antipodal vertices for each edge.
	  5. Precompute all sidepodal (compatible) edges for each edge.
	  6. Test all configurations where all three edges are on adjacent faces.
	  7. Test all configurations where two edges are on opposing faces, and the third
	     one is on a face adjacent to the two.
	  8. Test all configurations where two edges are on the same face (OBB aligns with
	     a face of the convex hull).
	  9. Return the best found OBB.
	*/

	OBB minOBB;
	minOBB.r = vec3(-FLT_MAX, -FLT_MAX, -FLT_MAX); // Degenerate marker.
	float minVolume = FLT_MAX;

	// Handle degenerate planar cases up front.
	if (hull.v.size() <= 3 || hull.f.empty())
		return minOBB;

	const std::vector<vec3> &vtx = hull.v;
	const int V = (int)vtx.size();
	const int F = (int)hull.f.size();

	// Precomputation: for each vertex in the convex hull, compute their neighboring vertices.
	std::vector<std::vector<int>> adjacencyData(V);

	// Precomputation: compute normalized face direction vectors for each face of the hull.
	std::vector<vec3> faceNormals(F);
	for (int i = 0; i < F; ++i)
	{
		if (hull.f[i].size() < 3)
			return minOBB; // Degenerate face, cannot process.
		faceNormals[i] = Normalized(cross(vtx[hull.f[i][1]] - vtx[hull.f[i][0]],
		                                       vtx[hull.f[i][2]] - vtx[hull.f[i][0]]));
	}

	// For each edge i, specifies the two vertices v0 and v1 through which that edge goes.
	std::vector<Edge> edges;
	edges.reserve(V * 2);
	// For each edge i, specifies the face indices f0 and f1 that share that edge.
	std::vector<std::pair<int, int>> facesForEdge;
	facesForEdge.reserve(V * 2);
	// For each vertex pair (v0, v1) through which there is an edge, specifies the index i of the edge.
	// O(V^2) array data structure (same as the original).
	const int EMPTY_EDGE = -1;
	std::vector<int> vertexPairsToEdges((size_t)V * V, EMPTY_EDGE);

	// Precomputation: for each edge through vertices (i,j), we need to know
	// the face indices for the two adjoining faces that share the edge.
	for (int fi = 0; fi < F; ++fi)
	{
		const std::vector<int> &face = hull.f[fi];
		int v0 = face[face.size() - 1];
		for (size_t j = 0; j < face.size(); ++j)
		{
			int v1 = face[j];
			if (vertexPairsToEdges[v0 * V + v1] == EMPTY_EDGE)
			{
				vertexPairsToEdges[v0 * V + v1] = (int)edges.size();
				vertexPairsToEdges[v1 * V + v0] = (int)edges.size();
				edges.push_back({ v0, v1 });
				facesForEdge.push_back({ fi, -1 }); // The -1 will be filled once we see the edge v1->v0.
			}
			else
				facesForEdge[vertexPairsToEdges[v0 * V + v1]].second = fi;
			v0 = v1;
		}
	}
	const int E = (int)edges.size();
	for (int i = 0; i < V; ++i)
		for (int j = i + 1; j < V; ++j)
			if (vertexPairsToEdges[i * V + j] != EMPTY_EDGE)
			{
				adjacencyData[i].push_back(j);
				adjacencyData[j].push_back(i);
			}

	// Throughout the algorithm, internal edges can all be discarded, so provide a helper
	// to test for that (edges inside faces with ~180 degree dihedral angle, or edges
	// adjacent to fewer than two faces).
	auto isInternalEdge = [&](int i) -> bool
	{
		const std::pair<int, int> &ff = facesForEdge[i];
		if (ff.second < 0)
			return true; // Should not happen for a closed hull.
		return dot(faceNormals[ff.first], faceNormals[ff.second]) > 1.f - 1e-4f;
	};

	// Stores for each edge index i the complete list of antipodal vertices for that edge.
	std::vector<std::vector<int>> antipodalPointsForEdge(E);
	// Naive O(E*V) search (a superset of the original's graph search, see
	// NAIVE_ANTIPODAL_SEARCH in OBB.cpp). Supersets are safe: the lists are only
	// used to search for the minimum along an axis, and extra (non-extreme)
	// candidates can never lower that minimum below the true hull minimum.
	for (int i = 0; i < E; ++i)
	{
		// Skip internal (numerically coplanar) edges: when f1a == f1b the
		// antipodal predicate degenerates and misclassifies the edge's own
		// endpoints as antipodal, which the original code interprets as
		// "degenerate planar input" and bails out. The original's graph search
		// never reaches these vertices, and the lists of internal edges are
		// never used downstream (all category loops skip internal edges).
		if (isInternalEdge(i))
			continue;
		vec3 f1a = faceNormals[facesForEdge[i].first];
		vec3 f1b = faceNormals[facesForEdge[i].second];
		for (int j = 0; j < V; ++j)
			if (IsVertexAntipodalToEdge(vtx, j, adjacencyData[j], f1a, f1b))
			{
				if (edges[i].first == j || edges[i].last == j)
				{
					// Edge is antipodal to a vertex of the same edge. This should be
					// possible only if the input is degenerate planar. Return an
					// invalid OBB; the caller then computes a planar box on the source
					// input set.
					return minOBB;
				}
				antipodalPointsForEdge[i].push_back(j);
			}
	}

	// Stores for each edge i the list of all sidepodal edge indices j that it can form an OBB with.
	std::vector<std::vector<int>> compatibleEdges(E);
	// Use an O(E*V) data structure for sidepodal vertices.
	std::vector<unsigned char> sidepodalVertices((size_t)E * V, 0);

	// Naive O(E^2) search (equivalent to the original's graph search, see
	// NAIVE_SIDEPODAL_SEARCH in OBB.cpp).
	// Important! An edge can be its own companion edge!
	for (int i = 0; i < E; ++i)
	{
		vec3 f1a = faceNormals[facesForEdge[i].first];
		vec3 f1b = faceNormals[facesForEdge[i].second];
		for (int j = i; j < E; ++j)
		{
			if (!AreEdgesCompatibleForOBB(f1a, f1b, faceNormals[facesForEdge[j].first], faceNormals[facesForEdge[j].second]))
				continue;
			if (!isInternalEdge(i))
				compatibleEdges[i].push_back(j);
			sidepodalVertices[i * V + edges[j].first] = 1;
			sidepodalVertices[i * V + edges[j].last] = 1;
			if (i != j)
			{
				if (!isInternalEdge(j))
					compatibleEdges[j].push_back(i);
				sidepodalVertices[j * V + edges[i].first] = 1;
				sidepodalVertices[j * V + edges[i].last] = 1;
			}
		}
	}

	// ----------------------------------------------------------------------------
	// Category A: Test all configurations where all three edges are on adjacent faces.
	// (Naive complete enumeration: all index triples i < j < k where k is sidepodal to
	// both i and j. The original restricts this with spatial orders + graph search,
	// which only skips work, never candidates.)
	// ----------------------------------------------------------------------------
	for (int i = 0; i < E; ++i)
	{
		if (isInternalEdge(i))
			continue;
		vec3 f1a = faceNormals[facesForEdge[i].first];
		vec3 f1b = faceNormals[facesForEdge[i].second];
		for (size_t j = 0; j < compatibleEdges[i].size(); ++j)
		{
			int edgeJ = compatibleEdges[i][j];
			if (edgeJ <= i)
				continue; // Remove symmetry.
			if (isInternalEdge(edgeJ))
				continue;
			vec3 f2a = faceNormals[facesForEdge[edgeJ].first];
			vec3 f2b = faceNormals[facesForEdge[edgeJ].second];
			for (int edgeK = edgeJ + 1; edgeK < E; ++edgeK)
			{
				if (isInternalEdge(edgeK))
					continue;
				if (!sidepodalVertices[i * V + edges[edgeK].first]
					|| !sidepodalVertices[i * V + edges[edgeK].last])
					continue;
				if (!sidepodalVertices[edgeJ * V + edges[edgeK].first]
					|| !sidepodalVertices[edgeJ * V + edges[edgeK].last])
					continue;
				vec3 f3a = faceNormals[facesForEdge[edgeK].first];
				vec3 f3b = faceNormals[facesForEdge[edgeK].second];

				vec3 n1[2], n2[2], n3[2];
				int nSolutions = ComputeBasis(f1a, f1b, f2a, f2b, f3a, f3b, n1, n2, n3);
				for (int s = 0; s < nSolutions; ++s)
					TestThreeAdjacentFaces(n1[s], n2[s], n3[s], i, edgeJ, edgeK,
						vtx, edges, antipodalPointsForEdge, &minVolume, &minOBB);
			}
		}
	}

	// ----------------------------------------------------------------------------
	// Category B: Test all configurations where two edges are on opposing faces, and
	// the third one is on a face adjacent to the two.
	// ----------------------------------------------------------------------------
	std::vector<int> antipodalEdges;
	std::vector<vec3> antipodalEdgeNormals;

	for (int i = 0; i < E; ++i)
	{
		if (isInternalEdge(i))
			continue;
		vec3 f1a = faceNormals[facesForEdge[i].first];
		vec3 f1b = faceNormals[facesForEdge[i].second];

		antipodalEdges.clear();
		antipodalEdgeNormals.clear();

		const std::vector<int> &antipodals = antipodalPointsForEdge[i];
		for (size_t j = 0; j < antipodals.size(); ++j)
		{
			int antipodalVertex = antipodals[j];
			const std::vector<int> &adjacents = adjacencyData[antipodalVertex];
			for (size_t k = 0; k < adjacents.size(); ++k)
			{
				int vAdj = adjacents[k];
				if (vAdj < antipodalVertex)
					continue; // Canonical order to be antipodalVertex < vAdj.

				int edge = vertexPairsToEdges[antipodalVertex * V + vAdj];
				if (edge == EMPTY_EDGE || i > edge)
					continue; // Canonical order to be i < edge.
				if (isInternalEdge(edge))
					continue;

				vec3 f2a = faceNormals[facesForEdge[edge].first];
				vec3 f2b = faceNormals[facesForEdge[edge].second];

				vec3 n;
				bool success = AreCompatibleOpposingEdges(f1a, f1b, f2a, f2b, n);
				if (success)
				{
					antipodalEdges.push_back(edge);
					antipodalEdgeNormals.push_back(Normalized(n));
				}
			}
		}

		const std::vector<int> &compatibleEdgesI = compatibleEdges[i];
		for (size_t j = 0; j < compatibleEdgesI.size(); ++j)
		{
			int edgeJ = compatibleEdgesI[j];
			for (size_t k = 0; k < antipodalEdges.size(); ++k)
			{
				int edgeK = antipodalEdges[k];

				vec3 n = antipodalEdgeNormals[k];
				float minN1 = dot(n, vtx[edges[edgeK].first]);
				float maxN1 = dot(n, vtx[edges[i].first]);

				// Test all mutual compatible edges.
				vec3 f3a = faceNormals[facesForEdge[edgeJ].first];
				vec3 f3b = faceNormals[facesForEdge[edgeJ].second];

				// Is edge3 compatible with direction n?
				// n3 = f3b + (f3a-f3b)*v
				// n1.n3 = 0
				// n1.f3b + n1.((f3a-f3b)*v) = 0
				// n1.f3b = (n1.(f3b-f3a))*v
				// If n1.(f3b-f3a) != 0:
				//    v = n1.f3b / n1.(f3b-f3a)
				// If n1.(f3b-f3a) == 0:
				//    n1.f3b must be zero as well, then arbitrary v is ok.
				float num = dot(n, f3b);
				float denom = dot(n, f3b - f3a);
				MoveSign(num, denom);

				const float epsilon = 1e-4f;
				if (denom < epsilon)
				{
					num = EqualAbs(num, 0.f) ? 0.f : -1.f;
					denom = 1.f;
				}

				if (num >= denom * -epsilon && num <= denom * (1.f + epsilon))
				{
					float v = num / denom;
					vec3 n3 = Normalized(f3b + (f3a - f3b) * v);
					vec3 n2 = Normalized(cross(n3, n));

					// Linear scans for the extremes along n2 (replacing the original's
					// graph searches ExtremeVertexConvex(adjacencyData, +/-n2)).
					float minN2 = FLT_MAX, maxN2 = -FLT_MAX;
					for (int a = 0; a < V; ++a)
					{
						float d = dot(n2, vtx[a]);
						if (d < minN2) minN2 = d;
						if (d > maxN2) maxN2 = d;
					}

					float maxN3 = dot(n3, vtx[edges[edgeJ].first]);

					float minN3 = FLT_MAX;
					const std::vector<int> &antipodalsEdge3 = antipodalPointsForEdge[edgeJ];
					if (antipodalsEdge3.empty())
					{
						for (int a = 0; a < V; ++a)
							minN3 = fminf(minN3, dot(n3, vtx[a]));
					}
					else
					{
						for (size_t a = 0; a < antipodalsEdge3.size(); ++a)
							minN3 = fminf(minN3, dot(n3, vtx[antipodalsEdge3[a]]));
					}

					float volume = (maxN1 - minN1) * (maxN2 - minN2) * (maxN3 - minN3);
					if (volume > 0.f && volume < minVolume)
					{
						minOBB.pos = (n * (minN1 + maxN1) + n2 * (minN2 + maxN2) + n3 * (minN3 + maxN3)) * 0.5f;
						minOBB.axis[0] = n;
						minOBB.axis[1] = n2;
						minOBB.axis[2] = n3;
						minOBB.r = vec3(maxN1 - minN1, maxN2 - minN2, maxN3 - minN3) * 0.5f;
						minVolume = volume;
					}
				}
			}
		}
	}

	// ----------------------------------------------------------------------------
	// Category C: Test all configurations where two edges are on the same face
	// (OBB aligns with a face of the convex hull).
	// ----------------------------------------------------------------------------
	for (int fi = 0; fi < F; ++fi)
	{
		vec3 n1 = faceNormals[fi];

		// Find the first non-internal edge of the face.
		int e1 = -1;
		int v0 = hull.f[fi][hull.f[fi].size() - 1];
		for (size_t j = 0; j < hull.f[fi].size(); ++j)
		{
			int v1 = hull.f[fi][j];
			int e = vertexPairsToEdges[v0 * V + v1];
			if (e != EMPTY_EDGE && !isInternalEdge(e))
			{
				e1 = e;
				break;
			}
			v0 = v1;
		}
		if (e1 == -1)
			continue; // All edges of this face were degenerate internal edges!

		const std::vector<int> &antipodals = antipodalPointsForEdge[e1];
		const std::vector<int> &compatibleEdgesI = compatibleEdges[e1];

		float maxN1 = dot(n1, vtx[edges[e1].first]);
		float minN1 = FLT_MAX;
		if (antipodals.empty())
		{
			for (int j = 0; j < V; ++j)
				minN1 = fminf(minN1, dot(n1, vtx[j]));
		}
		else
		{
			for (size_t j = 0; j < antipodals.size(); ++j)
				minN1 = fminf(minN1, dot(n1, vtx[antipodals[j]]));
		}

		for (size_t j = 0; j < compatibleEdgesI.size(); ++j)
		{
			int edge3 = compatibleEdgesI[j];
			vec3 f3a = faceNormals[facesForEdge[edge3].first];
			vec3 f3b = faceNormals[facesForEdge[edge3].second];

			// Is edge3 compatible with direction n1?
			float num = dot(n1, f3b);
			float denom = dot(n1, f3b - f3a);
			float v;
			if (!EqualAbs(denom, 0.f))
				v = num / denom;
			else
				v = EqualAbs(num, 0.f) ? 0.f : -1.f;

			const float epsilon = 1e-4f;
			if (v >= 0.f - epsilon && v <= 1.f + epsilon)
			{
				vec3 n3 = Normalized(f3b + (f3a - f3b) * v);
				vec3 n2 = Normalized(cross(n3, n1));

				float minN2 = FLT_MAX, maxN2 = -FLT_MAX;
				for (int a = 0; a < V; ++a)
				{
					float d = dot(n2, vtx[a]);
					if (d < minN2) minN2 = d;
					if (d > maxN2) maxN2 = d;
				}
				float maxN3 = dot(n3, vtx[edges[edge3].first]);

				float minN3 = FLT_MAX;
				const std::vector<int> &antipodalsEdge3 = antipodalPointsForEdge[edge3];
				if (antipodalsEdge3.empty())
				{
					for (int a = 0; a < V; ++a)
						minN3 = fminf(minN3, dot(n3, vtx[a]));
				}
				else
				{
					for (size_t a = 0; a < antipodalsEdge3.size(); ++a)
						minN3 = fminf(minN3, dot(n3, vtx[antipodalsEdge3[a]]));
				}

				float volume = (maxN1 - minN1) * (maxN2 - minN2) * (maxN3 - minN3);
				if (volume > 0.f && volume < minVolume)
				{
					minOBB.pos = (n1 * (minN1 + maxN1) + n2 * (minN2 + maxN2) + n3 * (minN3 + maxN3)) * 0.5f;
					minOBB.axis[0] = n1;
					minOBB.axis[1] = n2;
					minOBB.axis[2] = n3;
					minOBB.r = vec3(maxN1 - minN1, maxN2 - minN2, maxN3 - minN3) * 0.5f;
					minVolume = volume;
				}
			}
		}
	}

	if (minOBB.IsDegenerate())
		return minOBB; // No configurations found, input is probably degenerate planar.

	// The search for edge triplets does not follow cross-product orientation, so
	// fix that up at the very last step, if necessary.
	if (dot(cross(minOBB.axis[0], minOBB.axis[1]), minOBB.axis[2]) < 0.f)
		minOBB.axis[2] = -minOBB.axis[2];

	return minOBB;
}

OBB FixedOrientationEnclosingOBB(const std::vector<vec3> &pointArray, const vec3 &dir0, const vec3 &dir1)
{
	int d0, d1;
	float mind0, maxd0, mind1, maxd1, mind2, maxd2;
	ExtremePointsAlongDirection(pointArray, dir0, d0, d1, mind0, maxd0);
	ExtremePointsAlongDirection(pointArray, dir1, d0, d1, mind1, maxd1);
	vec3 edgeC = Normalized(cross(dir0, dir1));
	ExtremePointsAlongDirection(pointArray, edgeC, d0, d1, mind2, maxd2);
	float rd0 = (maxd0 - mind0) * 0.5f;
	float rd1 = (maxd1 - mind1) * 0.5f;
	float rd2 = (maxd2 - mind2) * 0.5f;
	OBB minOBB;
	minOBB.pos = dir0 * (mind0 + rd0) + dir1 * (mind1 + rd1) + edgeC * (mind2 + rd2);
	minOBB.axis[0] = dir0;
	minOBB.axis[1] = dir1;
	minOBB.axis[2] = edgeC;
	minOBB.r = vec3(rd0, rd1, rd2);
	return minOBB;
}

} // namespace

// ----------------------------------------------------------------------------
// Public entry point
// ----------------------------------------------------------------------------

OBB minobb(float *pts, int num_pts, int stride_bytes)
{
	OBB degenerate;
	degenerate.pos = vec3(0.f, 0.f, 0.f);
	degenerate.r = vec3(-FLT_MAX, -FLT_MAX, -FLT_MAX);
	degenerate.axis[0] = vec3(1.f, 0.f, 0.f);
	degenerate.axis[1] = vec3(0.f, 1.f, 0.f);
	degenerate.axis[2] = vec3(0.f, 0.f, 1.f);

	if (!pts || num_pts <= 0 || stride_bytes < 12)
		return degenerate;

	// Copy the (possibly strided) input into a contiguous array, removing duplicates.
	std::vector<vec3> points;
	points.reserve((size_t)num_pts);
	for (int i = 0; i < num_pts; ++i)
	{
		const float *p = (const float *)pts + (size_t)i * (stride_bytes / 4);
		points.push_back(vec3(p[0], p[1], p[2]));
	}
	std::sort(points.begin(), points.end(), [](const vec3 &a, const vec3 &b)
	{
		if (a.x != b.x) return a.x < b.x;
		if (a.y != b.y) return a.y < b.y;
		return a.z < b.z;
	});
	points.erase(std::unique(points.begin(), points.end(), [](const vec3 &a, const vec3 &b)
	{
		return a.x == b.x && a.y == b.y && a.z == b.z;
	}), points.end());

	const int n = (int)points.size();
	if (n == 0)
		return degenerate;

	// Handle the trivial cases (same as the original).
	if (n == 1)
	{
		OBB o;
		o.pos = points[0];
		o.r = vec3(0.f, 0.f, 0.f);
		o.axis[0] = vec3(1.f, 0.f, 0.f);
		o.axis[1] = vec3(0.f, 1.f, 0.f);
		o.axis[2] = vec3(0.f, 0.f, 1.f);
		return o;
	}
	if (n == 2)
	{
		OBB o;
		o.pos = (points[0] + points[1]) * 0.5f;
		o.axis[0] = points[1] - points[0];
		o.axis[0] = Normalized(o.axis[0]);
		PerpendicularBasis(o.axis[0], o.axis[1], o.axis[2]);
		float diameter = (float)sqrt((double)LengthSq(points[1] - points[0]));
		o.r = vec3(diameter * 0.5f, 0.f, 0.f);
		return o;
	}

	// Compute the convex hull of the input point set. This is because we need
	// vertex-edge-face connectivity information about the convex hull shape, and
	// this also allows discarding all points in the interior of the input hull,
	// which are irrelevant.
	Hull3 convexHull = ConvexHull3(points);
	if (convexHull.IsDegenerate())
		// The points are planar (or nearly so): compute a flat OBB with the 2D algorithm.
		return SmallestOBBVolume2DPlanar(points);

	OBB optimalObb = OptimalEnclosingOBB3D(convexHull);
	if (optimalObb.IsDegenerate())
	{
		// The category search found no configuration at all. For nearly-planar hulls the
		// numerically coplanar faces can break the flush-edge structure it relies on, and
		// the 2D planar path below assumes truly flat input. Try a coarse sphere sweep
		// (exact given each candidate axis) first, and keep the better of the two.
		OBB sweep = CoarseSweepEnclosingOBB(convexHull.v);
		OBB planar = SmallestOBBVolume2DPlanar(points);
		if (!sweep.IsDegenerate() && sweep.Volume() < planar.Volume())
			return sweep;
		return planar;
	}
	else
	{
		// Retighten the best box: recompute the extents of the found orientation with
		// exact min/max scans over the points. The search above works in float and the
		// three found axes can be off from perfectly orthogonal by up to 1e-3 (accepted
		// in ComputeBasis), which makes the center/extent bookkeeping of the winning
		// configuration inconsistent by a few ulps of the box size. Re-deriving the box
		// in the same orientation guarantees containment (up to pure float rounding).
		return FixedOrientationEnclosingOBB(points, optimalObb.axis[0], optimalObb.axis[1]);
	}
}