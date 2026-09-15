#include "minobb.h"

#include <vector>
#include <algorithm>
#include <cmath>
#include <cfloat>
#include <cstring>
#include <set>
#include <assert.h>

float dot(const vec3 &a, const vec3 &b)
{
	return a.x*b.x + a.y*b.y + a.z*b.z;
}

vec3 cross(const vec3 &a, const vec3 &b)
{
	return vec3(a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x);
}

float OBB::Volume() const
{
	return r.x * r.y * r.z * 8.f;
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

// ----------------------------------------------------------------------------
// Small math helpers
// ----------------------------------------------------------------------------

// Maximum of the three components (horizontal max).
static inline float hmax(const vec3 &v) { return fmaxf(v.x, fmaxf(v.y, v.z)); }
// Same semantics as MathGeoLib's EqualAbs(): |a - b| < epsilon (default 1e-4).
static inline bool EqualAbs(float a, float b, float epsilon = 1e-4f) { return fabsf(a - b) < epsilon; }

static float LengthSq(const vec3 &v) { return dot(v, v); }

// Normalizes the vector in place, returns the original length.
static float Normalize(vec3 &v)
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

static vec3 Normalized(const vec3 &v)
{
	vec3 u = v;
	Normalize(u);
	return u;
}

// A vector perpendicular to this one (this one must not be near-zero).
static vec3 Perpendicular(const vec3 &v)
{
	// Choose the smallest magnitude component and cross with the corresponding unit axis.
	const float ax = fabsf(v.x), ay = fabsf(v.y), az = fabsf(v.z);
	vec3 dir = (ax < ay && ax < az) ? vec3(1.f, 0.f, 0.f) :
	           (ay < az)           ? vec3(0.f, 1.f, 0.f) : vec3(0.f, 0.f, 1.f);
	return cross(dir, v);
}

// Computes an orthonormal basis (outU, outV) perpendicular to this vector
// (this vector must be normalized). Same semantics as MathGeoLib's
// vec3::PerpendicularBasis().
static void PerpendicularBasis(const vec3 &v, vec3 &outU, vec3 &outV)
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

static inline float2 operator - (const float2 *a, const float2 &b) { return *a - b; }

// Computes the convex hull of the points in place (returns it in the first
// n' elements, CCW oriented, no collinear or duplicate points).
// Port of MathGeoLib's float2_ConvexHullInPlace().
static int ConvexHull2InPlace(float2 *p, int n)
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
static float MinAreaRect2D(const float2 *inP, int n, float2 &center, float2 &uDir, float2 &vDir,
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
	// The hull is open (p[0..n-1], first point not repeated): NEXT_P must wrap
	// from the LAST hull point back to p[0]. Wrapping at &p[n] instead would make
	// NEXT_P(&p[n-1]) == &p[n], an out-of-bounds read whenever a caliper reaches
	// the final hull vertex (MathGeoLib's original hull repeated the first point
	// at index n, which this port does not).
	const float2 * const pEnd = &p[n-1];

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

// Double-precision vector and operators for the hull predicates. The input
// points are float32, and the point-vs-face-plane tests need more guard digits
// than float leaves after the coordinates themselves: with float arithmetic a
// coplanar point can measure "outside" a face by pure representation error,
// which corrupts the visible-region topology. All hull construction is done in
// double and converted back to float at the end (the hull vertices are original
// input points, so the conversion is exact).
struct dvec3
{
	double x, y, z;
};
static inline dvec3 dsub(const dvec3 &a, const dvec3 &b) { return dvec3{a.x - b.x, a.y - b.y, a.z - b.z}; }
static inline dvec3 dmul(const dvec3 &a, double s) { return dvec3{a.x * s, a.y * s, a.z * s}; }
static inline double ddot(const dvec3 &a, const dvec3 &b) { return a.x*b.x + a.y*b.y + a.z*b.z; }
static inline dvec3 dcross(const dvec3 &a, const dvec3 &b)
{
	return dvec3{a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x};
}
static inline double dlen2(const dvec3 &a) { return ddot(a, a); }
static inline dvec3 dnormalize(const dvec3 &a)
{
	double l = std::sqrt(dlen2(a));
	return l > 0.0 ? dmul(a, 1.0 / l) : dvec3{0.0, 0.0, 0.0};
}

// 2D convex hull (Andrew's monotone chain, double precision) for degenerate
// (planar or collinear) point sets. Projects the points onto their plane using
// the basis (lineDir, w) derived from the bootstrap points ia/ib/ic, and returns
// the flat polygon as a Hull3 with degenerate = true: a fan triangulation for
// the planar case, a bare vertex list for the collinear / single-point cases.
static Hull3 BuildPlanarHull(const std::vector<vec3> &pts, const std::vector<dvec3> &P,
				       int n, int ia, int ib, int ic, const dvec3 &lineDir, double scale)
{
	Hull3 hull;
	hull.degenerate = true;
	if (n == 1)
	{
		hull.v.push_back(pts[0]);
		return hull;
	}
	dvec3 icRel = dsub(P[ic], P[ia]);
	double icDist = std::sqrt(dlen2(dsub(icRel, dmul(lineDir, ddot(lineDir, icRel)))));
	if (icDist <= 1e-9 * scale)
	{
		// Collinear: the hull is the diameter segment.
		hull.v.push_back(pts[ia]);
		hull.v.push_back(pts[ib]);
		return hull;
	}
	// Plane basis: u = lineDir (near-diameter direction), w = the
	// perpendicular direction in the plane.
	dvec3 w = dnormalize(dsub(icRel, dmul(lineDir, ddot(lineDir, icRel))));
	// Project all points to the plane and run Andrew's monotone chain.
	struct P2 { double s, t; int idx; };
	std::vector<P2> q((size_t)n);
	for (int i = 0; i < n; ++i)
	{
		dvec3 rel = dsub(P[i], P[ia]);
		q[i] = P2{ ddot(lineDir, rel), ddot(w, rel), i };
	}
	std::sort(q.begin(), q.end(), [](const P2 &a, const P2 &b)
	{
		if (a.s != b.s) return a.s < b.s;
		if (a.t != b.t) return a.t < b.t;
		return a.idx < b.idx;
	});
	q.erase(std::unique(q.begin(), q.end(), [](const P2 &a, const P2 &b)
	{ return a.s == b.s && a.t == b.t; }), q.end());
	auto cross2 = [](const P2 &O, const P2 &A, const P2 &B)
	{
		return (A.s - O.s) * (B.t - O.t) - (A.t - O.t) * (B.s - O.s);
	};
	// Monotone chain: corners of the 2D convex hull in CCW order, no
	// duplicated endpoint. Collinear edge points are dropped (only the
	// extreme corners are kept).
	std::vector<int> h2;
	for (int i = 0; i < (int)q.size(); ++i)
	{
		while (h2.size() >= 2 &&
			cross2(q[h2[h2.size() - 2]], q[h2[h2.size() - 1]], q[i]) <= 0.0)
			h2.pop_back();
		h2.push_back(i);
	}
	for (int i = (int)q.size() - 2, t = (int)h2.size() + 1; i >= 0; --i)
	{
		while (h2.size() > (size_t)t &&
			cross2(q[h2[h2.size() - 2]], q[h2[h2.size() - 1]], q[i]) <= 0.0)
			h2.pop_back();
		h2.push_back(i);
	}
	if (!h2.empty())
		h2.pop_back(); // Drop the duplicated first point.
	hull.v.reserve(h2.size());
	for (int i : h2)
		hull.v.push_back(pts[q[i].idx]);
	if (h2.size() >= 3)
	{
		// Fan-triangulate the flat polygon, orienting all faces so their
		// normals point the same way (the +u x w plane normal).
		dvec3 nPlane = dcross(lineDir, w);
		for (size_t i = 1; i + 1 < h2.size(); ++i)
		{
			int a = 0, b = (int)i, c = (int)(i + 1);
			vec3 n3 = cross(hull.v[b] - hull.v[a], hull.v[c] - hull.v[a]);
			dvec3 n3d = dvec3{ (double)n3.x, (double)n3.y, (double)n3.z };
			if (ddot(n3d, nPlane) < 0.0)
				std::swap(b, c);
			hull.f.push_back({ a, b, c });
		}
	}
	return hull;
}

// Validates a hull built in double precision:
//  - every undirected edge belongs to exactly two faces,
//  - the Euler characteristic holds (F == 2*V - 4 for a closed convex polyhedron),
//  - no face has zero area,
//  - every vertex lies on or behind every face plane, within the coplanarity
//    tolerance (convexity / outward orientation).
static bool HullValid(const std::vector<dvec3> &v, const std::vector<std::vector<int>> &f, double scale)
{
	const double eps = 1e-6 * scale;
	const size_t V = v.size(), F = f.size();
	if (F != 2 * V - 4)
		return false;
	std::multiset<std::pair<int, int>> edges;
	for (size_t fi = 0; fi < F; ++fi)
		for (int j = 0; j < 3; ++j)
		{
			int a = f[fi][j], b = f[fi][(j + 1) % 3];
			edges.insert(std::make_pair(std::min(a, b), std::max(a, b)));
		}
	for (auto it = edges.begin(); it != edges.end(); )
	{
		auto range = edges.equal_range(*it);
		if (std::distance(range.first, range.second) != 2)
			return false;
		it = range.second;
	}
	for (size_t fi = 0; fi < F; ++fi)
	{
		const std::vector<int> &face = f[fi];
		dvec3 n = dcross(dsub(v[face[1]], v[face[0]]), dsub(v[face[2]], v[face[0]]));
		if (dlen2(n) <= 0.0)
			return false; // Degenerate (zero-area) face.
		const double nlen = std::sqrt(dlen2(n));
		for (size_t vi = 0; vi < V; ++vi)
		{
			int idx = (int)vi;
			if (idx == face[0] || idx == face[1] || idx == face[2])
				continue;
			if (ddot(n, dsub(v[idx], v[face[0]])) > eps * nlen)
				return false; // A vertex pokes through the face: non-convex.
		}
	}
	return true;
}

static std::vector<std::vector<int> > GenerateVertexAdjacencyData(const Hull3 &hull)
{
	std::vector<std::vector<int> > adjacencyData;
	adjacencyData.reserve(hull.v.size());
	adjacencyData.insert(adjacencyData.end(), hull.v.size(), std::vector<int>());
	for(size_t i = 0; i < hull.f.size(); ++i)
	{
		const std::vector<int> &face = hull.f[i];
		int v0 = face.back();
		for(size_t j = 0; j < face.size(); ++j)
		{
			int v1 = face[j];
			adjacencyData[v0].push_back(v1);
			v0 = v1;
		}
	}
	return adjacencyData;
}

static Hull3 BuildHull3Core(const std::vector<vec3> &ptsIn)
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
	{
		hull.degenerate = true;
		return hull;
	}

	// Work in double precision (see dvec3 above).
	std::vector<dvec3> P((size_t)n);
	double scale = 1.0;
	for (int i = 0; i < n; ++i)
	{
		P[i] = dvec3{(double)pts[i].x, (double)pts[i].y, (double)pts[i].z};
		scale = std::max(scale, std::sqrt(dlen2(P[i])));
	}
	const double eps = 1e-6 * scale; // Coplanarity tolerance (true distance).

	// Robust bootstrap: a well-conditioned tetrahedron. Take a lexicographic
	// extreme point, a near-diameter partner (two farthest-point rounds), the
	// point farthest from that line, and the point farthest from the plane
	// through the three. All O(n). The original "first non-degenerate
	// tetrahedron" choice is nearly degenerate for thin/curved point clouds and
	// makes the incremental construction numerically unstable.
	int ia = 0;
	for (int i = 1; i < n; ++i)
		if (P[i].x < P[ia].x || (P[i].x == P[ia].x &&
		    (P[i].y < P[ia].y || (P[i].y == P[ia].y && P[i].z < P[ia].z))))
			ia = i;
	auto farthestFrom = [&](int from)
	{
		int best = -1;
		double bestD = -1.0;
		for (int i = 0; i < n; ++i)
		{
			double d = dlen2(dsub(P[i], P[from]));
			if (d > bestD) { bestD = d; best = i; }
		}
		return best;
	};
	int ib = farthestFrom(ia);
	{
		int r = farthestFrom(ib);
		if (dlen2(dsub(P[r], P[ia])) > dlen2(dsub(P[ib], P[ia])))
			ib = r;
	}
	dvec3 lineDir = dnormalize(dsub(P[ib], P[ia]));
	int ic = ia;
	{
		double bestD = -1.0;
		for (int i = 0; i < n; ++i)
		{
			dvec3 rel = dsub(P[i], P[ia]);
			dvec3 perp = dsub(rel, dmul(lineDir, ddot(lineDir, rel)));
			double d = dlen2(perp);
			if (d > bestD) { bestD = d; ic = i; }
		}
	}
	dvec3 baseN = dcross(dsub(P[ib], P[ia]), dsub(P[ic], P[ia]));
	int id = ia;
	{
		double bestD = -1.0;
		for (int i = 0; i < n; ++i)
		{
			double d = std::fabs(ddot(baseN, dsub(P[i], P[ia])));
			if (d > bestD) { bestD = d; id = i; }
		}
	}
	const double baseNLen = std::sqrt(dlen2(baseN));
	const double tetThickness = baseNLen > 0.0
		? std::fabs(ddot(baseN, dsub(P[id], P[ia]))) / baseNLen : 0.0;
	if (baseNLen <= 1e-9 * scale || tetThickness <= 1e-9 * scale)
		// The points are planar, collinear, or there are fewer than 4 non-coplanar
		// unique points: return a flat 2D convex hull instead of a solid polyhedron.
		return BuildPlanarHull(pts, P, n, ia, ib, ic, lineDir, scale);

	// Incremental construction in double precision. `order` is the insertion
	// order of the remaining points. The result is order-independent in exact
	// arithmetic, but for near-coplanar inputs micro-slivers can occur whose
	// occurrence is order-dependent, so the caller validates the result and can
	// retry with a different order.
	auto buildWithOrder = [&](const std::vector<int> &order,
					    std::vector<dvec3> &hv, std::vector<std::vector<int>> &hf)
	{
		hv.clear();
		hf.clear();
		hv.push_back(P[ia]);
		hv.push_back(P[ib]);
		hv.push_back(P[ic]);
		hv.push_back(P[id]);

		// Add a face, making sure it is oriented CCW from outside (the normal points
		// away from the interior, i.e. away from the given reference point `ref`).
		auto addFace = [&](int a, int b, int c, int ref)
		{
			dvec3 n = dcross(dsub(hv[b], hv[a]), dsub(hv[c], hv[a]));
			if (ddot(n, dsub(hv[ref], hv[a])) > 0.0)
				std::swap(b, c); // Normal points towards the interior, flip.
			hf.push_back({ a, b, c });
		};
		addFace(0, 1, 2, 3);
		addFace(0, 1, 3, 2);
		addFace(0, 2, 3, 1);
		addFace(1, 2, 3, 0);

		for (int oi = 0; oi < (int)order.size(); ++oi)
		{
			int i = order[oi];
			if (i == ia || i == ib || i == ic || i == id)
				continue;
			const dvec3 &q = P[i];

			// Find all faces visible from q.
			std::vector<int> visible;
			for (size_t fi = 0; fi < hf.size(); ++fi)
			{
				const std::vector<int> &face = hf[fi];
				dvec3 n = dnormalize(dcross(dsub(hv[face[1]], hv[face[0]]), dsub(hv[face[2]], hv[face[0]])));
				// Distance from q to the face plane (positive = outside the hull).
				double dist = ddot(n, dsub(q, hv[face[0]]));
				if (dist > eps)
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
				const std::vector<int> &face = hf[fi];
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

			int qIdx = (int)hv.size();
			hv.push_back(q);

			// Rebuild the faces: keep the non-visible ones, add a new face for each horizon edge.
			std::vector<std::vector<int>> newFaces;
			newFaces.reserve(hf.size());
			for (size_t fi = 0; fi < hf.size(); ++fi)
			{
				bool vis = false;
				for (int vfi : visible)
					if ((int)fi == vfi) { vis = true; break; }
				if (!vis)
					newFaces.push_back(hf[fi]);
			}
			for (const DirEdge &he : horizon)
				newFaces.push_back({ he.a, he.b, qIdx }); // (a, b, q) is outward oriented (horizon runs CCW around the hole).
			hf.swap(newFaces);
		}

		// Robustness pass: ensure all face normals point strictly outward. On a
		// valid convex hull every other vertex must lie on or behind the face plane.
		for (size_t fi = 0; fi < hf.size(); ++fi)
		{
			std::vector<int> &face = hf[fi];
			dvec3 n = dcross(dsub(hv[face[1]], hv[face[0]]), dsub(hv[face[2]], hv[face[0]]));
			const double nlen = std::sqrt(dlen2(n));
			for (size_t vi = 0; vi < hv.size(); ++vi)
			{
				int idx = (int)vi;
				if (idx == face[0] || idx == face[1] || idx == face[2])
					continue;
				if (ddot(n, dsub(hv[idx], hv[face[0]])) > eps * nlen)
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
		std::vector<unsigned char> used(hv.size(), 0);
		for (size_t fi = 0; fi < hf.size(); ++fi)
			for (int j = 0; j < 3; ++j)
				used[hf[fi][j]] = 1;
		std::vector<int> remap(hv.size(), -1);
		std::vector<dvec3> newV;
		newV.reserve(hv.size());
		for (size_t i = 0; i < hv.size(); ++i)
			if (used[i])
			{
				remap[i] = (int)newV.size();
				newV.push_back(hv[i]);
			}
		for (size_t fi = 0; fi < hf.size(); ++fi)
			for (int j = 0; j < 3; ++j)
				hf[fi][j] = remap[hf[fi][j]];
		hv.swap(newV);
	};

	std::vector<int> order((size_t)n);
	for (int i = 0; i < n; ++i)
		order[i] = i;

	std::vector<dvec3> hv;
	std::vector<std::vector<int>> hf;
	buildWithOrder(order, hv, hf);
	if (!HullValid(hv, hf, scale))
	{
		// Retry with the reverse insertion order: near-coplanar micro-slivers are
		// order-dependent, and a different order often builds a clean hull.
		std::reverse(order.begin(), order.end());
		std::vector<dvec3> hv2;
		std::vector<std::vector<int>> hf2;
		buildWithOrder(order, hv2, hf2);
		if (HullValid(hv2, hf2, scale))
		{
			hv = std::move(hv2);
			hf = std::move(hf2);
		}
		// If neither order validates, keep the first result (best effort); the
		// OBB search has its own fallbacks for imperfect hulls.
	}

	// Convert back to float. The hull vertices are original input points, so
	// this is exact.
	hull.v.reserve(hv.size());
	for (size_t i = 0; i < hv.size(); ++i)
		hull.v.push_back(vec3((float)hv[i].x, (float)hv[i].y, (float)hv[i].z));
	hull.f = std::move(hf);
	return hull;
}

static Hull3 ConvexHull3(const std::vector<vec3> &ptsIn)
{
	// Note: MathGeoLib's Polyhedron::ConvexHull is an incremental algorithm whose
	// exact vertex set for nearly-degenerate inputs is path-dependent (initial
	// tetrahedron from 14 fixed directions + RNG-ordered conflict processing with
	// inPlaneEpsilon = 1e-4). We build the exact hull of the input instead; for
	// well-conditioned point sets (the intended use case) the two agree, and the
	// OBB search below is robust to the extra nearly-coplanar vertices.
	return BuildHull3Core(ptsIn);
}

Hull3 convex_hull(float *pts, int num_pts, int stride_bytes)
{
	if (!pts || num_pts <= 0 || stride_bytes < 12)
		return Hull3(); // Degenerate (no vertices, no faces).

	// Copy the (possibly strided) input into a contiguous array, removing
	// exact duplicates (BuildHull3Core does the same, but keep the contract
	// explicit at the API boundary).
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

	return ConvexHull3(points);
}

// ----------------------------------------------------------------------------
// OBB algorithm (ported from OBB.cpp)
// ----------------------------------------------------------------------------

struct Edge
{
	int first, second;
};


static OBB FixedOrientationEnclosingOBB(const std::vector<vec3> &points, const vec3 &dir0, const vec3 &dir1);

// Finds the extreme (min and max) points along a direction.
static void ExtremePointsAlongDirection(const std::vector<vec3> &points, const vec3 &dir,
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
static float SmallestOBBVolumeJiggle(const vec3 &edge_, const std::vector<vec3> &pointArray,
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
static OBB SmallestOBBVolume2DPlanar(const std::vector<vec3> &pointArray)
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
	empty.r = vec3(-FLT_MAX, -FLT_MAX, -FLT_MAX); // IsDegenerate() == true
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
static inline void MoveSign(float &dst, float &src)
{
	if (src < 0.f)
	{
		dst = -dst;
		src = -src;
	}
}

// Port of ComputeBasis().
static int ComputeBasis(const vec3 &f1a, const vec3 &f1b,
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
static bool AreEdgesCompatibleForOBB(const vec3 &f1a, const vec3 &f1b, const vec3 &f2a, const vec3 &f2b)
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
static bool AreCompatibleOpposingEdges(const vec3 &f1a, const vec3 &f1b, const vec3 &f2a, const vec3 &f2b, vec3 &outN)
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
static bool IsVertexAntipodalToEdge(const std::vector<vec3> &v, int vi, const std::vector<int> &neighbors, const vec3 &f1a, const vec3 &f1b)
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

// A heuristic(?) that checks of the face normals of two edges are not suitably oriented.
// This is used to skip certain configurations.
static bool AreEdgesBad(const vec3 &f1a, const vec3 &f1b, const vec3 &f2a, const vec3 &f2b)
{
	return false;
	// Currently disabled. It's not completely certain if there's a form of this heuristic that
	// might be perfect, needs more tweaking.
#if 0 
	float a1 = Abs(f1a.Dot(f1b));
	float a2 = Abs(f2a.Dot(f2b));
	float b1 = Abs(f1a.Dot(f2b));
	float b2 = Abs(f2a.Dot(f1b));
	const float limitEpsilon = 1e-4f;

	if ((a1 > 1.f - limitEpsilon && a2 < limitEpsilon) || (a2 > 1.f - limitEpsilon && a1 < limitEpsilon))
		return true;
	if ((b1 > 1.f - limitEpsilon && b2 < limitEpsilon) || (b2 > 1.f - limitEpsilon && b1 < limitEpsilon))
		return true;

	if ((a1 > 1.f - limitEpsilon || a1 < limitEpsilon) && (a2 > 1.f - limitEpsilon || a2 < limitEpsilon))
		return true;
	if ((b1 > 1.f - limitEpsilon || b1 < limitEpsilon) && (b2 > 1.f - limitEpsilon || b2 < limitEpsilon))
		return true;

	return false;
#endif
}

// Port of TestThreeAdjacentFaces().
static void TestThreeAdjacentFaces(const vec3 &n1, const vec3 &n2, const vec3 &n3,
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

int ExtremeVertexConvex(const Hull3 &hull, const std::vector<std::vector<int> > &adjacencyData, const vec3 &direction, 
	std::vector<unsigned int> &floodFillVisited, unsigned int floodFillVisitColor,
	float &mostExtremeDistance, int startingVertex)
{
#ifdef MATH_NUMSTEPS_STATS
	numSearchStepsDone = 0;
	numImprovementsMade = 0;
#endif
	float curD = dot(direction, hull.v[startingVertex]);
	const int *neighbors = &adjacencyData[startingVertex][0];
	const int *neighborsEnd = neighbors + adjacencyData[startingVertex].size();
	floodFillVisited[startingVertex] = floodFillVisitColor;

	int secondBest = -1;
	float secondBestD = curD - 1e-3f;
	while(neighbors != neighborsEnd)
	{
		int n = *neighbors++;
		if (floodFillVisited[n] != floodFillVisitColor)
		{
			float d = dot(direction, hull.v[n]);
			if (d > curD)
			{
				startingVertex = n;
				curD = d;
				floodFillVisited[startingVertex] = floodFillVisitColor;
				neighbors = &adjacencyData[startingVertex][0];
				neighborsEnd = neighbors + adjacencyData[startingVertex].size();
				secondBest = -1;
				secondBestD = curD - 1e-3f;
			}
			else if (d > secondBestD)
			{
				secondBest = n;
				secondBestD = d;
			}
		}
	}
	if (secondBest != -1 && floodFillVisited[secondBest] != floodFillVisitColor)
	{
		float secondMostExtreme = -FLT_MAX;
		int secondTry = ExtremeVertexConvex(hull, adjacencyData, direction, floodFillVisited, floodFillVisitColor, secondMostExtreme, secondBest);
		if (secondMostExtreme > curD)
		{
			mostExtremeDistance = secondMostExtreme;
			return secondTry;
		}
	}
	mostExtremeDistance = curD;
	return startingVertex;
}

vec3 PolyhedronFaceNormal(const Hull3 &poly, int faceIndex)
{
	const std::vector<int> &face = poly.f[faceIndex];
	if (face.size() == 3)
	{
		vec3 a = poly.v[face[0]];
		vec3 b = poly.v[face[1]];
		vec3 c = poly.v[face[2]];
		return Normalized(cross(b-a, c-a));
	}
	else if (face.size() > 3)
	{
		// Use Newell's method of computing the face normal for best stability.
		// See Christer Ericson, Real-Time Collision Detection, pp. 491-495.
		vec3 normal(0, 0, 0);
		int v0 = face.back();
		for(size_t i = 0; i < face.size(); ++i)
		{
			int v1 = face[i];
			normal.x += (double(poly.v[v0].y) - poly.v[v1].y) * (double(poly.v[v0].z) + poly.v[v1].z); // Project on yz
			normal.y += (double(poly.v[v0].z) - poly.v[v1].z) * (double(poly.v[v0].x) + poly.v[v1].x); // Project on xz
			normal.z += (double(poly.v[v0].x) - poly.v[v1].x) * (double(poly.v[v0].y) + poly.v[v1].y); // Project on xy
			v0 = v1;
		}
		return Normalized(normal);
	}
	else if (face.size() == 2)
		return Normalized(cross(poly.v[face[1]] - poly.v[face[0]], Perpendicular(poly.v[face[0]] - poly.v[face[1]]) - poly.v[face[0]]));
	else if (face.size() == 1)
		return vec3(0, 1, 0);
	else
		return vec3(__builtin_nan(0), __builtin_nan(0), __builtin_nan(0));
}

// Port of OBB::OptimalEnclosingOBB(const Polyhedron &).
// Returns an OBB with IsDegenerate() == true if the input is (near) planar.
static OBB OptimalEnclosingOBB3D(const Hull3 &hull)
{
	/* Outline of the algorithm:
	  0. Compute the convex hull of the point set (given as input to this function) O(VlogV)
	  1. Compute vertex adjacency data, i.e. given a vertex, return a list of its neighboring vertices. O(V)
	  2. Precompute face normal direction vectors, since these are needed often. (does not affect big-O complexity, just a micro-opt) O(F)
	  3. Compute edge adjacency data, i.e. given an edge, return the two indices of its neighboring faces. O(V)
	  4. Precompute antipodal vertices for each edge. O(A*ElogV), where A is the size of antipodal vertices per edge. A ~ O(1) on average.
	  5. Precompute all sidepodal edges for each edge. O(E*S), where S is the size of sidepodal edges per edge. S ~ O(sqrtE) on average.
	     - Sort the sidepodal edges to a linear order so that it's possible to do fast set intersection computations on them. O(E*S*logS), or O(E*sqrtE*logE).
	  6. Test all configurations where all three edges are on adjacent faces. O(E*S^2) = O(E^2) or if smart with graph search, O(ES) = O(E*sqrtE)?
	  7. Test all configurations where two edges are on opposing faces, and the third one is on a face adjacent to the two. O(E*sqrtE*logV)?
	  8. Test all configurations where two edges are on the same face (OBB aligns with a face of the convex hull). O(F*sqrtE*logV).
	  9. Return the best found OBB.
	*/

	OBB minOBB;
	minOBB.r = vec3(-FLT_MAX, -FLT_MAX, -FLT_MAX); // Degenerate marker.
	float minVolume = FLT_MAX;

	// Handle degenerate planar cases up front.
	if (hull.v.size() <= 3 || hull.f.size() <= 1)
		return minOBB;

	// Precomputation: for each vertex in the convex hull, compute their neighboring vertices.
	std::vector<std::vector<int> > adjacencyData = GenerateVertexAdjacencyData(hull); // O(V)

	const std::vector<vec3> &vtx = hull.v;
	const int V = (int)vtx.size();
	const int F = (int)hull.f.size();

	// Precomputation: Compute normalized face direction vectors for each face of the hull.
	std::vector<vec3> faceNormals(F);
	for(int i = 0; i < F; ++i) // O(F)
	{
		if (hull.f[i].size() < 3) return minOBB; // Degenerate face, cannot process.
		faceNormals[i] = PolyhedronFaceNormal(hull, i);
	}

	// For each edge i, specifies the two vertices v0 and v1 through which that edge goes.
	// This array does not have duplicates, i.e. there only exists one edge index for (v0->v1), and no
	// edge for (v1->v0).
	std::vector<Edge> edges;
	edges.reserve(V * 2);
	// For each edge i, specifies the two face indices f0 and f1 that share that edge.
	std::vector<std::pair<int, int>> facesForEdge;
	facesForEdge.reserve(V * 2);
	// For each vertex pair (v0, v1) through which there is an edge, specifies the index i of the edge that passes through them.
	// This map contains duplicates, so both (v0, v1) and (v1, v0) map to the same edge index.
	// Currently use a O(V^2) array for this data structure for performance.
	unsigned int *vertexPairsToEdges = new unsigned int[hull.v.size()*hull.v.size()];
	memset(vertexPairsToEdges, 0xFF, sizeof(unsigned int)*hull.v.size()*hull.v.size());
#define EMPTY_EDGE 0xFFFFFFFFU

	// Precomputation: for each edge through vertices (i,j), we need to know
	// the face indices for the two adjoining faces that share the edge.
	// This is O(V).
	for (int fi = 0; fi < F; ++fi)
	{
		const std::vector<int> &face = hull.f[fi];
		int v0 = face.back();
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

	// Throughout the algorithm, internal edges can all be discarded, so provide a helper macro to test for that.
#define IS_INTERNAL_EDGE(i) (dot(faceNormals[facesForEdge[i].first], faceNormals[facesForEdge[i].second]) > 1.f - 1e-4f)
	const int E = (int)edges.size();

	// Throughout the whole algorithm, this array stores an auxiliary structure for performing graph searches
	// on the vertices of the convex hull. Conceptually each index of the array stores a boolean whether we
	// have visited that vertex or not during the current search. However storing such booleans is slow, since
	// we would have to perform a linear-time scan through this array before next search to reset each boolean
	// to unvisited false state. Instead, store a number, called a "color" for each vertex to specify whether
	// that vertex has been visited, and manage a global color counter floodFillVisitColor that represents the
	// visited vertices. At any given time, the vertices that have already been visited have the value
	// floodFillVisited[i] == floodFillVisitColor in them. This gives a win that we can perform constant-time
	// clears of the floodFillVisited array, by simply incrementing the "color" counter to clear the array.
	std::vector<unsigned int> floodFillVisited(hull.v.size());
	unsigned int floodFillVisitColor = 1;

	// As a syntactic aid, use the helpers MARK_VISITED(v), HAVE_VISITED_VERTEX(v) and CLEAR_GRAPH_SEARCH to
	// remind of the conceptual meaning of these values.
#define MARK_VERTEX_VISITED(v) (floodFillVisited[(v)] = floodFillVisitColor)
#define HAVE_VISITED_VERTEX(v) (floodFillVisited[(v)] == floodFillVisitColor) // HAVE_VISITED_VERTEX(v) implies HAVE_QUEUED_VERTEX(v)
#define CLEAR_GRAPH_SEARCH() (++floodFillVisitColor)

	// Stores for each edge index i the complete list of antipodal vertices for that edge.
	std::vector<std::vector<int> > antipodalPointsForEdge(E);

	// The currently best variant for establishing a spatially coherent traversal order.
	std::vector<int> spatialFaceOrder;
	std::vector<int> spatialEdgeOrder;
	srand(123); // TODO: mini RNG
//	LCG rng(123);
	{ // Explicit scope for variables that are not needed after this.
		std::vector<std::pair<int, int> > traverseStackEdges;
		std::vector<unsigned int> visitedEdges(edges.size());
		std::vector<unsigned int> visitedFaces(hull.f.size());
		traverseStackEdges.push_back(std::make_pair(0, adjacencyData[0].front()));
		while(!traverseStackEdges.empty())
		{
			std::pair<int, int> e = traverseStackEdges.back();
			traverseStackEdges.pop_back();
			int thisEdge = vertexPairsToEdges[e.first*hull.v.size()+e.second];
			if (visitedEdges[thisEdge])
				continue;
			visitedEdges[thisEdge] = 1;
			if (!visitedFaces[facesForEdge[thisEdge].first])
			{
				visitedFaces[facesForEdge[thisEdge].first] = 1;
				spatialFaceOrder.push_back(facesForEdge[thisEdge].first);
			}
			if (!visitedFaces[facesForEdge[thisEdge].second])
			{
				visitedFaces[facesForEdge[thisEdge].second] = 1;
				spatialFaceOrder.push_back(facesForEdge[thisEdge].second);
			}
			if (!IS_INTERNAL_EDGE(thisEdge))
				spatialEdgeOrder.push_back(thisEdge);
			int v0 = e.second;
			size_t sizeBefore = traverseStackEdges.size();
			for(size_t i = 0; i < adjacencyData[v0].size(); ++i)
			{
				int v1 = adjacencyData[v0][i];
				int e1 = vertexPairsToEdges[v0*hull.v.size()+v1];
				if (visitedEdges[e1])
					continue;
				traverseStackEdges.push_back(std::make_pair(v0, v1));
			}
			// Take a random adjacent edge.
			int nNewEdges = (int)(traverseStackEdges.size() - sizeBefore);
			if (nNewEdges > 0)
			{
				int r = nNewEdges > 1 ? (rand() % (nNewEdges - 1)) : 0;
				std::swap(traverseStackEdges.back(), traverseStackEdges[sizeBefore+r]);
			}
		}
	}

	// Stores a memory of yet unvisited vertices for current graph search.
	std::vector<int> traverseStack;

	// Since we do several extreme vertex searches, and the search directions have a lot of spatial locality,
	// always start the search for the next extreme vertex from the extreme vertex that was found during the
	// previous iteration for the previous edge. This has been profiled to improve overall performance by as
	// much as 15-25%.
	int startingVertex = 0;

//#ifndef NAIVE_ANTIPODAL_SEARCH

	// Precomputation: for each edge, we need to compute the list of potential antipodal points (points on
	// the opposing face of an enclosing OBB of the face that is flush with the given edge of the polyhedron).
	// This is O(E*log(V)) ?
	//for (size_t i = 0; i < edges.size(); ++i) // O(E)
	for(size_t ii = 0; ii < spatialEdgeOrder.size(); ++ii)
	{
		size_t i = (size_t)spatialEdgeOrder[ii];
		vec3 f1a = faceNormals[facesForEdge[i].first];
		vec3 f1b = faceNormals[facesForEdge[i].second];

		float dummy;
		CLEAR_GRAPH_SEARCH(); // ExtremeVertexConvex performs a graph search, initialize the search data structure for it.
		startingVertex = ExtremeVertexConvex(hull, adjacencyData, -f1a, floodFillVisited, floodFillVisitColor, dummy, startingVertex); // O(log(V)?
		CLEAR_GRAPH_SEARCH(); // Search through the graph for all adjacent antipodal vertices.
		traverseStack.push_back(startingVertex);
		MARK_VERTEX_VISITED(startingVertex);
		while(!traverseStack.empty()) // In amortized analysis, only a constant number of vertices are antipodal points for any edge?
		{
			int v = traverseStack.back();
			traverseStack.pop_back();
			const std::vector<int> &neighbors = adjacencyData[v];
			if (IsVertexAntipodalToEdge(hull.v, v, neighbors, f1a, f1b))
			{
				if (edges[i].first == v || edges[i].second == v)
				{
					/* 
					LOGE("Edge %d: %d->%d is antipodal to vertex %d, which is part of the same edge! This should be possible only if the input is degenerate planar!",
						(int)i, edges[i].first, edges[i].second, v);
					*/
					delete[] vertexPairsToEdges;
					// Input set is degenerate planar. Return an invalid OBB.
					OBB degenerateObb;
					degenerateObb.r = vec3(-FLT_MAX, -FLT_MAX, -FLT_MAX); // Degenerate marker.
					return degenerateObb;

					// We could automatically compute a planar box here, but in order to be able to do that robustly,
					// one should definitely compute the planar box on the source input set, and not on a convex hull
					// computed from that input set. So it is possible that this computed box from convexHull will
					// be bad due to float imprecision. Instead, caller should call SmallestOBBVolume2DPlanar() on
					// the source point set if they want to get a flat OBB from the input point set.
					/////return SmallestOBBVolume2DPlanar((const vec3*)&hull.v[0], (int)hull.v.size());
				}
				antipodalPointsForEdge[i].push_back(v);
				for(size_t j = 0; j < neighbors.size(); ++j)
					if (!HAVE_VISITED_VERTEX(neighbors[j]))
					{
						traverseStack.push_back(neighbors[j]);
						MARK_VERTEX_VISITED(neighbors[j]);
					}
			}
		}
		// Robustness: If the above search did not find any antipodal points, add the first found extreme
		// point at least, since it is always an antipodal point. This is known to occur very rarely due
		// to numerical imprecision in the above loop over adjacent edges.
		if (antipodalPointsForEdge[i].empty())
		{
//			LOGW("Due to numerical stability issues(?), could not find an antipodal vertex for edge %d! Check the scale of your input dataset! Good scale is having coordinates range e.g. [0.0,100.0]", edges[i]);
			// Getting here is most likely a bug. Fall back to linear scan, which is very slow.
			for(size_t j = 0; j < hull.v.size(); ++j) // O(V)
				if (IsVertexAntipodalToEdge(hull.v, (int)j, adjacencyData[j], f1a, f1b))
					antipodalPointsForEdge[i].push_back((int)j);

//			antipodalPointsForEdge[i].push_back(startingVertex);
		}
	}
//#endif

	// Stores for each edge i the list of all sidepodal edge indices j that it can form an OBB with.
	std::vector<std::vector<int>> compatibleEdges(E);

	// Use an O(E*V) data structure for sidepodal vertices.
	std::vector<unsigned char> sidepodalVertices((size_t)E * V, 0);

	// Compute all sidepodal edges for each edge by performing a graph search. The set of sidepodal edges is
	// connected in the graph, which lets us avoid having to iterate over each edge pair of the convex hull.
	// Total running time is O(E*sqrtE).
//	for(size_t i = 0; i < edges.size(); ++i) // O(E)
	for(size_t ii = 0; ii < spatialEdgeOrder.size(); ++ii)
	{
		size_t i = (size_t)spatialEdgeOrder[ii];
		vec3 f1a = faceNormals[facesForEdge[i].first];
		vec3 f1b = faceNormals[facesForEdge[i].second];

		vec3 deadDirection = (f1a+f1b)*0.5f;
		vec3 basis1, basis2;
		PerpendicularBasis(deadDirection, basis1, basis2);

		float dummy;
		vec3 dir = Perpendicular(f1a);
		CLEAR_GRAPH_SEARCH();
		startingVertex = ExtremeVertexConvex(hull, adjacencyData, dir, floodFillVisited, floodFillVisitColor, dummy, startingVertex); // O(log|V|)
		CLEAR_GRAPH_SEARCH();
		traverseStack.push_back(startingVertex);
		while(!traverseStack.empty()) // O(sqrt(E))
		{
			int v = traverseStack.back();
			traverseStack.pop_back();
			if (HAVE_VISITED_VERTEX(v))
				continue;
			MARK_VERTEX_VISITED(v);

			const std::vector<int> &n = adjacencyData[v];
			for(size_t j = 0; j < n.size(); ++j)
			{
				int vAdj = n[j];
				if (HAVE_VISITED_VERTEX(vAdj))
					continue;

//				int edge = vertexPairsToEdges[std::make_pair(v, vAdj)];
				int edge = vertexPairsToEdges[v*hull.v.size()+vAdj];
//				if (IS_INTERNAL_EDGE(edge))
//					continue; // Edges inside faces with 180 degrees dihedral angles can be ignored.
				if (AreEdgesCompatibleForOBB(f1a, f1b, faceNormals[facesForEdge[edge].first], faceNormals[facesForEdge[edge].second]))
				{
					if ((int)i <= edge)
					{
						if (!IS_INTERNAL_EDGE(edge))
							compatibleEdges[i].push_back(edge);

						sidepodalVertices[i*hull.v.size()+edges[edge].first] = 1;
						sidepodalVertices[i*hull.v.size()+edges[edge].second] = 1;

//						sidepodalVertices[i].insert(edges[edge].first);
//						sidepodalVertices[i].insert(edges[edge].second);
						if ((int)i != edge)
						{
//							vec3 f2a = faceNormals[facesForEdge[edge].first];
//							vec3 f2b = faceNormals[facesForEdge[edge].second];

							if (!IS_INTERNAL_EDGE(edge))
								compatibleEdges[edge].push_back((int)i);
//							sidepodalVertices[edge].insert(edges[i].first);
//							sidepodalVertices[edge].insert(edges[i].second);
							sidepodalVertices[edge*hull.v.size()+edges[i].first] = 1;
							sidepodalVertices[edge*hull.v.size()+edges[i].second] = 1;
//							sidepodalVerticesForEdge[edge].push_back(edges[i].first);
//							sidepodalVerticesForEdge[edge].push_back(edges[i].second);
//							++numSmallerCompatibleEdgeIndices[edge];
						}
					}
					traverseStack.push_back(vAdj);
				}
			}
		}
	}

	// Take advantage of spatial locality: start the search for the extreme vertex from the extreme vertex
	// that was found during the previous iteration for the previous edge. This speeds up the search since
	// edge directions have some amount of spatial locality and the next extreme vertex is often close
	// to the previous one. Track two hint variables since we are performing extreme vertex searches to
	// two opposing directions at the same time.
	int extremeVertexSearchHint1 = 0;
	int extremeVertexSearchHint2 = 0;
	int extremeVertexSearchHint3 = 0;
	int extremeVertexSearchHint4 = 0;
	int extremeVertexSearchHint1_b = 0;
	int extremeVertexSearchHint2_b = 0;
	int extremeVertexSearchHint3_b = 0;

	// Stores a memory of yet unvisited vertices that are common sidepodal vertices to both currently chosen edges for current graph search.
	std::vector<int> traverseStackCommonSidepodals;

//	for(size_t i = 0; i < edges.size(); ++i) // O(|E|)
	for(size_t ii = 0; ii < spatialEdgeOrder.size(); ++ii)
	{
		size_t i = (size_t)spatialEdgeOrder[ii];
		vec3 f1a = faceNormals[facesForEdge[i].first];
		vec3 f1b = faceNormals[facesForEdge[i].second];

		vec3 deadDirection = (f1a+f1b)*0.5f;

//		vec3 e1 = (vec3(hull.v[edges[i].first]) - vec3(hull.v[edges[i].second])).Normalized();

		const std::vector<int> &compatibleEdgesI = compatibleEdges[i];

		for(size_t j = 0; j < compatibleEdgesI.size(); ++j) // O(sqrt(|E|))?
		{
			int edgeJ = compatibleEdgesI[j];
			if (edgeJ <= (int)i) continue; // Remove symmetry.
			vec3 f2a = faceNormals[facesForEdge[edgeJ].first];
			vec3 f2b = faceNormals[facesForEdge[edgeJ].second];
			if (AreEdgesBad(f1a, f1b, f2a, f2b)) continue;

			vec3 deadDirection2 = (f2a+f2b)*0.5f;

			vec3 searchDir = cross(deadDirection, deadDirection2);
			float len = Normalize(searchDir);
			if (len == 0.f)
			{
				searchDir = cross(f1a, f2a);
				len = Normalize(searchDir);
				if (len == 0.f)
					searchDir = Perpendicular(f1a);
			}

			CLEAR_GRAPH_SEARCH();
			float dummy;
			extremeVertexSearchHint1 = ExtremeVertexConvex(hull, adjacencyData, searchDir, floodFillVisited, floodFillVisitColor, dummy, extremeVertexSearchHint1); // O(log|V|)?
			CLEAR_GRAPH_SEARCH();
			extremeVertexSearchHint2 = ExtremeVertexConvex(hull, adjacencyData, -searchDir, floodFillVisited, floodFillVisitColor, dummy, extremeVertexSearchHint2); // O(log|V|)?

// Enable new smarter search for sidepodal vertices. Should be always on.
#define SECOND_GUESS_SIDEPODALS

			int secondSearch = -1;
#ifdef SECOND_GUESS_SIDEPODALS
			if (sidepodalVertices[edgeJ*hull.v.size()+extremeVertexSearchHint1]) traverseStackCommonSidepodals.push_back(extremeVertexSearchHint1);
			else traverseStack.push_back(extremeVertexSearchHint1);
			if (sidepodalVertices[edgeJ*hull.v.size()+extremeVertexSearchHint2]) traverseStackCommonSidepodals.push_back(extremeVertexSearchHint2);
			else secondSearch = extremeVertexSearchHint2;//traverseStack.push_back(extremeVertexSearchHint2);
#else
			traverseStackCommonSidepodals.push_back(extremeVertexSearchHint1);
			traverseStackCommonSidepodals.push_back(extremeVertexSearchHint2);
#endif

			// Bootstrap to a good vertex that is sidepodal to both edges.
			CLEAR_GRAPH_SEARCH();
			while(!traverseStack.empty())
			{
				int v = traverseStack.front();
				traverseStack.erase(traverseStack.begin());
				if (HAVE_VISITED_VERTEX(v))
					continue;
				MARK_VERTEX_VISITED(v);
				const std::vector<int> &n = adjacencyData[v];
				for(size_t k = 0; k < n.size(); ++k)
				{
					int vAdj = n[k];
					if (!HAVE_VISITED_VERTEX(vAdj) && sidepodalVertices[i*hull.v.size()+vAdj])
					{
						if (sidepodalVertices[edgeJ*hull.v.size()+vAdj])
						{
							traverseStack.clear();
							if (secondSearch != -1)
							{
								traverseStack.push_back(secondSearch);
								secondSearch = -1;
								MARK_VERTEX_VISITED(vAdj);
							}
							traverseStackCommonSidepodals.push_back(vAdj);
							break;
						}
						else
							traverseStack.push_back(vAdj);
					}
				}
			}

			CLEAR_GRAPH_SEARCH();
			while(!traverseStackCommonSidepodals.empty())
			{
				int v = traverseStackCommonSidepodals.back();
				traverseStackCommonSidepodals.pop_back();
				if (HAVE_VISITED_VERTEX(v))
					continue;
				MARK_VERTEX_VISITED(v);
				const std::vector<int> &n = adjacencyData[v];
				for(size_t k = 0; k < n.size(); ++k)
				{
					int vAdj = n[k];
//					int edgeK = vertexPairsToEdges[std::make_pair(v, vAdj)];
					int edgeK = vertexPairsToEdges[v*hull.v.size()+vAdj];
					if (IS_INTERNAL_EDGE(edgeK))
						continue; // Edges inside faces with 180 degrees dihedral angles can be ignored.
					if (sidepodalVertices[i*hull.v.size()+vAdj]
						&& sidepodalVertices[edgeJ*hull.v.size()+vAdj])
					{
						if (!HAVE_VISITED_VERTEX(vAdj))
							traverseStackCommonSidepodals.push_back(vAdj);

						if (edgeJ < edgeK)
						{
							// Test edge triplet i, edgeJ, edgeK.
							vec3 f3a = faceNormals[facesForEdge[edgeK].first];
							vec3 f3b = faceNormals[facesForEdge[edgeK].second];

							if (!AreEdgesBad(f1a, f1b, f3a, f3b) && !AreEdgesBad(f2a, f2b, f3a, f3b))
							{
								vec3 n1[2], n2[2], n3[2];
								int nSolutions = ComputeBasis(f1a, f1b, f2a, f2b, f3a, f3b, n1, n2, n3);
								for(int s = 0; s < nSolutions; ++s) // O(constant), nSolutions == 0, 1 or 2.
								{
									TestThreeAdjacentFaces(n1[s], n2[s], n3[s], (int)i, edgeJ, edgeK, hull.v,
										edges, antipodalPointsForEdge, &minVolume, &minOBB);
								}
							}
						}
					}
				}
			}
		}
	}

	std::vector<int> antipodalEdges;
	std::vector<vec3> antipodalEdgeNormals;

	// Main algorithm body for finding all search directions where the OBB is flush with the edges of the
	// convex hull from two opposing faces. This is O(E*sqrtE*logV)?
//	for (size_t i = 0; i < edges.size(); ++i) // O(E)
///	{
	for(size_t ii = 0; ii < spatialEdgeOrder.size(); ++ii)
	{
		size_t i = (size_t)spatialEdgeOrder[ii];
		vec3 f1a = faceNormals[facesForEdge[i].first];
		vec3 f1b = faceNormals[facesForEdge[i].second];

		antipodalEdges.clear();
		antipodalEdgeNormals.clear();

		const std::vector<int> &antipodals = antipodalPointsForEdge[i];
		for(size_t j = 0; j < antipodals.size(); ++j) // O(constant)?
		{
			int antipodalVertex = antipodals[j];
			const std::vector<int> &adjacents = adjacencyData[antipodalVertex];
			for(size_t k = 0; k < adjacents.size(); ++k) // O(constant)?
			{
				int vAdj = adjacents[k];
				if (vAdj < antipodalVertex)
					continue; // We search unordered edges, so no need to process edge (v1, v2) and (v2, v1) twice - take the canonical order to be antipodalVertex < vAdj

//				int edge = vertexPairsToEdges[std::make_pair(antipodalVertex, vAdj)];
				int edge = vertexPairsToEdges[antipodalVertex*hull.v.size()+vAdj];
				if ((int)i > edge) // We search pairs of edges, so no need to process twice - take the canonical order to be i < edge.
					continue;
				if (IS_INTERNAL_EDGE(edge))
					continue; // Edges inside faces with 180 degrees dihedral angles can be ignored.

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
		for(size_t j = 0; j < compatibleEdgesI.size(); ++j)
//		for(size_t j = 0; j < antipodalEdges.size(); ++j)
		{
			int edgeJ = compatibleEdgesI[j];
//			const std::vector<int> &compatibleEdgesJ = compatibleEdges[edge];
//			n = n.Normalized();
			for(size_t k = 0; k < antipodalEdges.size(); ++k)
			{
				int edgeK = antipodalEdges[k];

				vec3 n = antipodalEdgeNormals[k];
				float minN1 = dot(n, hull.v[edges[edgeK].first]);
				float maxN1 = dot(n, hull.v[edges[i].first]);

				// Test all mutual compatible edges.
				vec3 f3a = faceNormals[facesForEdge[edgeJ].first];
				vec3 f3b = faceNormals[facesForEdge[edgeJ].second];
				// Is edge3 compatible with direction n?
				// n3 = f3b + (f3a-f3b)*v
				// n1.n3 = 0
				// n1.(f3b + (f3a-f3b)*v) = 0
				// n1.f3b + n1.((f3a-f3b)*v) = 0
				// n1.f3b = (n1.(f3b-f3a))*v
				// If n1.(f3b-f3a) != 0:
				//    v = n1.f3b / n1.(f3b-f3a)
				// If n1.(f3b-f3a) == 0:
				//    n1.f3b must be zero as well, then arbitrary v is ok.
				float num = dot(n, f3b);
				float denom = dot(n, f3b-f3a);
				MoveSign(num, denom);

				const float epsilon = 1e-4f;
				if (denom < epsilon)//EqualAbs(denom, 0.f))
				{
					num = EqualAbs(num, 0.f) ? 0.f : -1.f;
					denom = 1.f;
				}

//				if (v >= 0.f - epsilon && v <= 1.f + epsilon)
				if (num >= denom * -epsilon && num <= denom * (1.f + epsilon))
				{
					float v = num / denom;
					vec3 n3 = Normalized(f3b + (f3a - f3b) * v);
					vec3 n2 = Normalized(cross(n3, n));

					float minN2, maxN2;

					CLEAR_GRAPH_SEARCH();
					int hint = ExtremeVertexConvex(hull, adjacencyData, n2, floodFillVisited, floodFillVisitColor, maxN2, (k == 0) ? extremeVertexSearchHint1 : extremeVertexSearchHint1_b); // O(logV)?
					if (k == 0) extremeVertexSearchHint1 = extremeVertexSearchHint1_b = hint;
					else extremeVertexSearchHint1_b = hint;

					CLEAR_GRAPH_SEARCH();
					hint = ExtremeVertexConvex(hull, adjacencyData, -n2, floodFillVisited, floodFillVisitColor, minN2, (k == 0) ? extremeVertexSearchHint2 : extremeVertexSearchHint2_b); // O(logV)?
					if (k == 0) extremeVertexSearchHint2 = extremeVertexSearchHint2_b = hint;
					else extremeVertexSearchHint2_b = hint;
					minN2 = -minN2;

					float maxN3 = dot(n3, hull.v[edges[edgeJ].first]);

					float minN3 = FLT_MAX;
					const std::vector<int> &antipodalsEdge3 = antipodalPointsForEdge[edgeJ];
					if (antipodalsEdge3.size() < 20) // If there are very few antipodal vertices, do a very tight loop and just iterate over each.
					{
						for(size_t a = 0; a < antipodalsEdge3.size(); ++a)
							minN3 = fminf(minN3, dot(n3, hull.v[antipodalsEdge3[a]]));
					}
					else
					{
						// Otherwise perform a spatial locality exploiting graph search.
						CLEAR_GRAPH_SEARCH();
						hint = ExtremeVertexConvex(hull, adjacencyData, -n3, floodFillVisited, floodFillVisitColor, minN3, (k == 0) ? extremeVertexSearchHint3 : extremeVertexSearchHint3_b); // O(logV)?
						if (k == 0) extremeVertexSearchHint3 = extremeVertexSearchHint3_b = hint;
						else extremeVertexSearchHint3_b = hint;
						minN3 = -minN3;
					}

					float volume = (maxN1 - minN1) * (maxN2 - minN2) * (maxN3 - minN3);
					if (volume < minVolume)
					{
						minOBB.pos = (n*(minN1 + maxN1) + n2*(minN2 + maxN2) + n3*(minN3 + maxN3)) * 0.5f;
						minOBB.axis[0] = n;
						minOBB.axis[1] = n2;
						minOBB.axis[2] = n3;
						minOBB.r[0] = (maxN1 - minN1) * 0.5f;
						minOBB.r[1] = (maxN2 - minN2) * 0.5f;
						minOBB.r[2] = (maxN3 - minN3) * 0.5f;
						minVolume = volume;
					}
				}
			}
		}
	}

	// Main algorithm body for computing all search directions where the OBB touches two edges on the same face.
	// This is O(F*sqrtE*logV)?
	for(size_t ii = 0; ii < spatialFaceOrder.size(); ++ii) // O(F)
	{
		size_t i = spatialFaceOrder[ii];
		vec3 n1 = faceNormals[i];

		// Find two edges on the face. Since we have flexibility to choose from multiple edges of the same face,
		// choose two that are possibly most opposing to each other, in the hope that their sets of sidepodal
		// edges are most mutually exclusive as possible, speeding up the search below.
		int e1 = -1;
		int v0 = hull.f[i].back();
		for(size_t j = 0; j < hull.f[i].size(); ++j)
		{
			int v1 = hull.f[i][j];
			int e = vertexPairsToEdges[v0*hull.v.size()+v1];
			if (!IS_INTERNAL_EDGE(e))
			{
				e1 = e;
				break;
			}
			v0 = v1;
		}
		if (e1 == -1)
			continue; // All edges of this face were degenerate internal edges! Just skip processing the whole face.

		const std::vector<int> &antipodals = antipodalPointsForEdge[e1];
		const std::vector<int> &compatibleEdgesI = compatibleEdges[e1];

		float maxN1 = dot(n1, hull.v[edges[e1].first]);
		float minN1;

		if (antipodals.size() < 20)
		{
			minN1 = FLT_MAX;
			for(size_t j = 0; j < antipodals.size(); ++j)
				minN1 = fminf(minN1, dot(n1, hull.v[antipodals[j]]));
		}
		else
		{
			CLEAR_GRAPH_SEARCH();
			extremeVertexSearchHint4 = ExtremeVertexConvex(hull, adjacencyData, -n1, floodFillVisited, floodFillVisitColor, minN1, extremeVertexSearchHint4); // O(logV)?
			minN1 = -minN1;
		}

		for(size_t j = 0; j < compatibleEdgesI.size(); ++j)
		{
			int edge3 = compatibleEdgesI[j];
			// Test all mutual compatible edges.
			vec3 f3a = faceNormals[facesForEdge[edge3].first];
			vec3 f3b = faceNormals[facesForEdge[edge3].second];

			// Is edge3 compatible with direction n?
			// n3 = f3b + (f3a-f3b)*v
			// n1.n3 = 0
			// n1.(f3b + (f3a-f3b)*v) = 0
			// n1.f3b + n1.((f3a-f3b)*v) = 0
			// n1.f3b = (n1.(f3b-f3a))*v
			// If n1.(f3b-f3a) != 0:
			//    v = n1.f3b / n1.(f3b-f3a)
			// If n1.(f3b-f3a) == 0:
			//    n1.f3b must be zero as well, then arbitrary v is ok.
			float num = dot(n1, f3b);
			float denom = dot(n1, f3b-f3a);
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

				float minN2, maxN2;
				CLEAR_GRAPH_SEARCH();
				extremeVertexSearchHint1 = ExtremeVertexConvex(hull, adjacencyData, n2, floodFillVisited, floodFillVisitColor, maxN2, extremeVertexSearchHint1); // O(logV)?
				CLEAR_GRAPH_SEARCH();
				extremeVertexSearchHint2 = ExtremeVertexConvex(hull, adjacencyData, -n2, floodFillVisited, floodFillVisitColor, minN2, extremeVertexSearchHint2); // O(logV)?
				minN2 = -minN2;
				float maxN3 = dot(n3, hull.v[edges[edge3].first]);

				const std::vector<int> &antipodalsEdge3 = antipodalPointsForEdge[edge3];
				float minN3 = FLT_MAX;
				if (antipodalsEdge3.size() < 20) // If there are very few antipodal vertices, do a very tight loop and just iterate over each.
				{
					for(size_t a = 0; a < antipodalsEdge3.size(); ++a)
						minN3 = fminf(minN3, dot(n3, hull.v[antipodalsEdge3[a]]));
				}
				else
				{
					// Otherwise perform a spatial locality exploiting graph search.
					CLEAR_GRAPH_SEARCH();
					extremeVertexSearchHint3 = ExtremeVertexConvex(hull, adjacencyData, -n3, floodFillVisited, floodFillVisitColor, minN3, extremeVertexSearchHint3); // O(logV)?
					minN3 = -minN3;
				}

				float volume = (maxN1 - minN1) * (maxN2 - minN2) * (maxN3 - minN3);
				if (volume < minVolume)
				{
					minOBB.pos = (n1*(minN1 + maxN1) + n2*(minN2 + maxN2) + n3*(minN3 + maxN3)) * 0.5f;
					minOBB.axis[0] = n1;
					minOBB.axis[1] = n2;
					minOBB.axis[2] = n3;
					minOBB.r[0] = (maxN1 - minN1) * 0.5f;
					minOBB.r[1] = (maxN2 - minN2) * 0.5f;
					minOBB.r[2] = (maxN3 - minN3) * 0.5f;
					assert(volume > 0.f);
					minVolume = volume;
				}
			}
		}
	}

	// The search for edge triplets does not follow cross-product orientation, so
	// fix that up at the very last step, if necessary.
	if (dot(cross(minOBB.axis[0], minOBB.axis[1]), minOBB.axis[2]) < 0.f)
		minOBB.axis[2] = -minOBB.axis[2];
	delete[] vertexPairsToEdges;
	return minOBB;
}

static OBB FixedOrientationEnclosingOBB(const std::vector<vec3> &pointArray, const vec3 &dir0, const vec3 &dir1)
{
	int d0, d1;
	vec3 mindir, maxdir;
	ExtremePointsAlongDirection(pointArray, dir0, d0, d1, mindir.x, maxdir.x);
	ExtremePointsAlongDirection(pointArray, dir1, d0, d1, mindir.y, maxdir.y);
	vec3 edgeC = Normalized(cross(dir0, dir1));
	ExtremePointsAlongDirection(pointArray, edgeC, d0, d1, mindir.z, maxdir.z);
	vec3 center = (mindir + maxdir) * 0.5f;
	OBB minOBB;
	minOBB.pos = dir0*center.x + dir1*center.y + edgeC*center.z;
	minOBB.axis[0] = dir0;
	minOBB.axis[1] = dir1;
	minOBB.axis[2] = edgeC;
	minOBB.r = center - mindir;
	return minOBB;
}

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
		// (exact given each candidate axis) first, and keep the better of the two. The
		// volume > 0 check rejects the sweep's "no result" sentinel, which can otherwise
		// (volume 0) beat any real box in the comparison below.
		OBB sweep = CoarseSweepEnclosingOBB(convexHull.v);
		OBB planar = SmallestOBBVolume2DPlanar(points);
		if (!sweep.IsDegenerate() && sweep.Volume() > 0.f && sweep.Volume() < planar.Volume())
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