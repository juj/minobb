#include "minobb.h"

#include <vector>
#include <algorithm>
#include <cmath>
#include <cfloat>
#include <cstdlib>
#include <cstring>
#include <unordered_map>

// ---------------------------------------------------------------------------
// Optional per-stage profiling.
//
// Compile with PERF_TRACING_ENABLED defined (e.g. clang++ -DPERF_TRACING_ENABLED)
// to instrument the hot code paths with stage timers and loop counters. The
// collected numbers are printed to stderr when the MINOBB_TRACE environment
// variable is set (so a single binary can be switched on and off at run time).
//
// All instrumentation goes through the TRACE_* macros below. When
// PERF_TRACING_ENABLED is not defined, every macro expands to a no-op that
// does not evaluate any of its arguments, so the generated code is identical
// to the uninstrumented version.
// ---------------------------------------------------------------------------
#ifdef PERF_TRACING_ENABLED
#include <chrono>
#include <cstdarg>
#include <cstdio>
#include <cstdlib>

static bool TraceEnabled()
{
	static const bool on = getenv("MINOBB_TRACE") != nullptr;
	return on;
}
static double TraceNow()
{
	return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}
static void TraceLine(const char *msg, double sec)
{
	if (TraceEnabled())
		fprintf(stderr, "trace: %-44s %10.4f s\n", msg, sec);
}
static void TraceFmt(double sec, const char *fmt, ...)
{
	if (!TraceEnabled())
		return;
	char buf[256];
	va_list ap;
	va_start(ap, fmt);
	vsnprintf(buf, sizeof(buf), fmt, ap);
	va_end(ap);
	TraceLine(buf, sec);
}
// Cumulative counters for the extreme-vertex graph search (the innermost
// loop of the OBB category search), reported as per-stage deltas.
static long g_evcCalls = 0; // ExtremeVertexConvex() invocations
static long g_evcSteps = 0; // neighbor relaxations inside ExtremeVertexConvex()

#define TRACE_START()               TraceNow()
#define TRACE_MARK(t0, stage)       do { TraceLine(stage, TraceNow() - (t0)); (t0) = TraceNow(); } while (0)
#define TRACE_FMT(t0, fmt, ...)     do { TraceFmt(TraceNow() - (t0), fmt, __VA_ARGS__); (t0) = TraceNow(); } while (0)
#define TRACE_TICK(t, accum)        do { (accum) += TraceNow() - (t); } while (0)
#define TRACE_INC(ctr)              do { ++(ctr); } while (0)
#define TRACE_EVC_CALL()            do { ++g_evcCalls; } while (0)
#define TRACE_EVC_STEP()            do { ++g_evcSteps; } while (0)
#define TRACE_EVC_RESET(bc, bs)     do { (bc) = g_evcCalls; (bs) = g_evcSteps; } while (0)
#define TRACE_EVC_CALL_DELTA(bc)    (g_evcCalls - (bc))
#define TRACE_EVC_STEP_DELTA(bs)    (g_evcSteps - (bs))
#else
// Tracing disabled: every macro is a no-op. The (void) casts keep the timer
// and counter locals "used" so that no warnings appear and the optimizer
// removes everything.
#define TRACE_START()               (0.0)
#define TRACE_MARK(t0, stage)       do { (void)(t0); } while (0)
#define TRACE_FMT(t0, fmt, ...)     do { (void)(t0); } while (0)
#define TRACE_TICK(t, accum)        do { (void)(t); (void)(accum); } while (0)
#define TRACE_INC(ctr)              do { (void)(ctr); } while (0)
#define TRACE_EVC_CALL()            do {} while (0)
#define TRACE_EVC_STEP()            do {} while (0)
#define TRACE_EVC_RESET(bc, bs)     do { (void)(bc); (void)(bs); } while (0)
#define TRACE_EVC_CALL_DELTA(bc)    (0L)
#define TRACE_EVC_STEP_DELTA(bs)    (0L)
#endif

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

static vec3 abs(const vec3 &p)
{
	return vec3(fabsf(p.x), fabsf(p.y), fabsf(p.z));
}

static vec3 Max(const vec3 &a, const vec3 &b)
{
	return vec3(std::max(a.x, b.x), std::max(a.y, b.y), std::max(a.z, b.z));
}

static float LengthSq(const vec3 &v) { return dot(v, v); }
static float hmax(const vec3 &v) { return fmaxf(v.x, fmaxf(v.y, v.z)); }
static bool EqualAbs(float a, float b, float epsilon = 1e-4f) { return fabsf(a - b) < epsilon; }

float OBB::Distance(const vec3 &p) const
{
	return sqrtf(LengthSq(Max(abs(LocalToWorldInverse(p)) - r, vec3(0,0,0))));
}

// Normalizes the vector in place, returns the original length.
static float Normalize(vec3 &v)
{
	float lenSq = LengthSq(v);
	if (lenSq == 0.f) return 0.f;
	float len = sqrtf(lenSq);
	v *= 1.f / len;
	return len;
}

static vec3 Normalized(const vec3 &v)
{
	vec3 u = v;
	Normalize(u);
	return u;
}

static vec3 Perpendicular(const vec3 &v)
{
	// Choose the smallest magnitude component and cross with the corresponding unit axis.
	vec3 a = abs(v);
	float x = (float)(a.x < a.y && a.x < a.z);
	float y = (float)(a.y <= a.x && a.y < a.z);
	float z = (float)(a.z <= a.x && a.z <= a.y);
	return cross(vec3(x, y, z), v);
}

static void PerpendicularBasis(const vec3 &v, vec3 &outU, vec3 &outV)
{
	outU = Normalized(Perpendicular(v));
	outV = Normalized(cross(outU, v));
}

// A double precision vector, for the steps where single precision is not accurate enough.
struct dvec3
{
	double x, y, z;

	dvec3() : x(0.0), y(0.0), z(0.0) {}
	dvec3(double _x, double _y, double _z) : x(_x), y(_y), z(_z) {}
	dvec3(const vec3 &v) : x(v.x), y(v.y), z(v.z) {}

	dvec3 operator + (const dvec3 &b) const { return dvec3(x + b.x, y + b.y, z + b.z); }
	dvec3 operator - (const dvec3 &b) const { return dvec3(x - b.x, y - b.y, z - b.z); }
	dvec3 operator * (double s) const { return dvec3(x * s, y * s, z * s); }
	vec3 ToFloat() const { return vec3((float)x, (float)y, (float)z); }
};

static double dot(const dvec3 &a, const dvec3 &b) { return a.x*b.x + a.y*b.y + a.z*b.z; }
static dvec3 cross(const dvec3 &a, const dvec3 &b) { return dvec3(a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x); }
static dvec3 Normalized(const dvec3 &v)
{
	double len = sqrt(dot(v, v));
	return len > 0.0 ? v * (1.0 / len) : v;
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

static float2 operator - (const float2 *a, const float2 &b) { return *a - b; }

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
// Convex hull helpers
// ----------------------------------------------------------------------------

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

// Returns the unit normal of a face of the hull. Computed in double precision as the sum of the cross
// products of a triangle fan of the face (i.e. Newell's method, relative to the first vertex), so that
// also small and thin faces get an accurate normal.
// The cross product of each triangle is that of its two shortest sides. A hull can have vertices that are
// only some 1e-17 apart (where a ring of vertices of a mesh has collapsed into a point, say), and a
// triangle with such a side is a sliver: its two long sides are parallel to the precision of doubles, so
// their cross product is noise, or zero. The short side is accurate, as the difference of two vertices
// that are next to each other, and it is not parallel to the long ones.
static vec3 PolyhedronFaceNormal(const Hull3 &poly, int faceIndex)
{
	const std::vector<int> &face = poly.f[faceIndex];
	dvec3 normal;
	const dvec3 a = poly.v[face[0]];
	for(size_t i = 1; i + 1 < face.size(); ++i)
	{
		const dvec3 b = poly.v[face[i]], c = poly.v[face[i+1]];
		const dvec3 ab = b - a, bc = c - b, ca = a - c;
		const double abSq = dot(ab, ab), bcSq = dot(bc, bc), caSq = dot(ca, ca);
		// (Any two sides, taken in the order of the triangle, give the same product.)
		normal = normal + (abSq >= bcSq && abSq >= caSq ? cross(bc, ca) : (bcSq >= caSq ? cross(ca, ab) : cross(ab, bc)));
	}
	return Normalized(normal).ToFloat();
}

// ----------------------------------------------------------------------------
// OBB algorithm (ported from OBB.cpp)
// ----------------------------------------------------------------------------

struct Edge
{
	int first, second;
};


static OBB FixedOrientationEnclosingOBB(const std::vector<vec3> &points, const vec3 &dir0, const vec3 &dir1);

// The axes of the box that FixedOrientationEnclosingOBB() makes for the directions dir0 and dir1: dir0, dir1
// made orthogonal to it, and their cross product, as unit vectors.
static void BoxAxes(const vec3 &dir0, const vec3 &dir1, vec3 axis[3])
{
	dvec3 a[3];
	a[0] = Normalized(dvec3(dir0));
	a[1] = Normalized(dvec3(dir1) - a[0] * dot(a[0], dvec3(dir1)));
	a[2] = cross(a[0], a[1]);
	for (int i = 0; i < 3; ++i)
		axis[i] = a[i].ToFloat();
}

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
static void MoveSign(float &dst, float &src)
{
	if (src < 0.f)
	{
		dst = -dst;
		src = -src;
	}
}

// Port of ComputeBasis(): finds the orthonormal bases (n1, n2, n3) where each ni is in the arc between the two
// face normals fia and fib of an edge, i.e. the boxes that are flush with the three edges on three mutually
// adjacent faces. Solved in double precision and with relative thresholds: the coefficients below are
// differences of products of the normals, which cancel heavily and are all tiny when the normals of each
// edge are close to each other (which they are on finely tessellated hulls).
static int ComputeBasis(const vec3 &f1a, const vec3 &f1b,
	const vec3 &f2a, const vec3 &f2b,
	const vec3 &f3a, const vec3 &f3b,
	vec3 *n1,
	vec3 *n2,
	vec3 *n3)
{
	const double eps = 1e-4;
	const double angleEps = 1e-3;

	// n1 = a + b*t, n2 = c + d*u, n3 = e + f*v, with t, u, v in [0, 1].
	const dvec3 a = f1b;
	const dvec3 b = dvec3(f1a) - dvec3(f1b);
	const dvec3 c = f2b;
	const dvec3 d = dvec3(f2a) - dvec3(f2b);
	const dvec3 e = f3b;
	const dvec3 f = dvec3(f3a) - dvec3(f3b);

	const double g = dot(a, c)*dot(d, e) - dot(a, d)*dot(c, e);
	const double h = dot(a, c)*dot(d, f) - dot(a, d)*dot(c, f);
	const double i = dot(b, c)*dot(d, e) - dot(b, d)*dot(c, e);
	const double j = dot(b, c)*dot(d, f) - dot(b, d)*dot(c, f);

	const double k = g*dot(b, e) - dot(a, e)*i;
	const double l = h*dot(b, e) + g*dot(b, f) - dot(a, f)*i - dot(a, e)*j;
	const double m = h*dot(b, f) - dot(a, f)*j;

	// Solve m*v^2 + l*v + k = 0.
	double roots[2];
	int nRoots = 0;
	const double magnitude = std::max(fabs(k), std::max(fabs(l), fabs(m)));
	if (fabs(m) <= 1e-12 * magnitude)
	{
		// The equation is linear instead.
		if (fabs(l) > 1e-12 * magnitude)
			roots[nRoots++] = -k / l;
	}
	else
	{
		double s = l*l - 4.0*m*k;
		if (s < 0.0 && s > -1e-12 * std::max(l*l, fabs(4.0*m*k)))
			s = 0.0; // A double root, up to rounding.
		if (s < 0.0)
			return 0; // Discriminant negative, no solutions for v.
		const double q = -0.5 * (l + (l < 0.0 ? -1.0 : 1.0) * sqrt(s));
		roots[nRoots++] = q / m;
		if (s > 0.0 && q != 0.0)
			roots[nRoots++] = k / q;
	}

	int nSolutions = 0;
	for (int r = 0; r < nRoots; ++r)
	{
		const double v = roots[r];
		const double t = -(g + h*v) / (i + j*v);
		const double u = -(dot(c, e) + dot(c, f)*v) / (dot(d, e) + dot(d, f)*v);
		// If we happened to divide by zero above, the following checks handle them.
		if (v >= -eps && t >= -eps && u >= -eps && v <= 1.0 + eps && t <= 1.0 + eps && u <= 1.0 + eps)
		{
			const dvec3 N1 = Normalized(a + b*t);
			const dvec3 N2 = Normalized(c + d*u);
			const dvec3 N3 = Normalized(e + f*v);
			if (fabs(dot(N1, N2)) < angleEps
				&& fabs(dot(N1, N3)) < angleEps
				&& fabs(dot(N2, N3)) < angleEps)
			{
				n1[nSolutions] = N1.ToFloat();
				n2[nSolutions] = N2.ToFloat();
				n3[nSolutions] = N3.ToFloat();
				++nSolutions;
			}
		}
	}
	return nSolutions;
}

// Returns false if no normal on the arc from f1a to f1b is perpendicular to a normal on the arc from f2a to f2b,
// i.e. if no box can have two faces that are flush with the two edges of those arcs.
/*
	n1 = f1a*t + f1b*(1-t) = f1b + (f1a-f1b)*t
	n2 = f2a*u + f2b*(1-u) = f2b + (f2a-f2b)*u

	n1.n2 = 0

	Does this equation have a solution within t & u \in [0,1]?

	// The function f(t,u) = n1.n2 is continuous and bilinear
	// with respect to t and u, so test the four corners to get the minimum
	// and maximum of the function. If minimum <= 0 and
	// maximum >= 0, we know it must have a zero inside t,u \in [0,1].
*/
// The tolerance makes this a safe quick test for ComputeBasis(), which lets t and u be 1e-4 off their arcs (that
// changes n1.n2 by at most 4e-4) and takes |n1.n2| < 1e-3 for perpendicular.
static bool CanBePerpendicular(const vec3 &f1a, const vec3 &f1b, const vec3 &f2a, const vec3 &f2b)
{
	const float tolerance = 2e-3f;
	float aa = dot(f1a, f2a), ab = dot(f1a, f2b), ba = dot(f1b, f2a), bb = dot(f1b, f2b);
	return fminf(fminf(aa, ab), fminf(ba, bb)) <= tolerance && fmaxf(fmaxf(aa, ab), fmaxf(ba, bb)) >= -tolerance;
}

// Tells whether a box can have its three faces flush with three edges at once, as far as a quick test can
// tell: this is for telling that ComputeBasis() has no solution, and for following the solutions of two edges
// over the hull. The first two edges are given by the ends f1a, f1b and f2a, f2b of their arcs of normals, and
// by the unit normals e1 and e2 of the great circles of those arcs (the directions of the edges, that is).
// A unit vector n3 is the third axis of a box whose other two axes are on the two great circles, if those axes,
// which are then along e1 x n3 and e2 x n3, are perpendicular to each other: if (e1 x n3).(e2 x n3) =
// e1.e2 - (e1.n3)(e2.n3) is zero. For n3 = f3b + (f3a - f3b) v on the arc of the third edge, of the squared
// length 1 - v (1 - v) |f3a - f3b|^2, this times that squared length is a quadratic polynomial q(v).
// The third axis can only be on the part of the third arc where |q| is at most `tolerance`, which is for the
// rounding errors. (ComputeBasis() accepts more than that: its tolerances, |n1.n2| < 1e-3 and so on, allow |q|
// to be up to 3e-3. But those are there so as not to miss the solutions that are at an end of an arc.)
// And then the other two axes have to be on the arcs of their edges, not just on the great circles: that part
// of the third arc must have a normal that is perpendicular to a normal on the first arc, and one that is
// perpendicular to a normal on the second arc, see CanBePerpendicular().
// If the third axis can be on the arc, `range` is set to the part of the arc where: from f3b at 0 to f3a at 1.
static bool CanBeThirdAxis(const vec3 &f1a, const vec3 &f1b, const vec3 &e1, const vec3 &f2a, const vec3 &f2b, const vec3 &e2,
	float e1e2, float tolerance, const vec3 &f3a, const vec3 &f3b, float arcLengthSq, float *range)
{
	const float pa = dot(e1, f3a), pb = dot(e1, f3b), ra = dot(e2, f3a), rb = dot(e2, f3b);
	const float q0 = e1e2 - pb * rb, q1 = e1e2 - pa * ra; // q(0) and q(1).
	const float a = e1e2 * arcLengthSq - (pa - pb) * (ra - rb), b = q1 - q0 - a; // q(v) = a v^2 + b v + q0.
	if (fabsf(q0) > tolerance && fabsf(q1) > tolerance)
	{
		if (q0 * q1 > 0.f)
		{
			// The usual case, and the end of it: q is far from zero and of the same sign at both ends of the arc,
			// and so is its extreme value in between, at v = -b / 2a, if it has one there.
			if (!(a > 0.f ? b < 0.f && -b < 2.f * a : b > 0.f && b < -2.f * a))
				return false;
			const float extreme = q0 - 0.25f * b * b / a;
			if (extreme * q0 > 0.f && fabsf(extreme) > tolerance)
				return false;
		}
		else
		{
			// The other usual case: q changes its sign on the arc, so it has one root there, and the third axis
			// can only be there. (The roots are computed without cancellation. A division by zero gives a
			// root that is not in [0, 1].)
			const float r = -0.5f * (b + (b < 0.f ? -1.f : 1.f) * sqrtf(b * b - 4.f * a * q0));
			const float root = r / a >= 0.f && r / a <= 1.f ? r / a : q0 / r;
			if (root >= 0.f && root <= 1.f)
			{
				range[0] = range[1] = root;
				const vec3 n3 = f3b + (f3a - f3b) * root;
				return CanBePerpendicular(f1a, f1b, n3, n3) && CanBePerpendicular(f2a, f2b, n3, n3);
			}
		}
	}
	// The first and the last v in [0, 1] at which |q| is within the tolerance: the end of the arc, or else where
	// q first reaches the tolerance when coming from that end.
	for(int end = 0; end < 2; ++end)
	{
		const float q = end == 0 ? q0 : q1;
		range[end] = (float)end;
		if (fabsf(q) <= tolerance)
			continue;
		const float c = q0 - (q > 0.f ? tolerance : -tolerance);
		const float discriminant = b * b - 4.f * a * c;
		if (!(discriminant >= 0.f))
			return false;
		const float r = -0.5f * (b + (b < 0.f ? -1.f : 1.f) * sqrtf(discriminant));
		const float roots[2] = { r / a, c / r };
		range[end] = -1.f;
		for(int k = 0; k < 2; ++k)
			if (roots[k] > 0.f && roots[k] < 1.0001f && (range[end] < 0.f || (roots[k] < range[end]) == (end == 0)))
				range[end] = fminf(roots[k], 1.f);
		if (range[end] < 0.f)
			return false;
	}
	const vec3 n3a = f3b + (f3a - f3b) * range[0], n3b = f3b + (f3a - f3b) * range[1];
	return CanBePerpendicular(f1a, f1b, n3a, n3b) && CanBePerpendicular(f2a, f2b, n3a, n3b);
}

// The boxes that have a face flush with each of two edges have the normals n1 = f1b + (f1a - f1b) t and
// n2 = f2b + (f2a - f2b) u of those faces perpendicular to each other: a + b t + c u + d t u = 0, with t and u in
// [0, 1]. They come in one or two families, in each of which the box turns from one end of the family to the
// other. Appends the direction n1 x n2 of the third axis of one box of each family to `axes`.
static void ThirdAxesOfBoxes(const vec3 &f1a, const vec3 &f1b, const vec3 &f2a, const vec3 &f2b, std::vector<vec3> &axes)
{
	const dvec3 base[2] = { f1b, f2b }, step[2] = { dvec3(f1a) - dvec3(f1b), dvec3(f2a) - dvec3(f2b) };
	const double a = dot(base[0], base[1]), d = dot(step[0], step[1]);
	{
		// Usually there is one family, with a box in the middle of the first arc: u is within [0, 1] at t = 1/2,
		// and has no pole at any t of [0, 1].
		const double b = dot(step[0], base[1]), c = dot(step[1], base[0]);
		const double u = -(a + b * 0.5) / (c + d * 0.5), pole = -c / d;
		if (u >= 0.0 && u <= 1.0 && !(pole >= 0.0 && pole <= 1.0))
		{
			axes.push_back(Normalized(cross(base[0] + step[0] * 0.5, base[1] + step[1] * u)).ToFloat());
			return;
		}
	}
	// As a function of t, u = -(a + b t) / (c + d t) is monotonic on each side of its pole t = -c/d. So between
	// the pole and where u crosses 0 and 1, u is either within [0, 1] or it is not: take the middle of each such
	// interval of t in which it is. Should there be none, there may still be boxes that all have the same t:
	// then do the same with u as a function of t. (The 1e-4 is the tolerance of ComputeBasis().)
	for (int swapped = 0; swapped < 2 && axes.empty(); ++swapped)
	{
		const double b = dot(step[swapped], base[1 - swapped]), c = dot(step[1 - swapped], base[swapped]);
		double cuts[5] = { 0.0, 1.0, -a / b, -(a + c) / (b + d), -c / d };
		int n = 2;
		for (int k = 2; k < 5; ++k)
			if (cuts[k] > 0.0 && cuts[k] < 1.0)
				cuts[n++] = cuts[k];
		std::sort(cuts, cuts + n);
		for (int k = 0; k + 1 < n; ++k)
		{
			const double x = (cuts[k] + cuts[k + 1]) * 0.5;
			const double y = -(a + b * x) / (c + d * x);
			if (y >= -1e-4 && y <= 1.0 + 1e-4)
			{
				const dvec3 n1 = base[swapped] + step[swapped] * x;
				const dvec3 n2 = base[1 - swapped] + step[1 - swapped] * std::min(std::max(y, 0.0), 1.0);
				axes.push_back(Normalized(swapped ? cross(n2, n1) : cross(n1, n2)).ToFloat());
			}
		}
	}
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

static int ClimbAlong(const std::vector<vec3> &vtx, const std::vector<std::vector<int> > &adjacencyData, const vec3 &direction, int startingVertex);

// Sets `found` to the vertices of the hull that are the farthest along `direction`: to all the vertices that
// are within `margin` of the farthest one, and perhaps some more. A climb from startingVertex gets to the
// farthest vertex, or near it. On a convex polyhedron the vertices that are at least as far as any given
// distance are connected, so the rest is a walk from neighbor to neighbor. (`margin` is to be far larger than
// what a distance rounds by. Then the walk also gets past the vertices that tie, where a climb stops.)
// `visited` has a mark for each vertex, and `color` is a mark that none of them has yet.
static void FarVerticesAlong(const std::vector<vec3> &vtx, const std::vector<std::vector<int> > &adjacencyData, const vec3 &direction,
	int startingVertex, float margin, std::vector<unsigned long long> &visited, unsigned long long color, std::vector<int> &found)
{
	found.clear();
	found.push_back(ClimbAlong(vtx, adjacencyData, direction, startingVertex));
	visited[found[0]] = color;
	float farthest = dot(direction, vtx[found[0]]);
	for (size_t i = 0; i < found.size(); ++i)
	{
		const std::vector<int> &neighbors = adjacencyData[found[i]];
		for (size_t j = 0; j < neighbors.size(); ++j)
		{
			const int n = neighbors[j];
			if (visited[n] == color)
				continue;
			const float d = dot(direction, vtx[n]);
			if (d < farthest - margin)
				continue;
			visited[n] = color;
			found.push_back(n);
			farthest = std::max(farthest, d);
		}
	}
}

// What MeasureBox() needs for measuring a box with only the vertices of the hull that decide its size, and
// its count of whether that pays off on the hull at hand: see MeasureBox(). Also the tolerance of the search.
struct BoxProbe
{
	// What share of the volume of the best box a box has to be below to take its place: 1 / (1 + tolerance),
	// see minVolume in OptimalEnclosingOBB3D().
	const float volumeShareToBeat;
	const std::vector<std::vector<int> > &adjacencyData;
	// The marks of its searches. (Not those of the caller, who can have a graph search of its own under way.)
	std::vector<unsigned long long> visited;
	unsigned long long visitColor;
	// The latest searches: the direction of each, the far vertices that it found along it, and when it was
	// last of use.
	enum { numSearches = 12 };
	vec3 direction[numSearches];
	std::vector<int> farVertices[numSearches];
	long long lastUse[numSearches], numUses;
	// What the searches have saved so far, less what they have taken, in vertices of a pass over the hull.
	long long balance;
	std::vector<vec3> points;

	BoxProbe(float volumeShareToBeat_, const std::vector<std::vector<int> > &adjacencyData_, size_t numVertices)
		: volumeShareToBeat(volumeShareToBeat_), adjacencyData(adjacencyData_), visited(numVertices), visitColor(0), numUses(0), balance(0)
	{
		for (int i = 0; i < numSearches; ++i)
			lastUse[i] = 0;
	}
};

// Measures the box with the axes n1 and n2 (and their cross product), and makes it the best box if its volume
// is below *minVolume: below the volume of the best box so far, less the tolerance of the search. *minVolume
// is then set for the next box to beat. See minVolume in OptimalEnclosingOBB3D().
// (hullV are the vertices of the hull as OptimalEnclosingOBB3D() gets them: at most 28 from the origin.)
// (Not to be inlined: this is called for few of the boxes that TestBox() is, and as a part of the code of its
// callers it slows the search of a small hull down by a percent or two.)
#if defined(_MSC_VER)
__declspec(noinline)
#else
__attribute__((noinline))
#endif
static void MeasureBox(const std::vector<vec3> &hullV, const vec3 &n1, const vec3 &n2, float *minVolume, OBB *minOBB, BoxProbe &probe)
{
	// The axes must be (roughly) orthonormal for this to be a box at all. This also catches zero vectors and NaNs.
	if (!(fabsf(LengthSq(n1) - 1.f) < 0.01f && fabsf(LengthSq(n2) - 1.f) < 0.01f && fabsf(dot(n1, n2)) < 0.01f))
		return;

	// Measuring the box takes passes over all the vertices of the hull. A hull with symmetries has thousands
	// of boxes that are as small as its best box, up to rounding, and `volume` makes about half of them out
	// to be smaller: all their passes are for nothing. So the box is first measured with only the six
	// vertices that decide its size: the farthest ones along its axes, both ways. That gives the same box as
	// all the vertices do, or a smaller one: so if it is no smaller than the best box, the box is of no use.
	//
	// Each of the six is the farthest one, as doubles tell it, of the far vertices that a search along the
	// edges of the hull finds for its direction: of all the vertices that are within 0.01 of the farthest
	// one. Or of the far vertices that an earlier search found, if that was along the same direction to
	// within 5e-5 in each coordinate: two such directions differ by less than 0.005 in how far apart they
	// have any two of the vertices, so the far vertices of one include the farthest vertex of the other. (A
	// hull with symmetries has the same axis in box after box, and where that is the axis of a body of
	// revolution, its far vertices are whole rings of vertices.)
	//
	// The searches take the time of a pass over 128 vertices or so, and more where many vertices tie, as on
	// the flat sides of a box that is densely covered with vertices. probe.balance keeps count, and once the
	// searches have taken much more than they have saved, there are no more of them.
	const long long numVertices = (long long)hullV.size();
	if (numVertices >= 256 && probe.balance >= -16 * numVertices)
	{
		const float sameDirection = 5e-5f, farMargin = 1e-2f;
		vec3 axis[3];
		BoxAxes(n1, n2, axis);
		// (FixedOrientationEnclosingOBB() measures from the first point it is given: the same one here, for the same rounding.)
		const dvec3 origin = hullV[0];
		probe.points.clear();
		probe.points.push_back(hullV[0]);
		long long cost = 128;
		for (int i = 0; i < 6; ++i)
		{
			const vec3 direction = (i & 1) ? -axis[i / 2] : axis[i / 2];
			// The search along this direction, if there is one. Else the one that has been of no use for the
			// longest makes way for a new search, which starts from where the search along the nearest
			// direction got to.
			int search = -1, oldest = 0, nearest = 0;
			float nearestDot = -FLT_MAX;
			for (int k = 0; k < BoxProbe::numSearches && search < 0; ++k)
			{
				if (probe.lastUse[k] < probe.lastUse[oldest])
					oldest = k;
				if (!probe.lastUse[k])
					continue;
				const vec3 difference = probe.direction[k] - direction;
				if (fabsf(difference.x) <= sameDirection && fabsf(difference.y) <= sameDirection && fabsf(difference.z) <= sameDirection)
					search = k;
				else if (dot(probe.direction[k], direction) > nearestDot)
				{
					nearestDot = dot(probe.direction[k], direction);
					nearest = k;
				}
			}
			if (search < 0)
			{
				search = oldest;
				FarVerticesAlong(hullV, probe.adjacencyData, direction, probe.lastUse[nearest] ? probe.farVertices[nearest][0] : 0, farMargin,
					probe.visited, ++probe.visitColor, probe.farVertices[search]);
				probe.direction[search] = direction;
				cost += 4 * (long long)probe.farVertices[search].size(); // (A vertex of a search takes as long as four of a pass.)
			}
			else
				cost += (long long)probe.farVertices[search].size() / 4;
			probe.lastUse[search] = ++probe.numUses;

			// The farthest one of them, by the distance that FixedOrientationEnclosingOBB() measures.
			const std::vector<int> &farVertices = probe.farVertices[search];
			int farthest = farVertices[0];
			double farthestDistance = -DBL_MAX;
			for (size_t j = 0; j < farVertices.size(); ++j)
			{
				const double distance = dot(dvec3(direction), dvec3(hullV[farVertices[j]]) - origin);
				if (distance > farthestDistance)
				{
					farthestDistance = distance;
					farthest = farVertices[j];
				}
			}
			probe.points.push_back(hullV[farthest]);
		}
		const bool smaller = FixedOrientationEnclosingOBB(probe.points, n1, n2).Volume() < *minVolume;
		probe.balance = std::min(probe.balance + (smaller ? 0 : numVertices) - cost, 16 * numVertices);
		if (!smaller)
			return;
	}

	OBB obb = FixedOrientationEnclosingOBB(hullV, n1, n2);
	if (obb.Volume() < *minVolume)
	{
		*minOBB = obb;
		*minVolume = obb.Volume() * probe.volumeShareToBeat;
	}
}

// Makes the box with the axes n1 and n2 (and their cross product) the best box, if it is smaller than
// the best box so far, by more than the tolerance of the search: if its volume is below *minVolume. `volume`
// is the volume that the search derived for the box from the vertices it assumed the box to be in contact
// with: that can only be smaller than the volume of the actual tightest box of that orientation, which
// therefore is measured only if `volume` is below *minVolume.
static inline void TestBox(const std::vector<vec3> &hullV, const vec3 &n1, const vec3 &n2, float volume,
	float *minVolume, OBB *minOBB, BoxProbe &probe)
{
	if (volume < *minVolume)
		MeasureBox(hullV, n1, n2, minVolume, minOBB, probe);
}

// Port of TestThreeAdjacentFaces().
static void TestThreeAdjacentFaces(const vec3 &n1, const vec3 &n2, const vec3 &n3,
	int edgeI, int edgeJ, int edgeK,
	const std::vector<vec3> &hullV, const std::vector<Edge> &edges,
	const std::vector<std::vector<int>> &antipodalPointsForEdge,
	float *minVolume, OBB *minOBB, BoxProbe &probe)
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
	TestBox(hullV, n1, n2, volume, minVolume, minOBB, probe);
}

// Climbs along the edges of the hull from startingVertex, each time to the neighbor that is the farthest along
// `direction`, and returns the vertex that has no neighbor farther along it. On a convex polyhedron that is an
// extreme vertex, unless the climb ends where vertices tie: see ExtremeVertexConvex(), which this is a cheaper
// substitute for when any vertex that is far along the direction will do.
static int ClimbAlong(const std::vector<vec3> &vtx, const std::vector<std::vector<int> > &adjacencyData, const vec3 &direction, int startingVertex)
{
	int v = startingVertex;
	float d = dot(direction, vtx[v]);
	for(;;)
	{
		const std::vector<int> &neighbors = adjacencyData[v];
		int farthest = v;
		for(size_t i = 0; i < neighbors.size(); ++i)
		{
			float neighborD = dot(direction, vtx[neighbors[i]]);
			if (neighborD > d)
			{
				d = neighborD;
				farthest = neighbors[i];
			}
		}
		if (farthest == v)
			return v;
		v = farthest;
	}
}

// Finds the vertex of the hull that is the farthest along `direction`, by climbing along the edges of the
// hull, starting from startingVertex. On a convex polyhedron the vertices that are at least as far as any
// given distance are connected, so the climb can only come to a halt too early where vertices tie: on a
// face or an edge that is perpendicular to the direction, to the precision of the distances. Such a
// plateau is therefore searched through for a vertex that is farther still.
// If `ties` is given, the returned vertex and all the vertices that tie with it are appended to it.
static int ExtremeVertexConvex(const Hull3 &hull, const std::vector<std::vector<int> > &adjacencyData, const vec3 &direction,
	std::vector<unsigned long long> &floodFillVisited, unsigned long long floodFillVisitColor,
	float &mostExtremeDistance, int startingVertex, std::vector<int> *ties = 0)
{
	TRACE_EVC_CALL();
	const float plateauEpsilon = 1e-4f;
	if (!ties)
	{
		// Usually there are no ties where the plain climb ends: then that is the extreme vertex.
		startingVertex = ClimbAlong(hull.v, adjacencyData, direction, startingVertex);
		mostExtremeDistance = dot(direction, hull.v[startingVertex]);
		const std::vector<int> &neighbors = adjacencyData[startingVertex];
		bool tied = false;
		for(size_t i = 0; i < neighbors.size() && !tied; ++i)
			tied = dot(direction, hull.v[neighbors[i]]) >= mostExtremeDistance - plateauEpsilon;
		if (!tied)
			return startingVertex;
	}
	static thread_local std::vector<int> plateau, visited;
	plateau.clear();
	visited.clear();

	float curD = dot(direction, hull.v[startingVertex]);
	floodFillVisited[startingVertex] = floodFillVisitColor;
	if (ties) visited.push_back(startingVertex);
	int v = startingVertex; // The vertex whose neighbors are examined: the farthest vertex so far, or one on its plateau.
	while(v != -1)
	{
		const std::vector<int> &neighbors = adjacencyData[v];
		const int from = v;
		v = -1;
		for(size_t i = 0; i < neighbors.size(); ++i)
		{
			TRACE_EVC_STEP();
			int n = neighbors[i];
			if (floodFillVisited[n] == floodFillVisitColor)
				continue;
			float d = dot(direction, hull.v[n]);
			if (d < curD - plateauEpsilon)
				continue;
			floodFillVisited[n] = floodFillVisitColor;
			if (ties) visited.push_back(n);
			if (d > curD)
			{
				// Climb on from this neighbor. The remaining neighbors are looked at later, if still relevant.
				plateau.push_back(from);
				startingVertex = v = n;
				curD = d;
				break;
			}
			plateau.push_back(n);
		}
		// No neighbor was farther: continue from a vertex that is (still) on the plateau, if any.
		while(v == -1 && !plateau.empty())
		{
			if (dot(direction, hull.v[plateau.back()]) >= curD - plateauEpsilon)
				v = plateau.back();
			plateau.pop_back();
		}
	}
	if (ties)
		for(size_t i = 0; i < visited.size(); ++i)
			if (dot(direction, hull.v[visited[i]]) >= curD - plateauEpsilon)
				ties->push_back(visited[i]);
	mostExtremeDistance = curD;
	return startingVertex;
}

// The volume bounds of the edges, see OptimalEnclosingOBB3D(), divide the directions of a plane into sectors.
// A direction and its opposite are the same here (the direction of a line), so half a turn has them all. These
// are the directions at the ends and in the middles of the sectors, for the largest number of sectors in use,
// as the cosines and sines of their angles: there are 4 maxSamples of them per turn.
struct PlaneDirections
{
	enum { maxSamples = 128 };
	double cosine[4 * maxSamples + 1], sine[4 * maxSamples + 1];
	PlaneDirections()
	{
		for (int k = 0; k <= 4 * maxSamples; ++k)
		{
			cosine[k] = cos(k * 3.14159265358979323846 / (2 * maxSamples));
			sine[k] = sin(k * 3.14159265358979323846 / (2 * maxSamples));
		}
	}
};

// What the bounds tell about the sectors is kept as a mask of 64 bits: one bit for each of 64 sectors that
// divide half a turn. Returns where the direction (x, y) of a plane is in that half a turn: the angle of the
// line along it, from 0 up to 64 (which is the same as 0). Accurate to 0.08 sectors.
static float SectorOfDirection(float x, float y)
{
	const float ax = fabsf(x), ay = fabsf(y), larger = fmaxf(ax, ay);
	if (!(larger > 0.f))
		return 0.f;
	const float ratio = fminf(ax, ay) / larger;
	float angle = ratio * (0.785398163f + 0.273f * (1.f - ratio)); // The arc tangent of the ratio, to 0.0038 radians.
	if (ay > ax)
		angle = 1.570796327f - angle;
	if ((x < 0.f) != (y < 0.f))
		angle = 3.141592654f - angle;
	const float sector = angle * (64.f / 3.141592654f);
	return sector < 64.f ? sector : 0.f;
}

// Returns the mask of the sectors from `from` to `to` (as SectorOfDirection() numbers them), the short way
// around, and of an eighth of a sector more at both ends, which makes up for the inaccuracy of the numbers.
static unsigned long long SectorsBetween(float from, float to)
{
	float turn = to - from;
	if (turn > 32.f)
		turn -= 64.f;
	else if (turn < -32.f)
		turn += 64.f;
	const float low = fminf(from, from + turn) - 0.125f, high = fmaxf(from, from + turn) + 0.125f;
	const int first = (int)floorf(low), count = (int)floorf(high) - first + 1;
	if (count >= 64)
		return ~0ULL;
	const unsigned long long sectors = (1ULL << count) - 1;
	const int shift = ((first % 64) + 64) % 64;
	return shift == 0 ? sectors : ((sectors << shift) | (sectors >> (64 - shift)));
}

// Takes two arcs of normals, from fb to fa and from gb to ga, and the dot products of their ends. The normals
// of the first arc that are perpendicular to a normal of the second one are those whose dot products with ga
// and gb do not have the same sign. Returns the mask of the sectors that they are in, in the plane that has
// the basis (u, v): the sectors of their components in that plane. Returns all the sectors if it cannot tell.
// The normals are to be close to the plane, as they are when the plane is the one of the volume bound of
// the edge of the second arc, and that arc is short enough for that bound to tell sectors apart.
static unsigned long long SectorsOfPerpendicularNormals(const vec3 &fa, const vec3 &fb, float faGa, float faGb, float fbGa, float fbGb,
	const vec3 &u, const vec3 &v)
{
	// Along the first arc, at fb + (fa - fb) t, the two dot products are linear in t. If both of them grow or
	// both shrink with t, their signs differ between where one is zero and where the other one is.
	const float slopeA = faGa - fbGa, slopeB = faGb - fbGb;
	if (!(slopeA * slopeB > 0.f))
		return ~0ULL;
	const float zeroA = -fbGa / slopeA, zeroB = -fbGb / slopeB;
	const float t0 = fminf(fmaxf(fminf(zeroA, zeroB), 0.f), 1.f), t1 = fminf(fmaxf(fmaxf(zeroA, zeroB), 0.f), 1.f);
	const vec3 from = fb + (fa - fb) * t0, to = fb + (fa - fb) * t1;
	// From one end of that piece of the arc to the other, the direction in the plane turns one way, by little
	// more than the angle between the two ends. The sectors tell directions apart only up to half a turn, so
	// this is for pieces of up to 60 degrees.
	const float d = dot(from, to);
	if (!(d > 0.f && d * d >= 0.25f * LengthSq(from) * LengthSq(to)))
		return ~0ULL;
	return SectorsBetween(SectorOfDirection(dot(from, u), dot(from, v)), SectorOfDirection(dot(to, u), dot(to, v)));
}

// Port of OBB::OptimalEnclosingOBB(const Polyhedron &).
// Returns an OBB with IsDegenerate() == true if the input is (near) planar.
// `faceNormals` are the unit normals of the faces of the hull.
// Searches for the smallest box around the hull. `volumeShareToBeat` is 1 / (1 + tolerance): the box that is
// returned has at most 1 + tolerance times the volume of the smallest box (1 for the smallest box itself).
static OBB OptimalEnclosingOBB3D(const Hull3 &hull, const std::vector<vec3> &faceNormals, float volumeShareToBeat)
{
	double t0 = TRACE_START();
	long evcCalls0 = 0, evcSteps0 = 0;
	TRACE_EVC_RESET(evcCalls0, evcSteps0);
	/* Outline of the algorithm:
	  0. Compute the convex hull of the point set (given as input to this function) O(VlogV)
	  1. Compute vertex adjacency data, i.e. given a vertex, return a list of its neighboring vertices. O(V)
	  2. Precompute face normal direction vectors, since these are needed often. (does not affect big-O complexity, just a micro-opt) O(F)
	  3. Compute edge adjacency data, i.e. given an edge, return the two indices of its neighboring faces. O(V)
	  4. Precompute antipodal vertices for each edge. O(A*ElogV), where A is the size of antipodal vertices per edge. A ~ O(1) on average.
	  5. Compute for each edge lower bounds for the width of the hull along the normals of the box faces that can be
	     flush with the edge, and for the volume of the boxes that have such a face. O(E)
	     The steps below skip whatever these bounds show to be no smaller than the best box found so far. The
	     volume bounds also tell in which directions around an edge the other axes of a smaller box can be: the
	     search for the sidepodal edges of the edge stays in those. For the edges whose arc of normals is long,
	     the bounds are computed for pieces of the arc, once the steps below turn out to take long with them.
	  6. Test all configurations where two edges are on opposing faces, and the third one is on a face adjacent to the two. O(E*sqrtE*logV)?
	  7. Test all configurations where two edges are on the same face (OBB aligns with a face of the convex hull). O(F*sqrtE*logV).
	  8. Test all configurations where all three edges are on adjacent faces. O(ES) = O(E*sqrtE)?, where S is the size
	     of sidepodal edges per edge, S ~ O(sqrtE) on average: for each edge and each of its sidepodal edges, the
	     third edges are found by a graph search along the boxes that are flush with the two.
	  9. Return the best found OBB.
	  The sidepodal edges of an edge are computed when steps 6-8 first need them. O(S) per edge.
	  With a tolerance, a box only replaces the best box if it is smaller by more than the tolerance, and the
	  steps above skip whatever cannot be that much smaller: see minVolume.
	*/

	OBB minOBB;
	minOBB.r = vec3(-FLT_MAX, -FLT_MAX, -FLT_MAX); // Degenerate marker.
	// The volume that a box has to be below to become the best box: the volume of the best box so far times
	// volumeShareToBeat, i.e. divided by 1 + tolerance. Everything that the search rules out is a box, or a set
	// of boxes, that is shown to be no smaller than this at the time. This only goes down, so at the end the
	// smallest box of all is no smaller than this either: the best box has at most 1 + tolerance times its
	// volume. Without a tolerance this is the volume of the best box, which then is the smallest box.
	// (Where the comments below say that something is no smaller than the best box, or cannot be smaller,
	// they mean no smaller than this.)
	// On a hull that has many boxes nearly as small as the smallest one, as a finely tessellated ball does, a
	// tolerance takes the search from minutes to seconds: without it, next to nothing can be ruled out there.
	float minVolume = FLT_MAX;

	// Handle degenerate planar cases up front.
	if (hull.v.size() <= 3 || hull.f.size() <= 1)
		return minOBB;

	// Precomputation: for each vertex in the convex hull, compute their neighboring vertices.
	std::vector<std::vector<int> > adjacencyData = GenerateVertexAdjacencyData(hull); // O(V)

	const std::vector<vec3> &vtx = hull.v;
	const int V = (int)vtx.size();
	const int F = (int)hull.f.size();

	for(int i = 0; i < F; ++i) // O(F)
		if (hull.f[i].size() < 3) return minOBB; // Degenerate face, cannot process.

	// For each edge i, specifies the two vertices v0 and v1 through which that edge goes.
	// This array does not have duplicates, i.e. there only exists one edge index for (v0->v1), and no
	// edge for (v1->v0).
	std::vector<Edge> edges;
	edges.reserve(V * 2);
	// For each edge i, specifies the two face indices f0 and f1 that share that edge.
	std::vector<std::pair<int, int>> facesForEdge;
	facesForEdge.reserve(V * 2);
	// The edge indices of the vertex pairs (v0, v1) through which there is an edge, in two forms:
	// For each neighbor of each vertex, in the order of adjacencyData, the index of the edge between the two.
	std::vector<std::vector<int> > adjacentEdges(V);
	// For each vertex of each face, the index of the edge that leads to it from the previous vertex of the face.
	std::vector<std::vector<int> > faceEdges(F);

	// Precomputation: for each edge through vertices (i,j), we need to know
	// the face indices for the two adjoining faces that share the edge.
	// This is O(V).
	{
		// Maps a vertex pair, the smaller index first, to the index of the edge that passes through them.
		std::unordered_map<unsigned long long, int> vertexPairsToEdges;
		vertexPairsToEdges.reserve((size_t)V * 4);
		for (int fi = 0; fi < F; ++fi)
		{
			const std::vector<int> &face = hull.f[fi];
			int v0 = face.back();
			for (size_t j = 0; j < face.size(); ++j)
			{
				int v1 = face[j];
				unsigned long long vertexPair = ((unsigned long long)std::min(v0, v1) << 32) | (unsigned int)std::max(v0, v1);
				std::pair<std::unordered_map<unsigned long long, int>::iterator, bool> edge =
					vertexPairsToEdges.insert(std::make_pair(vertexPair, (int)edges.size()));
				if (edge.second)
				{
					edges.push_back({ v0, v1 });
					facesForEdge.push_back({ fi, -1 }); // The -1 will be filled once we see the edge v1->v0.
				}
				else
					facesForEdge[edge.first->second].second = fi;
				faceEdges[fi].push_back(edge.first->second);
				v0 = v1;
			}
		}
		for (int v0 = 0; v0 < V; ++v0)
			for (size_t j = 0; j < adjacencyData[v0].size(); ++j)
			{
				int v1 = adjacencyData[v0][j];
				adjacentEdges[v0].push_back(vertexPairsToEdges[((unsigned long long)std::min(v0, v1) << 32) | (unsigned int)std::max(v0, v1)]);
			}
	}

	TRACE_FMT(t0, "obb: precompute adjacency+edges (V=%d F=%d E=%d)", V, F, (int)edges.size());

	// Throughout the algorithm, internal edges (edges between coplanar faces) can all be discarded. The faces of
	// the hull are its actual facets, so no two adjacent faces are exactly coplanar; but if their normals are
	// equal to the precision of single precision floats, the edge has no normal arc to speak of. Note that
	// the tolerance cannot be any larger than that: when the hull is flat, tilting a box face by an angle
	// changes the volume of the box by that angle times the aspect ratio of the box.
	const int E = (int)edges.size();
	std::vector<unsigned char> isInternalEdge(E);
	for (int i = 0; i < E; ++i)
	{
		dvec3 diff = dvec3(faceNormals[facesForEdge[i].first]) - dvec3(faceNormals[facesForEdge[i].second]);
		isInternalEdge[i] = dot(diff, diff) < 1e-12;
	}
#define IS_INTERNAL_EDGE(i) (isInternalEdge[i] != 0)

	// Throughout the whole algorithm, this array stores an auxiliary structure for performing graph searches
	// on the vertices of the convex hull. Conceptually each index of the array stores a boolean whether we
	// have visited that vertex or not during the current search. However storing such booleans is slow, since
	// we would have to perform a linear-time scan through this array before next search to reset each boolean
	// to unvisited false state. Instead, store a number, called a "color" for each vertex to specify whether
	// that vertex has been visited, and manage a global color counter floodFillVisitColor that represents the
	// visited vertices. At any given time, the vertices that have already been visited have the value
	// floodFillVisited[i] == floodFillVisitColor in them. This gives a win that we can perform constant-time
	// clears of the floodFillVisited array, by simply incrementing the "color" counter to clear the array.
	// (The counter has 64 bits, so that it cannot wrap around.)
	std::vector<unsigned long long> floodFillVisited(hull.v.size());
	unsigned long long floodFillVisitColor = 1;

	// As a syntactic aid, use the helpers MARK_VISITED(v), HAVE_VISITED_VERTEX(v) and CLEAR_GRAPH_SEARCH to
	// remind of the conceptual meaning of these values.
#define MARK_VERTEX_VISITED(v) (floodFillVisited[(v)] = floodFillVisitColor)
#define HAVE_VISITED_VERTEX(v) (floodFillVisited[(v)] == floodFillVisitColor) // HAVE_VISITED_VERTEX(v) implies HAVE_QUEUED_VERTEX(v)
#define CLEAR_GRAPH_SEARCH() (++floodFillVisitColor)

	// For TestBox(): the searches that it measures a box with, and the tolerance.
	BoxProbe boxProbe(volumeShareToBeat, adjacencyData, hull.v.size());

	// Stores for each edge index i the complete list of antipodal vertices for that edge.
	std::vector<std::vector<int> > antipodalPointsForEdge(E);

	// The currently best variant for establishing a spatially coherent traversal order.
	std::vector<int> spatialFaceOrder;
	std::vector<int> spatialEdgeOrder;
	srand(123); // TODO: mini RNG
//	LCG rng(123);
	{ // Explicit scope for variables that are not needed after this.
		std::vector<std::pair<int, int> > traverseStackEdges; // An edge, and the vertex of it to continue from.
		std::vector<unsigned int> visitedEdges(edges.size());
		std::vector<unsigned int> visitedFaces(hull.f.size());
		traverseStackEdges.push_back(std::make_pair(adjacentEdges[0].front(), adjacencyData[0].front()));
		while(!traverseStackEdges.empty())
		{
			std::pair<int, int> e = traverseStackEdges.back();
			traverseStackEdges.pop_back();
			int thisEdge = e.first;
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
				int e1 = adjacentEdges[v0][i];
				if (visitedEdges[e1])
					continue;
				traverseStackEdges.push_back(std::make_pair(e1, adjacencyData[v0][i]));
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

	TRACE_MARK(t0, "obb: spatial ordering (dual-graph walk)");

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
	long antiFallbacks = 0;
	long sidepodalSearches = 0, edgePairs = 0, edgePairsSearched = 0, edgeTriplets = 0, edgeTripletsSolved = 0, thirdEdgesTested = 0;
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
				// A vertex of the edge itself can pass the test only due to its tolerances (the hull
				// is nearly flat there): it is not antipodal to its own edge.
				if (edges[i].first == v || edges[i].second == v)
					continue;
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
			TRACE_INC(antiFallbacks);
//			LOGW("Due to numerical stability issues(?), could not find an antipodal vertex for edge %d! Check the scale of your input dataset! Good scale is having coordinates range e.g. [0.0,100.0]", edges[i]);
			// Getting here is most likely a bug. Fall back to linear scan, which is very slow.
			for(size_t j = 0; j < hull.v.size(); ++j) // O(V)
				if (edges[i].first != (int)j && edges[i].second != (int)j && IsVertexAntipodalToEdge(hull.v, (int)j, adjacencyData[j], f1a, f1b))
					antipodalPointsForEdge[i].push_back((int)j);

//			antipodalPointsForEdge[i].push_back(startingVertex);
		}
	}
//#endif
	TRACE_FMT(t0, "obb: antipodal precompute (evc calls=%ld steps=%ld fallbacks=%ld)",
		TRACE_EVC_CALL_DELTA(evcCalls0), TRACE_EVC_STEP_DELTA(evcSteps0), antiFallbacks);
	TRACE_EVC_RESET(evcCalls0, evcSteps0);

	// For each edge: the normals of its two faces, i.e. the ends of the arc of the normals that a face of a box
	// can have when it is flush with the edge; the unit vector in the middle of that arc, and the distance from
	// there to the ends of the arc.
	// Also the unit normal of the great circle of the arc, which is the direction of the edge, and the squared
	// distance between the ends of the arc.
	std::vector<vec3> edgeNormalA(E), edgeNormalB(E), arcMiddle(E), arcAxis(E);
	std::vector<float> arcChord(E), arcLengthSq(E);
	// For each edge, a lower bound for the width of the hull along the normals on its arc: for one dimension
	// of the boxes that have a face flush with the edge. With e a point of the edge and p any vertex, the hull
	// is at least n.(e - p) wide along n. For an n on the arc from fa to fb that is at least the smaller of
	// fa.(e - p) and fb.(e - p), if positive: n is fa and fb combined with weights that are not negative and
	// add up to at least one. The antipodal vertices of the edge are the vertices p to try.
	// The bounds are lowered by widthMargin, which is far more than what the rounding of the face normals and
	// of the box axes to floats can change a width by.
	const double widthMargin = 1e-4;
	std::vector<float> minWidth(E);
	float smallestMinWidth = FLT_MAX;
	for (int e = 0; e < E; ++e)
	{
		edgeNormalA[e] = faceNormals[facesForEdge[e].first];
		edgeNormalB[e] = faceNormals[facesForEdge[e].second];
		arcMiddle[e] = Normalized(edgeNormalA[e] + edgeNormalB[e]);
		arcChord[e] = sqrtf(std::max(LengthSq(edgeNormalA[e] - arcMiddle[e]), LengthSq(edgeNormalB[e] - arcMiddle[e])));
		arcAxis[e] = Normalized(cross(dvec3(edgeNormalA[e]), dvec3(edgeNormalB[e]))).ToFloat();
		arcLengthSq[e] = LengthSq(edgeNormalA[e] - edgeNormalB[e]);
		if (IS_INTERNAL_EDGE(e))
			continue;
		double width = 0.0;
		for (size_t j = 0; j < antipodalPointsForEdge[e].size(); ++j)
		{
			const dvec3 d = dvec3(vtx[edges[e].first]) - dvec3(vtx[antipodalPointsForEdge[e][j]]);
			width = std::max(width, std::min(dot(dvec3(edgeNormalA[e]), d), dot(dvec3(edgeNormalB[e]), d)));
		}
		minWidth[e] = (float)std::max(width - widthMargin, 0.0);
		smallestMinWidth = std::min(smallestMinWidth, minWidth[e]);
	}

	// Whether to compute the volume bounds of the edges, see below. That pays off only if the hull has enough
	// edges: the bounds take time to compute, and the edges of a small hull have few sidepodal edges to rule out.
	const bool boundVolumes = spatialEdgeOrder.size() >= 96;

	// The longer the arc of an edge, the less the bounds below can tell about it, and the more sidepodal edges
	// the edge has. A long arc can therefore be divided into pieces of equal length, see divideLongArcs() below,
	// and the bounds computed for each piece on its own: for the boxes whose face is flush with the edge and has
	// its normal on the piece. A piece is an arc like that of an edge, between two normals that the edge can be
	// flush with. The pieces are numbered on from the edges, and have their entries after those of the edges in
	// the data that the bounds work with: the two ends, the middle and the chord of the arc, minWidth,
	// minVolumeForEdge and openSectors. The pieces of edge e are those from piecesBegin[e] up to piecesEnd[e],
	// in the order from edgeNormalB to edgeNormalA; an edge with a short arc has none. edgeOfPiece tells the
	// edge of a piece, by the number of the piece less E. There are pieces only if dividedArcs says so.
	const float longArcChord = 0.07f; // An arc of 8 degrees: 4 degrees to both sides of its middle.
	const double pieceAngle = 6.0 * 3.14159265358979323846 / 180.0;
	// (arcChord is 2 sin(angle / 4).)
	auto numPiecesOfArc = [&](int e) { return (int)ceil(4.0 * asin(std::min(arcChord[e] * 0.5, 1.0)) / pieceAngle); };
	int numLongArcs = 0, numPieces = 0;
	if (boundVolumes)
		for(size_t ii = 0; ii < spatialEdgeOrder.size(); ++ii)
			if (arcChord[spatialEdgeOrder[ii]] > longArcChord)
			{
				++numLongArcs;
				numPieces += numPiecesOfArc(spatialEdgeOrder[ii]);
			}
	bool dividedArcs = false;
	std::vector<int> piecesBegin, piecesEnd, edgeOfPiece;

	// Take advantage of spatial locality: start the search for the extreme vertex along a direction from the
	// extreme vertex that an earlier search along a similar direction found. For that, the directions are
	// divided into cells (the six faces of a cube, each cut into a grid of squares), and for each cell the
	// vertex is stored that the last search along a direction of the cell ended at. As that vertex is far
	// along the other directions of the cell too, it also gives a lower bound for how far the hull extends
	// along them, without any search.
	// The volume bounds of the edges need such a far vertex for many more directions than there are cells,
	// and take it from here. For them the grid is finer, and every cell starts out with the vertex that a
	// climb along the direction of its center ends at.
	const int hintGrid = boundVolumes ? std::min(std::max((int)sqrt(E * 0.5), 8), 64) : std::min(std::max((int)sqrt(V / 48.0), 1), 32);
	std::vector<int> extremeVertexSearchHints(6 * hintGrid * hintGrid, 0);
	auto extremeVertexSearchHint = [&](const vec3 &direction) -> int &
	{
		const vec3 a = abs(direction);
		const int axis = a.x >= a.y && a.x >= a.z ? 0 : (a.y >= a.z ? 1 : 2);
		if (!(a[axis] > 0.f)) // A zero vector, or NaNs.
			return extremeVertexSearchHints[0];
		const float scale = hintGrid * 0.5f / a[axis];
		const float x = direction[(axis + 1) % 3] * scale + hintGrid * 0.5f, y = direction[(axis + 2) % 3] * scale + hintGrid * 0.5f;
		const int cellX = x >= 0.f ? std::min((int)x, hintGrid - 1) : 0, cellY = y >= 0.f ? std::min((int)y, hintGrid - 1) : 0;
		return extremeVertexSearchHints[((axis * 2 + (direction[axis] < 0.f)) * hintGrid + cellX) * hintGrid + cellY];
	};
	if (boundVolumes)
	{
		int v = 0;
		for (int side = 0; side < 6; ++side)
			for (int x = 0; x < hintGrid; ++x)
				for (int i = 0; i < hintGrid; ++i)
				{
					// Back and forth, so that each cell is next to the previous one, and the climb to its vertex is short.
					const int y = (x & 1) ? hintGrid - 1 - i : i;
					vec3 center;
					center[side / 2] = (side & 1) ? -1.f : 1.f;
					center[(side / 2 + 1) % 3] = (2 * x + 1 - hintGrid) / (float)hintGrid;
					center[(side / 2 + 2) % 3] = (2 * y + 1 - hintGrid) / (float)hintGrid;
					v = ClimbAlong(vtx, adjacencyData, center, v);
					extremeVertexSearchHints[(side * hintGrid + x) * hintGrid + y] = v;
				}
	}

	// For each edge, a lower bound for the volume of the boxes that have a face flush with the edge. An edge for
	// which that is no less than the volume of the best box so far is of no use to the search.
	//
	// The normal n1 of that face of the box is on the arc of the edge, where the hull is at least minWidth wide.
	// It is at most an angle t away from the middle m of the arc. The other two axes of the box are
	// perpendicular to n1, so each of them is n = u cos(b) + m sin(b), for a unit vector u in the plane that is
	// perpendicular to m and an angle |b| <= t. Any two vertices of the hull, d apart, show that the hull is at
	// least n.d >= (u.d) cos(t) - |m.d| sin(t) wide along n, if u.d >= 0.
	//
	// For the vertices to use, that plane is sampled: for numSamples directions that divide half a turn evenly,
	// and for their opposites, the search hints have a vertex that is far along the direction. That makes one
	// pair of vertices per sample, which are far apart along it. For a u in the sector between two consecutive
	// samples, the hull is at least as wide as the larger one of the two bounds that the pairs of those two
	// samples give. Over the sector, that is the smallest at an end of the sector, or where the two bounds are
	// equal. (Or it is negative there, which says nothing.) So each sector gets a lower bound for the width of
	// the hull along the axes n whose u is in the sector.
	//
	// The two axes are perpendicular to each other, so the u of one is a quarter of a turn away from the u of
	// the other, give or take an angle delta with sin(delta) <= tan(t)^2. For a short arc that is a fraction
	// of a sector: then the bound of each sector is made to hold for delta beyond its two ends as well, so that
	// the other u is in the sector that is a quarter of a turn away, as far as the bounds go. Otherwise all the
	// sectors are tried that the other u can be in. The smallest product of the bounds of two such sectors is
	// a lower bound for the area of the face of the box that the two axes span.
	//
	// On the side, the samples of each edge give a box to start the search with.
	// For small hulls this is left out, see boundVolumes: their bounds stay zero.
	// (For an edge whose arc is divided into pieces, the bound is the smallest one of the bounds of its pieces.
	// The pieces have their bounds after those of the edges.)
	std::vector<double> minVolumeForEdge(E, 0.0);
	// The bound also tells which of the sectors can have the u of an axis of a box that is smaller than the
	// best box. For each edge, that is kept as a mask of 64 sectors that divide half a turn, see
	// SectorOfDirection(): a sector that is not in the mask of an edge is of no use to the search, as far as
	// the boxes go that have a face flush with the edge. (The plane and its basis are those of the bound of the
	// edge: the basis that PerpendicularBasis() makes for the middle of the arc of the edge.)
	// (An edge whose arc is divided into pieces has no sectors of its own: its pieces have them.)
	std::vector<unsigned long long> openSectors(E, ~0ULL);
	const int minSamples = 16, maxSamples = PlaneDirections::maxSamples;
	const double pi = 3.14159265358979323846;
	static const PlaneDirections plane;
	auto boundVolume = [&](int e, int numSamples)
	{
		int farVertex[2 * PlaneDirections::maxSamples];
		// For the pair of vertices of each sample: how far apart they are along the two basis vectors of the
		// plane, times cos(t); and what the bound of the pair loses to the tilt of the axis.
		double pairU[PlaneDirections::maxSamples + 1], pairV[PlaneDirections::maxSamples + 1], pairLoss[PlaneDirections::maxSamples + 1];
		// For each sector: the bound for the width of the hull along the axes whose u is in the sector.
		double sectorWidth[PlaneDirections::maxSamples];
		const int step = 2 * PlaneDirections::maxSamples / numSamples; // From one sample to the next, in the directions of the plane.
		vec3 basisU, basisV;
		PerpendicularBasis(arcMiddle[e], basisU, basisV);
		for (int k = 0; k < 2 * numSamples; ++k)
			farVertex[k] = extremeVertexSearchHint(basisU * (float)plane.cosine[k * step] + basisV * (float)plane.sine[k * step]);
		// arcChord is 2 sin(t/2), rounded.
		const double chord = std::min((double)arcChord[e] + 1e-6, 1.4);
		const double cosTilt = 1.0 - chord * chord * 0.5, sinTilt = chord * sqrt(1.0 - chord * chord * 0.25);
		const double sinDelta = sinTilt * sinTilt / (cosTilt * cosTilt) + 1e-9;
		for (int k = 0; k <= numSamples; ++k)
		{
			const dvec3 d = dvec3(vtx[farVertex[k % (2 * numSamples)]]) - dvec3(vtx[farVertex[(k + numSamples) % (2 * numSamples)]]);
			pairU[k] = cosTilt * dot(dvec3(basisU), d);
			pairV[k] = cosTilt * dot(dvec3(basisV), d);
			pairLoss[k] = sinTilt * fabs(dot(dvec3(arcMiddle[e]), d)) + widthMargin;
		}
		// The bound of each sector: the smallest value in the sector of the larger one of the bounds of its two
		// pairs. For the direction (c, s) of the plane, the bound of pair j is c pairU[j] + s pairV[j] - pairLoss[j].
		// The sector is extended by delta at both ends, if delta is at most a quarter of a sector or so.
		const bool extend = sinDelta <= 0.5 * plane.sine[step / 2];
		const double sinExtend = extend ? sinDelta : 0.0, cosExtend = sqrt(1.0 - sinExtend * sinExtend);
		const double cosHalfSector = plane.cosine[step / 2] * cosExtend - plane.sine[step / 2] * sinExtend - 1e-9;
		for (int k = 0; k < numSamples; ++k)
		{
			const double u0 = pairU[k], v0 = pairV[k], l0 = pairLoss[k], u1 = pairU[k + 1], v1 = pairV[k + 1], l1 = pairLoss[k + 1];
			// At the two ends.
			const double cb = plane.cosine[k * step], sb = plane.sine[k * step], ce = plane.cosine[(k + 1) * step], se = plane.sine[(k + 1) * step];
			const double c0 = cb * cosExtend + sb * sinExtend, s0 = sb * cosExtend - cb * sinExtend;
			const double c1 = ce * cosExtend - se * sinExtend, s1 = se * cosExtend + ce * sinExtend;
			double bound = std::min(std::max(u0 * c0 + v0 * s0 - l0, u1 * c0 + v1 * s0 - l1), std::max(u0 * c1 + v0 * s1 - l0, u1 * c1 + v1 * s1 - l1));
			// Where the two are equal: c a + s b = l, for the differences a, b and l of the two pairs. That has
			// two solutions, if any. They count if they are in the sector. (Being a little off it does no harm.)
			const double a = u0 - u1, b = v0 - v1, l = l0 - l1, lengthSq = a * a + b * b;
			if (lengthSq > l * l)
			{
				const double root = sqrt(lengthSq - l * l), scale = 1.0 / lengthSq;
				const double cm = plane.cosine[k * step + step / 2], sm = plane.sine[k * step + step / 2];
				for (int side = 0; side < 2; ++side)
				{
					const double r = side == 0 ? root : -root, c = (l * a - r * b) * scale, sn = (l * b + r * a) * scale;
					if (c * cm + sn * sm >= cosHalfSector)
						bound = std::min(bound, u0 * c + v0 * sn - l0);
				}
			}
			sectorWidth[k] = std::max(bound, 0.0);
		}
		double area = DBL_MAX;
		if (extend)
		{
			// A box can be smaller than the best one only if both of the axes have their u in a sector that
			// leaves the face that small, together with the sector that is a quarter of a turn away.
			unsigned long long open = 0;
			for (int k = 0; k < numSamples / 2; ++k)
			{
				const double faceArea = sectorWidth[k] * sectorWidth[k + numSamples / 2];
				area = std::min(area, faceArea);
				if (minWidth[e] * faceArea < minVolume)
					for (int sector = k; sector < numSamples; sector += numSamples / 2)
					{
						const int first = sector * 64 / numSamples, last = ((sector + 1) * 64 - 1) / numSamples;
						open |= ((1ULL << (last - first + 1)) - 1) << first;
					}
			}
			openSectors[e] &= open;
		}
		else
		{
			const double delta = sinDelta < 1.0 ? asin(sinDelta) : pi * 0.5;
			const int spread = std::min((int)ceil(delta * numSamples / pi), numSamples / 2);
			for (int k = 0; k < numSamples; ++k)
				for (int j = numSamples / 2 - spread; j <= numSamples / 2 + spread; ++j)
					area = std::min(area, sectorWidth[k] * sectorWidth[(k + j + numSamples) % numSamples]);
		}
		minVolumeForEdge[e] = std::max(minVolumeForEdge[e], minWidth[e] * area);

		// The box to start with: the middle of the arc, and the two samples that make the smallest face.
		// Measured with the vertices of the hints, the box comes out no larger than it is. If it can still be
		// the best box, its widths are measured with the extreme vertices, searched for from those. (Not with
		// a plain climb, which stops where vertices tie. The mesh of a body of revolution has a seam of such
		// vertices, in pairs that are some 1e-17 apart: a climb that ends on it makes the box come out smaller
		// than it is, for edge after edge, and TestBox() then measures each such box over all the vertices.)
		int best = 0;
		double bestArea = DBL_MAX;
		for (int k = 0; k < numSamples / 2; ++k)
		{
			const int l = k + numSamples / 2;
			const double faceArea = (pairU[k] * plane.cosine[k * step] + pairV[k] * plane.sine[k * step]) * (pairU[l] * plane.cosine[l * step] + pairV[l] * plane.sine[l * step])
				/ (cosTilt * cosTilt);
			if (faceArea < bestArea)
			{
				bestArea = faceArea;
				best = k;
			}
		}
		const int edge = e < E ? e : edgeOfPiece[e - E];
		const std::vector<int> &antipodals = antipodalPointsForEdge[edge];
		float minN1 = FLT_MAX;
		for (size_t j = 0; j < antipodals.size(); ++j)
			minN1 = fminf(minN1, dot(arcMiddle[e], vtx[antipodals[j]]));
		const double widthN1 = dot(arcMiddle[e], vtx[edges[edge].first]) - minN1;
		if (widthN1 * bestArea < minVolume)
		{
			vec3 axis[2];
			double faceWidth[2];
			for (int a = 0; a < 2; ++a)
			{
				const int k = best + a * numSamples / 2;
				axis[a] = basisU * (float)plane.cosine[k * step] + basisV * (float)plane.sine[k * step];
				int &hint1 = extremeVertexSearchHint(axis[a]), &hint2 = extremeVertexSearchHint(-axis[a]);
				float dummy;
				CLEAR_GRAPH_SEARCH();
				hint1 = ExtremeVertexConvex(hull, adjacencyData, axis[a], floodFillVisited, floodFillVisitColor, dummy, farVertex[k]);
				CLEAR_GRAPH_SEARCH();
				hint2 = ExtremeVertexConvex(hull, adjacencyData, -axis[a], floodFillVisited, floodFillVisitColor, dummy, farVertex[k + numSamples]);
				faceWidth[a] = dot(dvec3(axis[a]), dvec3(vtx[hint1]) - dvec3(vtx[hint2]));
			}
			TestBox(vtx, arcMiddle[e], axis[0], (float)(widthN1 * faceWidth[0] * faceWidth[1]), &minVolume, &minOBB, boxProbe);
		}
	};
	// Computes the bounds of the given arcs. The more samples, the tighter the bound, and the longer it takes
	// to compute. So the arcs are bounded with few samples first, and those that are still in the search then,
	// with twice as many, and so on. How many arcs that rules out depends on the shape of the hull: on a ball,
	// where all boxes are about the same, it rules out few. So each number of samples is tried on every 16th
	// arc first, and used on the other arcs only if that rules out the given share of the arcs: firstShare
	// for the first number of samples, and sharePerSample for each sample of the others.
	auto boundArcs = [&](const std::vector<int> &arcs, double firstShare, double sharePerSample)
	{
		std::vector<int> open;
		for (int numSamples = minSamples; numSamples <= maxSamples; numSamples *= 2)
		{
			open.clear();
			for (size_t ii = 0; ii < arcs.size(); ++ii)
				if (minVolumeForEdge[arcs[ii]] < minVolume)
					open.push_back(arcs[ii]);
			const size_t every = 16;
			size_t tried = 0, ruledOut = 0;
			for (size_t i = 0; i < open.size(); i += every)
				boundVolume(open[i], numSamples);
			for (size_t i = 0; i < open.size(); i += every, ++tried)
				ruledOut += minVolumeForEdge[open[i]] >= minVolume;
			if (ruledOut < (numSamples == minSamples ? firstShare : sharePerSample * numSamples) * tried)
				continue;
			for (size_t i = 0; i < open.size(); ++i)
				if (i % every != 0)
					boundVolume(open[i], numSamples);
		}
	};
	// For the edges, a number of samples pays off like this: bounding an edge takes time in proportion to the
	// number of samples, and ruling one out saves the search for its sidepodal edges and all that is done with
	// them, which takes time in proportion to their number, about the square root of the number of edges. (The
	// factor between the two is a measured one.)
	const double shareOfEdgesPerSample = 0.064 / sqrt((double)E);
	if (boundVolumes)
		boundArcs(spatialEdgeOrder, shareOfEdgesPerSample * minSamples, shareOfEdgesPerSample);

	TRACE_MARK(t0, "obb: volume bounds of the edges");

	// Stores for each edge i the list of all sidepodal edge indices j that it can form an OBB with: the edges
	// that have a normal on their arc that is perpendicular to a normal on the arc of edge i (except for the
	// edges that minVolumeForEdge rules out, and those whose such normals are all in sectors that openSectors
	// rules out for edge i). The lists are stored one after another: the list of edge i is the
	// range from compatibleEdgesBegin[i] to compatibleEdgesEnd[i] of compatibleEdges. The list of an edge is
	// made by findSidepodalEdges() when it is first needed, which it never is for the edges that are ruled out.
	std::vector<int> compatibleEdges;
	std::vector<size_t> compatibleEdgesBegin(E, 0), compatibleEdgesEnd(E, 0);
	std::vector<unsigned char> haveSidepodalEdges(E, 0);
	// For the search for them: the dot products of the normal of a face with the two normals of the arc that is
	// searched for, for the faces for which faceDotsOfSearch says that they are of the current search.
	std::vector<float> faceDotA(F), faceDotB(F);
	std::vector<int> faceDotsOfSearch(F, -1);
	int sidepodalSearchNumber = 0;
	// For each edge, the last edge whose list it was put on: an edge can be sidepodal to several pieces of the
	// arc of another edge, and is listed for it only once. (For when arcs are divided.)
	std::vector<int> listedForEdge;

	// Making the pieces of the long arcs and computing their bounds takes time, which for most hulls is more
	// than the search spends on the long arcs as they are. So the search first goes without, and counts what it
	// does with the long arcs: the edges that it looks at while it searches for their sidepodal edges, and for
	// the third edges of the edge pairs that have a long arc. The pieces are made once it is clear that the
	// search has more work than that left to do on the long arcs: when categories 2 and 3 have already done
	// as much, with category 1 to come; or when category 1 is set to do as much on the edges that it has not
	// got to yet, at the rate of the edges so far. (Making the pieces can save far more than it takes, and
	// for a hull where it does not, this way it adds little.)
	// A small hull is left as it is: its edges have few enough sidepodal edges for category 1 to try them all
	// as third edges, see maxEdgesToTryAll, and that takes no longer for a long arc than for a short one.
	const size_t maxEdgesToTryAll = 128;
	size_t longArcWork = 0, longArcWorkBeforeCategory1 = 0;
	const size_t longArcBudget = (size_t)numPieces * 128; // (A piece takes the time of about 128 looks at an edge.)
	bool canDivideArcs = numLongArcs > 0 && (size_t)E > 2 * maxEdgesToTryAll;
	// Divides the long arcs into pieces and computes the bounds of the pieces. If those do not rule out at
	// least a quarter of the pieces, the arcs are left as they are after all. (A piece takes its first bound
	// if that rules out a quarter of the pieces. For more samples, ruling out a piece saves only its share of
	// the work on its edge, so that many more of the pieces have to be ruled out than of edges.)
	auto divideLongArcs = [&]()
	{
		canDivideArcs = false;
		piecesBegin.assign(E, 0);
		piecesEnd.assign(E, 0);
		std::vector<int> pieces;
		pieces.reserve(numPieces);
		for(size_t ii = 0; ii < spatialEdgeOrder.size(); ++ii)
		{
			const int e = spatialEdgeOrder[ii];
			if (!(arcChord[e] > longArcChord))
				continue;
			const int count = numPiecesOfArc(e);
			const dvec3 fa = edgeNormalA[e], fb = edgeNormalB[e];
			const dvec3 axis = Normalized(cross(fa, fb)), towardsA = cross(fb, axis);
			const double angle = atan2(dot(fa, towardsA), dot(fa, fb));
			piecesBegin[e] = (int)edgeNormalA.size();
			vec3 from = edgeNormalB[e];
			for (int k = 1; k <= count; ++k)
			{
				const vec3 to = k == count ? edgeNormalA[e] : Normalized(fb * cos(k * angle / count) + towardsA * sin(k * angle / count)).ToFloat();
				const vec3 middle = Normalized(from + to);
				double width = 0.0;
				for (size_t j = 0; j < antipodalPointsForEdge[e].size(); ++j)
				{
					const dvec3 d = dvec3(vtx[edges[e].first]) - dvec3(vtx[antipodalPointsForEdge[e][j]]);
					width = std::max(width, std::min(dot(dvec3(to), d), dot(dvec3(from), d)));
				}
				pieces.push_back((int)edgeNormalA.size());
				edgeNormalA.push_back(to);
				edgeNormalB.push_back(from);
				arcMiddle.push_back(middle);
				arcChord.push_back(sqrtf(std::max(LengthSq(to - middle), LengthSq(from - middle))));
				minWidth.push_back((float)std::max(width - widthMargin, 0.0));
				edgeOfPiece.push_back(e);
				from = to;
			}
			piecesEnd[e] = (int)edgeNormalA.size();
		}
		minVolumeForEdge.resize(edgeNormalA.size(), 0.0);
		openSectors.resize(edgeNormalA.size(), ~0ULL);
		boundArcs(pieces, 0.25, shareOfEdgesPerSample * numPieces / numLongArcs);
		size_t ruledOut = 0;
		for (size_t k = 0; k < pieces.size(); ++k)
			ruledOut += minVolumeForEdge[pieces[k]] >= minVolume;
		if (ruledOut * 4 < pieces.size())
			return;
		dividedArcs = true;
		listedForEdge.assign(E, -1);
		for (size_t ii = 0; ii < spatialEdgeOrder.size(); ++ii)
		{
			const int e = spatialEdgeOrder[ii];
			if (piecesBegin[e] < piecesEnd[e])
				minVolumeForEdge[e] = std::max(minVolumeForEdge[e], *std::min_element(minVolumeForEdge.begin() + piecesBegin[e], minVolumeForEdge.begin() + piecesEnd[e]));
		}
	};

	// The sidepodal edges of an edge are found by performing a graph search. The set of sidepodal edges is
	// connected in the graph, which lets us avoid having to iterate over each edge pair of the convex hull.
	// Total running time is O(E*sqrtE), if this is done for all edges.
	// Appends to compatibleEdges the edges that are sidepodal to edge i as far as the given arc goes: the arc
	// of the edge itself, or a piece of it.
	auto searchSidepodalEdges = [&](size_t i, int arc)
	{
		vec3 f1a = edgeNormalA[arc];
		vec3 f1b = edgeNormalB[arc];
		const bool pieces = arc != (int)i;
		++sidepodalSearchNumber;
		size_t looks = 0;

		// Start the search from the extreme vertex in a direction that is perpendicular to f1a: some of its
		// edges are sidepodal to this edge. If several vertices tie as the extreme one (the direction is the
		// normal of a face), any of them may be the one with those edges, so start from them all.
		// If only some of the sectors of the edge are of use, the search stays in those: it does not go over
		// the edges whose normals in question are all in other sectors. Then it starts in each run of
		// consecutive sectors, from the extreme vertices along the direction in the middle of the run and
		// along the opposite one: on both sides of the hull. (That direction is perpendicular to the middle
		// of the arc. The normals that are perpendicular to a normal of the arc and in the sectors of the
		// run are connected, on each side, so the search gets to all the edges that have one.)
		float dummy;
		const unsigned long long open = openSectors[arc];
		vec3 basisU, basisV;
		if (open == ~0ULL)
		{
			vec3 dir = Perpendicular(f1a);
			CLEAR_GRAPH_SEARCH();
			startingVertex = ExtremeVertexConvex(hull, adjacencyData, dir, floodFillVisited, floodFillVisitColor, dummy, startingVertex, &traverseStack); // O(log|V|)
		}
		else
		{
			PerpendicularBasis(arcMiddle[arc], basisU, basisV);
			for (int first = 0; first < 64; ++first)
				if (((open >> first) & 1) != 0 && ((open >> ((first + 63) % 64)) & 1) == 0)
				{
					int count = 1;
					while (((open >> ((first + count) % 64)) & 1) != 0)
						++count;
					// (Sector k is from k to k + 1, in units of 4 directions of the plane.)
					const int middle = (4 * first + 2 * count) % (2 * PlaneDirections::maxSamples);
					const vec3 dir = basisU * (float)plane.cosine[middle] + basisV * (float)plane.sine[middle];
					for (int side = 0; side < 2; ++side)
					{
						int &hint = extremeVertexSearchHint(side == 0 ? dir : -dir);
						CLEAR_GRAPH_SEARCH();
						hint = ExtremeVertexConvex(hull, adjacencyData, side == 0 ? dir : -dir, floodFillVisited, floodFillVisitColor, dummy, hint, &traverseStack);
					}
				}
		}
		CLEAR_GRAPH_SEARCH();
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

				++looks;
				// This is the test of CanBePerpendicular(), without the tolerance: the dot product of a normal on
				// the arc of edge i with a normal on the arc of the other edge is between the dot products of the
				// ends of the two arcs, i.e. of the normals of the two faces of each edge. Each face is shared by
				// several of the edges that are tested here, so its two dot products are computed only once.
				int edge = adjacentEdges[v][j];
				const int faces[2] = { facesForEdge[edge].first, facesForEdge[edge].second };
				for(int k = 0; k < 2; ++k)
					if (faceDotsOfSearch[faces[k]] != sidepodalSearchNumber)
					{
						faceDotsOfSearch[faces[k]] = sidepodalSearchNumber;
						faceDotA[faces[k]] = dot(f1a, faceNormals[faces[k]]);
						faceDotB[faces[k]] = dot(f1b, faceNormals[faces[k]]);
					}
				const float aa = faceDotA[faces[0]], ba = faceDotB[faces[0]], ab = faceDotA[faces[1]], bb = faceDotB[faces[1]];
				if (fminf(fminf(aa, ba), fminf(ab, bb)) <= 0.f && fmaxf(fmaxf(aa, ba), fmaxf(ab, bb)) >= 0.f
					&& (open == ~0ULL || (open & SectorsOfPerpendicularNormals(edgeNormalA[edge], edgeNormalB[edge], aa, ba, ab, bb, basisU, basisV)) != 0))
				{
					// Edges inside faces with 180 degrees dihedral angles can be ignored.
					// If the arc of the other edge is divided into pieces, one of those that are still in the
					// search has to pass the same tests.
					bool sidepodal = !IS_INTERNAL_EDGE(edge) && minVolumeForEdge[edge] < minVolume && (!pieces || listedForEdge[edge] != (int)i);
					if (sidepodal && dividedArcs && piecesBegin[edge] < piecesEnd[edge])
					{
						sidepodal = false;
						for (int piece = piecesBegin[edge]; piece < piecesEnd[edge] && !sidepodal; ++piece)
						{
							if (minVolumeForEdge[piece] >= minVolume)
								continue;
							const float paa = dot(f1a, edgeNormalA[piece]), pba = dot(f1b, edgeNormalA[piece]);
							const float pab = dot(f1a, edgeNormalB[piece]), pbb = dot(f1b, edgeNormalB[piece]);
							sidepodal = fminf(fminf(paa, pba), fminf(pab, pbb)) <= 0.f && fmaxf(fmaxf(paa, pba), fmaxf(pab, pbb)) >= 0.f
								&& (open == ~0ULL || (open & SectorsOfPerpendicularNormals(edgeNormalA[piece], edgeNormalB[piece], paa, pba, pab, pbb, basisU, basisV)) != 0);
						}
					}
					if (sidepodal)
					{
						compatibleEdges.push_back(edge);
						if (pieces)
							listedForEdge[edge] = (int)i;
					}
					traverseStack.push_back(vAdj);
				}
			}
		}
		if (canDivideArcs && arcChord[arc] > longArcChord)
			longArcWork += looks;
	};

	// Computes the sidepodal edges of edge i, unless that is done already. If the arc of the edge is divided
	// into pieces, they are searched for piece by piece, for the pieces that are still in the search.
	auto findSidepodalEdges = [&](size_t i)
	{
		if (haveSidepodalEdges[i])
			return;
		haveSidepodalEdges[i] = 1;
		TRACE_INC(sidepodalSearches);
		compatibleEdgesBegin[i] = compatibleEdges.size();
		const bool pieces = dividedArcs && piecesBegin[i] < piecesEnd[i];
		for (int arc = pieces ? piecesBegin[i] : (int)i, end = pieces ? piecesEnd[i] : (int)i + 1; arc < end; ++arc)
			if (!pieces || minVolumeForEdge[arc] < minVolume)
				searchSidepodalEdges(i, arc);
		compatibleEdgesEnd[i] = compatibleEdges.size();
	};

	// Categories 2 and 3 both fix one axis n1 of the box: the normal of a face of the box that is flush with
	// two edges of the hull at once. The hull extends from minN1 to maxN1 along it. This tests the boxes that
	// have that axis, and another face flush with an edge that is sidepodal to edge e1, one of those two edges.
	auto searchAxis = [&](const vec3 &n1, float minN1, float maxN1, size_t e1)
	{
		findSidepodalEdges(e1);
		for(size_t j = compatibleEdgesBegin[e1]; j < compatibleEdgesEnd[e1]; ++j)
		{
			int edge3 = compatibleEdges[j];
			if (minVolumeForEdge[edge3] >= minVolume)
				continue;
			const vec3 &f3a = edgeNormalA[edge3];
			const vec3 &f3b = edgeNormalB[edge3];

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
			MoveSign(num, denom);

			const float epsilon = 1e-4f;
			if (denom < epsilon)
			{
				num = EqualAbs(num, 0.f) ? 0.f : -1.f;
				denom = 1.f;
			}

			if (!(num >= denom * -epsilon && num <= denom * (1.f + epsilon))) // v >= -epsilon && v <= 1 + epsilon
				continue;

			float v = num / denom;
			vec3 n3 = Normalized(f3b + (f3a - f3b) * v);
			vec3 n2 = Normalized(cross(n3, n1));

			float maxN3 = dot(n3, hull.v[edges[edge3].first]);

			const std::vector<int> &antipodalsEdge3 = antipodalPointsForEdge[edge3];
			const bool fewAntipodals = antipodalsEdge3.size() < 20;
			int &extremeVertexSearchHint1 = extremeVertexSearchHint(n2);
			int &extremeVertexSearchHint2 = extremeVertexSearchHint(-n2);
			int &extremeVertexSearchHint3 = fewAntipodals ? extremeVertexSearchHint1 : extremeVertexSearchHint(-n3); // (Used only if not few.)
			float minN3 = FLT_MAX;
			if (fewAntipodals) // If there are very few antipodal vertices, do a very tight loop and just iterate over each.
			{
				for(size_t a = 0; a < antipodalsEdge3.size(); ++a)
					minN3 = fminf(minN3, dot(n3, hull.v[antipodalsEdge3[a]]));
				if (maxN3 < minN3) std::swap(minN3, maxN3); // XXX Numerical stability hack
			}
			else
				minN3 = -dot(-n3, hull.v[extremeVertexSearchHint3]); // For now. The extreme vertex is searched for below.

			// A search for an extreme vertex can only find a vertex that is farther along its direction than
			// the vertex it starts from. So if the box is no smaller than the best box already when measured
			// with the vertices that the searches would start from, there is no need to search.
			if (maxN1 >= minN1 && maxN3 >= minN3
				&& (maxN1 - minN1) * (dot(n2, hull.v[extremeVertexSearchHint1]) + dot(-n2, hull.v[extremeVertexSearchHint2])) * (maxN3 - minN3) >= minVolume)
				continue;

			float minN2, maxN2;
			CLEAR_GRAPH_SEARCH();
			extremeVertexSearchHint1 = ExtremeVertexConvex(hull, adjacencyData, n2, floodFillVisited, floodFillVisitColor, maxN2, extremeVertexSearchHint1); // O(logV)?
			CLEAR_GRAPH_SEARCH();
			extremeVertexSearchHint2 = ExtremeVertexConvex(hull, adjacencyData, -n2, floodFillVisited, floodFillVisitColor, minN2, extremeVertexSearchHint2); // O(logV)?
			minN2 = -minN2;
			if (maxN2 < minN2) std::swap(minN2, maxN2); // XXX Numerical stability hack

			if (!fewAntipodals)
			{
				// Otherwise perform a spatial locality exploiting graph search.
				CLEAR_GRAPH_SEARCH();
				extremeVertexSearchHint3 = ExtremeVertexConvex(hull, adjacencyData, -n3, floodFillVisited, floodFillVisitColor, minN3, extremeVertexSearchHint3); // O(logV)?
				minN3 = -minN3;
				if (maxN3 < minN3) std::swap(minN3, maxN3); // XXX Numerical stability hack
			}

			float volume = (maxN1 - minN1) * (maxN2 - minN2) * (maxN3 - minN3);
			TestBox(hull.v, n1, n2, volume, &minVolume, &minOBB, boxProbe);
		}
	};

	// Category 2: main algorithm body for finding all search directions where the OBB is flush with the
	// edges of the convex hull from two opposing faces. This is O(E*sqrtE*logV)?
	for(size_t ii = 0; ii < spatialEdgeOrder.size(); ++ii)
	{
		size_t i = (size_t)spatialEdgeOrder[ii];
		if (canDivideArcs && longArcWork > longArcBudget)
			divideLongArcs();
		if (minVolumeForEdge[i] >= minVolume)
			continue;
		vec3 f1a = edgeNormalA[i];
		vec3 f1b = edgeNormalB[i];

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

				int edge = adjacentEdges[antipodalVertex][k];
				if ((int)i > edge) // We search pairs of edges, so no need to process twice - take the canonical order to be i < edge.
					continue;
				if (IS_INTERNAL_EDGE(edge))
					continue; // Edges inside faces with 180 degrees dihedral angles can be ignored.
				if (minVolumeForEdge[edge] >= minVolume)
					continue;

				// The normal of the two opposing faces of the box, if the two edges can be flush with such.
				vec3 n;
				if (AreCompatibleOpposingEdges(f1a, f1b, edgeNormalA[edge], edgeNormalB[edge], n))
				{
					n = Normalized(n);
					searchAxis(n, dot(n, hull.v[edges[edge].first]), dot(n, hull.v[edges[i].first]), i);
				}
			}
		}
	}

	TRACE_FMT(t0, "obb: category 2: opposing faces (evc calls=%ld steps=%ld)",
		TRACE_EVC_CALL_DELTA(evcCalls0), TRACE_EVC_STEP_DELTA(evcSteps0));
	TRACE_EVC_RESET(evcCalls0, evcSteps0);

	// Category 3: main algorithm body for computing all search directions where the OBB touches two edges
	// on the same face. This is O(F*sqrtE*logV)?
	for(size_t ii = 0; ii < spatialFaceOrder.size(); ++ii) // O(F)
	{
		size_t i = spatialFaceOrder[ii];
		if (canDivideArcs && longArcWork > longArcBudget)
			divideLongArcs();
		vec3 n1 = faceNormals[i];

		// The edges that are sidepodal to the face are the ones that are sidepodal to any of its edges, as far
		// as the normal of the face goes: take the first edge of the face that has an arc of normals at all.
		// A box that is flush with the face is flush with all the edges of the face, so the face is of no use
		// if any of them is ruled out.
		int e1 = -1;
		bool ruledOut = false;
		for(size_t j = 0; j < faceEdges[i].size(); ++j)
		{
			int e = faceEdges[i][j];
			if (IS_INTERNAL_EDGE(e))
				continue;
			if (e1 == -1)
				e1 = e;
			ruledOut = ruledOut || minVolumeForEdge[e] >= minVolume;
		}
		if (e1 == -1)
			continue; // All edges of this face were degenerate internal edges! Just skip processing the whole face.
		if (ruledOut)
			continue;

		const std::vector<int> &antipodals = antipodalPointsForEdge[e1];

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
			int &extremeVertexSearchHint4 = extremeVertexSearchHint(-n1);
			extremeVertexSearchHint4 = ExtremeVertexConvex(hull, adjacencyData, -n1, floodFillVisited, floodFillVisitColor, minN1, extremeVertexSearchHint4); // O(logV)?
			minN1 = -minN1;
		}
		if (maxN1 < minN1) std::swap(minN1, maxN1); // XXX Numerical stability hack

		searchAxis(n1, minN1, maxN1, e1);
	}

	TRACE_FMT(t0, "obb: category 3: same face (evc calls=%ld steps=%ld)",
		TRACE_EVC_CALL_DELTA(evcCalls0), TRACE_EVC_STEP_DELTA(evcSteps0));
	TRACE_EVC_RESET(evcCalls0, evcSteps0);

	// Returns a lower bound for the width of the hull along the third axis of the boxes that have a face flush
	// with edge i and another one flush with edge J. That axis is n1 x n2, for an n1 on the arc of edge i and
	// an n2 on the arc of edge J. As a unit vector it is at most `turn` away from searchDir, the unit vector
	// along the cross product of the middles of the two arcs, whose length is `len`. Any two vertices of the
	// hull that are d apart are then at least d.searchDir (1 - turn^2/2) - turn |d - (d.searchDir) searchDir|
	// apart along it: such as the given vertices, which are extreme vertices along searchDir and -searchDir,
	// or at least along directions that are close to those.
	auto thirdWidthBound = [&](int i, int edgeJ, const vec3 &searchDir, float len, int vertex1, int vertex2) -> double
	{
		const dvec3 d = dvec3(vtx[vertex1]) - dvec3(vtx[vertex2]);
		const double w = dot(dvec3(searchDir), d);
		const double turn = (double)arcChord[i] + arcChord[edgeJ] + (1.0 - len) + 1e-6;
		return w * (1.0 - turn * turn * 0.5) - turn * sqrt(std::max(dot(d, d) - w * w, 0.0)) - widthMargin;
	};

	std::vector<vec3> thirdAxes;
	// For each face, the last pair of edges (by a running number) for which the box was tested whose third face
	// is flush with the face.
	std::vector<size_t> faceTestedForPair(F, 0);
	size_t pairNumber = 0;

	// Searches the boxes that have a face flush with edge i and another one flush with edge J, with the normals
	// of those faces on the given arcs: the arcs of the two edges, or pieces of them.
	auto searchPair = [&](size_t i, int edgeJ, int arc1, int arc2)
	{
		const double pairWidth = (double)minWidth[arc1] * minWidth[arc2];
		if (pairWidth * smallestMinWidth >= minVolume)
			return;
		const vec3 f1a = edgeNormalA[arc1], f1b = edgeNormalB[arc1], f2a = edgeNormalA[arc2], f2b = edgeNormalB[arc2];
		if (AreEdgesBad(f1a, f1b, f2a, f2b))
			return;

		vec3 searchDir = cross(arcMiddle[arc1], arcMiddle[arc2]);
		const float len = Normalize(searchDir);
		if (len == 0.f)
		{
			searchDir = cross(f1a, f2a);
			if (Normalize(searchDir) == 0.f)
				searchDir = Perpendicular(f1a);
		}

		// Often the vertices that the searches for the extreme vertices would start from are enough to tell
		// that these two edges are of no use.
		// (When the two arcs together are longer than about 60 degrees, the bound says nothing.)
		const bool boundThirdWidth = len > 0.f && arcChord[arc1] + arcChord[arc2] < 0.5f;
		if (boundThirdWidth && pairWidth * thirdWidthBound(arc1, arc2, searchDir, len, extremeVertexSearchHint(searchDir), extremeVertexSearchHint(-searchDir)) >= minVolume)
			return;

		// The normal of the box face that is flush with one of the two edges is the direction of an axis of
		// the boxes that are flush with the other edge: it has to be in a sector that is of use to that edge.
		// (For the arc of edge J as an axis of the boxes of the arc of edge i, that is so if the list of edge i
		// was made for that very arc: not for a piece of it.)
		if (openSectors[arc2] != ~0ULL || (openSectors[arc1] != ~0ULL && arc1 != (int)i))
		{
			const float aa = dot(f1a, f2a), ab = dot(f1a, f2b), ba = dot(f1b, f2a), bb = dot(f1b, f2b);
			vec3 basisU, basisV;
			if (openSectors[arc2] != ~0ULL)
			{
				PerpendicularBasis(arcMiddle[arc2], basisU, basisV);
				if ((openSectors[arc2] & SectorsOfPerpendicularNormals(f1a, f1b, aa, ab, ba, bb, basisU, basisV)) == 0)
					return;
			}
			if (openSectors[arc1] != ~0ULL && arc1 != (int)i)
			{
				PerpendicularBasis(arcMiddle[arc1], basisU, basisV);
				if ((openSectors[arc1] & SectorsOfPerpendicularNormals(f2a, f2b, aa, ba, ab, bb, basisU, basisV)) == 0)
					return;
			}
		}

		// (For divideLongArcs().)
		const size_t workPerLook = canDivideArcs && (arcChord[arc1] > longArcChord || arcChord[arc2] > longArcChord) ? 1 : 0;

		// Tests the box that has its faces flush with the edges i, J and K, if there is one. Returns whether
		// the third axis of any box that is flush with the edges i and J can be on the arc of edge K at all.
		const float axisDot = dot(arcAxis[i], arcAxis[edgeJ]);
		const float axisTolerance = 1e-5f;
		++pairNumber;
		auto testThirdEdge = [&](int edgeK) -> bool
		{
			const vec3 &f3a = edgeNormalA[edgeK];
			const vec3 &f3b = edgeNormalB[edgeK];
			TRACE_INC(thirdEdgesTested);
			longArcWork += workPerLook;
			float range[2];
			if (!CanBeThirdAxis(f1a, f1b, arcAxis[i], f2a, f2b, arcAxis[edgeJ], axisDot, axisTolerance, f3a, f3b, arcLengthSq[edgeK], range))
				return false;

			// If the third axis is at an end of the arc, it is the normal of a face of the hull, and all the
			// edges of that face give the same box: one of them is enough.
			if (range[1] < 1e-3f || range[0] > 1.f - 1e-3f)
			{
				const int face = range[1] < 1e-3f ? facesForEdge[edgeK].second : facesForEdge[edgeK].first;
				if (faceTestedForPair[face] == pairNumber)
					return true;
				if (edgeJ < edgeK)
					faceTestedForPair[face] = pairNumber;
			}

			// Test edge triplet i, edgeJ, edgeK.
			if (edgeJ < edgeK && pairWidth * minWidth[edgeK] < minVolume && minVolumeForEdge[edgeK] < minVolume
				&& !AreEdgesBad(f1a, f1b, f3a, f3b) && !AreEdgesBad(f2a, f2b, f3a, f3b))
			{
				vec3 n1[2], n2[2], n3[2];
				TRACE_INC(edgeTriplets);
				int nSolutions = ComputeBasis(f1a, f1b, f2a, f2b, f3a, f3b, n1, n2, n3);
				for(int s = 0; s < nSolutions; ++s) // O(constant), nSolutions == 0, 1 or 2.
				{
					TRACE_INC(edgeTripletsSolved);
					TestThreeAdjacentFaces(n1[s], n2[s], n3[s], (int)i, edgeJ, edgeK, hull.v,
						edges, antipodalPointsForEdge, &minVolume, &minOBB, boxProbe);
				}
			}
			return true;
		};

		// The third edge is sidepodal to edge i as well. If edge i has only few sidepodal edges, it is the
		// fastest to simply try them all. Most of them are ruled out by where their arc is. The third axis is
		// within `turn` of searchDir or its opposite (see thirdWidthBound(); the 2e-3 is for the tolerances of
		// ComputeBasis()), so the middle of the arc has to be within that plus the distance to its ends. And
		// the third axis is perpendicular to a normal on each of the two arcs, so its dot product with the
		// middle of an arc is at most the distance from there to the ends of that arc: the arc of the third
		// edge must have such a normal, which is tested for the shorter one of the two arcs.
		if (compatibleEdgesEnd[i] - compatibleEdgesBegin[i] <= maxEdgesToTryAll)
		{
			TRACE_INC(edgePairsSearched);
			longArcWork += workPerLook * ((compatibleEdgesEnd[i] - compatibleEdgesBegin[i]) / 4);
			const float turn = len > 0.f ? arcChord[arc1] + arcChord[arc2] + (1.f - len) + 2e-3f : 2.f;
			const int shorter = arcChord[arc1] <= arcChord[arc2] ? arc1 : arc2;
			const float tilt = arcChord[shorter] + 2e-3f;
			for(size_t k = compatibleEdgesBegin[i]; k < compatibleEdgesEnd[i]; ++k)
			{
				const int edgeK = compatibleEdges[k];
				const float reach = turn + arcChord[edgeK];
				if (edgeK <= edgeJ || pairWidth * minWidth[edgeK] >= minVolume || fabsf(dot(arcMiddle[edgeK], searchDir)) < 1.f - 0.5f * reach * reach)
					continue;
				const float a = dot(arcMiddle[shorter], edgeNormalA[edgeK]), b = dot(arcMiddle[shorter], edgeNormalB[edgeK]);
				if (fminf(a, b) <= tilt && fmaxf(a, b) >= -tilt)
					testThirdEdge(edgeK);
			}
			return;
		}

		// Otherwise find the extreme vertices of the hull along the third axis of a box that is flush with the
		// two edges, of each family of such boxes. They also tell the best if the two edges are of any use.
		// (The third axis of the first box points the same way as searchDir, except perhaps on arcs that are
		// too long for the bound to say anything.)
		thirdAxes.clear();
		ThirdAxesOfBoxes(f1a, f1b, f2a, f2b, thirdAxes);
		if (thirdAxes.empty())
			thirdAxes.push_back(searchDir);
		for(size_t k = 0; k < thirdAxes.size(); ++k)
			for(int side = 0; side < 2; ++side)
			{
				const vec3 direction = side == 0 ? thirdAxes[k] : -thirdAxes[k];
				int &hint = extremeVertexSearchHint(direction);
				float dummy;
				CLEAR_GRAPH_SEARCH();
				hint = ExtremeVertexConvex(hull, adjacencyData, direction, floodFillVisited, floodFillVisitColor, dummy, hint); // O(log|V|)?
				traverseStack.push_back(hint);
			}
		if (boundThirdWidth)
		{
			extremeVertexSearchHint(searchDir) = traverseStack[0];
			extremeVertexSearchHint(-searchDir) = traverseStack[1];
			if (pairWidth * thirdWidthBound(arc1, arc2, searchDir, len, traverseStack[0], traverseStack[1]) >= minVolume)
			{
				traverseStack.clear();
				return;
			}
		}
		TRACE_INC(edgePairsSearched);

		// Find the edges that the third face of the box can be flush with. Along a family of boxes, the third
		// axis of the box moves over the normals of the hull: over the normals that a face can have when it
		// touches the hull at a vertex, and from one vertex to a neighbor over the arc of normals of the edge
		// between them, which is then such a third edge. So the search goes from the extreme vertices of a
		// box of each family over those edges to their other vertices. (An edge is looked at only from the
		// first of its vertices that the search comes to.)
		CLEAR_GRAPH_SEARCH();
		while(!traverseStack.empty())
		{
			int v = traverseStack.back();
			traverseStack.pop_back();
			if (HAVE_VISITED_VERTEX(v))
				continue;
			MARK_VERTEX_VISITED(v);
			const std::vector<int> &n = adjacencyData[v];
			for(size_t k = 0; k < n.size(); ++k)
				// Edges inside faces with 180 degrees dihedral angles can be ignored.
				if (!HAVE_VISITED_VERTEX(n[k]) && !IS_INTERNAL_EDGE(adjacentEdges[v][k]) && testThirdEdge(adjacentEdges[v][k]))
					traverseStack.push_back(n[k]);
		}
	};

	if (canDivideArcs && longArcWork > longArcBudget)
		divideLongArcs();
	longArcWorkBeforeCategory1 = longArcWork;

	// Category 1: all configurations where the OBB is flush with three edges on adjacent faces.
	// This category takes the longest to search, and is therefore searched last: by now there is a box to beat,
	// and a pair or a triplet of edges is skipped when the bounds for the widths of the hull along the normals
	// of the edges show that no box that is flush with them can be smaller than that.
	for(size_t ii = 0; ii < spatialEdgeOrder.size(); ++ii)
	{
		size_t i = (size_t)spatialEdgeOrder[ii];
		if (canDivideArcs && (longArcWork - longArcWorkBeforeCategory1) * 8 > longArcBudget
			&& (double)(longArcWork - longArcWorkBeforeCategory1) * (spatialEdgeOrder.size() - ii) > (double)longArcBudget * ii)
			divideLongArcs();
		// (The other two faces of the box are flush with an edge each as well.)
		if (minVolumeForEdge[i] >= minVolume || (double)minWidth[i] * smallestMinWidth * smallestMinWidth >= minVolume) continue;
		findSidepodalEdges(i);

		for(size_t j = compatibleEdgesBegin[i]; j < compatibleEdgesEnd[i]; ++j) // O(sqrt(|E|))?
		{
			int edgeJ = compatibleEdges[j];
			if (edgeJ <= (int)i) continue; // Remove symmetry.
			TRACE_INC(edgePairs);
			if (minVolumeForEdge[edgeJ] >= minVolume) continue;
			// If an arc is divided into pieces, the boxes are searched piece by piece: for the pieces that are
			// still in the search, and that have normals that are perpendicular to each other. Except when the
			// third edges are found by trying all the sidepodal edges of edge i, which would be done all over
			// for each pair of pieces: then the two arcs are searched as they are, if there is such a pair of
			// pieces at all.
			const bool pieces1 = dividedArcs && piecesBegin[i] < piecesEnd[i], pieces2 = dividedArcs && piecesBegin[edgeJ] < piecesEnd[edgeJ];
			int begin1 = pieces1 ? piecesBegin[i] : (int)i, end1 = pieces1 ? piecesEnd[i] : (int)i + 1;
			int begin2 = pieces2 ? piecesBegin[edgeJ] : edgeJ, end2 = pieces2 ? piecesEnd[edgeJ] : edgeJ + 1;
			bool asTheyAre = !pieces1 && !pieces2;
			if (!asTheyAre && compatibleEdgesEnd[i] - compatibleEdgesBegin[i] <= maxEdgesToTryAll)
			{
				for (int arc1 = begin1; arc1 < end1 && !asTheyAre; ++arc1)
					for (int arc2 = begin2; arc2 < end2 && !asTheyAre && minVolumeForEdge[arc1] < minVolume; ++arc2)
						asTheyAre = minVolumeForEdge[arc2] < minVolume && CanBePerpendicular(edgeNormalA[arc1], edgeNormalB[arc1], edgeNormalA[arc2], edgeNormalB[arc2]);
				if (!asTheyAre)
					continue;
				begin1 = (int)i, end1 = (int)i + 1, begin2 = edgeJ, end2 = edgeJ + 1;
			}
			for (int arc1 = begin1; arc1 < end1; ++arc1)
				for (int arc2 = begin2; arc2 < end2 && minVolumeForEdge[arc1] < minVolume; ++arc2)
					if (minVolumeForEdge[arc2] < minVolume
						&& (asTheyAre || CanBePerpendicular(edgeNormalA[arc1], edgeNormalB[arc1], edgeNormalA[arc2], edgeNormalB[arc2])))
						searchPair(i, edgeJ, arc1, arc2);
		}
	}

	TRACE_FMT(t0, "obb: category 1: 3 adjacent faces (evc calls=%ld steps=%ld)",
		TRACE_EVC_CALL_DELTA(evcCalls0), TRACE_EVC_STEP_DELTA(evcSteps0));
	TRACE_FMT(t0, "obb: (pairs=%ld searched=%ld edges tested=%ld triplets=%ld solutions=%ld; sidepodal searches=%ld of %d)",
		edgePairs, edgePairsSearched, thirdEdgesTested, edgeTriplets, edgeTripletsSolved, sidepodalSearches, E);

	// The search for edge triplets does not follow cross-product orientation, so
	// fix that up at the very last step, if necessary.
	if (dot(cross(minOBB.axis[0], minOBB.axis[1]), minOBB.axis[2]) < 0.f)
		minOBB.axis[2] = -minOBB.axis[2];
	return minOBB;
}

// Computes the tightest box around the points that has the axes dir0, dir1 made orthogonal to dir0, and their
// cross product. This is done in double precision, relative to the first point. The returned box encloses
// the points: its half extents are measured from its center as it is returned, i.e. rounded to floats. (Far
// away from the origin the center cannot be represented accurately, which then costs some tightness.)
static OBB FixedOrientationEnclosingOBB(const std::vector<vec3> &pointArray, const vec3 &dir0, const vec3 &dir1)
{
	OBB obb;
	BoxAxes(dir0, dir1, obb.axis);
	dvec3 axis[3];
	const dvec3 origin = pointArray[0];
	dvec3 center = origin;
	for (int i = 0; i < 3; ++i)
	{
		axis[i] = obb.axis[i];
		double minD = DBL_MAX, maxD = -DBL_MAX;
		for (size_t j = 0; j < pointArray.size(); ++j)
		{
			double d = dot(axis[i], dvec3(pointArray[j]) - origin);
			minD = std::min(minD, d);
			maxD = std::max(maxD, d);
		}
		center = center + axis[i] * ((minD + maxD) * 0.5);
	}
	obb.pos = center.ToFloat();
	for (int i = 0; i < 3; ++i)
	{
		double r = 0.0;
		for (size_t j = 0; j < pointArray.size(); ++j)
			r = std::max(r, fabs(dot(axis[i], dvec3(pointArray[j]) - dvec3(obb.pos))));
		obb.r[i] = (float)r;
		if (obb.r[i] < r)
			obb.r[i] = nextafterf(obb.r[i], FLT_MAX);
	}
	return obb;
}

// ----------------------------------------------------------------------------
// Public entry point
// ----------------------------------------------------------------------------

// True if the box is thinner than what the precision of single precision floats can resolve at its size.
static bool IsFlat(const OBB &obb)
{
	return std::min(obb.r.x, std::min(obb.r.y, obb.r.z)) < 2e-6f * hmax(obb.r);
}

static float LargestFaceArea(const OBB &obb)
{
	return 4.f * std::max(obb.r.x * obb.r.y, std::max(obb.r.y * obb.r.z, obb.r.x * obb.r.z));
}

// Returns the box that has the given axis, and the smallest area perpendicular to it among such boxes:
// the minimum area rectangle of the points projected along the axis (rotating calipers).
static OBB SmallestOBBAlongAxis(const std::vector<vec3> &pointArray, const vec3 &axis)
{
	vec3 u, v;
	PerpendicularBasis(axis, u, v);
	std::vector<float2> pts(pointArray.size());
	for (size_t i = 0; i < pointArray.size(); ++i)
		pts[i] = float2(dot(u, pointArray[i]), dot(v, pointArray[i]));
	float2 rectCenter, uDir, vDir;
	float minU = 0.f, maxU = 0.f, minV = 0.f, maxV = 0.f;
	MinAreaRect2D(&pts[0], (int)pts.size(), rectCenter, uDir, vDir, minU, maxU, minV, maxV);
	return FixedOrientationEnclosingOBB(pointArray, axis, u * uDir.x + v * uDir.y);
}

OBB minobb(const Hull3 &hull, float tolerance)
{
	OBB degenerate;
	degenerate.pos = vec3(0.f, 0.f, 0.f);
	degenerate.r = vec3(-FLT_MAX, -FLT_MAX, -FLT_MAX);
	degenerate.axis[0] = vec3(1.f, 0.f, 0.f);
	degenerate.axis[1] = vec3(0.f, 1.f, 0.f);
	degenerate.axis[2] = vec3(0.f, 0.f, 1.f);

	if (hull.v.empty())
		return degenerate;

	// The hull vertices are input points and every input point lies on or inside
	// the hull, so for any axis direction the extreme input point is a hull
	// vertex. All min/max scans in this function therefore run over the hull
	// vertices only, which is exact and much cheaper than scanning the raw input.
	const std::vector<vec3> &points = hull.v;

	const int n = (int)points.size();

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

	// The search works in single precision and with absolute tolerances. To make it independent of where
	// the input is and how large it is, it is run on a copy of the hull that is centered at the origin
	// and scaled to a fixed size: its largest half extent is in [8, 16). The scale is a power of two, so
	// scaling does not round.
	dvec3 minP = points[0], maxP = points[0];
	for (int i = 1; i < n; ++i)
	{
		minP = dvec3(std::min(minP.x, (double)points[i].x), std::min(minP.y, (double)points[i].y), std::min(minP.z, (double)points[i].z));
		maxP = dvec3(std::max(maxP.x, (double)points[i].x), std::max(maxP.y, (double)points[i].y), std::max(maxP.z, (double)points[i].z));
	}
	const dvec3 center = (minP + maxP) * 0.5;
	int exponent;
	frexp(std::max(maxP.x - minP.x, std::max(maxP.y - minP.y, maxP.z - minP.z)) * 0.5, &exponent);
	const double scale = ldexp(1.0, 4 - exponent);
	Hull3 local;
	local.f = hull.f;
	local.degenerate = hull.degenerate;
	local.v.reserve(n);
	for (int i = 0; i < n; ++i)
		local.v.push_back(((dvec3(points[i]) - center) * scale).ToFloat());

	OBB obb;
	if (hull.IsDegenerate())
		// The points are planar: compute a flat OBB with the 2D algorithm. Running it on
		// the hull vertices is exact: a linear projection commutes with the convex hull,
		// so the 2D hull of the projected input equals the 2D hull of the projected hull
		// vertices.
		obb = SmallestOBBVolume2DPlanar(local.v);
	else
	{
		// The face normals are computed from the original hull, which the copy matches only up to rounding.
		std::vector<vec3> faceNormals(hull.f.size());
		for (size_t i = 0; i < hull.f.size(); ++i)
			faceNormals[i] = PolyhedronFaceNormal(hull, (int)i);

		double t0 = TRACE_START();
		// (A negative tolerance, or a NaN, counts as none.)
		obb = OptimalEnclosingOBB3D(local, faceNormals, tolerance > 0.f ? (float)(1.0 / (1.0 + tolerance)) : 1.f);
		TRACE_MARK(t0, "minobb: OptimalEnclosingOBB3D");
		if (obb.IsDegenerate())
		{
			// The category search found no configuration at all. For nearly-planar hulls the
			// numerically coplanar faces can break the flush-edge structure it relies on, and
			// the 2D planar path below assumes truly flat input. Try a coarse sphere sweep
			// (exact given each candidate axis) first, and keep the better of the two. The
			// volume > 0 check rejects the sweep's "no result" sentinel, which can otherwise
			// (volume 0) beat any real box in the comparison below.
			OBB sweep = CoarseSweepEnclosingOBB(local.v);
			obb = SmallestOBBVolume2DPlanar(local.v);
			if (!sweep.IsDegenerate() && sweep.Volume() > 0.f && sweep.Volume() < obb.Volume())
				obb = sweep;
		}
		else if (IsFlat(obb))
		{
			// The hull is flat to the precision of single precision floats: typically a planar model whose
			// vertices are off its plane by rounding errors. The thickness of its box is then noise (the
			// axes of the box cannot even be represented accurately enough to resolve it), so there is no
			// point in minimizing the volume of the box as opposed to its area: take the box with the
			// smallest area among the boxes of the same thin axis.
			const int thin = obb.r.x <= obb.r.y && obb.r.x <= obb.r.z ? 0 : (obb.r.y <= obb.r.z ? 1 : 2);
			OBB planar = SmallestOBBAlongAxis(local.v, obb.axis[thin]);
			if (IsFlat(planar) && LargestFaceArea(planar) < LargestFaceArea(obb))
				obb = planar;
		}
	}

	// The search only determines the orientation of the box. The box itself is the tightest box of
	// that orientation around the vertices of the input hull.
	double t0 = TRACE_START();
	obb = FixedOrientationEnclosingOBB(points, obb.axis[0], obb.axis[1]);
	TRACE_MARK(t0, "minobb: fit the box (3x O(n) scans)");
	return obb;
}