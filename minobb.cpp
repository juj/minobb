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
static vec3 PolyhedronFaceNormal(const Hull3 &poly, int faceIndex)
{
	const std::vector<int> &face = poly.f[faceIndex];
	dvec3 normal;
	for(size_t i = 1; i + 1 < face.size(); ++i)
		normal = normal + cross(dvec3(poly.v[face[i]]) - dvec3(poly.v[face[0]]), dvec3(poly.v[face[i+1]]) - dvec3(poly.v[face[0]]));
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

// Makes the box with the axes n1 and n2 (and their cross product) the best box, if it is smaller than
// the best box so far. `volume` is the volume that the search derived for it from the vertices it assumed
// the box to be in contact with: that can only be smaller than the volume of the actual tightest box of
// that orientation, which therefore is measured only if `volume` is below the best volume so far.
static void TestBox(const std::vector<vec3> &hullV, const vec3 &n1, const vec3 &n2, float volume,
	float *minVolume, OBB *minOBB)
{
	if (!(volume < *minVolume))
		return;
	// The axes must be (roughly) orthonormal for this to be a box at all. This also catches zero vectors and NaNs.
	if (!(fabsf(LengthSq(n1) - 1.f) < 0.01f && fabsf(LengthSq(n2) - 1.f) < 0.01f && fabsf(dot(n1, n2)) < 0.01f))
		return;
	OBB obb = FixedOrientationEnclosingOBB(hullV, n1, n2);
	if (obb.Volume() < *minVolume)
	{
		*minOBB = obb;
		*minVolume = obb.Volume();
	}
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
	TestBox(hullV, n1, n2, volume, minVolume, minOBB);
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

// Port of OBB::OptimalEnclosingOBB(const Polyhedron &).
// Returns an OBB with IsDegenerate() == true if the input is (near) planar.
// `faceNormals` are the unit normals of the faces of the hull.
static OBB OptimalEnclosingOBB3D(const Hull3 &hull, const std::vector<vec3> &faceNormals)
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
	     The steps below skip whatever these bounds show to be no smaller than the best box found so far.
	  6. Test all configurations where two edges are on opposing faces, and the third one is on a face adjacent to the two. O(E*sqrtE*logV)?
	  7. Test all configurations where two edges are on the same face (OBB aligns with a face of the convex hull). O(F*sqrtE*logV).
	  8. Test all configurations where all three edges are on adjacent faces. O(ES) = O(E*sqrtE)?, where S is the size
	     of sidepodal edges per edge, S ~ O(sqrtE) on average: for each edge and each of its sidepodal edges, the
	     third edges are found by a graph search along the boxes that are flush with the two.
	  9. Return the best found OBB.
	  The sidepodal edges of an edge are computed when steps 6-8 first need them. O(S) per edge.
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

	// Take advantage of spatial locality: start the search for the extreme vertex along a direction from the
	// extreme vertex that an earlier search along a similar direction found. For that, the directions are
	// divided into cells (the six faces of a cube, each cut into a grid of squares), and for each cell the
	// vertex is stored that the last search along a direction of the cell ended at. As that vertex is far
	// along the other directions of the cell too, it also gives a lower bound for how far the hull extends
	// along them, without any search.
	const int hintGrid = std::min(std::max((int)sqrt(V / 48.0), 1), 32);
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

	// For each edge, a lower bound for the volume of the boxes that have a face flush with the edge. An edge for
	// which that is no less than the volume of the best box so far is of no use to the search.
	// The normal n1 of that face of the box is on the arc of the edge, where the hull is at least minWidth wide.
	// The other two axes n2 and n3 of the box are perpendicular to n1. So they are at most as far from the plane
	// that is perpendicular to the middle of the arc, as n1 is from that middle. In that plane, the hull is
	// measured along numSamples directions and their opposites, by climbing to a vertex that is far along each.
	// n2 and n3 are both within `turn` (as unit vectors) of one of those directions s. The two vertices found
	// for s and -s, which are d apart, are at least d.s (1 - turn^2/2) - turn |d - (d.s) s| apart along such an
	// axis, and the hull is at least that wide. As n2 and n3 are perpendicular, their two directions are a
	// quarter of a turn apart, give or take `spread` samples. The smallest product of two such widths is a lower
	// bound for the area of the face of the box that n2 and n3 span.
	// On the side, the samples of each edge give a box to start the search with.
	// Computing the bound of an edge takes about as long as finding a hundred sidepodal edges for it, which is
	// more than the edges of a small hull have. So this is left out for small hulls: their bounds stay zero.
	std::vector<double> minVolumeForEdge(E, 0.0);
	if (spatialEdgeOrder.size() >= 512)
	{
		const int numSamples = 32;
		const double pi = 3.14159265358979323846;
		std::vector<int> farVertex(2 * numSamples);
		std::vector<vec3> sample(2 * numSamples);
		std::vector<float> sampleCos(2 * numSamples), sampleSin(2 * numSamples);
		std::vector<double> width(numSamples), widthBound(numSamples);
		for (int k = 0; k < 2 * numSamples; ++k)
		{
			sampleCos[k] = (float)cos(k * pi / numSamples);
			sampleSin[k] = (float)sin(k * pi / numSamples);
		}
		auto boundVolume = [&](int e)
		{
			vec3 basisU, basisV;
			PerpendicularBasis(arcMiddle[e], basisU, basisV);
			for (int k = 0; k < 2 * numSamples; ++k)
			{
				sample[k] = basisU * sampleCos[k] + basisV * sampleSin[k];
				int &hint = extremeVertexSearchHint(sample[k]);
				farVertex[k] = hint = ClimbAlong(vtx, adjacencyData, sample[k], hint);
			}
			const double chord = std::min((double)arcChord[e], 1.0);
			const double turn = sqrt(std::max(2.0 - 2.0 * sqrt(1.0 - chord * chord), 0.0)) + 2.0 * sin(pi / (4.0 * numSamples)) + 1e-6;
			for (int k = 0; k < numSamples; ++k)
			{
				const dvec3 d = dvec3(vtx[farVertex[k]]) - dvec3(vtx[farVertex[k + numSamples]]);
				width[k] = dot(dvec3(sample[k]), d);
				widthBound[k] = std::max(width[k] * (1.0 - turn * turn * 0.5) - turn * sqrt(std::max(dot(d, d) - width[k] * width[k], 0.0)) - widthMargin, 0.0);
			}
			const int spread = (int)ceil(asin(std::min(2.0 * turn + turn * turn, 1.0)) * numSamples / pi);
			double area = DBL_MAX;
			for (int k = 0; k < numSamples; ++k)
				for (int j = numSamples / 2 - spread; j <= numSamples / 2 + spread; ++j)
					area = std::min(area, widthBound[k] * widthBound[(k + j + numSamples) % numSamples]);
			minVolumeForEdge[e] = minWidth[e] * area;

			// The box to start with: the middle of the arc, and the two samples that make the smallest face.
			int best = 0;
			for (int k = 1; k < numSamples / 2; ++k)
				if (width[k] * width[k + numSamples / 2] < width[best] * width[best + numSamples / 2])
					best = k;
			float minN1 = FLT_MAX;
			for (size_t j = 0; j < antipodalPointsForEdge[e].size(); ++j)
				minN1 = fminf(minN1, dot(arcMiddle[e], vtx[antipodalPointsForEdge[e][j]]));
			TestBox(vtx, arcMiddle[e], sample[best], (float)((dot(arcMiddle[e], vtx[edges[e].first]) - minN1) * width[best] * width[best + numSamples / 2]),
				&minVolume, &minOBB);
		};
		// How many edges this rules out depends on the shape of the hull: on a ball, where all boxes are about
		// the same, it rules out none. So try it on every 16th edge first, and go on only if that pays off.
		const size_t every = 16;
		size_t ruledOut = 0;
		for (size_t ii = 0; ii < spatialEdgeOrder.size(); ii += every)
			boundVolume(spatialEdgeOrder[ii]);
		for (size_t ii = 0; ii < spatialEdgeOrder.size(); ii += every)
			ruledOut += minVolumeForEdge[spatialEdgeOrder[ii]] >= minVolume;
		if (ruledOut * every * 10 >= spatialEdgeOrder.size())
			for (size_t ii = 0; ii < spatialEdgeOrder.size(); ++ii)
				if (ii % every != 0)
					boundVolume(spatialEdgeOrder[ii]);
	}

	TRACE_MARK(t0, "obb: volume bounds of the edges");

	// Stores for each edge i the list of all sidepodal edge indices j that it can form an OBB with: the edges
	// that have a normal on their arc that is perpendicular to a normal on the arc of edge i (except for the
	// edges that minVolumeForEdge rules out). The lists are stored one after another: the list of edge i is the
	// range from compatibleEdgesBegin[i] to compatibleEdgesEnd[i] of compatibleEdges. The list of an edge is
	// made by findSidepodalEdges() when it is first needed, which it never is for the edges that are ruled out.
	std::vector<int> compatibleEdges;
	std::vector<size_t> compatibleEdgesBegin(E, 0), compatibleEdgesEnd(E, 0);
	std::vector<unsigned char> haveSidepodalEdges(E, 0);
	// For the search for them: the smallest and the largest dot product of the normal of a face with the two
	// normals of the current edge i, for the faces for which faceDotsOfEdge says that they are of edge i.
	std::vector<float> faceMinDot(F), faceMaxDot(F);
	std::vector<int> faceDotsOfEdge(F, -1);

	// Computes the sidepodal edges of edge i, unless that is done already, by performing a graph search. The set
	// of sidepodal edges is connected in the graph, which lets us avoid having to iterate over each edge pair of
	// the convex hull. Total running time is O(E*sqrtE), if this is done for all edges.
	auto findSidepodalEdges = [&](size_t i)
	{
		if (haveSidepodalEdges[i])
			return;
		haveSidepodalEdges[i] = 1;
		TRACE_INC(sidepodalSearches);
		vec3 f1a = edgeNormalA[i];
		vec3 f1b = edgeNormalB[i];

		// Start the search from the extreme vertex in a direction that is perpendicular to f1a: some of its
		// edges are sidepodal to this edge. If several vertices tie as the extreme one (the direction is the
		// normal of a face), any of them may be the one with those edges, so start from them all.
		float dummy;
		vec3 dir = Perpendicular(f1a);
		CLEAR_GRAPH_SEARCH();
		startingVertex = ExtremeVertexConvex(hull, adjacencyData, dir, floodFillVisited, floodFillVisitColor, dummy, startingVertex, &traverseStack); // O(log|V|)
		CLEAR_GRAPH_SEARCH();
		compatibleEdgesBegin[i] = compatibleEdges.size();
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

				// This is the test of CanBePerpendicular(), without the tolerance: the dot product of a normal on
				// the arc of edge i with a normal on the arc of the other edge is between the dot products of the
				// ends of the two arcs, i.e. of the normals of the two faces of each edge. Each face is shared by
				// several of the edges that are tested here, so its two dot products are computed only once.
				int edge = adjacentEdges[v][j];
				const int faces[2] = { facesForEdge[edge].first, facesForEdge[edge].second };
				for(int k = 0; k < 2; ++k)
					if (faceDotsOfEdge[faces[k]] != (int)i)
					{
						faceDotsOfEdge[faces[k]] = (int)i;
						float a = dot(f1a, faceNormals[faces[k]]), b = dot(f1b, faceNormals[faces[k]]);
						faceMinDot[faces[k]] = fminf(a, b);
						faceMaxDot[faces[k]] = fmaxf(a, b);
					}
				if (fminf(faceMinDot[faces[0]], faceMinDot[faces[1]]) <= 0.f && fmaxf(faceMaxDot[faces[0]], faceMaxDot[faces[1]]) >= 0.f)
				{
					// Edges inside faces with 180 degrees dihedral angles can be ignored.
					if (!IS_INTERNAL_EDGE(edge) && minVolumeForEdge[edge] < minVolume)
						compatibleEdges.push_back(edge);
					traverseStack.push_back(vAdj);
				}
			}
		}
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
			TestBox(hull.v, n1, n2, volume, &minVolume, &minOBB);
		}
	};

	// Category 2: main algorithm body for finding all search directions where the OBB is flush with the
	// edges of the convex hull from two opposing faces. This is O(E*sqrtE*logV)?
	for(size_t ii = 0; ii < spatialEdgeOrder.size(); ++ii)
	{
		size_t i = (size_t)spatialEdgeOrder[ii];
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
	auto thirdWidthBound = [&](size_t i, int edgeJ, const vec3 &searchDir, float len, int vertex1, int vertex2) -> double
	{
		const dvec3 d = dvec3(vtx[vertex1]) - dvec3(vtx[vertex2]);
		const double w = dot(dvec3(searchDir), d);
		const double turn = (double)arcChord[i] + arcChord[edgeJ] + (1.0 - len) + 1e-6;
		return w * (1.0 - turn * turn * 0.5) - turn * sqrt(std::max(dot(d, d) - w * w, 0.0)) - widthMargin;
	};

	std::vector<vec3> thirdAxes;
	const size_t maxEdgesToTryAll = 128;
	// For each face, the last pair of edges (by a running number) for which the box was tested whose third face
	// is flush with the face.
	std::vector<size_t> faceTestedForPair(F, 0);
	size_t pairNumber = 0;

	// Category 1: all configurations where the OBB is flush with three edges on adjacent faces.
	// This category takes the longest to search, and is therefore searched last: by now there is a box to beat,
	// and a pair or a triplet of edges is skipped when the bounds for the widths of the hull along the normals
	// of the edges show that no box that is flush with them can be smaller than that.
	for(size_t ii = 0; ii < spatialEdgeOrder.size(); ++ii)
	{
		size_t i = (size_t)spatialEdgeOrder[ii];
		// (The other two faces of the box are flush with an edge each as well.)
		if (minVolumeForEdge[i] >= minVolume || (double)minWidth[i] * smallestMinWidth * smallestMinWidth >= minVolume) continue;
		vec3 f1a = edgeNormalA[i];
		vec3 f1b = edgeNormalB[i];
		findSidepodalEdges(i);

		for(size_t j = compatibleEdgesBegin[i]; j < compatibleEdgesEnd[i]; ++j) // O(sqrt(|E|))?
		{
			int edgeJ = compatibleEdges[j];
			if (edgeJ <= (int)i) continue; // Remove symmetry.
			const double pairWidth = (double)minWidth[i] * minWidth[edgeJ];
			TRACE_INC(edgePairs);
			if (minVolumeForEdge[edgeJ] >= minVolume || pairWidth * smallestMinWidth >= minVolume) continue;
			vec3 f2a = edgeNormalA[edgeJ];
			vec3 f2b = edgeNormalB[edgeJ];
			if (AreEdgesBad(f1a, f1b, f2a, f2b)) continue;

			vec3 searchDir = cross(arcMiddle[i], arcMiddle[edgeJ]);
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
			const bool boundThirdWidth = len > 0.f && arcChord[i] + arcChord[edgeJ] < 0.5f;
			if (boundThirdWidth && pairWidth * thirdWidthBound(i, edgeJ, searchDir, len, extremeVertexSearchHint(searchDir), extremeVertexSearchHint(-searchDir)) >= minVolume)
				continue;

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
							edges, antipodalPointsForEdge, &minVolume, &minOBB);
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
				const float turn = len > 0.f ? arcChord[i] + arcChord[edgeJ] + (1.f - len) + 2e-3f : 2.f;
				const size_t shorter = arcChord[i] <= arcChord[edgeJ] ? i : (size_t)edgeJ;
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
				continue;
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
				if (pairWidth * thirdWidthBound(i, edgeJ, searchDir, len, traverseStack[0], traverseStack[1]) >= minVolume)
				{
					traverseStack.clear();
					continue;
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
	dvec3 axis[3];
	axis[0] = Normalized(dvec3(dir0));
	axis[1] = Normalized(dvec3(dir1) - axis[0] * dot(axis[0], dvec3(dir1)));
	axis[2] = cross(axis[0], axis[1]);

	OBB obb;
	const dvec3 origin = pointArray[0];
	dvec3 center = origin;
	for (int i = 0; i < 3; ++i)
	{
		obb.axis[i] = axis[i].ToFloat();
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

OBB minobb(const Hull3 &hull)
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
		obb = OptimalEnclosingOBB3D(local, faceNormals);
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