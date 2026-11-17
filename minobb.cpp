#include "minobb.h"

#include <vector>
#include <algorithm>
#include <cmath>
#include <cfloat>
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

// Finds the vertex of the hull that is the farthest along `direction`, by climbing along the edges of the
// hull, starting from startingVertex. On a convex polyhedron the vertices that are at least as far as any
// given distance are connected, so the climb can only come to a halt too early where vertices tie: on a
// face or an edge that is perpendicular to the direction, to the precision of the distances. Such a
// plateau is therefore searched through for a vertex that is farther still.
// If `ties` is given, the returned vertex and all the vertices that tie with it are appended to it.
static int ExtremeVertexConvex(const Hull3 &hull, const std::vector<std::vector<int> > &adjacencyData, const vec3 &direction,
	std::vector<unsigned int> &floodFillVisited, unsigned int floodFillVisitColor,
	float &mostExtremeDistance, int startingVertex, std::vector<int> *ties = 0)
{
	TRACE_EVC_CALL();
	const float plateauEpsilon = 1e-4f;
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

	// Stores for each edge i the list of all sidepodal edge indices j that it can form an OBB with.
	std::vector<std::vector<int>> compatibleEdges(E);

	// Use an O(E*V) data structure for sidepodal vertices: one bit for each vertex of each edge.
	std::vector<unsigned int> sidepodalVertices(((size_t)E * V + 31) / 32, 0);
	auto IsSidepodalVertex = [&](size_t edge, int vertex) -> bool
	{
		size_t bit = edge * V + vertex;
		return ((sidepodalVertices[bit >> 5] >> (bit & 31)) & 1) != 0;
	};
	auto SetSidepodalVertex = [&](size_t edge, int vertex)
	{
		size_t bit = edge * V + vertex;
		sidepodalVertices[bit >> 5] |= 1u << (bit & 31);
	};

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

		// Start the search from the extreme vertex in a direction that is perpendicular to f1a: some of its
		// edges are sidepodal to this edge. If several vertices tie as the extreme one (the direction is the
		// normal of a face), any of them may be the one with those edges, so start from them all.
		float dummy;
		vec3 dir = Perpendicular(f1a);
		CLEAR_GRAPH_SEARCH();
		startingVertex = ExtremeVertexConvex(hull, adjacencyData, dir, floodFillVisited, floodFillVisitColor, dummy, startingVertex, &traverseStack); // O(log|V|)
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

				int edge = adjacentEdges[v][j];
//				if (IS_INTERNAL_EDGE(edge))
//					continue; // Edges inside faces with 180 degrees dihedral angles can be ignored.
				if (AreEdgesCompatibleForOBB(f1a, f1b, faceNormals[facesForEdge[edge].first], faceNormals[facesForEdge[edge].second]))
				{
					if ((int)i <= edge)
					{
						if (!IS_INTERNAL_EDGE(edge))
							compatibleEdges[i].push_back(edge);

						SetSidepodalVertex(i, edges[edge].first);
						SetSidepodalVertex(i, edges[edge].second);

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
							SetSidepodalVertex(edge, edges[i].first);
							SetSidepodalVertex(edge, edges[i].second);
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

	TRACE_FMT(t0, "obb: sidepodal precompute (evc calls=%ld steps=%ld)",
		TRACE_EVC_CALL_DELTA(evcCalls0), TRACE_EVC_STEP_DELTA(evcSteps0));
	TRACE_EVC_RESET(evcCalls0, evcSteps0);

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

	// Category 1: all configurations where the OBB is flush with three edges on adjacent faces.
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
			if (IsSidepodalVertex(edgeJ, extremeVertexSearchHint1)) traverseStackCommonSidepodals.push_back(extremeVertexSearchHint1);
			else traverseStack.push_back(extremeVertexSearchHint1);
			if (IsSidepodalVertex(edgeJ, extremeVertexSearchHint2)) traverseStackCommonSidepodals.push_back(extremeVertexSearchHint2);
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
					if (!HAVE_VISITED_VERTEX(vAdj) && IsSidepodalVertex(i, vAdj))
					{
						if (IsSidepodalVertex(edgeJ, vAdj))
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
					int edgeK = adjacentEdges[v][k];
					if (IS_INTERNAL_EDGE(edgeK))
						continue; // Edges inside faces with 180 degrees dihedral angles can be ignored.
					if (IsSidepodalVertex(i, vAdj)
						&& IsSidepodalVertex(edgeJ, vAdj))
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

	TRACE_FMT(t0, "obb: category 1: 3 adjacent faces (evc calls=%ld steps=%ld)",
		TRACE_EVC_CALL_DELTA(evcCalls0), TRACE_EVC_STEP_DELTA(evcSteps0));
	TRACE_EVC_RESET(evcCalls0, evcSteps0);

	std::vector<int> antipodalEdges;
	std::vector<vec3> antipodalEdgeNormals;

	// Category 2: main algorithm body for finding all search directions where the OBB is flush with the
	// edges of the convex hull from two opposing faces. This is O(E*sqrtE*logV)?
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

				int edge = adjacentEdges[antipodalVertex][k];
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
					TestBox(hull.v, n, n2, volume, &minVolume, &minOBB);
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

		// Find two edges on the face. Since we have flexibility to choose from multiple edges of the same face,
		// choose two that are possibly most opposing to each other, in the hope that their sets of sidepodal
		// edges are most mutually exclusive as possible, speeding up the search below.
		int e1 = -1;
		for(size_t j = 0; j < faceEdges[i].size(); ++j)
		{
			int e = faceEdges[i][j];
			if (!IS_INTERNAL_EDGE(e))
			{
				e1 = e;
				break;
			}
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
			if (maxN1 < minN1) std::swap(minN1, maxN1); // XXX Numerical stability hack
		}
		else
		{
			CLEAR_GRAPH_SEARCH();
			extremeVertexSearchHint4 = ExtremeVertexConvex(hull, adjacencyData, -n1, floodFillVisited, floodFillVisitColor, minN1, extremeVertexSearchHint4); // O(logV)?
			minN1 = -minN1;
			if (maxN1 < minN1) std::swap(minN1, maxN1); // XXX Numerical stability hack
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
				if (maxN2 < minN2) std::swap(minN2, maxN2); // XXX Numerical stability hack
				float maxN3 = dot(n3, hull.v[edges[edge3].first]);

				const std::vector<int> &antipodalsEdge3 = antipodalPointsForEdge[edge3];
				float minN3 = FLT_MAX;
				if (antipodalsEdge3.size() < 20) // If there are very few antipodal vertices, do a very tight loop and just iterate over each.
				{
					for(size_t a = 0; a < antipodalsEdge3.size(); ++a)
						minN3 = fminf(minN3, dot(n3, hull.v[antipodalsEdge3[a]]));
					if (maxN3 < minN3) std::swap(minN3, maxN3); // XXX Numerical stability hack
				}
				else
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
		}
	}

	TRACE_FMT(t0, "obb: category 3: same face (evc calls=%ld steps=%ld)",
		TRACE_EVC_CALL_DELTA(evcCalls0), TRACE_EVC_STEP_DELTA(evcSteps0));

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

	// The search keeps a table of one bit for each vertex of each edge of the hull. Give up on a hull for
	// which that table alone would take more than 4 GB: such a hull has tens of thousands of vertices, and
	// the search would take hours on it in any case.
	size_t numEdges = 0;
	for (size_t i = 0; i < hull.f.size(); ++i)
		numEdges += hull.f[i].size() / 2;
	if ((double)numEdges * n > 8.0 * 4e9)
		return degenerate;

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