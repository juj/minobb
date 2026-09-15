// testobb.cpp
//
// Verifies minobb() (self-contained port of MathGeoLib's OBB::OptimalEnclosingOBB)
// against the four worked examples A)-D) in c:\code\minobb\minobb.txt
// (Jylanki 2015, "Optimal bounding boxes for non-triangular meshes", section 5).
//
// Reference volumes were computed two independent ways:
//  1) The original MathGeoLib OBB::OptimalEnclosingOBB() compiled from
//     C:\code\MathGeoLib (ground_truth.cpp).
//  2) An independent dense SO(3) search + local refinement in double precision
//     (python, scipy Nelder-Mead multi-start), which confirmed the same minima
//     and the contact structures described by the paper.
//
//     A: 37.3231583   (flush with edges 1-2, 1-4, 2-3 on three mutually adjacent faces)
//     B: 6.85714149   (= 48/7; flush with edges 0-1 and 2-3 on opposite faces,
//                       plus one more edge flush on an adjacent face)
//     C: 100          (flush with face 0-2-3, opposite face touches vertex 1)
//     D: 28.7701874   (flush with only two edges, which touch three distinct faces)
//
// For each example the test checks:
//  1. All input points are enclosed by the returned OBB.
//  2. The OBB axes form an orthonormal right-handed basis.
//  3. The volume matches the reference minimum within 1e-4 relative error.
//  4. The contact structure described in the paper holds (see contactsA-D below).
//
// Also verifies that the stride_bytes argument works by feeding one example with
// points embedded in a 20-byte struct.

#include <stdio.h>
#include <math.h>
#include "minobb.h"

static int g_numFailures = 0;

#define CHECK(cond, ...) do { \
	if (!(cond)) { \
		++g_numFailures; \
		printf("FAIL: %s (line %d): ", #cond, __LINE__); \
		printf(__VA_ARGS__); \
		printf("\n"); \
	} \
} while (0)

// Local-space coordinates of point p in frame o.
static vec3 toLocal(const OBB &o, const vec3 &p)
{
	vec3 d = p - o.pos;
	return vec3(dot(o.axis[0], d), dot(o.axis[1], d), dot(o.axis[2], d));
}

// True if the OBB is valid and encloses all points (with a small tolerance).
static bool encloses(const OBB &o, const vec3 *pts, int n)
{
	if (o.IsDegenerate())
		return false;
	for (int i = 0; i < n; ++i)
	{
		vec3 q = toLocal(o, pts[i]);
		if (q[0] < -o.r[0] - 1e-4f || q[0] > o.r[0] + 1e-4f
		 || q[1] < -o.r[1] - 1e-4f || q[1] > o.r[1] + 1e-4f
		 || q[2] < -o.r[2] - 1e-4f || q[2] > o.r[2] + 1e-4f)
			return false;
	}
	return true;
}

// True if the OBB axes form an orthonormal basis.
static bool isOrthonormal(const OBB &o)
{
	for (int i = 0; i < 3; ++i)
	{
		float len = dot(o.axis[i], o.axis[i]);
		if (fabsf(len - 1.f) > 1e-4f)
			return false;
		for (int j = i + 1; j < 3; ++j)
			if (fabsf(dot(o.axis[i], o.axis[j])) > 1e-4f)
				return false;
	}
	return true;
}

// An edge (i,j) is "flush" with an OBB face if both endpoints project to the
// same coordinate on some axis d and that coordinate is at the extreme (+/- r[d]).
// Outputs the axis and side (1 = +, -1 = -) of the face.
static bool edgeFlush(const OBB &o, const vec3 *pts, int i, int j, int &outAxis, int &outSide)
{
	vec3 a = toLocal(o, pts[i]);
	vec3 b = toLocal(o, pts[j]);
	for (int d = 0; d < 3; ++d)
	{
		if (fabsf(a[d] - b[d]) < 1e-4f)
		{
			if (fabsf(a[d] - o.r[d]) < 1e-4f)
			{
				outAxis = d;
				outSide = 1;
				return true;
			}
			if (fabsf(a[d] + o.r[d]) < 1e-4f)
			{
				outAxis = d;
				outSide = -1;
				return true;
			}
		}
	}
	return false;
}

// True if a point lies exactly on one of the six faces of the OBB. Returns the
// face encoded as axis*2 + side (side 0 = -, 1 = +), or -1.
static int pointOnFace(const OBB &o, const vec3 &p)
{
	vec3 q = toLocal(o, p);
	for (int d = 0; d < 3; ++d)
	{
		if (fabsf(q[d] - o.r[d]) < 1e-4f)
			return d * 2 + 1;
		if (fabsf(q[d] + o.r[d]) < 1e-4f)
			return d * 2 + 0;
	}
	return -1;
}

// The set of faces the edge (i,j) is flush with (1 or 2 faces if it lies on an
// OBB corner line). Returns the number of faces.
static int edgeFlushFaces(const OBB &o, const vec3 *pts, int i, int j, int *outFaces)
{
	vec3 a = toLocal(o, pts[i]);
	vec3 b = toLocal(o, pts[j]);
	int n = 0;
	// The edge endpoints must coincide on axis d and sit at the extreme.
	for (int d = 0; d < 3; ++d)
	{
		if (fabsf(a[d] - b[d]) < 1e-4f)
		{
			if (fabsf(a[d] - o.r[d]) < 1e-4f)
				outFaces[n++] = d * 2 + 1;
			else if (fabsf(a[d] + o.r[d]) < 1e-4f)
				outFaces[n++] = d * 2 + 0;
		}
	}
	return n;
}

struct PaddedPoint
{
	float x, y, z;
	float padding[2]; // To test stride_bytes = 20.
};

typedef void (*ContactsFn)(const char *, const OBB &, const vec3 *, int);

static void runExample(const char *name, const float *refPts, int n, float refVolume, ContactsFn checkContacts)
{
	vec3 pts[n];
	for (int i = 0; i < n; ++i)
		pts[i] = vec3(refPts[3*i], refPts[3*i+1], refPts[3*i+2]);

	OBB o = minobb(convex_hull((float *)refPts, n, 12));
	printf("%s: volume = %.9g (ref %.9g)\n", name, o.Volume(), refVolume);
	printf("    pos = (%.6f, %.6f, %.6f), r = (%.6f, %.6f, %.6f)\n",
		o.pos[0], o.pos[1], o.pos[2], o.r[0], o.r[1], o.r[2]);
	for (int i = 0; i < 3; ++i)
		printf("    axis[%d] = (%.6f, %.6f, %.6f)\n", i, o.axis[i][0], o.axis[i][1], o.axis[i][2]);

	CHECK(!o.IsDegenerate(), "%s: OBB is degenerate", name);
	CHECK(encloses(o, pts, n), "%s: OBB does not enclose all input points", name);
	CHECK(isOrthonormal(o), "%s: OBB axes are not orthonormal", name);
	CHECK(fabsf(o.Volume() - refVolume) <= refVolume * 1e-4f,
		"%s: volume %.9g differs from reference %.9g", name, o.Volume(), refVolume);
	checkContacts(name, o, pts, n);
	printf("\n");
}

// A) The OBB is flush with edges 1-2, 1-4 and 2-3, and these edges touch three
//    mutually adjacent faces of the OBB.
static void contactsA(const char *name, const OBB &o, const vec3 *pts, int n)
{
	(void)name; (void)n;
	int axis12, side12, axis14, side14, axis23, side23;
	CHECK(edgeFlush(o, pts, 1, 2, axis12, side12), "A: edge (1,2) is not flush with any face");
	CHECK(edgeFlush(o, pts, 1, 4, axis14, side14), "A: edge (1,4) is not flush with any face");
	CHECK(edgeFlush(o, pts, 2, 3, axis23, side23), "A: edge (2,3) is not flush with any face");
	CHECK(axis12 != axis14 && axis12 != axis23 && axis14 != axis23,
		"A: edges (1,2), (1,4), (2,3) should be flush with three mutually adjacent (distinct) faces");
}

// B) The OBB is flush with edges 0-1, 0-2, 2-3. Edges 0-1 and 2-3 lie on opposite faces.
static void contactsB(const char *name, const OBB &o, const vec3 *pts, int n)
{
	(void)name; (void)n;
	int axis01, side01, axis23, side23;
	CHECK(edgeFlush(o, pts, 0, 1, axis01, side01), "B: edge (0,1) is not flush with any face");
	CHECK(edgeFlush(o, pts, 2, 3, axis23, side23), "B: edge (2,3) is not flush with any face");
	CHECK(axis01 == axis23 && side01 != side23,
		"B: edges (0,1) and (2,3) should lie on opposite faces");
	// At least three edges flush in total (Theorem 7.1).
	int numFlush = 0;
	int a, s;
	for (int i = 0; i < n; ++i)
		for (int j = i + 1; j < n; ++j)
			if (edgeFlush(o, pts, i, j, a, s))
				++numFlush;
	CHECK(numFlush >= 3, "B: expected at least 3 flush edges, got %d", numFlush);
}

// C) The OBB is flush with the face formed by vertices 0 2 3, and the face opposite
//    to that touches vertex 1.
static void contactsC(const char *name, const OBB &o, const vec3 *pts, int n)
{
	(void)name; (void)n;
	int f0 = pointOnFace(o, pts[0]);
	int f2 = pointOnFace(o, pts[2]);
	int f3 = pointOnFace(o, pts[3]);
	int f1 = pointOnFace(o, pts[1]);
	CHECK(f0 >= 0, "C: vertex 0 is not on any OBB face");
	CHECK(f0 == f2 && f0 == f3, "C: vertices 0, 2, 3 should all lie on the same OBB face");
	CHECK(f1 >= 0 && f1 != f0, "C: vertex 1 is not on a face of the OBB");
	// The face touching vertex 1 is opposite to the face flush with 0-2-3.
	CHECK(f1 == (f0 ^ 1), "C: vertex 1 should be on the face opposite 0-2-3 (face %d vs %d)", f1, f0);
}

// D) The OBB is flush with only two edges of the polyhedron, but these edges touch
//    three distinct faces of the OBB.
static void contactsD(const char *name, const OBB &o, const vec3 *pts, int n)
{
	(void)name; (void)n;
	// Collect all flush edges of the (convex hull = the input set here) and the
	// faces they touch.
	int flushEdges[16][2];
	int flushFaces[16][2];
	int numFlush = 0;
	for (int i = 0; i < n; ++i)
		for (int j = i + 1; j < n; ++j)
		{
			if (numFlush < 16)
			{
				int faces[2];
				int nf = edgeFlushFaces(o, pts, i, j, faces);
				if (nf > 0)
				{
					flushEdges[numFlush][0] = i;
					flushEdges[numFlush][1] = j;
					for (int k = 0; k < 2; ++k)
						flushFaces[numFlush][k] = (k < nf) ? faces[k] : -1;
					++numFlush;
				}
			}
		}
	printf("    D: flush edges: ");
	for (int i = 0; i < numFlush; ++i)
		printf("(%d,%d)->{face%d%sface%d} ", flushEdges[i][0], flushEdges[i][1],
			flushFaces[i][0], flushFaces[i][1] >= 0 ? "," : "", flushFaces[i][1]);
	printf("\n");
	// There must exist a pair of flush edges touching three distinct faces total.
	bool found = false;
	for (int i = 0; i < numFlush && !found; ++i)
		for (int j = i + 1; j < numFlush; ++j)
		{
			int distinct = 0;
			int used[6] = { 0, 0, 0, 0, 0, 0 };
			for (int k = 0; k < 2; ++k)
				if (flushFaces[i][k] >= 0)
					used[flushFaces[i][k]] = 1;
			for (int k = 0; k < 2; ++k)
				if (flushFaces[j][k] >= 0)
					used[flushFaces[j][k]] = 1;
			for (int f = 0; f < 6; ++f)
				distinct += used[f];
			if (distinct >= 3)
				found = true;
		}
	CHECK(found, "D: no two flush edges touch three distinct OBB faces (numFlush=%d)", numFlush);
}

int main()
{
	// A)
	{
		const float pts[] = {
			1.f, 0.f, 2.f,
			1.f, 4.f, 3.f,
			4.f, 0.f, 4.f,
			4.f, 2.f, 1.f,
			3.f, 2.f, 0.f };
		runExample("A", pts, 5, 37.3231583f, contactsA);
	}
	// B)
	{
		const float pts[] = {
			0.f, 2.f, 0.f,
			0.f, 2.f, 2.f,
			0.f, 4.f, 0.f,
			2.f, 0.f, 2.f };
		runExample("B", pts, 4, 6.85714149f, contactsB);
	}
	// C)
	{
		const float pts[] = {
			0.f, 0.f, 0.f,
			5.f, 2.f, 2.f,
			5.f, 5.f, 0.f,
			10.f, 0.f, 0.f };
		runExample("C", pts, 4, 100.f, contactsC);
	}
	// D)
	{
		const float pts[] = {
			0.f, 4.f, 2.f,
			0.f, 4.f, 4.f,
			2.f, 4.f, 2.f,
			3.f, 0.f, 1.f,
			1.f, 4.f, 0.f };
		runExample("D", pts, 5, 28.7701874f, contactsD);
	}

	// Stride test: example C with points embedded in 20-byte structs.
	{
		const float ref[] = {
			0.f, 0.f, 0.f,
			5.f, 2.f, 2.f,
			5.f, 5.f, 0.f,
			10.f, 0.f, 0.f };
		PaddedPoint padded[4];
		for (int i = 0; i < 4; ++i)
		{
			padded[i].x = ref[3*i];
			padded[i].y = ref[3*i+1];
			padded[i].z = ref[3*i+2];
			for (int k = 0; k < 2; ++k)
				padded[i].padding[k] = 999.f; // Junk data that must be ignored.
		}
		CHECK(sizeof(PaddedPoint) == 20, "test setup: expected 20 byte padded struct");
		OBB o = minobb(convex_hull((float *)&padded[0], 4, (int)sizeof(PaddedPoint)));
		vec3 pts[4] = { vec3(0,0,0), vec3(5,2,2), vec3(5,5,0), vec3(10,0,0) };
		printf("stride(20): volume = %.9g (ref 100)\n", o.Volume());
		CHECK(!o.IsDegenerate(), "stride: OBB is degenerate");
		CHECK(encloses(o, pts, 4), "stride: OBB does not enclose all points");
		CHECK(fabsf(o.Volume() - 100.f) <= 100.f * 1e-4f, "stride: volume %.9g != 100", o.Volume());
		printf("\n");
	}

	// Degenerate input sanity: planar points should give a flat (zero volume) box.
	{
		const float pts[] = {
			0.f, 0.f, 0.f,
			5.f, 0.f, 0.f,
			5.f, 5.f, 0.f,
			0.f, 5.f, 0.f,
			2.f, 3.f, 0.f };
		OBB o = minobb(convex_hull((float *)pts, 5, 12));
		vec3 p[5] = { vec3(0,0,0), vec3(5,0,0), vec3(5,5,0), vec3(0,5,0), vec3(2,3,0) };
		printf("planar: volume = %.9g\n", o.Volume());
		CHECK(!o.IsDegenerate(), "planar: OBB is degenerate");
		CHECK(encloses(o, p, 5), "planar: OBB does not enclose all points");
		CHECK(o.Volume() < 1e-3f, "planar: volume %.9g should be ~0", o.Volume());
		printf("\n");
	}

	// Nearly-planar regression test: a flat triangle, a point 1e-5 above it
	// (numerically coplanar "internal" hull edges) and a point well below.
	// The true minimum volume is 6.0890 (independent double-precision search);
	// the pre-fix code returned 10.15 (2D planar fallback) or bailed out.
	{
		const float delta = 1e-5f;
		const float pts[] = {
			0.f, 0.f, 0.f,
			2.f, 0.f, 0.f,
			0.f, 2.f, 0.f,
			0.9f, 1.1f, delta,
			1.3f, -0.2f, -2.f };
		vec3 p[5] = { vec3(0,0,0), vec3(2,0,0), vec3(0,2,0), vec3(0.9f,1.1f,delta), vec3(1.3f,-0.2f,-2.f) };
		OBB o = minobb(convex_hull((float *)pts, 5, 12));
		printf("near-planar: volume = %.6f\n", o.Volume());
		CHECK(!o.IsDegenerate(), "near-planar: OBB is degenerate");
		CHECK(encloses(o, p, 5), "near-planar: OBB does not enclose all points");
		CHECK(fabsf(o.Volume() - 6.089046f) / 6.089046f < 0.01f,
			"near-planar: volume %.6f should be ~6.089 (true minimum)", o.Volume());
		printf("\n");
	}

	if (g_numFailures == 0)
	{
		printf("ALL TESTS PASSED\n");
		return 0;
	}
	printf("%d CHECK(S) FAILED\n", g_numFailures);
	return 1;
}
