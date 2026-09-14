// gtwrap.cpp: C interface around MathGeoLib for the comparison tools.
#include "MathGeoLib.h"
using namespace math;

extern "C" void GT_ResetWinRec();
extern "C" void GT_GetWinRec(int *out);
extern "C" float GT_GetWinVol();

// Stubs: the real winner-recording hooks live in the debug build (OBB_dbg.cpp),
// which is not linked here. findcase.cpp only uses these for diagnostics.
extern "C" void GT_ResetWinRec() {}
extern "C" void GT_GetWinRec(int *out) { for (int i = 0; i < 11; ++i) out[i] = -1; }
extern "C" float GT_GetWinVol() { return 0.f; }

extern "C" double gt_volume(const float *v, int n)
{
	if (n <= 0) return 0.0;
	vec *p = new vec[n];
	for (int i = 0; i < n; ++i)
		p[i] = vec(v[3*i], v[3*i+1], v[3*i+2]);
	OBB o = OBB::OptimalEnclosingOBB(p, n);
	double r = o.Volume();
	delete[] p;
	return r;
}

// out: pos(3), r(3), axis0(3), axis1(3), axis2(3), volume(1), degenerate(1)
extern "C" void gt_obb(const float *v, int n, double *out)
{
	vec *p = new vec[n];
	for (int i = 0; i < n; ++i)
		p[i] = vec(v[3*i], v[3*i+1], v[3*i+2]);
	OBB o = OBB::OptimalEnclosingOBB(p, n);
	out[0] = o.pos[0]; out[1] = o.pos[1]; out[2] = o.pos[2];
	out[3] = o.r[0];   out[4] = o.r[1];   out[5] = o.r[2];
	for (int i = 0; i < 3; ++i)
	{
		out[6+i*3+0] = o.axis[i][0];
		out[6+i*3+1] = o.axis[i][1];
		out[6+i*3+2] = o.axis[i][2];
	}
	out[15] = o.Volume();
	out[16] = o.IsDegenerate() ? 1.0 : 0.0;
	delete[] p;
}

// Convex hull of the points. faceverts: F*16 ints, facecount: F bytes (face vertex counts).
// Returns the number of hull vertices.
extern "C" int gt_hull(const float *v, int n, int *outV, int *outF, int *faceverts, int *facecount)
{
	if (n <= 0) { *outV = *outF = 0; return 0; }
	vec *p = new vec[n];
	for (int i = 0; i < n; ++i)
		p[i] = vec(v[3*i], v[3*i+1], v[3*i+2]);
	Polyhedron h = Polyhedron::ConvexHull(p, n);
	*outV = (int)h.v.size();
	int F = 0;
	for (size_t i = 0; i < h.f.size(); ++i)
	{
		if ((int)h.f[i].v.size() > 16)
			continue;
		facecount[F] = (int)h.f[i].v.size();
		for (size_t j = 0; j < h.f[i].v.size(); ++j)
			faceverts[F*16 + j] = h.f[i].v[j];
		++F;
	}
	*outF = F;
	delete[] p;
	return *outV;
}
