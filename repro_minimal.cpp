// repro_minimal.cpp: minimal 5-point set exercising the nearly-planar code
// paths of minobb.cpp.
//
// Geometry: a flat triangle pA,pB,pC in the z=0 plane, a point pD just delta
// above it (its whole 1-ring is {pA,pB,pC}), and a point pE well below.
// The convex hull has 5 vertices; the three "top" edges (pA,pD), (pB,pD),
// (pC,pD) are shared by pairs of numerically coplanar faces (dihedral
// deviation ~ delta/2.8 << 1e-4), i.e. "internal edges" in OBB terminology.
//
// Two historical bugs are triggered by this input:
//  1) Pre-fix antipodal predicate: pD's 1-ring lies within delta of the flat
//     plane, so the degenerate predicate classified pD as antipodal to its
//     own edge -> spurious "degenerate planar" bail-out. Fixed by skipping
//     internal edges in the antipodal precomputation.
//  2) Category-search completeness: with pD in the hull the flush-edge
//     structure is broken, the category search finds NO configuration, and
//     the naive 2D planar fallback returned 10.15 (66% above the optimum).
//     Fixed with a coarse sphere-sweep fallback (exact given each candidate
//     axis: range along the axis x minimum-area rectangle of the projection).
//
// Fixed result: volume 6.0890 - the true minimum (independent double-
// precision search: 6.0890). MathGeoLib itself returns 6.9681 here (its
// incremental hull drops pB instead of keeping pD, and its category search
// is also suboptimal on the resulting tetrahedron).
//
// Build:  g++ -O2 -I. repro_minimal.cpp -o repro_minimal.exe
#include <cstdio>
#include <vector>
#include <cmath>

#include "minobb.cpp"

using namespace std;

int main()
{
	const float delta = 1e-5f;
	// pA,pB,pC: flat triangle in the z=0 plane. pD: bump, delta above it
	// (its whole 1-ring is {pA,pB,pC}). pE: far below the plane.
	// Chosen so no 4 points are accidentally coplanar.
	float v[15] =
	{
		0.f,   0.f,   0.f,
		2.f,   0.f,   0.f,
		0.f,   2.f,   0.f,
		0.9f,  1.1f,  delta,
		1.3f, -0.2f, -2.f,
	};
	OBB o = minobb(v, 5, 12);
	printf("volume = %.6f\n", o.Volume());
	printf("r = (%.6f, %.6f, %.6f)\n", o.r.x, o.r.y, o.r.z);

	// Containment check.
	float worst = 0.f;
	for (int i = 0; i < 5; ++i)
	{
		vec3 p(v[3*i], v[3*i+1], v[3*i+2]);
		vec3 lp = o.LocalToWorldInverse(p);
		for (int a = 0; a < 3; ++a)
			worst = Maxf(worst, Absf(lp[a]) - o.r[a]);
	}
	printf("worst containment violation = %.3e %s\n", worst, worst > 1e-4f ? "  <-- FAILS TO CONTAIN" : "");

	// True minimum (independent double-precision two-level search): 6.0890.
	printf("true minimal volume (double-precision search) ~= 6.0890\n");
	return 0;
}
