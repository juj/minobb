// convex_hull.cpp
//
// Quickhull (Barber, Dobkin, Huhdanpaa 1996) on top of exact predicates.
//
// All robustness comes from the orientation predicates orient2d()/orient3d(),
// whose result always has the mathematically correct sign. They evaluate the
// determinant in double precision along with a bound for its rounding error
// (the "stage A" filter of Shewchuk 1997), and only when the determinant is
// within the bound re-evaluate it exactly. That is cheap for f32 input: the
// product of two floats is exact in a double, so the determinant is a short
// sum of doubles that can be accumulated without error.
//
// With exact predicates the textbook algorithm needs no tolerances and no
// repair steps: a point is outside a face iff it is strictly above its plane,
// the faces visible from an outside point form a disc, and so on. Points on
// the surface of the hull are never added to it, but a vertex added earlier
// may end up in the middle of an edge or a facet of the growing hull. So as
// the last step, the exactly coplanar triangles are merged into the actual
// polygonal facets, of which only the corners are output.

#include "convex_hull.h"

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>

// The exact arithmetic needs strict IEEE-754 semantics, also in fast-math builds.
#if defined(__clang__) || defined(_MSC_VER)
#pragma float_control(precise, on)
#elif defined(__GNUC__)
#pragma GCC optimize("no-fast-math")
#endif

namespace
{

// Returns the leading term of the exact sum of e[0..n) (clobbers e): it has the
// sign of the sum, and approximates its value. This is Shewchuk's
// Grow-Expansion: e[0..m) holds the running sum as nonoverlapping terms of
// increasing magnitude, into which the remaining terms are added one by one.
double exact_sum(double *e, int n)
{
	int m = 0;
	for (int i = 0; i < n; ++i)
	{
		double b = e[i];
		int k = 0;
		for (int j = 0; j < m; ++j)
		{
			double x = e[j] + b, t = x - e[j], y = (e[j] - (x - t)) + (b - t); // x + y == e[j] + b, exactly.
			b = x;
			if (y != 0) e[k++] = y;
		}
		if (b != 0) e[k++] = b;
		m = k;
	}
	return m ? e[m - 1] : 0;
}

// Twice the signed area of triangle abc projected along coordinate axis k:
// positive iff a, b, c wind counterclockwise about +k. The sign is exact.
double orient2d(int k, const vec3 &a, const vec3 &b, const vec3 &c)
{
	const int u = (k + 1) % 3, v = (k + 2) % 3;
	const double au = a[u], av = a[v], bu = b[u], bv = b[v], cu = c[u], cv = c[v];
	double l = (bu - au) * (cv - av), r = (bv - av) * (cu - au), det = l - r, mag = fabs(l) + fabs(r);
	if (fabs(det) > 3.3306690738754716e-16 * mag || mag == 0) return det;
	double e[6] = { bu * cv, -bu * av, -au * cv, -bv * cu, bv * au, av * cu };
	return exact_sum(e, 6);
}

// Six times the signed volume of tetrahedron abcd: positive iff d is above the
// plane of a, b, c, i.e. on the side from which a, b, c are seen winding
// counterclockwise. The sign is exact.
double orient3d(const vec3 &a, const vec3 &b, const vec3 &c, const vec3 &d)
{
	double u[3], v[3], w[3], det = 0, mag = 0;
	for (int k = 0; k < 3; ++k)
	{
		u[k] = (double)b[k] - a[k];
		v[k] = (double)c[k] - a[k];
		w[k] = (double)d[k] - a[k];
	}
	for (int k = 0, k1 = 1, k2 = 2; k < 3; k1 = k2, k2 = k++)
	{
		double l = u[k1] * v[k2], r = u[k2] * v[k1];
		det += (l - r) * w[k];
		mag += (fabs(l) + fabs(r)) * fabs(w[k]);
	}
	if (fabs(det) > 7.7715611723761027e-16 * mag || mag == 0) return det;

	// Exact evaluation: det = |b c d| - |a c d| + |a b d| - |a b c|, a sum of 24
	// products of three floats. The product of two floats is exact in a double;
	// splitting it into its high 26 bits and the rest makes the products with
	// the third float exact as well.
	const vec3 *p[4] = { &a, &b, &c, &d };
	double e[48];
	int n = 0;
	for (int i = 0; i < 4; ++i)
	{
		const vec3 &q = *p[i < 1], &r = *p[1 + (i < 2)], &s = *p[2 + (i < 3)];
		for (int k = 0; k < 3; ++k)
			for (int j = 1; j <= 2; ++j) // The terms +q[k]*r[k+1]*s[k+2] and -q[k]*r[k+2]*s[k+1].
			{
				double qr = (double)q[k] * r[(k + j) % 3], hi;
				double z = (i + j) % 2 ? s[(k + 3 - j) % 3] : -s[(k + 3 - j) % 3];
				uint64_t bits;
				memcpy(&bits, &qr, 8);
				bits &= ~0x7FFFFFFull;
				memcpy(&hi, &bits, 8);
				e[n++] = hi * z;
				e[n++] = (qr - hi) * z;
			}
	}
	return exact_sum(e, n);
}

// Hull of exactly coplanar points (Andrew's monotone chain): a single polygon
// wound counterclockwise about +k, a coordinate axis not parallel to the plane.
void planar_hull(const std::vector<vec3> &P, int k, Hull3 &hull)
{
	const int u = (k + 1) % 3, v = (k + 2) % 3;
	std::vector<int> order(P.size()), h;
	for (size_t i = 0; i < order.size(); ++i) order[i] = (int)i;
	std::sort(order.begin(), order.end(), [&](int a, int b)
		{ return P[a][u] != P[b][u] ? P[a][u] < P[b][u] : P[a][v] < P[b][v]; });
	for (int pass = 0; pass < 2; ++pass, std::reverse(order.begin(), order.end())) // Lower, then upper chain.
	{
		const size_t keep = pass ? h.size() : 1;
		for (int i : order)
		{
			while (h.size() > keep && orient2d(k, P[h[h.size() - 2]], P[h.back()], P[i]) <= 0) h.pop_back();
			h.push_back(i);
		}
	}
	h.pop_back(); // The first point again.
	hull.f.emplace_back();
	for (int i : h)
	{
		hull.f[0].push_back((int)hull.v.size());
		hull.v.push_back(P[i]);
	}
}

struct Face
{
	int v[3];     // Corners, counterclockwise when seen from outside.
	int adj[3];   // adj[i] is the face across the edge v[i] -> v[(i+1)%3].
	int outside;  // The outside set: head of the list of points above this face, farthest one first. -1 if none.
	bool dead;    // No longer part of the hull.
	double n[3];  // Plane normal (v[1]-v[0]) x (v[2]-v[0]).
	double err;   // Rounding error bound of height().
	double far;   // height() of the farthest outside point.
};

// The index of vertex v in face f.
int corner(const Face &f, int v) { return f.v[0] == v ? 0 : f.v[1] == v ? 1 : 2; }

struct QuickHull
{
	std::vector<vec3> P;         // The input points.
	double lo[3], hi[3];         // Their bounding box.
	std::vector<Face> F;         // Face pool.
	std::vector<int> spare;      // Dead faces, to be recycled.
	std::vector<int> work;       // Faces that have outside points, i.e. are yet to be processed.
	std::vector<int> fresh;      // Faces created by the latest add_point().
	std::vector<int> link;       // Per point: the next point in the same outside set. Scratch for hull vertices.
	std::vector<int> vis, hor;   // Scratch of add_point(): the visible faces, and the horizon edges as face * 3 + edge.

	// Height of point q above face f in units of |f.n|: positive iff q is strictly outside of f.
	double height(const Face &f, int q) const
	{
		const vec3 &a = P[f.v[0]], &p = P[q];
		double h = f.n[0] * ((double)p.x - a.x) + f.n[1] * ((double)p.y - a.y) + f.n[2] * ((double)p.z - a.z);
		return fabs(h) > f.err ? h : orient3d(a, P[f.v[1]], P[f.v[2]], p);
	}

	int add_face(int a, int b, int c)
	{
		int i = (int)F.size();
		if (spare.empty()) F.emplace_back();
		else { i = spare.back(); spare.pop_back(); }
		Face &f = F[i];
		f.v[0] = a; f.v[1] = b; f.v[2] = c;
		f.outside = -1;
		f.dead = false;
		// The plane is cached for height(), which then computes the same determinant as orient3d(). Its
		// error bound is also the same, except evaluated for the bounding box instead of the actual point.
		double u[3], w[3];
		for (int k = 0; k < 3; ++k)
		{
			u[k] = (double)P[b][k] - P[a][k];
			w[k] = (double)P[c][k] - P[a][k];
		}
		f.err = 0;
		for (int k = 0, k1 = 1, k2 = 2; k < 3; k1 = k2, k2 = k++)
		{
			double l = u[k1] * w[k2], r = u[k2] * w[k1];
			f.n[k] = l - r;
			f.err += (fabs(l) + fabs(r)) * std::max(P[a][k] - lo[k], hi[k] - P[a][k]);
		}
		f.err *= 7.7715611723761027e-16;
		return i;
	}

	// Puts point q into the outside set of the first fresh face that it is above of, if any.
	void assign(int q)
	{
		for (int i : fresh)
		{
			Face &f = F[i];
			double h = height(f, q);
			if (h <= 0) continue;
			if (f.outside < 0) work.push_back(i);
			if (f.outside < 0 || h > f.far) { link[q] = f.outside; f.outside = q; f.far = h; }
			else { link[q] = link[f.outside]; link[f.outside] = q; }
			return;
		}
	}

	// Adds point p, which is above face f0, to the hull.
	void add_point(int p, int f0)
	{
		// Flood fill the faces visible from p, collecting their edges to non-visible faces: the horizon.
		vis.assign(1, f0);
		hor.clear();
		F[f0].dead = true;
		for (size_t i = 0; i < vis.size(); ++i)
			for (int e = 0; e < 3; ++e)
			{
				int g = F[vis[i]].adj[e];
				if (F[g].dead) continue;
				if (height(F[g], p) > 0) { F[g].dead = true; vis.push_back(g); }
				else hor.push_back(vis[i] * 3 + e);
			}

		// Replace the visible faces with a cone of new faces from the horizon to p.
		fresh.clear();
		for (int h : hor)
		{
			int a = F[h / 3].v[h % 3], b = F[h / 3].v[(h + 1) % 3], g = F[h / 3].adj[h % 3];
			int f = add_face(a, b, p);
			F[f].adj[0] = g;
			F[g].adj[corner(F[g], b)] = f;
			link[a] = f; // The new face at each horizon vertex, to stitch the cone together below.
			fresh.push_back(f);
		}
		for (int f : fresh)
		{
			int g = link[F[f].v[1]];
			F[f].adj[1] = g;
			F[g].adj[2] = f;
		}

		// Hand the outside points of the visible faces over to the new faces.
		for (int f : vis)
		{
			for (int q = F[f].outside, next; q >= 0; q = next)
			{
				next = link[q];
				assign(q);
			}
			spare.push_back(f);
		}
	}

	// Outputs the facets of the finished hull: the maximal sets of coplanar faces, as polygons.
	void output(Hull3 &hull)
	{
		// Label the facets.
		std::vector<int> facet(F.size(), -1), stack;
		int num_facets = 0;
		for (int i = 0; i < (int)F.size(); ++i)
		{
			if (F[i].dead || facet[i] >= 0) continue;
			facet[i] = num_facets;
			stack.assign(1, i);
			while (!stack.empty())
			{
				const Face &f = F[stack.back()];
				stack.pop_back();
				for (int e = 0; e < 3; ++e)
				{
					int g = f.adj[e], apex = F[g].v[(corner(F[g], f.v[e]) + 1) % 3];
					if (facet[g] < 0 && height(f, apex) == 0) { facet[g] = num_facets; stack.push_back(g); }
				}
			}
			++num_facets;
		}

		// Walk the boundary of each facet. A boundary vertex is a corner of the facet iff the
		// facet on the other side changes there (otherwise it is in the middle of an edge).
		hull.f.resize(num_facets);
		std::fill(link.begin(), link.end(), -1); // From here on: point -> index in hull.v.
		for (int i = 0; i < (int)F.size(); ++i)
			for (int j = 0; j < 3 && !F[i].dead; ++j)
			{
				const int r = facet[i];
				if (!hull.f[r].empty() || facet[F[i].adj[j]] == r) continue;
				int f = i, e = j;
				do
				{
					int b = F[f].v[(e + 1) % 3], across = facet[F[f].adj[e]];
					for (e = (e + 1) % 3; facet[F[f].adj[e]] == r; e = corner(F[f], b)) f = F[f].adj[e];
					if (facet[F[f].adj[e]] == across) continue;
					if (link[b] < 0) { link[b] = (int)hull.v.size(); hull.v.push_back(P[b]); }
					hull.f[r].push_back(link[b]);
				} while (f != i || e != j);
			}
	}
};

} // ~namespace

Hull3 convex_hull(const float *pts, int num_pts, int stride_bytes)
{
	Hull3 hull;
	hull.degenerate = true;
	QuickHull q;
	std::vector<vec3> &P = q.P;
	P.reserve(std::max(num_pts, 0));
	for (int i = 0; i < num_pts; ++i)
	{
		vec3 p;
		memcpy(&p, (const char *)pts + (size_t)i * stride_bytes, sizeof p);
		if (std::isfinite(p.x) && std::isfinite(p.y) && std::isfinite(p.z)) P.push_back(p);
	}
	const int n = (int)P.size();
	if (n == 0) return hull;

	// Find the initial simplex s[0..3]. First the two extreme points along the longest axis of the bounding box.
	int ilo[3] = { 0, 0, 0 }, ihi[3] = { 0, 0, 0 }, s[4] = { 0, 0, 0, 0 }, axis = 0;
	for (int i = 1; i < n; ++i)
		for (int k = 0; k < 3; ++k)
		{
			if (P[i][k] < P[ilo[k]][k]) ilo[k] = i;
			if (P[i][k] > P[ihi[k]][k]) ihi[k] = i;
		}
	for (int k = 0; k < 3; ++k)
	{
		q.lo[k] = P[ilo[k]][k];
		q.hi[k] = P[ihi[k]][k];
		if (q.hi[k] - q.lo[k] > q.hi[axis] - q.lo[axis]) axis = k;
	}
	s[0] = ilo[axis];
	s[1] = ihi[axis];
	if (s[0] == s[1]) // All points are equal.
	{
		hull.v.push_back(P[0]);
		return hull;
	}

	// Then the point farthest from their line. It is searched for in plain floating point: only if that
	// comes up with a point that is exactly on the line, the exact predicate is used to find one that is not.
	const vec3 a = P[s[0]], b = P[s[1]];
	const double u[3] = { (double)b.x - a.x, (double)b.y - a.y, (double)b.z - a.z };
	auto off_line = [&](int i)
	{
		return orient2d(0, a, b, P[i]) != 0 || orient2d(1, a, b, P[i]) != 0 || orient2d(2, a, b, P[i]) != 0;
	};
	double best = 0;
	for (int i = 0; i < n; ++i)
	{
		const double w[3] = { (double)P[i].x - a.x, (double)P[i].y - a.y, (double)P[i].z - a.z };
		const double d = fabs(u[1] * w[2] - u[2] * w[1]) + fabs(u[2] * w[0] - u[0] * w[2]) + fabs(u[0] * w[1] - u[1] * w[0]);
		if (d > best) { best = d; s[2] = i; }
	}
	for (int i = 0; i < n && !off_line(s[2]); ++i) s[2] = i;
	if (!off_line(s[2])) // All points are collinear.
	{
		hull.v.push_back(a);
		hull.v.push_back(b);
		return hull;
	}

	// And the point farthest from the plane of those three.
	q.add_face(s[0], s[1], s[2]);
	best = 0;
	for (int i = 0; i < n; ++i)
	{
		double d = q.height(q.F[0], i);
		if (fabs(d) > fabs(best)) { best = d; s[3] = i; }
	}
	if (best == 0) // All points are coplanar.
	{
		int k = 0;
		for (int i = 0; i < 3; ++i)
		{
			double d = fabs(orient2d(i, P[s[0]], P[s[1]], P[s[2]]));
			if (d > best) { best = d; k = i; }
		}
		planar_hull(P, k, hull);
		return hull;
	}
	hull.degenerate = false;

	// Build the simplex, oriented so that s[3] is below the face s[0] s[1] s[2].
	if (best > 0) std::swap(s[1], s[2]);
	q.F.clear();
	static const int V[4][3] = { { 0, 1, 2 }, { 1, 0, 3 }, { 2, 1, 3 }, { 0, 2, 3 } };
	static const int A[4][3] = { { 1, 2, 3 }, { 0, 3, 2 }, { 0, 1, 3 }, { 0, 2, 1 } };
	for (int i = 0; i < 4; ++i)
	{
		q.fresh.push_back(q.add_face(s[V[i][0]], s[V[i][1]], s[V[i][2]]));
		memcpy(q.F[i].adj, A[i], sizeof A[i]);
	}
	q.link.resize(n);
	for (int i = 0; i < n; ++i) q.assign(i);

	// Grow the hull by the farthest outside point of each face in turn, until no points remain outside.
	// Going breadth first keeps the hull evenly refined, and thus the horizons short.
	for (std::vector<int> batch; !q.work.empty(); batch.clear())
	{
		batch.swap(q.work);
		for (int f : batch)
		{
			const int p = q.F[f].outside;
			if (q.F[f].dead || p < 0) continue; // The face was removed (and maybe recycled) in the meantime.
			q.F[f].outside = q.link[p];
			q.add_point(p, f);
		}
	}
	q.output(hull);
	return hull;
}
