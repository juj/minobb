// test/test_minobb.cpp
//
// Usage: test_minobb <file.glb | file.gltf | file.txt> [--tolerance fraction | --ground-truth [threads]]
//
// Computes the convex hull and the minimum volume OBB of the vertex positions
// of a glTF file (or of the points in a text file with one "x y z" per line),
// and prints a JSON document that tells how good the box of minobb() is:
//   - how far its axes are from orthonormal, and how far the input points are
//     outside of it,
//   - the extents of the tightest box of the same orientation (measured in
//     double precision).
// minobb() is run with the given tolerance (0 for the minimum volume box), or
// with its default tolerance if none is given.
//
// With --ground-truth, the true minimum volume box is searched for and printed
// instead ("gt"), and minobb() is not run. That is an exhaustive search in
// double precision, which shares no code or shortcuts with minobb.cpp. It
// relies on a theorem of O'Rourke (1985): a minimum volume box of a convex
// polyhedron has two adjacent faces that are each flush with an edge of the
// polyhedron. For each pair of hull edges (e1, e2), the boxes with a face
// normal n1 in the arc of normals of e1 and an adjacent face normal n2 in the
// arc of e2 form a one-parameter family, whose volume is minimized
// numerically. A family is skipped only when a lower bound of its volume shows
// that it cannot contain a smaller box than the best one so far. This takes
// O(E^2) time at the very least: seconds for hulls of thousands of vertices,
// and minutes on all the given threads for hulls of tens of thousands.
//
// Two more reference boxes are printed along with it:
//   - "sweep" (hulls of up to 400 vertices): the result of a second,
//     independent search that cross-checks the first one. One box axis is
//     sampled over the hemisphere, the other two axes are the exact minimum
//     area rectangle of the projection of the hull, and the best samples are
//     refined locally.
//   - "flat": the box that has the smallest area among the boxes that share the
//     thinnest axis of the ground truth box. This is the reference for hulls
//     that are flat to the precision of floats, where volume means nothing.

#define _CRT_SECURE_NO_WARNINGS

#include "minobb.h"
#include "glb.h"

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <thread>

struct D3
{
	double x, y, z;
	D3 operator+(const D3 &b) const { return { x + b.x, y + b.y, z + b.z }; }
	D3 operator-(const D3 &b) const { return { x - b.x, y - b.y, z - b.z }; }
	D3 operator*(double s) const { return { x * s, y * s, z * s }; }
};
static double dot(const D3 &a, const D3 &b) { return a.x * b.x + a.y * b.y + a.z * b.z; }
static D3 cross(const D3 &a, const D3 &b) { return { a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x }; }
static D3 unit(const D3 &a) { return a * (1 / sqrt(dot(a, a))); }
static double distance(const D3 &a, const D3 &b) { return sqrt(dot(a - b, a - b)); }
static D3 perpendicular(const D3 &a) { return unit(cross(a, fabs(a.z) > 0.9 ? D3{ 1, 0, 0 } : D3{ 0, 0, 1 })); }

struct Box
{
	double volume;
	D3 axis[3];
	double extent[3]; // In ascending order.
};

// The convex hull in double precision, with what the searches need to know about it.
struct Polyhedron
{
	struct Edge { int a, b, f0, f1; }; // Vertices and faces.
	std::vector<D3> v;
	std::vector<std::vector<int>> adjacent; // The neighbors of each vertex.
	std::vector<Edge> edges;
	std::vector<D3> normals;                // The unit normals of the faces.
	std::vector<D3> na, nb;                 // For each edge, the normals of its faces f0 and f1: the ends of its arc of normals.
	std::vector<int> opposite;              // For each edge, the vertex that is the farthest from it against the middle of its arc.
	double tie;                             // Distances that are closer than this count as equal.

	explicit Polyhedron(const Hull3 &hull)
	{
		double size = 0;
		for (const vec3 &p : hull.v)
		{
			v.push_back({ p.x, p.y, p.z });
			size = std::max(size, (double)std::max(fabsf(p.x), std::max(fabsf(p.y), fabsf(p.z))));
		}
		tie = 1e-9 * size;
		adjacent.resize(v.size());
		std::vector<std::pair<long long, int>> halfEdges; // (from << 32 | to, face)
		for (int f = 0; f < (int)hull.f.size(); ++f)
		{
			const std::vector<int> &face = hull.f[f];
			D3 n = { 0, 0, 0 };
			for (size_t i = 0; i < face.size(); ++i)
			{
				const int a = face[i], b = face[(i + 1) % face.size()];
				n = n + cross(v[a] - v[face[0]], v[b] - v[face[0]]);
				halfEdges.push_back({ (long long)a << 32 | b, f });
			}
			normals.push_back(unit(n));
		}
		if (hull.degenerate) return;
		std::sort(halfEdges.begin(), halfEdges.end());
		for (const std::pair<long long, int> &h : halfEdges)
		{
			const int a = (int)(h.first >> 32), b = (int)(h.first & 0xFFFFFFFF);
			adjacent[a].push_back(b);
			if (a < b) edges.push_back({ a, b, h.second, std::lower_bound(halfEdges.begin(), halfEdges.end(), std::make_pair((long long)b << 32 | a, 0))->second });
		}
		int start = 0;
		for (const Edge &e : edges)
		{
			na.push_back(normals[e.f0]);
			nb.push_back(normals[e.f1]);
			opposite.push_back(start = support((na.back() + nb.back()) * -1, start));
		}
	}

	// The vertex that is the farthest along d, found by climbing along the edges from `start`. On a convex
	// polyhedron the vertices that are above any given level are connected, so the climb cannot get stuck:
	// except on a plateau of vertices that tie within rounding, which is searched for a way further up.
	int support(const D3 &d, int start) const
	{
		double best = dot(d, v[start]);
		for (;;)
		{
			bool ties = true;
			for (bool moved = true; moved;)
			{
				moved = ties = false;
				for (int n : adjacent[start])
				{
					const double x = dot(d, v[n]);
					if (x > best) { best = x; start = n; moved = true; break; }
					ties = ties || x >= best - tie;
				}
			}
			if (!ties) return start;
			static thread_local std::vector<int> mark, plateau;
			static thread_local int stamp = 0;
			mark.resize(v.size(), 0);
			++stamp;
			plateau.assign(1, start);
			mark[start] = stamp;
			int higher = -1;
			while (!plateau.empty() && higher < 0)
			{
				const int i = plateau.back();
				plateau.pop_back();
				for (int n : adjacent[i])
				{
					if (mark[n] == stamp) continue;
					mark[n] = stamp;
					const double x = dot(d, v[n]);
					if (x > best) { higher = n; best = x; break; }
					if (x >= best - tie) plateau.push_back(n);
				}
			}
			if (higher < 0) return start;
			start = higher;
		}
	}

	// The extent of the hull along d. The vertices `lo` and `hi` are where to start looking for the extremes.
	double width(const D3 &d, int &lo, int &hi) const
	{
		hi = support(d, hi);
		lo = support(d * -1, lo);
		return dot(d, v[hi]) - dot(d, v[lo]);
	}

	// Measures the tightest box with the axes of `box`, by brute force.
	void measure(Box &box) const
	{
		for (int k = 0; k < 3; ++k)
		{
			double lo = INFINITY, hi = -INFINITY;
			for (const D3 &p : v)
			{
				lo = std::min(lo, dot(box.axis[k], p));
				hi = std::max(hi, dot(box.axis[k], p));
			}
			box.extent[k] = hi - lo;
		}
		box.volume = box.extent[0] * box.extent[1] * box.extent[2];
		std::sort(box.extent, box.extent + 3);
	}
};

// ---------------------------------------------------------------------------
// Ground truth: the search over all pairs of edges.
// ---------------------------------------------------------------------------

// Minimizes the volume over the boxes that have a face normal n1 in the normal arc of edge e1, and the normal
// n2 of an adjacent face in the normal arc of edge e2. Updates `best`. The two vertices of `hint3` are where to
// start looking for the extreme vertices along the third axis, and are updated. Counts the work in `stats`:
// pairs that have such boxes, intervals of them that were sampled, and local minima that were refined.
static void search_pair(const Polyhedron &p, int e1, int e2, Box &best, int *hint3, long long *stats)
{
	// n1(t) = f1b + d1 t and n2(u) = f2b + d2 u for t, u in [0, 1] cover the two arcs. They are perpendicular
	// when a + b t + c u + d t u = 0, i.e. u(t) = -(a + b t) / (c + d t).
	const D3 &f1a = p.na[e1], &f1b = p.nb[e1], &f2a = p.na[e2], &f2b = p.nb[e2];
	const D3 d1 = f1a - f1b, d2 = f2a - f2b;
	const double a = dot(f1b, f2b), b = dot(d1, f2b), c = dot(d2, f1b), d = dot(d1, d2);
	// The bilinear form has its extremes at the corners of the unit square: no sign change there, no solution.
	if (std::min(std::min(a, a + b), std::min(a + c, a + b + c + d)) > 1e-12) return;
	if (std::max(std::max(a, a + b), std::max(a + c, a + b + c + d)) < -1e-12) return;
	++stats[0];

	int hint[6] = { p.opposite[e1], p.edges[e1].a, p.opposite[e2], p.edges[e2].a, hint3[0], hint3[1] };
	D3 axis[3];  // The axes and the widths of the box that `volume` measured last.
	double w[3];
	auto u_of = [&](double t) { return -(a + b * t) / (c + d * t); };
	auto normals = [&](double t, D3 &n1, D3 &n2) -> bool
	{
		const double u = std::min(std::max(u_of(t), 0.0), 1.0);
		n1 = unit(f1b + d1 * t);
		n2 = f2b + d2 * u;
		n2 = n2 - n1 * dot(n1, n2); // Exactly perpendicular, also if u was clamped.
		const double length = sqrt(dot(n2, n2));
		n2 = n2 * (1 / length);
		return length > 1e-9;
	};
	auto volume = [&](double t) -> double
	{
		if (!normals(t, axis[0], axis[1])) return INFINITY;
		axis[2] = cross(axis[0], axis[1]);
		for (int k = 0; k < 3; ++k) w[k] = p.width(axis[k], hint[2 * k], hint[2 * k + 1]);
		const double vol = w[0] * w[1] * w[2];
		if (vol < best.volume)
		{
			best.volume = vol;
			for (int k = 0; k < 3; ++k) best.axis[k] = axis[k];
		}
		return vol;
	};
	// Returns whether no box of the interval [l, r] of t can be smaller than `best`, right after `volume` has
	// measured the box at some t of the interval and returned `vol`. From there to any other t of the interval,
	// n1 and n2 move along their arcs in one direction, i.e. by at most as far as to the ends of the interval,
	// and n3 = n1 x n2 by at most the sum of the two. Along a moved axis n', the hull is at least as wide as
	// the two extreme vertices of the measured axis n are apart along n'. With d the vector between those two
	// and w = n.d the measured width, that is n'.d >= w (1 - s^2 / 2) - s |d - w n| for |n' - n| <= s, because
	// n'.n = 1 - |n' - n|^2 / 2. (The 1e-8 covers a clamped u, with which n2 is not exactly on its arc.)
	auto hopeless = [&](double vol, double l, double r) -> bool
	{
		D3 l1, l2, r1, r2;
		if (!std::isfinite(vol) || !normals(l, l1, l2) || !normals(r, r1, r2)) return false;
		double s[3], bound = 1;
		s[0] = std::max(distance(l1, axis[0]), distance(r1, axis[0])) + 1e-8;
		s[1] = std::max(distance(l2, axis[1]), distance(r2, axis[1])) + 1e-8;
		s[2] = s[0] + s[1];
		for (int k = 0; k < 3; ++k)
		{
			const D3 d = p.v[hint[2 * k + 1]] - p.v[hint[2 * k]];
			bound *= std::max(w[k] * (1 - s[k] * s[k] / 2) - s[k] * sqrt(std::max(dot(d, d) - w[k] * w[k], 0.0)), 0.0);
		}
		return bound >= best.volume;
	};

	// u(t) is monotonic between its pole and the values of t where it crosses 0 and 1. So on each interval
	// between those, u(t) is either within [0, 1] throughout, or not at all.
	double cuts[5] = { 0, 1, -a / b, -(a + c) / (b + d), -c / d };
	int n = 2;
	for (int i = 2; i < 5; ++i)
		if (cuts[i] > 0 && cuts[i] < 1) cuts[n++] = cuts[i];
	std::sort(cuts, cuts + n);
	for (int i = 0; i < n; ++i)
	{
		const double ui = u_of(cuts[i]);
		if (ui > -1e-9 && ui < 1 + 1e-9) volume(cuts[i]);
		if (i + 1 == n) break;
		const double l = cuts[i], r = cuts[i + 1], um = u_of((l + r) / 2);
		if (!(um >= -1e-9 && um <= 1 + 1e-9) || !(r > l)) continue; // (With slack: u(t) is often constant 0 or 1.)

		// Sample the interval, and refine each local minimum of the samples by golden section search. But first
		// see if the sample in the middle already rules out the whole interval: on a large hull the arcs are
		// short, and that is all there is to do for most of the pairs.
		const int K = 16;
		double f[K + 1];
		f[K / 2] = volume(l + (r - l) * (K / 2) / K);
		if (hopeless(f[K / 2], l, r)) continue;
		++stats[1];
		for (int k = 0; k <= K; ++k)
			if (k != K / 2) f[k] = volume(l + (r - l) * k / K);
		for (int k = 0; k <= K; ++k)
		{
			if ((k > 0 && f[k - 1] < f[k]) || (k < K && f[k + 1] < f[k])) continue;
			const double g = 0.6180339887498949;
			double x0 = l + (r - l) * std::max(k - 1, 0) / K, x3 = l + (r - l) * std::min(k + 1, K) / K;
			if (hopeless(volume(l + (r - l) * k / K), x0, x3)) continue;
			++stats[2];
			double x1 = x3 - g * (x3 - x0), x2 = x0 + g * (x3 - x0), y1 = volume(x1), y2 = volume(x2);
			while (x3 - x0 > 1e-11)
			{
				if (y1 <= y2) { x3 = x2; x2 = x1; y2 = y1; x1 = x3 - g * (x3 - x0); y1 = volume(x1); }
				else { x0 = x1; x1 = x2; y1 = y2; x2 = x0 + g * (x3 - x0); y2 = volume(x2); }
			}
			volume(x0);
			volume(x3);
		}
	}
	hint3[0] = hint[4];
	hint3[1] = hint[5];
}

// The search over all pairs of edges, on the given number of threads.
static Box ground_truth(const Polyhedron &p, int threads, long long *stats)
{
	const int E = (int)p.edges.size();
	struct Worker
	{
		Box best = { INFINITY, {}, {} };
		bool found = false; // Whether `best` is a box of this thread, and not just the volume of the box of another one.
		long long stats[3] = { 0, 0, 0 };
		std::thread thread;
	};
	std::vector<Worker> workers(std::max(threads, 1));
	std::atomic<int> next(0);
	std::atomic<double> smallest(INFINITY); // The smallest volume that any of the threads has found.
	auto work = [&](Worker &me)
	{
		std::vector<std::pair<double, int>> row;
		int hint3[2][2] = { { 0, 0 }, { 0, 0 } };
		for (int i; (i = next++) < E;)
		{
			// A box that another thread has found is as good a reason to skip a family as one of our own.
			double known = smallest;
			if (known < me.best.volume) { me.best.volume = known; me.found = false; }
			known = me.best.volume;

			// The edges whose arcs have a normal that is perpendicular to a normal of the arc of edge i, sorted
			// by the angle around that arc. The third axis of the boxes then turns steadily from one pair to
			// the next, and its extreme vertices are found near the previous ones.
			const D3 f1a = p.na[i], f1b = p.nb[i], m = unit(f1a + f1b), x = perpendicular(m), y = cross(m, x);
			row.clear();
			for (int j = i; j < E; ++j)
			{
				// (The same test as at the start of search_pair(), on the same four numbers, but with more slack.)
				const double c0 = dot(f1a, p.na[j]), c1 = dot(f1a, p.nb[j]), c2 = dot(f1b, p.na[j]), c3 = dot(f1b, p.nb[j]);
				if (std::min(std::min(c0, c1), std::min(c2, c3)) > 2e-12) continue;
				if (std::max(std::max(c0, c1), std::max(c2, c3)) < -2e-12) continue;
				const D3 m2 = p.na[j] + p.nb[j];
				row.push_back({ atan2(dot(m2, y), dot(m2, x)), j });
			}
			std::sort(row.begin(), row.end());
			// The family of a pair of edges is parameterized over the arc of the first edge. That misses the
			// boxes that have an axis parallel to the second edge (then all of the second arc is perpendicular
			// to a single normal of the first one), so try each pair both ways around.
			for (const std::pair<double, int> &j : row)
			{
				search_pair(p, i, j.second, me.best, hint3[0], me.stats);
				if (j.second != i) search_pair(p, j.second, i, me.best, hint3[1], me.stats);
			}
			if (me.best.volume < known)
			{
				me.found = true;
				while (me.best.volume < known && !smallest.compare_exchange_weak(known, me.best.volume)) {}
			}
		}
	};
	for (Worker &w : workers) w.thread = std::thread(work, std::ref(w));
	Box best = { INFINITY, {}, {} };
	for (Worker &w : workers)
	{
		w.thread.join();
		if (w.found && w.best.volume < best.volume) best = w.best;
		for (int k = 0; k < 3; ++k) stats[k] += w.stats[k];
	}
	return best;
}

// ---------------------------------------------------------------------------
// The cross-check: one axis over the hemisphere, minimum area rectangle for the rest.
// ---------------------------------------------------------------------------

struct P2 { double x, y; };

// Returns the area of the minimum area rectangle around the points, and the direction of one of its sides.
static double min_area_rectangle(std::vector<P2> &q, P2 &side)
{
	// Convex hull (monotone chain). A minimum area rectangle has a side along one of its edges: try them all.
	std::sort(q.begin(), q.end(), [](const P2 &a, const P2 &b) { return a.x < b.x || (a.x == b.x && a.y < b.y); });
	std::vector<P2> h;
	auto turn = [](const P2 &o, const P2 &a, const P2 &b) { return (a.x - o.x) * (b.y - o.y) - (a.y - o.y) * (b.x - o.x); };
	for (int pass = 0; pass < 2; ++pass, std::reverse(q.begin(), q.end()))
	{
		const size_t keep = pass ? h.size() : 1;
		for (const P2 &p : q)
		{
			while (h.size() > keep && turn(h[h.size() - 2], h.back(), p) <= 0) h.pop_back();
			h.push_back(p);
		}
	}
	h.pop_back();
	double best = h.size() < 3 ? 0 : INFINITY;
	for (size_t i = 0; i < h.size() && h.size() > 1; ++i)
	{
		double ex = h[(i + 1) % h.size()].x - h[i].x, ey = h[(i + 1) % h.size()].y - h[i].y;
		const double length = sqrt(ex * ex + ey * ey);
		ex /= length; ey /= length;
		double ulo = INFINITY, uhi = -INFINITY, wlo = INFINITY, whi = -INFINITY;
		for (const P2 &p : h)
		{
			const double u = p.x * ex + p.y * ey, w = p.y * ex - p.x * ey;
			ulo = std::min(ulo, u); uhi = std::max(uhi, u);
			wlo = std::min(wlo, w); whi = std::max(whi, w);
		}
		if ((uhi - ulo) * (whi - wlo) <= best)
		{
			best = (uhi - ulo) * (whi - wlo);
			side = { ex, ey };
		}
	}
	return best;
}

// Returns the volume of the smallest box that has n as one of its axes. Its axes go to `axis`, if given.
static double best_box_along(const Polyhedron &p, const D3 &n, D3 *axis = nullptr)
{
	const D3 u = perpendicular(n), w = cross(n, u);
	double lo = INFINITY, hi = -INFINITY;
	std::vector<P2> q(p.v.size());
	for (size_t i = 0; i < p.v.size(); ++i)
	{
		lo = std::min(lo, dot(n, p.v[i]));
		hi = std::max(hi, dot(n, p.v[i]));
		q[i] = { dot(u, p.v[i]), dot(w, p.v[i]) };
	}
	P2 side = { 1, 0 };
	const double area = min_area_rectangle(q, side);
	if (axis)
	{
		axis[0] = n;
		axis[1] = u * side.x + w * side.y;
		axis[2] = cross(axis[0], axis[1]);
	}
	return (hi - lo) * area;
}

static Box sweep(const Polyhedron &p)
{
	// Sample the hemisphere of directions with a step of one degree.
	const int N = 180;
	const double PI = 3.14159265358979323846;
	auto direction = [&](int i, int j) { return D3{ sin(PI * i / N) * cos(PI * j / N), sin(PI * i / N) * sin(PI * j / N), cos(PI * i / N) }; };
	std::vector<std::vector<double>> grid(N / 2 + 1, std::vector<double>(2 * N));
	for (int i = 0; i <= N / 2; ++i)
		for (int j = 0; j < 2 * N; ++j) grid[i][j] = best_box_along(p, direction(i, j));

	// Refine the best local minima of the grid, by a randomized pattern search with a shrinking step.
	std::vector<std::pair<double, D3>> minima;
	for (int i = 0; i <= N / 2; ++i)
		for (int j = 0; j < 2 * N; ++j)
		{
			bool minimum = true;
			for (int di = -1; di <= 1; ++di)
				for (int dj = -1; dj <= 1; ++dj)
					if (i + di >= 0 && i + di <= N / 2 && grid[i + di][(j + dj + 2 * N) % (2 * N)] < grid[i][j]) minimum = false;
			if (minimum) minima.push_back({ grid[i][j], direction(i, j) });
		}
	std::sort(minima.begin(), minima.end(), [](const std::pair<double, D3> &a, const std::pair<double, D3> &b) { return a.first < b.first; });
	if (minima.size() > 60) minima.resize(60);
	Box best = { INFINITY, {}, {} };
	unsigned random = 12345;
	for (std::pair<double, D3> m : minima)
	{
		for (double step = PI / N; step > 1e-11;)
		{
			const D3 t1 = perpendicular(m.second), t2 = cross(m.second, t1);
			bool improved = false;
			for (int k = 0; k < 12; ++k)
			{
				random = random * 1664525u + 1013904223u;
				const double angle = 2 * PI * (random >> 8) / 16777216.0;
				const D3 n = unit(m.second + t1 * (cos(angle) * step) + t2 * (sin(angle) * step));
				const double volume = best_box_along(p, n);
				if (volume < m.first) { m.first = volume; m.second = n; improved = true; }
			}
			if (!improved) step *= 0.5;
		}
		if (m.first < best.volume) best.volume = best_box_along(p, m.second, best.axis);
	}
	return best;
}

// ---------------------------------------------------------------------------

static double seconds()
{
	return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

static void print(const char *name, const Box &b)
{
	printf("\"%s\": {\"volume\": %.17g, \"extents\": [%.17g, %.17g, %.17g], \"axes\": [[%.9g, %.9g, %.9g], [%.9g, %.9g, %.9g], [%.9g, %.9g, %.9g]]},\n",
		name, b.volume, b.extent[0], b.extent[1], b.extent[2], b.axis[0].x, b.axis[0].y, b.axis[0].z,
		b.axis[1].x, b.axis[1].y, b.axis[1].z, b.axis[2].x, b.axis[2].y, b.axis[2].z);
}

int main(int argc, char **argv)
{
	const std::string path = argc > 1 ? argv[1] : "";
	const bool groundTruth = argc > 2 && !strcmp(argv[2], "--ground-truth");
	const int threads = argc > 3 ? atoi(argv[3]) : 1;
	std::vector<float> pts;
	std::string error;
	if (path.size() > 4 && path.substr(path.size() - 4) == ".txt")
	{
		FILE *f = fopen(path.c_str(), "rb");
		float x, y, z;
		while (f && fscanf(f, "%f %f %f", &x, &y, &z) == 3) pts.insert(pts.end(), { x, y, z });
		if (f) fclose(f);
	}
	else glb_read_positions(path.c_str(), pts, error);
	const int n = (int)pts.size() / 3;
	if (!n)
	{
		printf("{\"error\": \"%s\"}\n", error.empty() ? "no input points" : error.c_str());
		return 1;
	}

	const double t0 = seconds();
	const Hull3 hull = convex_hull(pts.data(), n, 12);
	const double t1 = seconds();
	const Polyhedron p(hull);
	printf("{\n\"points\": %d,\n\"hull\": {\"vertices\": %d, \"faces\": %d, \"edges\": %d, \"degenerate\": %s},\n", n, (int)hull.v.size(),
		(int)hull.f.size(), (int)p.edges.size(), hull.degenerate ? "true" : "false");

	double timeMinobb = 0, timeGroundTruth = 0, timeSweep = 0;
	if (!groundTruth)
	{
		const double t2 = seconds();
		const OBB obb = argc > 3 && !strcmp(argv[2], "--tolerance") ? minobb(hull, (float)atof(argv[3])) : minobb(hull);
		timeMinobb = seconds() - t2;

		// Examine the box of minobb().
		D3 axis[3];
		for (int i = 0; i < 3; ++i) axis[i] = { obb.axis[i].x, obb.axis[i].y, obb.axis[i].z };
		double orthonormality = 0, outside = 0;
		for (int i = 0; i < 3; ++i)
			for (int j = i; j < 3; ++j) orthonormality = std::max(orthonormality, fabs(dot(axis[i], axis[j]) - (i == j)));
		for (int i = 0; i < n; ++i)
		{
			const D3 q = D3{ pts[3 * i], pts[3 * i + 1], pts[3 * i + 2] } - D3{ obb.pos.x, obb.pos.y, obb.pos.z };
			for (int k = 0; k < 3 && std::isfinite(q.x + q.y + q.z); ++k) outside = std::max(outside, fabs(dot(q, axis[k])) - obb.r[k]);
		}
		Box mine = { 0, {}, {} };
		mine.axis[0] = unit(axis[0]);
		mine.axis[1] = unit(axis[1] - mine.axis[0] * dot(mine.axis[0], axis[1]));
		mine.axis[2] = cross(mine.axis[0], mine.axis[1]);
		const bool valid = !obb.IsDegenerate() && std::isfinite(mine.axis[0].x + mine.axis[1].x + mine.axis[2].x);
		if (valid)
		{
			p.measure(mine);
			printf("\"reported_volume\": %.9g,\n\"orthonormality_error\": %.3g,\n\"outside\": %.3g,\n\"diagonal\": %.9g,\n", obb.Volume(),
				orthonormality, outside, 2 * sqrt((double)obb.r.x * obb.r.x + (double)obb.r.y * obb.r.y + (double)obb.r.z * obb.r.z));
			print("minobb", mine);
		}
		printf("\"valid\": %s,\n", valid ? "true" : "false");
	}
	else
	{
		D3 thin = { 0, 0, 1 }; // For a flat hull, the normal of its plane.
		if (!hull.degenerate)
		{
			long long stats[3] = { 0, 0, 0 };
			const double t2 = seconds();
			Box gt = ground_truth(p, threads, stats);
			p.measure(gt);
			timeGroundTruth = seconds() - t2;
			print("gt", gt);
			printf("\"pairs\": {\"searched\": %lld, \"sampled\": %lld, \"refined\": %lld},\n", stats[0], stats[1], stats[2]);
			if (p.v.size() <= 400)
			{
				Box sw = sweep(p);
				p.measure(sw);
				timeSweep = seconds() - t2 - timeGroundTruth;
				print("sweep", sw);
			}
			int hint[2] = { 0, 0 };
			double thinnest = INFINITY;
			for (int k = 0; k < 3; ++k)
				if (p.width(gt.axis[k], hint[0], hint[1]) < thinnest)
				{
					thinnest = p.width(gt.axis[k], hint[0], hint[1]);
					thin = gt.axis[k];
				}
		}
		else if (!p.normals.empty()) thin = p.normals[0];
		else if (p.v.size() == 2) thin = perpendicular(unit(p.v[1] - p.v[0]));
		Box flat = { 0, {}, {} };
		best_box_along(p, thin, flat.axis);
		p.measure(flat);
		print("flat", flat);
	}
	printf("\"seconds\": {\"hull\": %.6f, \"minobb\": %.6f, \"ground_truth\": %.6f, \"sweep\": %.6f}\n}\n", t1 - t0, timeMinobb, timeGroundTruth, timeSweep);
	return 0;
}
