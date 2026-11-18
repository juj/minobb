// test/test_minsphere.cpp
//
// Usage: test_minsphere <file.glb | file.gltf | @name>
//        test_minsphere --list
//
// Computes the minimum enclosing sphere of the vertex positions of a glTF
// file, or of the built-in synthetic point set @name (--list prints their
// names), both from the points and from their convex hull, verifies the two
// spheres, and prints the verdict as a JSON document to stdout.
//
// A sphere passes iff
//   - it contains every (finite) input point: |p - pos| <= r, checked in
//     double precision with a margin that is larger than the rounding errors
//     of the check itself, so that it holds exactly,
//   - no smaller sphere contains the points: a lower bound for the radius of
//     any sphere around the support points of the sphere (see LowerBound())
//     is as large as the radius, up to the rounding of the center and of the
//     radius to floats,
//   - its support points are input points that lie on it, up to the same
//     rounding.
// The second check is a proof and not a comparison with another algorithm:
// the bound holds for every sphere that contains the support points.
//
// Exit status: 0 = the spheres are correct, 1 = they are not.

#include "minsphere.h"
#include "glb.h"

#include <algorithm>
#include <cfloat>
#include <chrono>
#include <cmath>
#include <cstdarg>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>

typedef std::vector<vec3> Points;

static double Now()
{
	return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

// Returns the time that one call of f() takes, in seconds: the fastest of the runs that fit in a few
// milliseconds (one run, if that takes longer), with calls that are too fast for the timer timed in batches.
template<typename F>
static double TimeCall(F f)
{
	double best = INFINITY, total = 0;
	int batch = 1;
	for (int run = 0; run < 64 && total < 0.005; ++run)
	{
		const double t0 = Now();
		for (int i = 0; i < batch; ++i)
			f();
		const double t = Now() - t0;
		total += t;
		if (t < 1e-4 && batch < (1 << 20))
			batch *= 4;
		else
			best = std::min(best, t / batch);
	}
	return best;
}

static std::string error;

static void Fail(const char *fmt, ...)
{
	if (!error.empty())
		return; // The first error is the one reported.
	char text[512];
	va_list args;
	va_start(args, fmt);
	vsnprintf(text, sizeof text, fmt, args);
	va_end(args);
	error = text;
}

static bool IsFinite(const vec3 &p)
{
	return std::fabs(p.x) <= FLT_MAX && std::fabs(p.y) <= FLT_MAX && std::fabs(p.z) <= FLT_MAX;
}

// ---------------------------------------------------------------------------
// Verification.
// ---------------------------------------------------------------------------

struct D3 { double x, y, z; };
static D3 operator-(const D3 &a, const D3 &b) { return { a.x - b.x, a.y - b.y, a.z - b.z }; }
static double Dot(const D3 &a, const D3 &b) { return a.x * b.x + a.y * b.y + a.z * b.z; }
static D3 ToD3(const vec3 &p) { return { p.x, p.y, p.z }; }

// A lower bound for the radius of any sphere that contains the k points p[0..k) (k <= 4).
//
// For weights w >= 0 that sum to 1, with m the weighted average of the points, every point x has
//    max |x - p_i|^2  >=  sum w_i |x - p_i|^2  =  |x - m|^2 + sum w_i |p_i - m|^2  >=  sum w_i |p_i - m|^2.
// So the square root of the last sum is a bound, whatever the weights are. It is the largest when the
// weights are those of the center of the smallest sphere around the points, which passes through some of
// them: the weights of the sphere through each subset of the points are tried, if they are not negative.
static double LowerBound(const D3 *p, int k)
{
	double best = 0;
	for (int subset = 1; subset < (1 << k); ++subset)
	{
		// The points of the subset, relative to the first one.
		D3 e[4];
		int index[4], m = 0;
		for (int i = 0; i < k; ++i)
			if (subset & (1 << i))
				index[m++] = i;
		for (int i = 1; i < m; ++i)
			e[i - 1] = p[index[i]] - p[index[0]];

		// The center c = sum s_i e_i of the sphere through the origin and the points e is equally far from
		// each: e_i . c = |e_i|^2 / 2. That is the linear system G s = diag(G) / 2 with G_ij = e_i . e_j,
		// solved here by Gaussian elimination with pivoting.
		const int d = m - 1;
		double G[3][4];
		for (int i = 0; i < d; ++i)
		{
			for (int j = 0; j < d; ++j)
				G[i][j] = Dot(e[i], e[j]);
			G[i][d] = 0.5 * G[i][i];
		}
		bool singular = false;
		for (int col = 0; col < d && !singular; ++col)
		{
			int pivot = col;
			for (int row = col + 1; row < d; ++row)
				if (std::fabs(G[row][col]) > std::fabs(G[pivot][col]))
					pivot = row;
			if (G[pivot][col] == 0)
			{
				singular = true;
				break;
			}
			for (int j = 0; j <= d; ++j)
				std::swap(G[col][j], G[pivot][j]);
			for (int row = 0; row < d; ++row)
				if (row != col)
				{
					const double f = G[row][col] / G[col][col];
					for (int j = col; j <= d; ++j)
						G[row][j] -= f * G[col][j];
				}
		}
		if (singular)
			continue;

		double w[4], sum = 0;
		w[0] = 1;
		for (int i = 0; i < d; ++i)
		{
			w[i + 1] = G[i][d] / G[i][i];
			w[0] -= w[i + 1];
		}
		bool valid = true;
		for (int i = 0; i < m; ++i)
		{
			if (!(w[i] >= 0))
				valid = false;
			sum += w[i];
		}
		if (!valid || !(sum > 0))
			continue;

		// The bound of these weights, with the points measured from the first one for accuracy.
		D3 mean = { 0, 0, 0 };
		for (int i = 1; i < m; ++i)
		{
			mean.x += w[i] / sum * e[i - 1].x;
			mean.y += w[i] / sum * e[i - 1].y;
			mean.z += w[i] / sum * e[i - 1].z;
		}
		double bound = w[0] / sum * Dot(mean, mean);
		for (int i = 1; i < m; ++i)
			bound += w[i] / sum * Dot(e[i - 1] - mean, e[i - 1] - mean);
		best = std::max(best, bound);
	}
	return std::sqrt(best);
}

static double Ulp(float x)
{
	x = std::fabs(x);
	return (double)std::nextafter(x, FLT_MAX) - (double)x;
}

struct Verdict
{
	double excess = 0;  // How much larger the radius is than the lower bound, relative to the radius.
	double allowed = 0; // How much it may be.
};

// Verifies the sphere `s` of the points `pts`, whose support points are indices to `source`.
static Verdict Verify(const char *what, const Sphere &s, const Points &pts, const Points &source, int numFinite)
{
	Verdict verdict;
	if (numFinite == 0)
	{
		if (!s.IsDegenerate() || s.numSupport != 0)
			Fail("%s: no points, but the sphere is not marked degenerate", what);
		return verdict;
	}
	if (s.IsDegenerate() || !IsFinite(s.pos) || !(s.r <= FLT_MAX))
	{
		Fail("%s: the sphere is not valid (r = %g)", what, s.r);
		return verdict;
	}

	// Containment. The squared distance below has a rounding error of at most a few DBL_EPSILON of itself:
	// with the margin, a pass means that the point is inside in exact arithmetic.
	const D3 c = ToD3(s.pos);
	const double r2 = (double)s.r * (double)s.r;
	double worst = 0;
	for (const vec3 &p : pts)
	{
		if (!IsFinite(p))
			continue;
		const D3 d = ToD3(p) - c;
		worst = std::max(worst, Dot(d, d));
	}
	if (!(worst * (1 + 8 * DBL_EPSILON) <= r2))
		Fail("%s: a point is outside the sphere: at the distance %.17g, r = %.17g", what, std::sqrt(worst), (double)s.r);

	// The support points.
	if (s.numSupport < 1 || s.numSupport > 4)
	{
		Fail("%s: %d support points", what, s.numSupport);
		return verdict;
	}
	D3 support[4];
	for (int i = 0; i < s.numSupport; ++i)
	{
		if (s.support[i] < 0 || s.support[i] >= (int)source.size() || !IsFinite(source[s.support[i]]))
		{
			Fail("%s: support point %d has the index %d", what, i, s.support[i]);
			return verdict;
		}
		for (int j = 0; j < i; ++j)
			if (s.support[j] == s.support[i])
				Fail("%s: a point is twice in the support set", what);
		support[i] = ToD3(source[s.support[i]]);
	}

	// What the rounding of the center to floats can add to the radius (half a unit in the last place of
	// each coordinate), and the rounding of the radius itself (it is rounded up, and padded by less than a unit).
	const double centerError = 0.5 * std::sqrt(Ulp(s.pos.x) * Ulp(s.pos.x) + Ulp(s.pos.y) * Ulp(s.pos.y) + Ulp(s.pos.z) * Ulp(s.pos.z));
	const double slack = centerError + 3 * Ulp(s.r) + 1e-12 * s.r;

	// Optimality: no sphere around the support points is smaller than the bound.
	const double bound = LowerBound(support, s.numSupport);
	verdict.excess = s.r > 0 ? ((double)s.r - bound) / s.r : 0;
	verdict.allowed = s.r > 0 ? slack / s.r : 0;
	if (!((double)s.r <= bound + slack))
		Fail("%s: the sphere is not the smallest: r = %.9g, but the support points allow %.9g (the rounding accounts for %.3g)",
			what, (double)s.r, bound, slack);

	// The support points are on the sphere.
	for (int i = 0; i < s.numSupport; ++i)
	{
		const double distance = std::sqrt(Dot(support[i] - c, support[i] - c));
		if (!(distance >= (double)s.r - 2 * slack) && s.numSupport > 1)
			Fail("%s: support point %d is not on the sphere: at the distance %.9g, r = %.9g", what, i, distance, (double)s.r);
	}
	return verdict;
}

// ---------------------------------------------------------------------------
// Synthetic point sets.
// ---------------------------------------------------------------------------

static uint32_t seed = 12345;
static double Random() // In [0, 1).
{
	seed = seed * 1664525u + 1013904223u;
	return (seed >> 8) / 16777216.0;
}
static double Random(double a, double b) { return a + (b - a) * Random(); }

static vec3 RandomInBall()
{
	for (;;)
	{
		const double x = Random(-1, 1), y = Random(-1, 1), z = Random(-1, 1);
		if (x * x + y * y + z * z <= 1)
			return vec3((float)x, (float)y, (float)z);
	}
}

static vec3 RandomOnSphere()
{
	for (;;)
	{
		const double x = Random(-1, 1), y = Random(-1, 1), z = Random(-1, 1), l = std::sqrt(x * x + y * y + z * z);
		if (l > 0.1 && l <= 1)
			return vec3((float)(x / l), (float)(y / l), (float)(z / l));
	}
}

static Points Transformed(Points pts, float scale, const vec3 &offset = vec3())
{
	for (vec3 &p : pts)
		p = p * scale + offset;
	return pts;
}

static Points Ball(int n) { Points p; for (int i = 0; i < n; ++i) p.push_back(RandomInBall()); return p; }
static Points OnSphere(int n) { Points p; for (int i = 0; i < n; ++i) p.push_back(RandomOnSphere()); return p; }

static Points Empty() { return Points(); }
static Points One() { return Points(1, vec3(1.5f, -2.25f, 3.f)); }
static Points Two() { return { vec3(1, 2, 3), vec3(-4, 0.5f, 7) }; }
static Points Same() { return Points(100, vec3(0.1f, 0.2f, 0.3f)); }
static Points Collinear() { Points p; for (int i = 0; i < 200; ++i) { const float t = (float)Random(-3, 5); p.push_back(vec3(t, 2 * t, -t)); } return p; }
static Points Square() { return { vec3(0, 0, 0), vec3(1, 0, 0), vec3(1, 1, 0), vec3(0, 1, 0) }; }
static Points RightTriangle() { return { vec3(0, 0, 0), vec3(3, 0, 0), vec3(0, 4, 0) }; }
static Points ObtuseTriangle() { return { vec3(0, 0, 0), vec3(10, 0, 0), vec3(4, 1, 0) }; }
static Points AcuteTriangle() { return { vec3(0, 0, 1), vec3(10, 0, 0), vec3(4, 9, 2) }; }
static Points Tetrahedron() { return { vec3(1, 1, 1), vec3(1, -1, -1), vec3(-1, 1, -1), vec3(-1, -1, 1) }; }
static Points FlatTetrahedron() { return { vec3(0, 0, 0), vec3(1, 0, 0), vec3(0, 1, 0), vec3(0.3f, 0.3f, 1e-6f) }; }
static Points Cube() { Points p; for (int i = 0; i < 8; ++i) p.push_back(vec3((float)(i & 1), (float)(i >> 1 & 1), (float)(i >> 2 & 1))); return p; }
static Points Grid() { Points p; for (int x = 0; x < 20; ++x) for (int y = 0; y < 20; ++y) for (int z = 0; z < 20; ++z) p.push_back(vec3((float)x, (float)y * 0.5f, (float)z * 3)); return p; }
static Points Circle()
{
	// Points of a circle in a tilted plane: all of them are (nearly) on the smallest sphere.
	Points p;
	for (int i = 0; i < 2000; ++i)
	{
		const double a = Random(0, 6.283185307179586), x = std::cos(a), y = std::sin(a);
		p.push_back(vec3((float)(x + 0.5 * y), (float)(y - 0.25 * x), (float)(0.3 * x + 0.7 * y)));
	}
	return p;
}
static Points IntegerSphere()
{
	// The integer points of a sphere around the origin: exactly on one sphere, all of them.
	Points p;
	for (int x = -40; x <= 40; ++x)
		for (int y = -40; y <= 40; ++y)
			for (int z = -40; z <= 40; ++z)
				if (x * x + y * y + z * z == 1386)
					p.push_back(vec3((float)x, (float)y, (float)z));
	return p;
}
static Points Hemisphere() { Points p = OnSphere(20000); for (vec3 &q : p) q.z = std::fabs(q.z); return p; }
static Points Cap() { Points p; while (p.size() < 20000) { const vec3 q = RandomOnSphere(); if (q.z > 0.9f) p.push_back(q); } return p; }
static Points Needle() { Points p; for (int i = 0; i < 5000; ++i) { const float t = (float)Random(-1, 1); p.push_back(vec3(t + (float)Random(-1e-6, 1e-6), 2 * t + (float)Random(-1e-6, 1e-6), -t)); } return p; }
static Points Disc() { Points p = Ball(5000); for (vec3 &q : p) q.z *= 1e-7f; return p; }
static Points TwoClusters() { Points p = Transformed(Ball(5000), 0.01f, vec3(-5, 1, 2)), q = Transformed(Ball(5000), 0.02f, vec3(6, -3, 0)); p.insert(p.end(), q.begin(), q.end()); return p; }
static Points WithNonFinite()
{
	Points p = Ball(5000);
	for (int i = 0; i < 50; ++i)
		p[(size_t)(Random() * p.size())][i % 3] = i % 4 == 0 ? NAN : i % 4 == 1 ? INFINITY : i % 4 == 2 ? -INFINITY : FLT_MAX;
	p[0] = vec3(NAN, NAN, NAN);
	p.back() = vec3(INFINITY, 0, 0);
	return p;
}
static Points NothingFinite() { return { vec3(NAN, 0, 0), vec3(0, INFINITY, 0), vec3(1, 2, -INFINITY) }; }
static Points Sorted() { Points p = Ball(50000); std::sort(p.begin(), p.end(), [](const vec3 &a, const vec3 &b) { return a.x < b.x; }); return p; }
static Points Spiral()
{
	// Points that spiral outwards: every one is outside the sphere of the ones before it.
	Points p;
	for (int i = 0; i < 20000; ++i)
	{
		const double a = i * 0.01, r = 1 + i * 1e-4;
		p.push_back(vec3((float)(r * std::cos(a)), (float)(r * std::sin(a)), (float)(0.1 * std::sin(a * 0.37))));
	}
	return p;
}

static const struct Synthetic { const char *name; Points (*make)(); } synthetic[] = {
	{ "empty", Empty }, { "one", One }, { "two", Two }, { "same", Same }, { "collinear", Collinear },
	{ "square", Square }, { "right_triangle", RightTriangle }, { "obtuse_triangle", ObtuseTriangle },
	{ "acute_triangle", AcuteTriangle }, { "tetrahedron", Tetrahedron }, { "flat_tetrahedron", FlatTetrahedron },
	{ "cube", Cube }, { "grid", Grid }, { "circle", Circle }, { "integer_sphere", IntegerSphere },
	{ "ball", [] { return Ball(100000); } }, { "sphere", [] { return OnSphere(100000); } },
	{ "hemisphere", Hemisphere }, { "cap", Cap }, { "needle", Needle }, { "disc", Disc },
	{ "two_clusters", TwoClusters }, { "sorted", Sorted }, { "spiral", Spiral },
	{ "sphere_far", [] { return Transformed(OnSphere(50000), 1.f, vec3(1e5f, -2e5f, 3e5f)); } },
	{ "ball_far", [] { return Transformed(Ball(50000), 1.f, vec3(-4096, 1e6f, 65536)); } },
	{ "ball_tiny", [] { return Transformed(Ball(20000), 1e-30f); } },
	{ "ball_denormal", [] { return Transformed(Ball(20000), 1e-41f); } },
	{ "ball_huge", [] { return Transformed(Ball(20000), 1e30f); } },
	{ "sphere_huge", [] { return Transformed(OnSphere(20000), 3e38f); } },
	{ "cube_huge", [] { return Transformed(Cube(), 3e38f, vec3(-1e38f, -1e38f, -1e38f)); } },
	{ "non_finite", WithNonFinite }, { "nothing_finite", NothingFinite },
	{ "ball_small", [] { return Ball(5); } }, { "ball_ten", [] { return Ball(10); } }, { "sphere_five", [] { return OnSphere(5); } },
};

// ---------------------------------------------------------------------------

int main(int argc, char **argv)
{
	const std::string name = argc > 1 ? argv[1] : "";
	if (name == "--list")
	{
		for (const Synthetic &s : synthetic) printf("@%s\n", s.name);
		return 0;
	}
	if (name.empty())
	{
		fprintf(stderr, "usage: %s <file.glb | file.gltf | @name>\n       %s --list\n", argv[0], argv[0]);
		return 2;
	}

	Points pts;
	const double t0 = Now();
	if (name[0] == '@')
	{
		bool found = false;
		for (const Synthetic &s : synthetic)
			if (name.substr(1) == s.name)
			{
				pts = s.make();
				found = true;
			}
		if (!found)
			Fail("no such synthetic point set");
	}
	else
	{
		std::vector<float> flat;
		std::string readError;
		if (!glb_read_positions(name.c_str(), flat, readError))
			Fail("%s", readError.c_str());
		pts.resize(flat.size() / 3);
		if (!flat.empty())
			memcpy((void *)pts.data(), flat.data(), pts.size() * sizeof(vec3));
	}
	const double loadTime = Now() - t0;

	int numFinite = 0;
	for (const vec3 &p : pts)
		numFinite += IsFinite(p);

	Sphere fromPoints, fromHull;
	Hull3 hull;
	Verdict verdictPoints, verdictHull;
	double pointsTime = 0, hullTime = 0, hullSphereTime = 0;
	if (error.empty())
	{
		const float *data = pts.empty() ? nullptr : &pts[0].x;
		pointsTime = TimeCall([&] { fromPoints = minsphere(data, (int)pts.size(), sizeof(vec3)); });
		hullTime = TimeCall([&] { hull = convex_hull(data, (int)pts.size(), sizeof(vec3)); });
		hullSphereTime = TimeCall([&] { fromHull = minsphere(hull); });

		verdictPoints = Verify("from the points", fromPoints, pts, pts, numFinite);
		verdictHull = Verify("from the hull", fromHull, pts, hull.v, numFinite);

		// The sphere of a point set is the same in a struct with a stride, and unaligned.
		if (!pts.empty() && pts.size() <= 200000)
		{
			std::vector<char> strided(pts.size() * 20 + 1);
			for (size_t i = 0; i < pts.size(); ++i)
				memcpy(&strided[1 + i * 20], &pts[i], sizeof(vec3));
			const Sphere s = minsphere((const float *)&strided[1], (int)pts.size(), 20);
			if (!(s.pos == fromPoints.pos) || s.r != fromPoints.r)
				Fail("the sphere of the same points with a stride of 20 bytes is different");
		}
	}

	printf("{\n\"points\": %d,\n\"finite_points\": %d,\n\"hull_vertices\": %d,\n\"ok\": %s,\n\"error\": \"",
		(int)pts.size(), numFinite, (int)hull.v.size(), error.empty() ? "true" : "false");
	for (char c : error) printf(c == '"' || c == '\\' ? "\\%c" : "%c", (unsigned char)c < 32 ? ' ' : c);
	printf("\",\n\"seconds\": {\"load\": %.6f, \"sphere\": %.9f, \"hull\": %.9f, \"sphere_of_hull\": %.9f},\n",
		loadTime, pointsTime, hullTime, hullSphereTime);
	const Sphere *spheres[2] = { &fromPoints, &fromHull };
	const Verdict *verdicts[2] = { &verdictPoints, &verdictHull };
	const char *names[2] = { "sphere", "sphere_of_hull" };
	for (int i = 0; i < 2; ++i)
	{
		const Sphere &s = *spheres[i];
		// (A sphere that is not valid has no numbers that JSON could carry.)
		const bool valid = !s.IsDegenerate() && IsFinite(s.pos) && s.r <= FLT_MAX;
		printf("\"%s\": {\"degenerate\": %s, \"center\": [%.9g, %.9g, %.9g], \"radius\": %.9g, \"support\": %d, \"excess\": %.3g, \"allowed\": %.3g}%s\n",
			names[i], s.IsDegenerate() ? "true" : "false", valid ? s.pos.x : 0.f, valid ? s.pos.y : 0.f, valid ? s.pos.z : 0.f,
			valid ? s.r : 0.f, s.numSupport, verdicts[i]->excess, verdicts[i]->allowed, i == 0 ? "," : "");
	}
	printf("}\n");
	return error.empty() ? 0 : 1;
}
