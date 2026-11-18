// minsphere.cpp
//
// Minimum enclosing sphere of a point set, see minsphere.h.
//
// Adapted from MathGeoLib's Sphere::OptimalEnclosingSphere(). That function
// keeps four support points, walks through the points, and when it meets a
// point outside the sphere, computes the smallest sphere of the four support
// points and the new point, replaces the support point that became redundant
// and starts over. It decides with fixed tolerances (1e-4 here, 5e-3 there)
// in float arithmetic, and it guards against going around in circles with
// flags, which is what made it fragile: the result depended on the scale of
// the input, and could be a sphere much larger than the smallest one, or one
// that left some of the points outside.
//
// What is kept is the scheme (a support set, and a new sphere from the
// support set and a point outside), and the way a sphere is fit through
// points: FitSphereThroughPoints() below. What is different:
//
// - The spheres are computed in doubles, in which the differences of the float
//   coordinates are exact, and there are no tolerances: nothing depends on
//   the scale of the points.
// - The support set has one to four points, as many as hold the sphere in
//   place, instead of always four.
// - The point taken in is the one farthest outside the sphere, not the first
//   one found. The sphere grows with each such exchange, so no state can come
//   back, and a handful of exchanges are enough.
// - The new sphere is chosen among all the spheres that the new point spans
//   with up to three of the old support points, by the radius that each needs
//   to contain all five points: the smallest one wins. No sphere has to be
//   judged right or wrong by a threshold.
// - At the end the radius is measured from the center as rounded to floats,
//   which is what makes the result contain the points.
//
// And for speed, as each exchange costs a pass over the points:
//
// - A large point set is first solved for every 64th of its points. That
//   sphere is close to the final one, so few exchanges are left for the
//   passes over all the points.
// - The points that cannot be on the final sphere are dropped along the way:
//   the sphere of the support points bounds the final radius from below, and
//   the farthest point from above, which leaves the final center little room.
//   With a good first sphere nearly all the points go in the second pass, and
//   the passes after that (the last one, too) are over the few that are left.
// - A pass computes the distances in floats first, with a bound for their
//   rounding errors, and in doubles only for the blocks of points that can
//   have the farthest point in them: see Scan.
//
// - The points that are kept are copied to a list of their own in loops
//   without branches, eight points at a time, skipping the eights that have
//   nothing to keep.
//
// A model of 15 million vertices takes two passes over its vertices, 30 ms.

#include "minsphere.h"

#include <algorithm>
#include <cfloat>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <vector>

// Build with -DMINSPHERE_TRACE to have each round of the search printed to stderr.
#ifdef MINSPHERE_TRACE
#include <cstdio>
#endif

namespace
{

// A point set: `n` float triples, `stride` bytes apart.
struct Points
{
	const char *data;
	size_t stride;
	int n;

	void Get(int i, double p[3]) const
	{
		float f[3];
		memcpy(f, data + (size_t)i * stride, sizeof f);
		p[0] = f[0]; p[1] = f[1]; p[2] = f[2];
	}
};

inline double Dot(const double a[3], const double b[3]) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }

inline double DistanceSq(const double a[3], const double b[3])
{
	const double x = a[0] - b[0], y = a[1] - b[1], z = a[2] - b[2];
	return x * x + y * y + z * z;
}

/* Computes the (s,t) coordinates of the smallest sphere that passes through the three points (0,0,0), ab and ac:
   its center is s*ab + t*ac. (When fitting a sphere through three points a, b and c, pass in b-a and c-a.)

   The center p of a sphere through the points 0, B and C is equally far from each, so

      BP == B^2/2 and
      CP == C^2/2,

   and for the smallest such sphere p is in the plane of the three points: P == s*B + t*C. Substituted, this gives

      ( B^2  BC  ) * (s) = (B^2 / 2)
      ( BC   C^2 )   (t)   (C^2 / 2)

   which is solved by inverting the 2x2 matrix.

   Returns false if the points are collinear, in which case no sphere passes through them. */
bool FitSphereThroughPoints(const double ab[3], const double ac[3], double &s, double &t)
{
	const double BB = Dot(ab, ab);
	const double CC = Dot(ac, ac);
	const double BC = Dot(ab, ac);

	const double denom = BB * CC - BC * BC;
	if (!(denom > 0.0))
		return false;

	const double f = 0.5 / denom;
	s = (CC * BB - BC * CC) * f;
	t = (CC * BB - BC * BB) * f;
	return true;
}

/* Computes the (s,t,u) coordinates of the sphere that passes through the four points (0,0,0), ab, ac and ad:
   its center is s*ab + t*ac + u*ad.

   As above, the center P == s*B + t*C + u*D is equally far from the four points:

      ( B^2  BC  BD )   (s)   (B^2 / 2)
      ( BC   C^2 CD ) * (t) = (C^2 / 2)
      ( BD   CD  D^2)   (u)   (D^2 / 2)

   Returns false if the points are coplanar, in which case no sphere passes through them. */
bool FitSphereThroughPoints(const double ab[3], const double ac[3], const double ad[3], double &s, double &t, double &u)
{
	const double BB = Dot(ab, ab);
	const double BC = Dot(ab, ac);
	const double BD = Dot(ab, ad);
	const double CC = Dot(ac, ac);
	const double CD = Dot(ac, ad);
	const double DD = Dot(ad, ad);

	// The inverse of the symmetric matrix, by its cofactors.
	const double c00 = CC * DD - CD * CD;
	const double c01 = BD * CD - BC * DD;
	const double c02 = BC * CD - BD * CC;
	const double c11 = BB * DD - BD * BD;
	const double c12 = BC * BD - BB * CD;
	const double c22 = BB * CC - BC * BC;
	const double det = BB * c00 + BC * c01 + BD * c02;
	if (!(det > 0.0))
		return false;

	const double f = 0.5 / det;
	s = (c00 * BB + c01 * CC + c02 * DD) * f;
	t = (c01 * BB + c11 * CC + c12 * DD) * f;
	u = (c02 * BB + c12 * CC + c22 * DD) * f;
	return true;
}

// A sphere with the points that it was fit through.
struct Ball
{
	double c[3];    // Center.
	double r2;      // Radius squared. Negative: there is no sphere yet.
	int n;          // The number of support points.
	int idx[4];     // The support points: their indices,
	double p[4][3]; // their coordinates,
	double w[4];    // and the center as their weighted average: the weights are >= 0 and sum to 1.

	Ball() : r2(-1.0), n(0) { c[0] = c[1] = c[2] = 0.0; }
};

// Fits the smallest sphere through the k points t[0..k) (1 <= k <= 4): the one whose center is in the same
// point, line or plane with them. Outputs the center, both as a point and as the weights that give it as a
// weighted average of the points. Returns false if there is no such sphere (collinear or coplanar points),
// and also if the center is not in between the points (it has a negative weight): then the smallest sphere
// that contains the points does not pass through all of them, and a subset of them has a smaller one.
bool FitSphere(const double t[4][3], int k, double center[3], double w[4])
{
	double e[3][3], st[3] = { 0.0, 0.0, 0.0 };
	for (int i = 1; i < k; ++i)
		for (int j = 0; j < 3; ++j)
			e[i - 1][j] = t[i][j] - t[0][j];

	if (k == 2)
		st[0] = 0.5;
	else if (k == 3)
	{
		if (!FitSphereThroughPoints(e[0], e[1], st[0], st[1]))
			return false;
	}
	else if (k == 4)
	{
		if (!FitSphereThroughPoints(e[0], e[1], e[2], st[0], st[1], st[2]))
			return false;
	}

	w[0] = 1.0;
	for (int i = 1; i < k; ++i)
	{
		w[i] = st[i - 1];
		w[0] -= st[i - 1];
	}
	for (int i = 0; i < k; ++i)
		if (!(w[i] >= 0.0))
			return false;

	for (int j = 0; j < 3; ++j)
	{
		center[j] = t[0][j];
		for (int i = 1; i < k; ++i)
			center[j] += st[i - 1] * e[i - 1][j];
	}
	return true;
}

// Returns the smallest sphere that contains the support points of the sphere `b`, and the point q (of index qi),
// which is outside `b`. (This is OptimalEnclosingSphere() of five points of MathGeoLib.)
//
// The smallest sphere around the support points and q passes through q, since without q it would be `b`. So it
// is the smallest sphere through q and some (at most three) of the support points, with its center in between
// those: all such spheres are tried. Each is measured by the radius that it needs for containing all the
// points, and the one that needs the least is the smallest sphere. (The sphere that is the answer needs no
// more than its own radius. Rounding errors can make it look like needing a hair more, or make another sphere
// that is as good win, and neither does any harm, where an "is it inside" test with a tolerance would.)
Ball Enclose(const Ball &b, const double q[3], int qi)
{
	// The subsets of the support points, the smallest subsets first: of spheres that are equally good the one
	// through the fewest points is chosen, as that is the support set which has no redundant points.
	static const unsigned char subsets[15] = { 0, 1, 2, 4, 8, 3, 5, 6, 9, 10, 12, 7, 11, 13, 14 };

	Ball best;
	best.r2 = DBL_MAX;
	for (int i = 0; i < 15; ++i)
	{
		const int subset = subsets[i];
		if (subset >> b.n)
			continue;

		Ball s;
		s.n = 1;
		s.idx[0] = qi;
		memcpy(s.p[0], q, sizeof s.p[0]);
		for (int j = 0; j < b.n; ++j)
			if (subset & (1 << j))
			{
				s.idx[s.n] = b.idx[j];
				memcpy(s.p[s.n], b.p[j], sizeof s.p[0]);
				++s.n;
			}
		if (!FitSphere(s.p, s.n, s.c, s.w))
			continue;

		s.r2 = DistanceSq(s.c, q);
		for (int j = 0; j < b.n; ++j)
			s.r2 = std::max(s.r2, DistanceSq(s.c, b.p[j]));
		// (A sphere through more points has to be smaller by more than a rounding error to be taken.)
		if (s.r2 < best.r2 * (1.0 - 16.0 * DBL_EPSILON))
			best = s;
	}
	return best;
}

// A lower bound for the radius of the smallest sphere around the support points of `b`, squared, and the
// point `mean` that the bound is about: any sphere of radius R around the support points has its center
// within sqrt(R^2 - bound) of `mean`.
//
// With the weights w of the support points p, and their weighted average m, any point x has
//
//    max |x - p_i|^2  >=  sum w_i |x - p_i|^2  =  |x - m|^2 + sum w_i |p_i - m|^2,
//
// so a sphere around x that contains the support points has at least the radius that the right hand side
// gives. The sum is the bound: for the weights of the sphere's own center it is the radius of `b` squared,
// and it is a bound for any weights, also ones that have rounding errors in them.
double LowerBound(const Ball &b, double mean[3])
{
	mean[0] = mean[1] = mean[2] = 0.0;
	for (int i = 0; i < b.n; ++i)
		for (int j = 0; j < 3; ++j)
			mean[j] += b.w[i] * (b.p[i][j] - b.p[0][j]);
	for (int j = 0; j < 3; ++j)
		mean[j] += b.p[0][j];

	double bound = 0.0;
	for (int i = 0; i < b.n; ++i)
		bound += b.w[i] * DistanceSq(b.p[i], mean);
	return bound;
}

// The passes over the points go through them in blocks of this many, with simple loops that have no
// branches in them, which compilers turn to fast code.
enum { BLOCK = 256 };

// A point set of at least SAMPLE_MIN_POINTS points is first solved for every SAMPLE_STEP'th of its points.
enum { SAMPLE_STEP = 64, SAMPLE_MIN_POINTS = 16384 };

// Returns the points [first, first + count) as xyz triples: where they are, if they are packed, and
// otherwise copied to buf.
inline const float *Load(const Points &pts, int first, int count, float *buf)
{
	if (pts.stride == 3 * sizeof(float))
		return (const float *)(pts.data + (size_t)first * (3 * sizeof(float)));
	for (int i = 0; i < count; ++i)
		memcpy(buf + 3 * i, pts.data + (size_t)(first + i) * pts.stride, 3 * sizeof(float));
	return buf;
}

// Computes the squared distances of `count` points from c. A point that is not finite gets -1.
inline void DistancesSq(const float *p, int count, const double c[3], double *d2)
{
	const double cx = c[0], cy = c[1], cz = c[2];
	for (int i = 0; i < count; ++i)
	{
		const double dx = p[3 * i] - cx, dy = p[3 * i + 1] - cy, dz = p[3 * i + 2] - cz;
		const double d = dx * dx + dy * dy + dz * dz;
		d2[i] = d <= DBL_MAX ? d : -1.0;
	}
}

// The same in float arithmetic: for a first look, see Scan.
inline void DistancesSq(const float *p, int count, const float c[3], float *d2)
{
	const float cx = c[0], cy = c[1], cz = c[2];
	for (int i = 0; i < count; ++i)
	{
		const float dx = p[3 * i] - cx, dy = p[3 * i + 1] - cy, dz = p[3 * i + 2] - cz;
		d2[i] = dx * dx + dy * dy + dz * dz;
	}
}

// Returns the largest of the `count` numbers (and of `least`). NaNs are passed over.
template<typename T>
inline T Largest(const T *d2, int count, T least)
{
	// (Several running maxima side by side: one alone would wait for itself at every number.)
	T m[8] = { least, least, least, least, least, least, least, least };
	int i = 0;
	for (; i + 8 <= count; i += 8)
		for (int j = 0; j < 8; ++j)
			m[j] = d2[i + j] > m[j] ? d2[i + j] : m[j];
	for (; i < count; ++i)
		m[0] = d2[i] > m[0] ? d2[i] : m[0];
	for (int j = 1; j < 8; ++j)
		m[0] = m[j] > m[0] ? m[j] : m[0];
	return m[0];
}

// Sets keep[i] to 1 for the numbers that are at least `limit`, and to 0 for the others (NaNs among them).
// Returns how many were set to 1.
template<typename T>
inline int Flag(const T *d2, int count, T limit, unsigned char *keep)
{
	for (int i = 0; i < count; ++i)
		keep[i] = d2[i] >= limit;
	int kept = 0;
	for (int i = 0; i < count; ++i)
		kept += keep[i];
	return kept;
}

// The size of the steps between floats at the magnitude x: an upper bound for it.
double UlpOfFloat(double x)
{
	float f = (float)std::min(std::fabs(x), (double)FLT_MAX);
	if ((double)f < std::fabs(x))
		f = std::nextafter(f, FLT_MAX);
	if (f >= FLT_MAX)
		return (double)FLT_MAX - (double)std::nextafter(FLT_MAX, 0.f);
	return (double)std::nextafter(f, FLT_MAX) - (double)f;
}

// One pass over points: finds the point that is the farthest from the center c, and tells which points are
// at least sqrt(keep2) away from it.
//
// The distances are first computed in float arithmetic, from the center as rounded to floats, which is
// twice as fast as in doubles. They are off by rounding errors that have a bound: `error` for the rounding
// of the center, and 3e-7 of the squared distance for the arithmetic (a subtraction of floats is exact to
// half a unit in its last place, and the squares and their sum have no cancellation in them). So the float
// distances tell which blocks of points cannot have the farthest point in them, which is most of them, and
// only the other blocks are computed again in doubles. A point is dropped by its float distance only if it is
// below the threshold by more than the bound, and in the blocks that were computed in doubles, by that
// distance. (A sum of squares that overflows floats is infinite, which sends its block to the doubles. One
// that underflows has no relative bound, so thresholds that small are not used.)
struct Scan
{
	double c[3];     // The center.
	float cf[3];     // The center as floats,
	double error;    // and how far that is from the center.
	double keep2;    // The points at least this far (squared) are kept.
	float keepF2;    // The same for float distances: lower by the error bound.
	double far2;     // The squared distance of the farthest point so far. (-1: there is none yet.)
	float threshold; // A block whose largest float distance is below this cannot have a point farther than far2.
	int numBlocks;   // How many blocks have been looked at with float distances since the last check,
	int numRedone;   // and how many of them had to be computed again in doubles.
	int doublesOnly; // This many of the next blocks are computed in doubles right away.
	int kept;        // How many points of the last block are to be kept.

	Scan(const double center[3], double keepSquared) : keep2(keepSquared), far2(-1.0), threshold(0.f), numBlocks(0), numRedone(0), doublesOnly(0), kept(0)
	{
		for (int j = 0; j < 3; ++j)
		{
			c[j] = center[j];
			cf[j] = (float)center[j];
		}
		const double f[3] = { cf[0], cf[1], cf[2] };
		error = std::sqrt(DistanceSq(c, f));
		keepF2 = FloatThreshold(keep2);
	}

	// Float distances below the returned number are certainly below d2 as real distances. (0: none are.)
	float FloatThreshold(double d2) const
	{
		const double d = std::sqrt(std::max(d2, 0.0)) - error;
		const double t = d * d * (1.0 - 1e-6);
		return d > 0.0 && t >= 1e-30 ? (float)t : 0.f;
	}

	// Looks at `count` (at most BLOCK) points. Sets keep[i] to 1 for the points to keep and to 0 for the
	// others, and `kept` to the number of the points to keep: if that is 0, keep[] is not set at all. (keep
	// can be null, for a pass that drops no points: then `kept` is the number of the points.)
	// Returns the index of the farthest point so far, if it is among these, and -1 if it is not.
	inline int Block(const float *p, int count, unsigned char *keep)
	{
		// Where the points are all about as far from the center (those of a ball, say), or each block is
		// farther than the ones before it, the float distances rule no blocks out, and are not worth
		// computing: when most of the last 32 blocks had to be computed again, the next 128 are computed in
		// doubles right away.
		bool doubles = doublesOnly > 0;
		float d2f[BLOCK];
		if (doubles)
			--doublesOnly;
		else
		{
			DistancesSq(p, count, cf, d2f);
			const float largest = Largest(d2f, count, 0.f);
			doubles = largest >= threshold;
			numRedone += doubles;
			if (++numBlocks == 32)
			{
				if (numRedone >= 24)
					doublesOnly = 128;
				numBlocks = numRedone = 0;
			}
			if (!doubles)
			{
				kept = 0;
				if (!keep)
					kept = count;
				else if (!(largest < keepF2)) // (Otherwise all the points are dropped, which is the common case.)
					kept = Flag(d2f, count, keepF2, keep); // (The points that are not finite are dropped: their distance is a NaN.)
				return -1;
			}
		}

		double d2[BLOCK];
		DistancesSq(p, count, c, d2);
		kept = keep ? Flag(d2, count, keep2, keep) : count;
		const double largest = Largest(d2, count, far2);
		if (largest > far2)
		{
			far2 = largest;
			threshold = FloatThreshold(far2);
			for (int i = 0; i < count; ++i)
				if (d2[i] == largest)
					return i;
		}
		return -1;
	}
};

// An array that is not initialized when it is made or grows: a std::vector would write zeros all over the
// memory first, which is a pass over it for nothing.
template<typename T>
struct Array
{
	T *data;
	size_t size;

	Array() : data(nullptr), size(0) {}
	~Array() { delete[] data; }
	Array(const Array &) = delete;
	Array &operator=(const Array &) = delete;

	// Makes room for `newSize` elements, and keeps the first `used` ones.
	void Grow(size_t newSize, size_t used)
	{
		T *grown = new T[newSize];
		if (used)
			memcpy(grown, data, used * sizeof(T));
		delete[] data;
		data = grown;
		size = newSize;
	}
};

// Appends the points of a block that have their keep flag set to the list of points `out` and their indices
// to `outIndex`, at the position `kept` of the lists. The index of the point i of the block is index[i], or
// without `index`, firstIndex + i. Returns the new `kept`.
// (The lists can be the ones that the block is in: the points only move towards the start.)
inline int KeepPoints(const float *p, const int *index, int firstIndex, int count, const unsigned char *keep,
	float *out, int *outIndex, int kept)
{
	// Each point is written to the list, and the list grows by one only if the point is kept: that has no
	// branches to guess wrong, however the kept points are scattered. The points are gone through eight at a
	// time, and the eights that have nothing to keep, which the points that are next to each other in a
	// model often make, are skipped.
	int i = 0;
	for (; i + 8 <= count; i += 8)
	{
		uint64_t flags;
		memcpy(&flags, keep + i, sizeof flags);
		if (!flags)
			continue;
		for (int j = i; j < i + 8; ++j)
		{
			out[3 * kept] = p[3 * j]; out[3 * kept + 1] = p[3 * j + 1]; out[3 * kept + 2] = p[3 * j + 2];
			outIndex[kept] = index ? index[j] : firstIndex + j;
			kept += keep[j];
		}
	}
	for (; i < count; ++i)
	{
		out[3 * kept] = p[3 * i]; out[3 * kept + 1] = p[3 * i + 1]; out[3 * kept + 2] = p[3 * i + 2];
		outIndex[kept] = index ? index[i] : firstIndex + i;
		kept += keep[i];
	}
	return kept;
}

// The state of the search for the smallest sphere of a point set.
struct Search
{
	Ball ball;

	// The points that can still be on the final sphere, once some have been dropped (compacted == true):
	// their coordinates and their indices. Before that, all the points can.
	bool compacted = false;
	int numActive = 0;
	Array<float> active;
	Array<int> activeIndex;

	bool converged = false;
};

// Finds the smallest sphere of the points, as doubles.
void FindSmallestSphere(const Points &pts, Search &s)
{
	const int n = pts.n;
	Ball &ball = s.ball;
	s.numActive = n;

	// A large point set gets its first sphere from a sample of its points: the smallest sphere of every
	// 64th point (found by this same function) is already close to that of all of them, which leaves little
	// to do in the passes over all the points, and lets most of the points be dropped in the second pass.
	std::vector<float> sample;
	if (n >= SAMPLE_MIN_POINTS)
	{
		const int count = (n + SAMPLE_STEP - 1) / SAMPLE_STEP;
		sample.resize((size_t)count * 3);
		for (int i = 0; i < count; ++i)
			memcpy(&sample[(size_t)i * 3], pts.data + (size_t)i * SAMPLE_STEP * pts.stride, 3 * sizeof(float));
		const Points samplePoints = { (const char *)sample.data(), 3 * sizeof(float), count };
		Search sub;
		FindSmallestSphere(samplePoints, sub);
		ball = sub.ball;
		for (int i = 0; i < ball.n; ++i)
			ball.idx[i] *= SAMPLE_STEP;
	}

	float buf[3 * BLOCK];
	unsigned char keep[BLOCK];
	double upper2 = DBL_MAX; // The square of an upper bound for the radius of the final sphere.
	for (int round = 0; round < 100000; ++round)
	{
		// A point p is dropped when it cannot be on the final sphere. The final sphere contains the support
		// points of the current one and its radius is at most the upper bound, so its center x is within
		// reach = sqrt(upper^2 - lower^2) of `mean`, see LowerBound(). Its radius is at least `lower`. So a
		// point that is closer than lower - reach to `mean` is inside the final sphere, not on it:
		// |p - x| <= |p - mean| + reach < lower. (The scan measures distances from the center of the sphere,
		// which is `mean` up to rounding: the difference is added to the reach.)
		//
		// The points that are dropped are left out of the last pass as well, which measures the radius from
		// the center as rounded to floats, see MinSphere(). That rounding moves the center by at most
		// `rounding`, so a point that is two of those further inside cannot be the farthest one from the
		// rounded center either: the support points are farther from it.
		double keep2 = 0.0; // The points at least this far from the center (squared) are kept: all, to begin with.
		if (upper2 < DBL_MAX && ball.n >= 2)
		{
			double mean[3];
			const double lower2 = LowerBound(ball, mean);
			// (The bounds have rounding errors of some 1e-15 of themselves, which the square root would turn to 1e-8.)
			const double reach = std::sqrt(std::max(upper2 - lower2, 0.0) + 64.0 * DBL_EPSILON * upper2) + std::sqrt(DistanceSq(mean, ball.c));
			double rounding = 0.0;
			for (int j = 0; j < 3; ++j)
			{
				const double ulp = UlpOfFloat(std::fabs(mean[j]) + reach);
				rounding += 0.25 * ulp * ulp;
			}
			rounding = std::sqrt(rounding);
			const double keepDistance = (std::sqrt(lower2) - reach - 2.0 * rounding) * (1.0 - 1e-9);
			if (keepDistance > 0.0)
				keep2 = keepDistance * keepDistance;
		}

		// One pass over the points that are left: finds the farthest one from the center, and drops points.
		Scan scan(ball.c, keep2);
		int farIndex = -1;
		int kept = 0;
		if (!s.compacted)
		{
			// The points are copied to a list of their own only when at least half of them can be dropped:
			// until then the passes are over all the points. How many can be dropped is told by the sample,
			// or without one, by the previous pass, which counted them.
			bool collect = false;
			size_t expected = (size_t)s.numActive;
			if (keep2 > 0.0 && !sample.empty())
			{
				const size_t count = sample.size() / 3;
				size_t sampleKept = 0;
				for (size_t i = 0; i < count; ++i)
				{
					const double p[3] = { sample[3 * i], sample[3 * i + 1], sample[3 * i + 2] };
					sampleKept += DistanceSq(p, ball.c) >= keep2;
				}
				collect = sampleKept <= count / 2;
				expected = (size_t)((double)sampleKept / (double)count * n * 1.5) + 4 * BLOCK;
			}
			else if (keep2 > 0.0)
				collect = s.numActive <= n / 2;

			for (int first = 0; first < n; first += BLOCK)
			{
				const int count = std::min<int>(BLOCK, n - first);
				const float *p = Load(pts, first, count, buf);
				const int farthest = scan.Block(p, count, keep2 > 0.0 ? keep : nullptr);
				if (farthest >= 0)
					farIndex = first + farthest;

				if (!collect)
					kept += scan.kept;
				else if (scan.kept > 0)
				{
					if (s.activeIndex.size < (size_t)kept + count)
					{
						const size_t size = std::max(expected, s.activeIndex.size * 2) + BLOCK;
						s.active.Grow(size * 3, (size_t)kept * 3);
						s.activeIndex.Grow(size, (size_t)kept);
					}
					kept = KeepPoints(p, nullptr, first, count, keep, s.active.data, s.activeIndex.data, kept);
				}
			}
			s.compacted = collect;
		}
		else
		{
			float *p = s.active.data;
			int *index = s.activeIndex.data;
			for (int first = 0; first < s.numActive; first += BLOCK)
			{
				const int count = std::min<int>(BLOCK, s.numActive - first);
				const int farthest = scan.Block(p + 3 * first, count, keep);
				if (farthest >= 0)
					farIndex = index[first + farthest];

				// (The points move towards the start of the list, each to a place at or before its own.)
				if (scan.kept > 0)
					kept = KeepPoints(p + 3 * first, index + first, 0, count, keep, p, index, kept);
			}
		}
		s.numActive = kept;

#ifdef MINSPHERE_TRACE
		fprintf(stderr, "trace: %d points, round %d: %d support points, r %.9g, the farthest point is %.3g r outside, %d points left%s\n",
			n, round, ball.n, std::sqrt(ball.r2), std::sqrt(scan.far2 / ball.r2) - 1.0, s.numActive, s.compacted ? "" : " (not dropped yet)");
#endif
		if (farIndex < 0)
			return; // No (finite) points.
		upper2 = std::min(upper2, scan.far2);
		if (!(scan.far2 > ball.r2))
		{
			s.converged = true; // All the points are inside: this is the smallest sphere.
			return;
		}

		double q[3];
		pts.Get(farIndex, q);
		const Ball next = Enclose(ball, q, farIndex);
		if (!(next.r2 > ball.r2))
		{
			s.converged = true; // The sphere would not grow: the point is outside only by a rounding error.
			return;
		}
		ball = next;
	}
}

Sphere MinSphere(const Points &pts)
{
	Sphere sphere;
	Search s;
	FindSmallestSphere(pts, s);
	const Ball &ball = s.ball;
	if (ball.n == 0)
		return sphere; // No points.

	// The center as floats, and the radius that contains all the points from there: the distance of the
	// farthest point, which is one of those that were not dropped (see the rounds above).
	sphere.pos = vec3((float)ball.c[0], (float)ball.c[1], (float)ball.c[2]);
	const double center[3] = { sphere.pos.x, sphere.pos.y, sphere.pos.z };
	Scan scan(center, 0.0);
	float buf[3 * BLOCK];
	const bool all = !s.compacted || !s.converged;
	const int count = all ? pts.n : s.numActive;
	for (int first = 0; first < count; first += BLOCK)
	{
		const int blockCount = std::min<int>(BLOCK, count - first);
		scan.Block(all ? Load(pts, first, blockCount, buf) : s.active.data + 3 * first, blockCount, nullptr);
	}

	// The radius is rounded up, past the rounding errors of the distances (a few times 1e-16 of them).
	const double r2 = std::max(scan.far2, 0.0) * (1.0 + 16.0 * DBL_EPSILON);
	float r = (float)std::sqrt(r2);
	while ((double)r * (double)r < r2)
		r = std::nextafter(r, FLT_MAX);
	sphere.r = r;

	sphere.numSupport = ball.n;
	for (int i = 0; i < ball.n; ++i)
		sphere.support[i] = ball.idx[i];
	return sphere;
}

} // ~namespace

float Sphere::Volume() const
{
	return 4.f / 3.f * 3.14159265358979323846f * r * r * r;
}

float Sphere::Distance(const vec3 &p) const
{
	const double c[3] = { pos.x, pos.y, pos.z }, q[3] = { p.x, p.y, p.z };
	return (float)(std::sqrt(DistanceSq(c, q)) - (double)r);
}

bool Sphere::Contains(const vec3 &p) const
{
	const double c[3] = { pos.x, pos.y, pos.z }, q[3] = { p.x, p.y, p.z };
	return DistanceSq(c, q) <= (double)r * (double)r;
}

Sphere minsphere(const float *pts, int num_pts, int stride_bytes)
{
	const Points points = { (const char *)pts, (size_t)stride_bytes, pts && num_pts > 0 ? num_pts : 0 };
	return MinSphere(points);
}

Sphere minsphere(const Hull3 &hull)
{
	return minsphere(hull.v.empty() ? nullptr : &hull.v[0].x, (int)hull.v.size(), (int)sizeof(vec3));
}
