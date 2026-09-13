// exact5b.cpp: proper minimum-OBB search for the 5-point set.
// Stage 1: sweep the box's "thickness" axis n1 over the sphere.
// Stage 2: for each n1, compute the EXACT minimum-area rectangle of the
//          projected point set (2D convex hull + rotating calipers).
// Volume(n1) = range_along_n1 * minrect_area(perp projection).
#include <cstdio>
#include <cmath>
#include <vector>
#include <array>
#include <algorithm>
using namespace std;
typedef array<double, 3> dvec;
double dot(const dvec a, const dvec b) { return a[0]*b[0] + a[1]*b[1] + a[2]*b[2]; }
void cross(const dvec a, const dvec b, dvec &o)
{
	o[0] = a[1]*b[2] - a[2]*b[1];
	o[1] = a[2]*b[0] - a[0]*b[2];
	o[2] = a[0]*b[1] - a[1]*b[0];
}
void norm(dvec &a)
{
	double l = sqrt(dot(a, a));
	a[0] /= l; a[1] /= l; a[2] /= l;
}

// 2D: monotone chain hull of projected points (returns CCW hull, no dup last).
struct P2 { double x, y; };
static double cross2(const P2 &O, const P2 &A, const P2 &B)
{
	return (A.x - O.x) * (B.y - O.y) - (A.y - O.y) * (B.x - O.x);
}
static vector<P2> hull2(const vector<P2> &pts)
{
	vector<P2> h;
	vector<P2> s = pts;
	sort(s.begin(), s.end(), [](const P2 &a, const P2 &b) { return a.x < b.x || (a.x == b.x && a.y < b.y); });
	int n = (int)s.size();
	if (n < 3) return s;
	for (int i = 0; i < n; ++i)
	{
		while (h.size() >= 2 && cross2(h[h.size()-2], h.back(), s[i]) <= 1e-15) h.pop_back();
		h.push_back(s[i]);
	}
	int lower = (int)h.size();
	for (int i = n - 2; i >= 0; --i)
	{
		while ((int)h.size() > lower && cross2(h[h.size()-2], h.back(), s[i]) <= 1e-15) h.pop_back();
		h.push_back(s[i]);
	}
	h.pop_back();
	return h;
}
// Rotating calipers minimum rectangle area of a CCW convex hull.
static double minrect_area(const vector<P2> &h)
{
	int n = (int)h.size();
	if (n == 1) return 0.0;
	if (n == 2) return 0.0; // degenerate
	double best = 1e30;
	for (int i = 0; i < n; ++i)
	{
		const P2 &a = h[i];
		const P2 &b = h[(i + 1) % n];
		double ex = b.x - a.x, ey = b.y - a.y;
		double len = sqrt(ex*ex + ey*ey);
		double ux = ex / len, uy = ey / len;
		double vx = -uy, vy = ux;
		double umn = 1e30, umx = -1e30, vmn = 1e30, vmx = -1e30;
		for (int j = 0; j < n; ++j)
		{
			double dx = h[j].x - a.x, dy = h[j].y - a.y;
			double u = dx*ux + dy*uy;
			double v = dx*vx + dy*vy;
			umn = min(umn, u); umx = max(umx, u);
			vmn = min(vmn, v); vmx = max(vmx, v);
		}
		best = min(best, (umx - umn) * (vmx - vmn));
	}
	return best;
}

int main()
{
	vector<dvec> pts;
	pts.push_back({0,0,0});
	pts.push_back({2,0,0});
	pts.push_back({0,2,0});
	pts.push_back({0.9,1.1,1e-5});
	pts.push_back({1.3,-0.2,-2});

	// Center the points for numerical hygiene.
	dvec c = {0,0,0};
	for (auto &p : pts) { c[0]+=p[0]; c[1]+=p[1]; c[2]+=p[2]; }
	c[0] /= pts.size(); c[1] /= pts.size(); c[2] /= pts.size();
	for (auto &p : pts) { p[0]-=c[0]; p[1]-=c[1]; p[2]-=c[2]; }

	double best = 1e30;
	dvec bestN = {0,0,1};
	dvec bestU = {1,0,0}, bestV = {0,1,0};
	// Sweep n1 over the full sphere.
	int STEPS = 180;
	for (int ii = 0; ii <= 180; ++ii)
		for (int j = 0; j < STEPS; ++j)
		{
			double th = ii * M_PI / 180.0;
			double ph = 2 * M_PI * j / STEPS;
			dvec n = {sin(th)*cos(ph), sin(th)*sin(ph), cos(th)};
			// Frame: u = n x up (if not parallel), v = n x u.
			dvec up = {0,0,1};
			if (fabs(n[2]) > 0.99) up = {1,0,0};
			dvec u, v;
			cross(n, up, u); norm(u);
			cross(n, u, v); norm(v);
			double umn = 1e30, umx = -1e30;
			vector<P2> proj;
			for (auto &p : pts)
			{
				double a = dot(n, p);
				umn = min(umn, a); umx = max(umx, a);
				proj.push_back({dot(u, p), dot(v, p)});
			}
			double area = minrect_area(hull2(proj));
			double vol = (umx - umn) * area;
			if (vol < best)
			{
				best = vol;
				bestN = n; bestU = u; bestV = v;
			}
		}
	printf("sweep (0.5 deg x 0.5 deg): vol=%.9f n=(%.6f,%.6f,%.6f)\n", best, bestN[0], bestN[1], bestN[2]);
	for (int lvl = 0; lvl < 5; ++lvl)
	{
		double base = pow(10.0, -lvl - 1) * 0.5; // half-width in degrees
		double bestL = best;
		dvec nL = bestN, uL = bestU, vL = bestV;
		for (int i = -10; i <= 10; ++i)
			for (int j2 = -10; j2 <= 10; ++j2)
			{
				// perturb bestN around itself
				dvec t1 = {1,0,0};
				if (fabs(bestN[0]) > 0.9) t1 = {0,1,0};
				dvec w1, w2, cand;
				cross(bestN, t1, w1); norm(w1);
				cross(bestN, w1, w2); norm(w2);
				double a1 = i * base * M_PI / 180.0;
				double a2 = j2 * base * M_PI / 180.0;
				// rotate bestN by a1 around w1
				double ca = cos(a1), sa = sin(a1);
				cand[0] = bestN[0]*ca + w1[0]*sa + (dot(bestN, w1)) * (1 - ca);
				cand[1] = bestN[1]*ca + w1[1]*sa + (dot(bestN, w1)) * (1 - ca);
				cand[2] = bestN[2]*ca + w1[2]*sa + (dot(bestN, w1)) * (1 - ca);
				norm(cand);
				// then rotate cand by a2 around w2 (approx, recompute w2 from cand)
				cross(cand, t1, w2); norm(w2);
				ca = cos(a2); sa = sin(a2);
				dvec cand2;
				cand2[0] = cand[0]*ca + w2[0]*sa + (dot(cand, w2)) * (1 - ca);
				cand2[1] = cand[1]*ca + w2[1]*sa + (dot(cand, w2)) * (1 - ca);
				cand2[2] = cand[2]*ca + w2[2]*sa + (dot(cand, w2)) * (1 - ca);
				norm(cand2);
				dvec up = {0,0,1};
				if (fabs(cand2[2]) > 0.99) up = {1,0,0};
				dvec uu, vv;
				cross(cand2, up, uu); norm(uu);
				cross(cand2, uu, vv); norm(vv);
				double umn = 1e30, umx = -1e30;
				vector<P2> proj;
				for (auto &p : pts)
				{
					double a = dot(cand2, p);
					umn = min(umn, a); umx = max(umx, a);
					proj.push_back({dot(uu, p), dot(vv, p)});
				}
				double vol = (umx - umn) * minrect_area(hull2(proj));
				if (vol < bestL)
				{
					bestL = vol;
					nL = cand2; uL = uu; vL = vv;
				}
			}
		best = bestL; bestN = nL; bestU = uL; bestV = vL;
	}
	printf("refined: vol=%.9f n=(%.7f,%.7f,%.7f)\n", best, bestN[0], bestN[1], bestN[2]);
	printf("  u=(%.7f,%.7f,%.7f) v=(%.7f,%.7f,%.7f)\n", bestU[0], bestU[1], bestU[2], bestV[0], bestV[1], bestV[2]);
	return 0;
}
