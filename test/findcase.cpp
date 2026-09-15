// findcase.cpp: generate random point sets (like the original pts_200: radius ~8) and
// report the relative volume difference between MathGeoLib and minobb.cpp.
// Usage: findcase.exe <seed> <nsets>
#include <cstdio>
#include <cstdlib>
#include <cmath>
#include <vector>
#include <algorithm>
#include "minobb.cpp"
using namespace std;

extern "C" double gt_volume(const float *v, int n);
extern "C" void GT_ResetWinRec();
extern "C" void GT_GetWinRec(int *out);
extern "C" float GT_GetWinVol();

struct Cand { double rel; int n; long seed; };

int main(int argc, char **argv)
{
	long baseSeed = argc > 1 ? atol(argv[1]) : 12345;
	int nsets = argc > 2 ? atoi(argv[2]) : 200;
	vector<Cand> best;
	for (long s = baseSeed; s < baseSeed + nsets; ++s)
	{
		srand((unsigned)s);
		int n = 50 + rand() % 350; // 50..399 points
		vector<float> v;
		for (int i = 0; i < n; ++i)
		{
			// uniform in ball of radius 8
			float x, y, z;
			do { x = rand()/(float)RAND_MAX*16.f - 8.f; y = rand()/(float)RAND_MAX*16.f - 8.f; z = rand()/(float)RAND_MAX*16.f - 8.f; }
			while (x*x + y*y + z*z > 64.f);
			v.push_back(x); v.push_back(y); v.push_back(z);
		}
		GT_ResetWinRec();
		double gt = gt_volume(&v[0], n);
		OBB mine = minobb(convex_hull(&v[0], n, 12));
		double my = mine.Volume();
		double rel = (gt > 0 && my > 0) ? fabs(gt - my) / fmax(gt, my) : 0.0;
		if (rel > 1e-4)
		{
			printf("seed %ld n=%d gt=%.6f mine=%.6f rel=%.6e\n", s, n, gt, my, rel);
			int rec[11]; GT_GetWinRec(rec);
			printf("   gt winner: cat=%d edges=(%d,%d)(%d,%d)(%d,%d) vol=%.6f cfgs A/B/C=%d/%d/%d\n",
				rec[1], rec[2], rec[3], rec[4], rec[5], rec[6], rec[7], GT_GetWinVol(), rec[8], rec[9], rec[10]);
			// write the set out for later use
			char fn[64]; snprintf(fn, sizeof(fn), "case_seed%d.txt", (int)s);
			FILE *f = fopen(fn, "wb");
			for (int i = 0; i < n; ++i)
				fprintf(f, "%.9g %.9g %.9g\n", v[3*i], v[3*i+1], v[3*i+2]);
			fclose(f);
			Cand c; c.rel = rel; c.n = n; c.seed = s;
			best.push_back(c);
		}
	}
	printf("total candidates with rel>1e-4: %d\n", (int)best.size());
	return 0;
}
