#include <cstdio>
#include <vector>
#include "minobb.cpp"
using namespace std;
int main(int argc, char **argv)
{
	for (int a = 1; a < argc; ++a)
	{
		FILE *f = fopen(argv[a], "rb");
		if (!f) continue;
		vector<float> v; float x, y, z;
		while (fscanf(f, "%f %f %f", &x, &y, &z) == 3) { v.push_back(x); v.push_back(y); v.push_back(z); }
		fclose(f);
		int n = (int)v.size() / 3;
		OBB o = minobb(&v[0], n, 12);
		float worst = 0.f; int wv = -1, wa = -1;
		for (int i = 0; i < n; ++i)
		{
			vec3 p(v[3*i], v[3*i+1], v[3*i+2]);
			vec3 lp = o.LocalToWorldInverse(p);
			for (int j = 0; j < 3; ++j)
				if (Absf(lp[j]) - o.r[j] > worst) { worst = Absf(lp[j]) - o.r[j]; wv = i; wa = j; }
		}
		printf("%s: n=%d vol=%.6f worstViolation=%.3e (point %d axis %d) degenerate=%d\n",
			argv[a], n, o.Volume(), worst, wv, wa, (int)o.IsDegenerate());
	}
	return 0;
}
