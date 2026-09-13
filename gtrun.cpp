#include <cstdio>
#include <vector>
#include <cmath>
extern "C" double gt_volume(const float *v, int n);
extern "C" void gt_obb(const float *v, int n, double *out);
int main(int argc, char **argv)
{
	float v[15] = {0,0,0, 2,0,0, 0,2,0, 0.9f,1.1f,1e-5f, 1.3f,-0.2f,-2.f};
	double out[17];
	gt_obb(v, 5, out);
	printf("gt: vol=%.6f degenerate=%d r=(%.4f,%.4f,%.4f)\n", out[15], (int)out[16], out[3], out[4], out[5]);
	for (int a = 0; a < 3; ++a)
		printf("  axis%d = (%.6f, %.6f, %.6f)\n", a, out[6+a*3+0], out[6+a*3+1], out[6+a*3+2]);
	// Flush analysis against the 5-point hull.
	int hullE[10][2] = {{0,1},{0,2},{0,3},{0,4},{1,2},{1,3},{1,4},{2,3},{3,4},{3,4}};
	hullE[9][0] = 3; hullE[9][1] = 4;
	double pos[3] = {out[0], out[1], out[2]};
	double ax[3][3];
	for (int a = 0; a < 3; ++a)
		for (int b = 0; b < 3; ++b)
			ax[a][b] = out[6+a*3+b];
	for (int e = 0; e < 10; ++e)
	{
		double e0[3], e1[3];
		for (int b = 0; b < 3; ++b)
		{
			e0[b] = v[3*hullE[e][0]+b];
			e1[b] = v[3*hullE[e][1]+b];
		}
		double ex = e1[0]-e0[0], ey = e1[1]-e0[1], ez = e1[2]-e0[2];
		double el = sqrt(ex*ex+ey*ey+ez*ez);
		ex /= el; ey /= el; ez /= el;
		for (int a = 0; a < 3; ++a)
		{
			double d = ex*ax[a][0] + ey*ax[a][1] + ez*ax[a][2];
			if (fabs(d) > 0.9999)
			{
				double t0[3], t1[3];
				for (int b = 0; b < 3; ++b)
				{
					t0[b] = e0[b] - pos[b];
					t1[b] = e1[b] - pos[b];
				}
				double u0 = t0[0]*ax[a][0] + t0[1]*ax[a][1] + t0[2]*ax[a][2];
				double u1 = t1[0]*ax[a][0] + t1[1]*ax[a][1] + t1[2]*ax[a][2];
				double ra = out[3+a];
				if (fabs(fabs(u0) - ra) < 1e-3 && fabs(fabs(u1) - ra) < 1e-3)
					printf("  FLUSH edge (%d,%d) along axis%d (u=%.4f)\n", hullE[e][0], hullE[e][1], a, u0);
			}
		}
	}
	if (argc > 1)
	{
		FILE *f = fopen(argv[1], "rb");
		std::vector<float> vv;
		float x, y, z;
		while (fscanf(f, "%f %f %f", &x, &y, &z) == 3)
		{
			vv.push_back(x);
			vv.push_back(y);
			vv.push_back(z);
		}
		fclose(f);
		printf("gt %s: vol=%.6f\n", argv[1], gt_volume(vv.data(), (int)vv.size() / 3));
	}
	return 0;
}
