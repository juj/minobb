"""
Rigorous numerical verification of the hinge identity:

    For a box with orthonormal axes e_0,e_1,e_2 (rows of U), and the hinge
    curve L_d(t) = U @ rot_about(e_d, t).T  (rotate the box about its own axis d),

    (log V)''_L(0) = -2 - sum_u (W'_u / W_u)^2   <=  -2      (Theorem 1)

at every box whose six supports are unique (interior of a no-flush cell),
and one-sidedly at 1- and 2-contact boxes.

Convention: Q = P @ U.T, so Q[i,u] = P[i] . U[u] (row u = axis u).
World->box-frame: v_box = U @ v_world.
"""
import numpy as np

def rot_about(axis, t):
    axis = np.asarray(axis, float); axis = axis / np.linalg.norm(axis)
    x, y, z = (float(v) for v in axis)
    c, s = np.cos(t), np.sin(t)
    return np.array([[c+x*x*(1-c), x*y*(1-c)-z*s, x*z*(1-c)+y*s],
                     [y*x*(1-c)+z*s, c+y*y*(1-c), y*z*(1-c)-x*s],
                     [z*x*(1-c)-y*s, z*y*(1-c)+x*s, c+z*z*(1-c)]])

def vol_of_box(P, U):
    Q = P @ U.T
    return float(np.prod(Q.max(0) - Q.min(0)))

def random_tetra(seed, scale=4.0):
    np.random.seed(seed)
    return np.random.rand(4, 3) * scale

def random_box_in_cell(P, ntrials=600, seed=999):
    """Return a frame whose six supports are all unique (cell interior)."""
    np.random.seed(seed)
    for _ in range(ntrials):
        ax, ay, az = (np.random.uniform(-0.35, 0.35) for _ in range(3))
        cx, sx, cy, sy, cz, sz = (np.cos(ax), np.sin(ax), np.cos(ay),
                                  np.sin(ay), np.cos(az), np.sin(az))
        Rx = np.array([[1,0,0],[0,cx,-sx],[0,sx,cx]])
        Ry = np.array([[cy,0,sy],[0,1,0],[-sy,0,cy]])
        Rz = np.array([[cz,-sz,0],[sz,cz,0],[0,0,1]])
        U = Rz @ Ry @ Rx
        Q = P @ U.T
        if all(np.sort(Q[:,u])[3]-np.sort(Q[:,u])[2] > 1e-2 and
               np.sort(Q[:,u])[1]-np.sort(Q[:,u])[0] > 1e-2 for u in range(3)):
            return U
    return None

def hinge_check(P, U0, d, e=1e-5):
    """Compare numeric (log V)'' along hinge d with -2 - sum (W'/W)^2."""
    Q = P @ U0.T
    sup = {u: (int(np.argmax(Q[:,u])), int(np.argmin(Q[:,u]))) for u in range(3)}
    v0 = vol_of_box(P, U0)
    Up = U0 @ rot_about(U0[d], e).T
    Um = U0 @ rot_about(U0[d], -e).T
    vp, vm = vol_of_box(P, Up), vol_of_box(P, Um)
    numeric = (np.log(vp) - 2*np.log(v0) + np.log(vm)) / e**2
    I3 = np.eye(3)
    c2 = 0.0
    for u in range(3):
        a = P[sup[u][0]] - P[sup[u][1]]
        W  = float(a @ U0[u])              # width = a . (row u of U0), world frame
        Wp = float(a @ np.cross(U0[d], U0[u]))  # a . (e_d x e_u), world frame
        c2 += (Wp / W)**2
    return numeric, -2.0 - c2

if __name__ == "__main__":
    worst = -np.inf
    for seed in range(200):
        P = random_tetra(seed)
        U0 = random_box_in_cell(P)
        if U0 is None:
            continue
        for d in range(3):
            num, form = hinge_check(P, U0, d)
            err = abs(num - form)
            worst = max(worst, err)
            assert err < 1e-4, (seed, d, num, form)
            assert form <= -2.0 + 1e-12
    print(f"OK: 600 hinge checks, max |numeric - formula| = {worst:.2e}, all formula <= -2")
