import numpy as np

def hessian_check(P, U0, sup):
    """M = sym(A) - 3I - K^T K  ;  returns max eigenvalue.
    A columns: a_u^b/W_u ; K: c(omega) = K omega, c_u = a_u^b.(omega x e_u)/W_u."""
    I3 = np.eye(3)
    cols = []; K = np.zeros((3,3))
    for u in range(3):
        a = P[sup[u][0]]-P[sup[u][1]]
        ab = U0.T @ a
        W = float(ab @ U0[u])   # a . (row u)
        cols.append(ab/W)
        for v in range(3):
            K[u,v] = float(ab @ np.cross(I3[v], I3[u]))/W
    A = np.column_stack(cols)
    M = 0.5*(A + A.T) - 3*np.eye(3) - K.T@K
    return M

def random_tetra(seed):
    np.random.seed(seed)
    return np.random.rand(4,3)*4

def random_box(P, tries=400):
    np.random.seed(12345)
    for _ in range(tries):
        ax = np.random.uniform(-0.35,0.35)
        ay = np.random.uniform(-1.2,1.2)
        az = np.random.uniform(-0.35,0.35)
        cx,sx,cy,sy,cz,sz = np.cos(ax),np.sin(ax),np.cos(ay),np.sin(ay),np.cos(az),np.sin(az)
        Rx = np.array([[1,0,0],[0,cx,-sx],[0,sx,cx]])
        Ry = np.array([[cy,0,sy],[0,1,0],[-sy,0,cy]])
        Rz = np.array([[cz,-sz,0],[sz,cz,0],[0,0,1]])
        U = Rz@Ry@Rx
        Q = P @ U.T
        if all(np.sort(Q[:,u])[3]-np.sort(Q[:,u])[2] > 1e-2 and np.sort(Q[:,u])[1]-np.sort(Q[:,u])[0] > 1e-2 for u in range(3)):
            return U
    return None

worst = -np.inf; worstcase = None
n_checked = 0
for seed in range(300):
    P = random_tetra(seed)
    U = random_box(P)
    if U is None: continue
    Q = P @ U.T
    sup = {u: (int(np.argmax(Q[:,u])), int(np.argmin(Q[:,u]))) for u in range(3)}
    M = hessian_check(P, U, sup)
    ev = np.linalg.eigvalsh(M)
    n_checked += 1
    if ev[2] > worst:
        worst = ev[2]; worstcase = (seed, ev.copy())
print(f"checked {n_checked} boxes in cell interiors of 300 random tetrahedra")
print(f"worst (largest) Hessian eigenvalue: {worst:.6f} at case {worstcase[0]}, eigs {worstcase[1]}")
