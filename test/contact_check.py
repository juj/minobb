"""
Independent global-minimum search + edge-face contact counter.
Re-verification of the numerical evidence in proof_conjecture_7_1.md.

Pipeline per tetrahedron (all tetrahedron vertex pairs are edges):
  1. coarse SO(3) Euler grid -> top K candidates
  2. Nelder-Mead refinement (3 params, log V)
  3. dense verification grid: assert no frame beats V_best
  4. count edge-face contacts of the winning box
"""
import numpy as np
from scipy.optimize import minimize

def frames_from_euler(axs, ays, azs):
    """Cartesian product -> (N,3,3) array of frames."""
    axs, ays, azs = np.meshgrid(axs, ays, azs, indexing='ij')
    ax, ay, az = axs.ravel(), ays.ravel(), azs.ravel()
    cx, sx = np.cos(ax), np.sin(ax)
    cy, sy = np.cos(ay), np.sin(ay)
    cz, sz = np.cos(az), np.sin(az)
    F = np.zeros((len(ax), 3, 3))
    # Rx
    F[:,1,1] = cx;  F[:,1,2] = -sx;  F[:,2,1] = sx;  F[:,2,2] = cx
    # multiply Ry (from left): R = Ry Rx
    R = F.copy()
    R[:,0,0] = cy*F[:,0,0];              R[:,0,1] = cy*F[:,0,1];              R[:,0,2] = cy*F[:,0,2]
    R[:,1,0] = sy*F[:,2,0];              R[:,1,1] = sy*F[:,2,1] + F[:,1,1];   R[:,1,2] = sy*F[:,2,2] + F[:,1,2]
    R[:,2,0] = -sy*F[:,0,0];             R[:,2,1] = -sy*F[:,0,1];             R[:,2,2] = -sy*F[:,0,2]
    # multiply Rz (from left): R = Rz Ry Rx
    G = np.empty_like(R)
    G[:,0,0] = cz*R[:,0,0] - sz*R[:,1,0]
    G[:,0,1] = cz*R[:,0,1] - sz*R[:,1,1]
    G[:,0,2] = cz*R[:,0,2] - sz*R[:,1,2]
    G[:,1,0] = sz*R[:,0,0] + cz*R[:,1,0]
    G[:,1,1] = sz*R[:,0,1] + cz*R[:,1,1]
    G[:,1,2] = sz*R[:,0,2] + cz*R[:,1,2]
    G[:,2,:] = R[:,2,:]
    return G

def vols(P, F):
    """V for each frame: (N,)"""
    Q = F @ P.T          # (N,3,4): Q[f,u,i]
    return (Q.max(2) - Q.min(2)).prod(1)

def vol_one(P, U):
    Q = P @ U.T
    return float(np.prod(Q.max(0) - Q.min(0)))

def frame_one(ax, ay, az):
    cx, sx, cy, sy, cz, sz = (np.cos(ax), np.sin(ax), np.cos(ay),
                              np.sin(ay), np.cos(az), np.sin(az))
    Rx = np.array([[1,0,0],[0,cx,-sx],[0,sx,cx]])
    Ry = np.array([[cy,0,sy],[0,1,0],[-sy,0,cy]])
    Rz = np.array([[cz,-sz,0],[sz,cz,0],[0,0,1]])
    return Rz @ Ry @ Rx

def rotvec_to_mat(t):
    ang = np.linalg.norm(t)
    if ang < 1e-12:
        return np.eye(3)
    x, y, z = t / ang
    c, s = np.cos(ang), np.sin(ang)
    return (c*np.eye(3) + (1-c)*np.outer(t/ang, t/ang) + s*np.array([
        [0,-z,y],[z,0,-x],[-y,x,0]]))

def logvol_local(P, U0, t):
    U = U0 @ rotvec_to_mat(t).T
    return np.log(max(vol_one(P, U), 1e-300))

def count_contacts(P, U, eps=2e-5):
    n = len(P)
    Q = P @ U.T
    W = Q.max(0) - Q.min(0)
    contacts = []
    for i in range(n):
        for j in range(i+1, n):
            for u in range(3):
                hi, lo = Q[:,u].max(), Q[:,u].min()
                if abs(Q[i,u]-Q[j,u]) < eps*W[u] and Q[i,u] > hi - eps*W[u]:
                    contacts.append(((i,j), (u, '+')))
                if abs(Q[i,u]-Q[j,u]) < eps*W[u] and Q[i,u] < lo + eps*W[u]:
                    contacts.append(((i,j), (u, '-')))
    return contacts

def solve(P):
    F1 = frames_from_euler(np.linspace(0, np.pi, 10, endpoint=False),
                           np.linspace(0, 2*np.pi, 20, endpoint=False),
                           np.linspace(0, 2*np.pi, 20, endpoint=False))
    v1 = vols(P, F1)
    idx = np.argsort(v1)[:12]
    cands = []
    for k in idx:
        U0 = F1[k]
        r = minimize(lambda t: logvol_local(P, U0, t), np.zeros(3),
                     method='Nelder-Mead',
                     options=dict(xatol=1e-13, fatol=1e-15, maxiter=6000,
                                  initial_simplex=np.array([[0,0,0],[.05,0,0],[0,.05,0],[0,0,.05]])))
        U = U0 @ rotvec_to_mat(r.x).T
        cands.append((vol_one(P, U), U))
    cands.sort(key=lambda c: c[0])
    v_best, U_best = cands[0]
    F2 = frames_from_euler(np.linspace(0, np.pi, 20, endpoint=False),
                           np.linspace(0, 2*np.pi, 40, endpoint=False),
                           np.linspace(0, 2*np.pi, 40, endpoint=False))
    worst = float(vols(P, F2).min())
    return v_best, U_best, worst >= v_best*(1-2e-3), count_contacts(P, U_best)

if __name__ == "__main__":
    from collections import Counter
    cnt = Counter()
    bad = 0
    for seed in range(500, 540):
        np.random.seed(seed)
        P = np.random.rand(4, 3) * 4
        v, U, ok, contacts = solve(P)
        cnt[len(contacts)] += 1
        if not ok:
            bad += 1
            print(f"seed {seed}: VERIFICATION FAILED v={v:.6f} contacts={len(contacts)}")
        if len(contacts) < 3:
            print(f"seed {seed}: *** <3 contacts: {contacts}")
    print(f"40 fresh tetrahedra (seeds 500-539): contact histogram {dict(cnt)}, "
          f"verification failures: {bad}")
