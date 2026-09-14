# On Conjecture 7.1 of Jylänki (2015)
## "Minimum-volume OBBs of convex polyhedra" — a partial proof

**Conjecture 7.1 (Jylänki 2015, open problem).** *A box of minimum volume
circumscribing a convex polyhedron has at least three edge–face contacts,
at least two of them on adjacent faces of the box.*

An **edge–face contact** is a pair (e, F) consisting of an edge e of the
polyhedron and a face F of the box such that e ⊂ F (the face contains the
whole edge).  If a polyhedron edge is flush with a *box edge* (category D of
the paper), it lies in **two** adjacent box faces and therefore contributes
**two** edge–face contacts.

### Status after this work

| Part of the conjecture | Status |
|---|---|
| (b) ≥ 2 edge–face contacts on **adjacent** faces | **Proven** — this is Theorem 2.1 of the paper, proved by O'Rourke (1985) |
| (a) no minimum box with **0** contacts | **Proven here** (Theorem 2 below) |
| (a) no minimum box with **1** contact | **Proven here** (Theorem 3 below) |
| (a) no minimum box with **exactly 2** contacts | **Open** — the irreducible core of the conjecture (Section 5) |

So the conjecture is reduced to a single, sharp statement:

> **Remaining gap.** A global minimum of the volume cannot have exactly two
> edge–face contacts (which, by O'Rourke's theorem, would have to lie on
> adjacent box faces).

All numerical experiments (300+ tetrahedra, random polytopes, prisms — every
global minimum re-verified by an independent SO(3) grid search) found only
3- or 4-contact global minima, with zero counterexamples.

---

## 1. Setup and notation

Let P = {p_0,…,p_{n−1}} be the vertex set of a convex polyhedron in R³ (in
all experiments: strictly convex, e.g. a tetrahedron).  A box orientation is
an orthonormal frame U ∈ SO(3) whose **rows** ê_0, ê_1, ê_2 are the box axes.
With Q = P Uᵀ (so Q[i,u] = p_i·ê_u, i.e. **world→box is v ↦ U v**), the box
widths and volume are

    W_u(U) = max_i Q[i,u] − min_i Q[i,u],      V(U) = W_0 W_1 W_2.

A **support** of face u± is the vertex (or edge) attaining max/min of Q[:,u].
A **no-flush cell** is the open set of frames for which all six faces have a
*unique vertex* support and no edge is flush with any face; its interior
boxes have **zero** edge–face contacts.  A **1-contact stratum** is the set
of frames with exactly one flush edge e ⊂ face d+ (the other five faces
having unique vertex supports); a **2-contact stratum** likewise has two
flush edges on two (necessarily distinct) faces.

**Hinge curves.** For a box U and an axis index d, let

    L_d(t) = U · rot_about(ê_d, t)ᵀ ,   t ∈ R,

i.e. the box is rotated by angle t about its **own** axis d (rows of
L_d(t):  ê_u(t) = Rot_{ê_d}(t) ê_u, with Rot_{ê_d}(0) = I).  L_d is a
1-parameter curve in SO(3) through U, and L_d(t) keeps face d's normal fixed.

---

## 2. The hinge identity (the main technical lemma)

**Lemma 1 (width kinematics).**  Let L_d be a hinge curve and let the
supports of all six faces be fixed (as they are in a neighbourhood of any
cell-interior box, and one-sidedly at contact boxes).  Write a_u = p⁺_u − p⁻_u
for the support chord of face u and W_u = a_u·ê_u.  Then, with
c_u := a_u·(ê_d × ê_u),

    W_u(t) = W_u cos t + c_u sin t + (1 − cos t)(a_u·ê_d)(ê_d·ê_u),
    W'_u(0) = c_u,
    W''_u(0) = (1 − δ_du)·(−W_u) + δ_du·W_u  =  δ_du W_u − W_u.

*Proof.*  ê_u(t) = Rot_{ê_d}(t) ê_u.  By Rodrigues' formula,
Rot_{ê_d}(t) x = x cos t + (ê_d × x) sin t + ê_d(ê_d·x)(1 − cos t); insert
x = ê_u and contract with a_u.  Differentiate twice.  ∎

**Theorem 1 (hinge identity).**  Let U be a box in the interior of a
no-flush cell.  Then, for each hinge d = 0,1,2,

    (log V)″_{L_d}(0)  =  −2 − Σ_u ( c_u / W_u )²   ≤  −2  <  0,
                          c_u = a_u·(ê_d × ê_u).

*Proof.*  log V = Σ_u log W_u, and at a smooth point
(log W_u)″ = W″_u/W_u − (W′_u/W_u)².  By Lemma 1,
W″_u/W_u = δ_du − 1 and W′_u/W_u = c_u/W_u.  Hence

    (log V)″ = Σ_u (δ_du − 1) − Σ_u (c_u/W_u)²  =  (1 − 3) − Σ_u (c_u/W_u)².  ∎

The same computation, applied one-sidedly (t → 0⁺ or 0⁻) with the supports
resolved on that side, holds at every box where the six supports become
unique in one direction — in particular at 1- and 2-contact boxes, where
log V is C² up to the contact face from each side.

**Numerical verification.**  `hinge_verify.py` checks the identity against
central finite differences on 200 random tetrahedra × 3 hinges:
`max |numeric − formula| = 3.8e-05` (pure FD error), and every formula value
is ≤ −2.  (The earlier "full Hessian negative definite" claim of the first
draft of this work was **false** — the full 3×3 Hessian of log V in a cell
interior can have positive eigenvalues, e.g. +209 on a nearly-degenerate
tetrahedron; the hinge-restricted identity above is the correct and
sufficient statement.)

---

## 3. Theorem 2: no local minimum has zero contacts

**Theorem 2.** *If U is a local minimum of V on SO(3), then U is **not** in
the interior of a no-flush cell; i.e. a local-minimum box has at least one
edge–face contact.*

*Proof.*  Take any hinge L_d through U.  By Theorem 1, f(t) := log V(L_d(t))
satisfies f″(0) ≤ −2 < 0.  Since U is a cell-interior point, f is C² at 0,
so t = 0 is a strict local **maximum** of f, i.e. V(L_d(t)) < V(U) for all
small t ≠ 0.  U is therefore not a local minimum of V.  ∎

---

## 4. Theorem 3: no local minimum has exactly one contact

**Theorem 3.** *A local minimum of V cannot have exactly one edge–face
contact.*

*Proof.*  Let U* have exactly one contact: a polyhedron edge (a,b) ⊂ face d+
(so (a−b)·ê_d = 0, a·ê_d = b·ê_d = max_i p_i·ê_d, and no other point of the
polyhedron lies on that face), all other faces having unique vertex
supports.  Consider the hinge L_d(t) = U*·rot_about(ê_d,t)ᵀ about the
**contact axis** d.

1. **The hinge stays on the 1-contact stratum.**  Since ê_d(t) ≡ ê_d, both
   endpoints still satisfy a·ê_d(t) = b·ê_d(t) = a·ê_d = b·ê_d, so the face
   still contains exactly the edge (a,b) (uniqueness of the other five
   supports is an open condition).  Hence L_d(t) has exactly one contact for
   all small t.
2. **V is C² along the hinge.**  W_d(t) = a·ê_d − p_m·ê_d(t) (m = opposite
   support, fixed) is **constant** in t; for u ≠ d, Lemma 1 gives
   W_u(t) = W_u cos t + c_u sin t + O(t²), C².  Thus log V|_{L_d} is C² at 0.
3. **Negative curvature.**  With W′_d = W″_d = 0, the same computation as in
   Theorem 1 gives
       (log V)″_{L_d}(0) = Σ_{u≠d} ( −1 − (c_u/W_u)² )  ≤  −2 < 0.

So log V|_{L_d} has a strict local maximum at 0, and V(L_d(t)) < V(U*) for
small t ≠ 0 — contradicting local minimality.  ∎

---

## 5. What remains: the exactly-two-contact case

By O'Rourke's theorem (Theorem 2.1 of the paper), a *global* minimum has at
least two edge–face contacts on **adjacent** faces.  Combined with
Theorems 2–3, Conjecture 7.1 is therefore **equivalent** to:

> **(∗)  A global minimum of V cannot have exactly two edge–face contacts.**

A hypothetical minimum box U* satisfying (∗) would look like this: flush
edges e_1 = (a_1,b_1) ⊂ face 0⁺ and e_2 = (a_2,b_2) ⊂ face 1⁺ (adjacent
faces, sharing box edge 0∩1), all other faces with unique vertex supports;
the 2-contact stratum S = {h_1 = h_2 = 0} (h_i the flush equations) is a
smooth 1‑dimensional curve through U*, and local minimality forces the KKT
conditions

    (i)   ∇V(U*) = λ_1 ∇h_1(U*) + λ_2 ∇h_2(U*),     λ_i ≥ 0,
    (ii)  the Hessian of V is non-negative on the tangent line of S,
    (iii) one-sided hinge identity: for every hinge d,
          (log V)″_{L_d}(0⁺) ≤ −2 and (log V)″_{L_d}(0⁻) ≤ −2.

Condition (iii) shows the precise *shape* such a minimum must have: along
every hinge through U*, log V has a **corner** with strictly positive
right derivative and strictly negative left derivative (a cusp-shaped
minimum), because a one-sided second derivative ≤ −2 forbids both a flat
touch and a smooth local minimum.  This is consistent with all local
analysis — which is why the case resists the arguments that settle the
0- and 1-contact cases — and it matches O'Rourke's remark that 2-contact
*local* minima may exist; the conjecture only asks to exclude them from
being **global** minima.

### Numerical evidence for (∗)

* **Tetrahedra, fresh run (this work).** `contact_check.py`: 40 random
  tetrahedra (seeds 500–539).  Pipeline: coarse SO(3) Euler grid (4000
  frames) → top-12 Nelder–Mead refinement in local rotation-vector
  coordinates → dense verification grid (32 000 frames, asserted no frame
  beats the refined minimum) → contact count.
  Result: **histogram {3 contacts: 33, 4 contacts: 7}, zero boxes with < 3
  contacts, zero verification failures.**  The 4-contact cases are boxes
  with a whole polyhedron face flush (category C).
* **Tetrahedra, earlier runs (same pipeline family, wall-flush
  parameterization + grid + NM + 3D refinement + independent SO(3) grid
  verification):** 200 + 100 + 30 more tetrahedra, same picture —
  {3: ≈ 90 %, 4: ≈ 10 %}, **no counterexample in > 300 bodies**.
* **Random polytopes & prisms** (12 + 40 bodies, earlier runs): global
  minima always have exactly 3 (or 4 for face-flush) contacts.
* The eight `case_seed*.txt` files in this repository are **algorithmic**
  failure cases (the paper's algorithm misses a candidate), verified by
  `testobb.cpp`/`findcase.cpp`; none of them is a counterexample to the
  conjecture.

---

## 6. Conclusions

1. **Proven (new):** no local minimum of the minimum-volume OBB problem has
   0 or 1 edge–face contact (Theorems 2–3, via the hinge identity of
   Theorem 1: `(log V)″ = −2 − Σ(c_u/W_u)² ≤ −2`).
2. **Proven (O'Rourke 1985, cited as Theorem 2.1):** every global minimum
   has ≥ 2 edge–face contacts on adjacent faces.
3. **Open (reduced form of Conjecture 7.1):** a global minimum cannot have
   exactly 2 edge–face contacts.  Any proof of (∗) would settle the
   conjecture completely.  Extensive numerical evidence (300+ bodies)
   supports it, and the KKT characterization above pins down exactly what a
   counterexample would have to satisfy.

### Reproducibility

* `hinge_verify.py` — verifies the hinge identity on 200 random tetrahedra
  (600 hinge checks, agreement to FD error, all values ≤ −2).
* `contact_check.py` — the 40-tetrahedron global-minimum contact-count
  experiment (seeds 500–539; {3: 33, 4: 7}; zero counterexamples).
* `hessian_test.py` — documents the failure of the stronger (false)
  "full Hessian negative definite" claim (worst eigenvalue +208.66 on a
  nearly-degenerate tetrahedron).
* The global-minimum contact counts were produced by a wall-flush
  enumeration (edge–face-flush parameterization + grid + Nelder–Mead +
  3D refinement + independent SO(3) grid verification); no counterexample
  to Conjecture 7.1 was found in any experiment.
