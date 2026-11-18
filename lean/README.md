# MinBox — a Lean 4 proof of Conjecture 7.1

A machine-checked proof that a locally minimal oriented bounding box of a convex polyhedron has
at least three edge–face contacts, two of them on adjacent box faces
(Conjecture 7.1 of J. Jylänki, *An Exact Algorithm for Finding Minimum Oriented Bounding
Boxes*, 2015). It formalizes the argument of [`site/proof.html`](../site/proof.html); [`site/lean-walkthrough.html`](../site/lean-walkthrough.html) walks through the
Lean statements one by one for readers who do not know Lean.

Lean `v4.35.0`, Mathlib `v4.35.0`. No `sorry`; the main theorems depend only on the standard
axioms `propext`, `Classical.choice`, `Quot.sound`.

## Build and check

```
lake exe cache get      # once: fetch prebuilt Mathlib
lake build
lake env lean Verify.lean   # prints the theorem statements and their axioms
```

## What is proved

The polyhedron is a finite set `K` of points of `ℝ³` (its vertices). A box orientation is a
matrix `R ∈ SO3`; the box axes are the columns of `R`.

| Lean name | Meaning |
|---|---|
| `supp K u`, `width K u` | support function and width of `K` in direction `u` |
| `boxVolume K R` | volume of the smallest box with orientation `R` containing `K` |
| `contactSet K u` | the points of `K` on the supporting plane with outward normal `u` |
| `faceNormal R (m, b)` | outward normal of one of the six box faces (`±` the `m`-th column) |
| `HasEdge K R f` | box face `f` touches `K` in at least two points (so along an edge) |
| `HasFace K R f` | box face `f` touches `K` in three non-collinear points (a polygon is flush) |
| `IsEdge K E` | `E` is the point set of an edge: a contact set that is a segment |
| `IsContact K R f E` | edge–face contact: box face `f` contains the edge `E` |

Main theorems (all for `R ∈ SO3` with `0 < boxVolume K R`):

* `three_contacts` (`Main.lean`) — if `R` is a local minimum of `boxVolume K` on `SO3`, then
  two box faces on different axes each contain an edge, and either some box face is flush with
  a polygon or three different box faces each contain an edge.
* `three_edge_face_contacts` (`Count.lean`) — the literal statement: there are three distinct
  pairs (box face, polyhedron edge) with the edge in the face, the first two on faces of
  different axes.
* `three_contacts_of_isMinOn` — the same for a global minimum (the conjecture as stated).
* `exists_minimal_box_with_three_contacts` — if `K` has positive width in every direction, a
  box of minimal volume exists and has the three contacts.

## Files, and how they follow the writeup

| File | Content | Writeup |
|---|---|---|
| `Defs.lean` | definitions, support function, contact sets | §2 |
| `Algebra.lean` | real-number core: `hess` and `hess_nonpos`, `hess_axis_le`, `hess_eq_zero` (Lemma 3); `sq_le_one_of_abs` (Lemma 2); the exact quartic `polyA_sub_polyB` along the two-edge curve, `c2_eq_hess` (its second-order term is `-½ H(ω)`), `quartic_core`; `caseB_algebra` | §4 |
| `Motion.lean` | `eventually_supp_attained` (contact vertices persist), `eventually_width_eq` (`F = G` on `M`), `frame_eventually` (local minimality along a curve of rotations) | §3 |
| `Cases.lean` | `caseA`: rotation about a box axis; `caseB`: the curve keeping two edge contacts | §5, §6 |
| `Main.lean` | case analysis in the box frame, transport to arbitrary `R` | §1, §5, §6 |
| `Existence.lean` | `SO3` is compact, `boxVolume` is continuous, a minimal box exists | — |
| `Count.lean` | a face of a face is a face; a polygon has at least three edges; literal count | §1 |

## Where the formal proof differs from the writeup

The structure is the same; three steps are done differently because they are easier to
formalize.

* **No calculus on SO(3).** Curves of rotations are given by explicit orthogonal frames with
  polynomial entries (normalised afterwards), so every volume comparison becomes a polynomial
  inequality "for all small `t`". The second-order term of that polynomial is exactly
  `-½ H(ω)`.
* **Torque balance without a separating hyperplane.** The symmetry of the contact matrix is
  obtained entry by entry from three one-parameter motions (two coordinate-plane rotations and
  the two-edge curve itself).
* **Diagonal case without AM–GM.** When `H(ω) = 0`, the difference of the two volume
  polynomials along the curve is exactly `6 t⁴`.

Also, every case of the writeup's table except the generic two-edge one is handled by a single
lemma (`caseA`, rotation about a box axis), which needs no bound on `p, q, r` at all.
