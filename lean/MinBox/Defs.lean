import Mathlib

/-!
# Bounding boxes of finite point sets in `ℝ³`: definitions

The polyhedron is given by a finite set `K` of points (its vertices; extra points inside the
hull do no harm).  A box orientation is a rotation matrix `R`; the box axes are the columns of
`R`, and the smallest enclosing box with that orientation has volume
`boxVolume K R = ∏ₘ width K (axis R m)`.
-/

open Filter Topology Matrix

noncomputable section

namespace MinBox

open Classical in
/-- Support function of the finite point set `K` (equivalently of its convex hull):
`supp K u = max_{x ∈ K} x · u`. -/
def supp (K : Finset (Fin 3 → ℝ)) (u : Fin 3 → ℝ) : ℝ :=
  if h : K.Nonempty then K.sup' h (fun x => x ⬝ᵥ u) else 0

/-- Width of `K` in direction `u`. -/
def width (K : Finset (Fin 3 → ℝ)) (u : Fin 3 → ℝ) : ℝ := supp K u + supp K (-u)

/-- The `m`-th axis of the box with orientation `R`: the `m`-th column of `R`. -/
def axis (R : Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3) : Fin 3 → ℝ := fun a => R a m

/-- Volume of the smallest box with orientation `R` that contains `K`. -/
def boxVolume (K : Finset (Fin 3 → ℝ)) (R : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∏ m, width K (axis R m)

/-- The rotation group, written out explicitly. -/
def SO3 : Set (Matrix (Fin 3) (Fin 3) ℝ) := {R | Rᵀ * R = 1 ∧ R.det = 1}

open Classical in
/-- The points of `K` on its supporting plane with outward normal `u`: the vertices of the
contact set of `K` with a box face of outward normal `u`. -/
def contactSet (K : Finset (Fin 3 → ℝ)) (u : Fin 3 → ℝ) : Finset (Fin 3 → ℝ) :=
  K.filter (fun x => ∀ y ∈ K, y ⬝ᵥ u ≤ x ⬝ᵥ u)

/-- Outward normal of a box face.  The six faces are indexed by an axis `m` and a sign:
`(m, true)` is the face with outward normal `+R eₘ`, `(m, false)` the opposite one. -/
def faceNormal (R : Matrix (Fin 3) (Fin 3) ℝ) (f : Fin 3 × Bool) : Fin 3 → ℝ :=
  if f.2 then axis R f.1 else -axis R f.1

/-- The box face `f` contains (at least) an edge of the polyhedron: its contact set has two
distinct vertices. -/
def HasEdge (K : Finset (Fin 3 → ℝ)) (R : Matrix (Fin 3) (Fin 3) ℝ) (f : Fin 3 × Bool) : Prop :=
  1 < (contactSet K (faceNormal R f)).card

/-- The box face `f` is flush with a polygonal face of the polyhedron: its contact set has three
non-collinear vertices. -/
def HasFace (K : Finset (Fin 3 → ℝ)) (R : Matrix (Fin 3) (Fin 3) ℝ) (f : Fin 3 × Bool) : Prop :=
  ¬ Collinear ℝ (contactSet K (faceNormal R f) : Set (Fin 3 → ℝ))

/-- Standard basis vector. -/
def e (m : Fin 3) : Fin 3 → ℝ := Pi.single m 1

/-! ## Basic lemmas -/

variable {K : Finset (Fin 3 → ℝ)}

@[simp] lemma dot_e (x : Fin 3 → ℝ) (m : Fin 3) : x ⬝ᵥ e m = x m := by simp [e]

@[simp] lemma e_dot (x : Fin 3 → ℝ) (m : Fin 3) : e m ⬝ᵥ x = x m := by simp [e]

lemma e_apply (m a : Fin 3) : e m a = if a = m then 1 else 0 := by simp [e, Pi.single_apply]

lemma axis_one (m : Fin 3) : axis 1 m = e m := by
  funext a; simp [axis, e, Matrix.one_apply, Pi.single_apply]

lemma supp_of_nonempty (hK : K.Nonempty) (u : Fin 3 → ℝ) :
    supp K u = K.sup' hK (fun x => x ⬝ᵥ u) := by
  simp [supp, hK]

lemma le_supp {x : Fin 3 → ℝ} (hx : x ∈ K) (u : Fin 3 → ℝ) : x ⬝ᵥ u ≤ supp K u := by
  rw [supp_of_nonempty ⟨x, hx⟩]
  exact Finset.le_sup' (fun x => x ⬝ᵥ u) hx

lemma exists_eq_supp (hK : K.Nonempty) (u : Fin 3 → ℝ) : ∃ x ∈ K, supp K u = x ⬝ᵥ u := by
  rw [supp_of_nonempty hK]
  exact Finset.exists_mem_eq_sup' hK _

lemma supp_smul {c : ℝ} (hc : 0 ≤ c) (u : Fin 3 → ℝ) : supp K (c • u) = c * supp K u := by
  by_cases hK : K.Nonempty
  · apply le_antisymm
    · obtain ⟨x, hx, hx'⟩ := exists_eq_supp hK (c • u)
      rw [hx', dotProduct_smul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (le_supp hx u) hc
    · obtain ⟨y, hy, hy'⟩ := exists_eq_supp hK u
      have := le_supp hy (c • u)
      rwa [dotProduct_smul, smul_eq_mul, ← hy'] at this
  · simp [supp, hK]

lemma width_smul {c : ℝ} (hc : 0 ≤ c) (u : Fin 3 → ℝ) : width K (c • u) = c * width K u := by
  unfold width
  rw [← smul_neg, supp_smul hc, supp_smul hc]; ring

lemma width_nonneg (K : Finset (Fin 3 → ℝ)) (u : Fin 3 → ℝ) : 0 ≤ width K u := by
  unfold width
  by_cases hK : K.Nonempty
  · obtain ⟨x, hx⟩ := hK
    have h1 := le_supp hx u
    have h2 := le_supp hx (-u)
    rw [dotProduct_neg] at h2
    linarith
  · simp [supp, hK]

lemma nonempty_of_boxVolume_pos {R : Matrix (Fin 3) (Fin 3) ℝ} (h : 0 < boxVolume K R) :
    K.Nonempty := by
  by_contra hK
  simp [boxVolume, width, supp, hK] at h

lemma width_pos_of_boxVolume_pos {R : Matrix (Fin 3) (Fin 3) ℝ} (h : 0 < boxVolume K R)
    (m : Fin 3) : 0 < width K (axis R m) := by
  rcases (width_nonneg K (axis R m)).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have : boxVolume K R = 0 := Finset.prod_eq_zero (Finset.mem_univ m) heq.symm
    linarith

/-! ## Contact sets -/

lemma mem_contactSet {u x : Fin 3 → ℝ} :
    x ∈ contactSet K u ↔ x ∈ K ∧ ∀ y ∈ K, y ⬝ᵥ u ≤ x ⬝ᵥ u := by
  simp [contactSet]

lemma contactSet_subset (K : Finset (Fin 3 → ℝ)) (u : Fin 3 → ℝ) : contactSet K u ⊆ K :=
  fun _ hx => (mem_contactSet.1 hx).1

lemma dot_eq_supp_of_mem {u x : Fin 3 → ℝ} (hx : x ∈ contactSet K u) : x ⬝ᵥ u = supp K u := by
  obtain ⟨hxK, hmax⟩ := mem_contactSet.1 hx
  obtain ⟨y, hy, hy'⟩ := exists_eq_supp ⟨x, hxK⟩ u
  exact le_antisymm (le_supp hxK u) (hy' ▸ hmax y hy)

lemma contactSet_nonempty (hK : K.Nonempty) (u : Fin 3 → ℝ) : (contactSet K u).Nonempty := by
  obtain ⟨x, hx, hx'⟩ := exists_eq_supp hK u
  exact ⟨x, mem_contactSet.2 ⟨hx, fun y hy => hx' ▸ le_supp hy u⟩⟩

lemma dot_eq_of_mem_contactSet {u x y : Fin 3 → ℝ} (hx : x ∈ contactSet K u)
    (hy : y ∈ contactSet K u) : x ⬝ᵥ u = y ⬝ᵥ u := by
  rw [dot_eq_supp_of_mem hx, dot_eq_supp_of_mem hy]

/-- Two points of the contact set of the face `+eₘ` have the same `m`-th coordinate. -/
lemma coord_eq_of_mem_pos {m : Fin 3} {x y : Fin 3 → ℝ} (hx : x ∈ contactSet K (e m))
    (hy : y ∈ contactSet K (e m)) : x m = y m := by
  simpa using dot_eq_of_mem_contactSet hx hy

/-- Two points of the contact set of the face `-eₘ` have the same `m`-th coordinate. -/
lemma coord_eq_of_mem_neg {m : Fin 3} {x y : Fin 3 → ℝ} (hx : x ∈ contactSet K (-e m))
    (hy : y ∈ contactSet K (-e m)) : x m = y m := by
  simpa using dot_eq_of_mem_contactSet hx hy

/-- The width along a coordinate axis is the coordinate difference of two contact points. -/
lemma width_e_eq {m : Fin 3} {P Q : Fin 3 → ℝ} (hP : P ∈ contactSet K (e m))
    (hQ : Q ∈ contactSet K (-e m)) : width K (e m) = P m - Q m := by
  unfold width
  rw [← dot_eq_supp_of_mem hP, ← dot_eq_supp_of_mem hQ]
  simp; ring

/-- Points of `K` lie in the box: a coordinate difference is at most the width. -/
lemma abs_coord_sub_le {x y : Fin 3 → ℝ} (hx : x ∈ K) (hy : y ∈ K) (m : Fin 3) :
    |x m - y m| ≤ width K (e m) := by
  have h1 := le_supp hx (e m)
  have h2 := le_supp hy (e m)
  have h3 := le_supp hx (-e m)
  have h4 := le_supp hy (-e m)
  simp only [dot_e, dotProduct_neg] at h1 h2 h3 h4
  unfold width
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-! ## Vectors with three prescribed coordinates -/

/-- The vector with coordinates `a, b, c` along the axes `i, j, k`. -/
def lin3 (i j k : Fin 3) (a b c : ℝ) : Fin 3 → ℝ := a • e i + b • e j + c • e k

lemma dot_lin3 (x : Fin 3 → ℝ) (i j k : Fin 3) (a b c : ℝ) :
    x ⬝ᵥ lin3 i j k a b c = a * x i + b * x j + c * x k := by
  simp [lin3, dotProduct_add, dotProduct_smul]

lemma lin3_dot (x : Fin 3 → ℝ) (i j k : Fin 3) (a b c : ℝ) :
    lin3 i j k a b c ⬝ᵥ x = a * x i + b * x j + c * x k := by
  rw [dotProduct_comm, dot_lin3]

section distinct

variable {i j k : Fin 3}

lemma cases3 (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (m : Fin 3) : m = i ∨ m = j ∨ m = k := by
  revert i j k m; decide

lemma prod3 (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (f : Fin 3 → ℝ) :
    ∏ m, f m = f i * f j * f k := by
  have h3 : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2 := by decide
  rw [Fin.prod_univ_three]
  rcases h3 i with rfl | rfl | rfl <;> rcases h3 j with rfl | rfl | rfl <;>
    rcases h3 k with rfl | rfl | rfl <;>
    first | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk | ring

lemma lin3_apply (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b c : ℝ) :
    lin3 i j k a b c i = a ∧ lin3 i j k a b c j = b ∧ lin3 i j k a b c k = c := by
  simp [lin3, e_apply, hij, hik, hjk, hij.symm, hik.symm, hjk.symm]

lemma lin3_dot_lin3 (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b c a' b' c' : ℝ) :
    lin3 i j k a b c ⬝ᵥ lin3 i j k a' b' c' = a * a' + b * b' + c * c' := by
  obtain ⟨h1, h2, h3⟩ := lin3_apply hij hik hjk a b c
  rw [dot_lin3, h1, h2, h3]; ring

lemma lin3_e_i (i j k : Fin 3) : lin3 i j k 1 0 0 = e i := by simp [lin3]

lemma lin3_e_j (i j k : Fin 3) : lin3 i j k 0 1 0 = e j := by simp [lin3]

lemma lin3_e_k (i j k : Fin 3) : lin3 i j k 0 0 1 = e k := by simp [lin3]

end distinct

lemma continuous_lin3 (i j k : Fin 3) {a b c : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) : Continuous fun s => lin3 i j k (a s) (b s) (c s) := by
  unfold lin3; fun_prop

end MinBox
