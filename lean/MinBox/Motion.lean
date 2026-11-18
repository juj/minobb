import MinBox.Defs

/-!
# Moving the box

Two tools:

* **Persistence of contacts.**  If a direction `N s` tends to `u`, then for small `s` the
  supporting vertex of `K` in direction `N s` belongs to the contact set of `u`.
* **Local minimality along a moving frame.**  A family of pairwise orthogonal vectors
  `N s m` that starts at the standard frame gives, after normalisation, a curve of rotation
  matrices through the identity.  Local minimality of the box volume at the identity then
  yields an inequality between the widths along `N s m` and the lengths of `N s m`.
-/

open Filter Topology Matrix

noncomputable section

namespace MinBox

variable {K : Finset (Fin 3 → ℝ)}

/-! ## Persistence of contacts -/

lemma tendsto_dot {l : Filter ℝ} {f g : ℝ → Fin 3 → ℝ} {a b : Fin 3 → ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun s => f s ⬝ᵥ g s) l (𝓝 (a ⬝ᵥ b)) := by
  simp only [dotProduct]
  exact tendsto_finsetSum _ fun i _ => (tendsto_pi_nhds.1 hf i).mul (tendsto_pi_nhds.1 hg i)

/-- For `N s → u`, the support function at `N s` is eventually attained on the contact set
of `u` (the "contact vertices can only come from the old contact set" step). -/
lemma eventually_supp_attained (hK : K.Nonempty) {N : ℝ → Fin 3 → ℝ} {u : Fin 3 → ℝ}
    (hN : ContinuousAt N 0) (h0 : N 0 = u) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∃ y ∈ contactSet K u, supp K (N s) = y ⬝ᵥ N s := by
  obtain ⟨y0, hy0⟩ := contactSet_nonempty hK u
  have hNt : Tendsto N (𝓝 0) (𝓝 u) := h0 ▸ hN.tendsto
  have key : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ K, ∃ y ∈ contactSet K u, x ⬝ᵥ N s ≤ y ⬝ᵥ N s := by
    refine (Filter.eventually_all_finset K).2 fun x hx => ?_
    by_cases hxc : x ∈ contactSet K u
    · exact Eventually.of_forall fun s => ⟨x, hxc, le_rfl⟩
    · have hlt : x ⬝ᵥ u < y0 ⬝ᵥ u := by
        by_contra hcon
        rw [not_lt] at hcon
        refine hxc (mem_contactSet.2 ⟨hx, fun y hy => ?_⟩)
        exact ((mem_contactSet.1 hy0).2 y hy).trans hcon
      have h1 : Tendsto (fun s => x ⬝ᵥ N s) (𝓝 0) (𝓝 (x ⬝ᵥ u)) :=
        tendsto_dot tendsto_const_nhds hNt
      have h2 : Tendsto (fun s => y0 ⬝ᵥ N s) (𝓝 0) (𝓝 (y0 ⬝ᵥ u)) :=
        tendsto_dot tendsto_const_nhds hNt
      filter_upwards [h1.eventually_lt h2 hlt] with s hs
      exact ⟨y0, hy0, hs.le⟩
  filter_upwards [key] with s hs
  obtain ⟨x, hx, hx'⟩ := exists_eq_supp hK (N s)
  obtain ⟨y, hy, hxy⟩ := hs x hx
  refine ⟨y, hy, le_antisymm (hx' ▸ hxy) (le_supp (contactSet_subset K u hy) _)⟩

/-- For `N s → u`, the width along `N s` is eventually the chord between a vertex of the contact
set of `u` and a vertex of the contact set of `-u`. -/
lemma eventually_width_pair (hK : K.Nonempty) {N : ℝ → Fin 3 → ℝ} {u : Fin 3 → ℝ}
    (hN : ContinuousAt N 0) (h0 : N 0 = u) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∃ P ∈ contactSet K u, ∃ Q ∈ contactSet K (-u),
      width K (N s) = (P - Q) ⬝ᵥ N s := by
  have hN' : ContinuousAt (fun s => -N s) 0 := hN.neg
  have h0' : (fun s => -N s) 0 = -u := by simp [h0]
  filter_upwards [eventually_supp_attained hK hN h0, eventually_supp_attained hK hN' h0']
    with s ⟨P, hP, hP'⟩ ⟨Q, hQ, hQ'⟩
  refine ⟨P, hP, Q, hQ, ?_⟩
  unfold width
  rw [hP', hQ', sub_dotProduct, dotProduct_neg]; ring

/-- If moreover all vertices of each of the two contact sets have the same height along `N s`
(the box face keeps its contact set), the width along `N s` is the chord between any fixed
choice of contact points: this is "`F = G` on `M`". -/
lemma eventually_width_eq (hK : K.Nonempty) {N : ℝ → Fin 3 → ℝ} {u : Fin 3 → ℝ}
    (hN : ContinuousAt N 0) (h0 : N 0 = u) {P Q : Fin 3 → ℝ}
    (hP : ∀ s, ∀ y ∈ contactSet K u, y ⬝ᵥ N s = P ⬝ᵥ N s)
    (hQ : ∀ s, ∀ y ∈ contactSet K (-u), y ⬝ᵥ N s = Q ⬝ᵥ N s) :
    ∀ᶠ s in 𝓝 (0 : ℝ), width K (N s) = (P - Q) ⬝ᵥ N s := by
  filter_upwards [eventually_width_pair hK hN h0] with s ⟨P', hP', Q', hQ', h⟩
  rw [h, sub_dotProduct, sub_dotProduct, hP s P' hP', hQ s Q' hQ']

/-! ## Local minimality along a moving orthogonal frame -/

lemma dot_self_nonneg' (v : Fin 3 → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simp only [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- **Local minimality along a frame.**  Let `N s m` (`m = 0,1,2`) be pairwise orthogonal vectors
depending continuously on `s`, with `N 0 m = eₘ`.  If the identity orientation is a local
minimum of the box volume over `SO(3)`, then for small `s`

`boxVolume K 1 * ∏ ‖N s m‖ ≤ ∏ width K (N s m)`. -/
theorem frame_eventually {N : ℝ → Fin 3 → Fin 3 → ℝ}
    (hcont : ∀ m, ContinuousAt (fun s => N s m) 0)
    (h0 : ∀ m, N 0 m = e m)
    (horth : ∀ s m n, m ≠ n → N s m ⬝ᵥ N s n = 0)
    (hmin : IsLocalMinOn (boxVolume K) SO3 1) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      boxVolume K 1 * ∏ m, √(N s m ⬝ᵥ N s m) ≤ ∏ m, width K (N s m) := by
  set ℓ : ℝ → Fin 3 → ℝ := fun s m => √(N s m ⬝ᵥ N s m) with hℓ
  have hNt : ∀ m, Tendsto (fun s => N s m) (𝓝 0) (𝓝 (e m)) := fun m => h0 m ▸ (hcont m).tendsto
  -- the lengths tend to 1
  have hℓc : ∀ m, Tendsto (fun s => ℓ s m) (𝓝 0) (𝓝 1) := by
    intro m
    have h1 : Tendsto (fun s => N s m ⬝ᵥ N s m) (𝓝 0) (𝓝 (e m ⬝ᵥ e m)) :=
      tendsto_dot (hNt m) (hNt m)
    have h2 := (Real.continuous_sqrt.tendsto (e m ⬝ᵥ e m)).comp h1
    have h3 : √(e m ⬝ᵥ e m) = 1 := by simp [e_apply]
    rw [h3] at h2
    exact h2
  have hpos : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ m, 0 < ℓ s m :=
    Filter.eventually_all.2 fun m => (hℓc m).eventually (lt_mem_nhds one_pos)
  -- the normalised frame as a matrix
  set Q : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun s => Matrix.of fun a m => N s m a / ℓ s m with hQ
  have hQ1 : Tendsto Q (𝓝 0) (𝓝 1) := by
    refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun m => ?_
    have h1 : Tendsto (fun s => N s m a / ℓ s m) (𝓝 0) (𝓝 (e m a / 1)) :=
      (tendsto_pi_nhds.1 (hNt m) a).div (hℓc m) one_ne_zero
    have h2 : (1 : Matrix (Fin 3) (Fin 3) ℝ) a m = e m a / 1 := by
      rw [Matrix.one_apply, e_apply, div_one]
    rw [h2]
    exact h1
  have horthQ : ∀ s, (∀ m, 0 < ℓ s m) → (Q s)ᵀ * Q s = 1 := by
    intro s hs
    ext m n
    have hsum : ((Q s)ᵀ * Q s) m n = (N s m ⬝ᵥ N s n) / (ℓ s m * ℓ s n) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Q, Matrix.of_apply, dotProduct,
        Finset.sum_div]
      refine Finset.sum_congr rfl fun a _ => ?_
      have := (hs m).ne'
      have := (hs n).ne'
      field_simp
    rw [hsum, Matrix.one_apply]
    split_ifs with h
    · subst h
      have hsq : ℓ s m * ℓ s m = N s m ⬝ᵥ N s m := Real.mul_self_sqrt (dot_self_nonneg' _)
      rw [← hsq]
      exact div_self (mul_pos (hs m) (hs m)).ne'
    · rw [horth s m n h, zero_div]
  have hdet : Tendsto (fun s => (Q s).det) (𝓝 0) (𝓝 1) := by
    have h : Tendsto (fun s => (Q s).det) (𝓝 0) (𝓝 (1 : Matrix (Fin 3) (Fin 3) ℝ).det) :=
      ((Continuous.matrix_det continuous_id).tendsto (1 : Matrix (Fin 3) (Fin 3) ℝ)).comp hQ1
    rwa [Matrix.det_one] at h
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), Q s ∈ SO3 := by
    filter_upwards [hpos, hdet.eventually (lt_mem_nhds one_pos)] with s hs hd
    refine ⟨horthQ s hs, ?_⟩
    have h2 : (Q s).det * (Q s).det = 1 := by
      have := congrArg Matrix.det (horthQ s hs)
      simpa [Matrix.det_mul, Matrix.det_transpose] using this
    nlinarith
  have hQt : Tendsto Q (𝓝 0) (𝓝[SO3] 1) := tendsto_nhdsWithin_iff.2 ⟨hQ1, hmem⟩
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), boxVolume K 1 ≤ boxVolume K (Q s) := hQt.eventually hmin
  filter_upwards [hev, hpos] with s hs hl
  have hvol : boxVolume K (Q s) = (∏ m, width K (N s m)) / ∏ m, ℓ s m := by
    unfold boxVolume
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun m _ => ?_
    have hax : axis (Q s) m = (ℓ s m)⁻¹ • N s m := by
      funext a
      simp [axis, Q, div_eq_inv_mul]
    rw [hax, width_smul (inv_nonneg.2 (hl m).le), div_eq_inv_mul]
  rw [hvol, le_div_iff₀ (Finset.prod_pos fun m _ => hl m)] at hs
  exact hs

/-- The frame whose `i`-th, `j`-th and remaining vectors are `a`, `b`, `c`. -/
def frame3 (i j : Fin 3) (a b c : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun m => if m = i then a else if m = j then b else c

/-- `frame_eventually` for three curves attached to three distinct axes `i, j, k`. -/
theorem frame_eventually3 {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {Ni Nj Nk : ℝ → Fin 3 → ℝ}
    (hi : ContinuousAt Ni 0) (hj : ContinuousAt Nj 0) (hk : ContinuousAt Nk 0)
    (hi0 : Ni 0 = e i) (hj0 : Nj 0 = e j) (hk0 : Nk 0 = e k)
    (hoij : ∀ s, Ni s ⬝ᵥ Nj s = 0) (hoik : ∀ s, Ni s ⬝ᵥ Nk s = 0)
    (hojk : ∀ s, Nj s ⬝ᵥ Nk s = 0)
    (hmin : IsLocalMinOn (boxVolume K) SO3 1) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      width K (e i) * width K (e j) * width K (e k) *
          (√(Ni s ⬝ᵥ Ni s) * √(Nj s ⬝ᵥ Nj s) * √(Nk s ⬝ᵥ Nk s)) ≤
        width K (Ni s) * width K (Nj s) * width K (Nk s) := by
  have fi : ∀ a b c : Fin 3 → ℝ, frame3 i j a b c i = a := fun a b c => by simp [frame3]
  have fj : ∀ a b c : Fin 3 → ℝ, frame3 i j a b c j = b := fun a b c => by
    simp [frame3, hij.symm]
  have fk : ∀ a b c : Fin 3 → ℝ, frame3 i j a b c k = c := fun a b c => by
    simp [frame3, hik.symm, hjk.symm]
  have key := frame_eventually (K := K) (N := fun s => frame3 i j (Ni s) (Nj s) (Nk s))
    (by
      intro m
      rcases cases3 hij hik hjk m with rfl | rfl | rfl
      · simpa only [fi] using hi
      · simpa only [fj] using hj
      · simpa only [fk] using hk)
    (by
      intro m
      rcases cases3 hij hik hjk m with rfl | rfl | rfl
      · simpa only [fi] using hi0
      · simpa only [fj] using hj0
      · simpa only [fk] using hk0)
    (by
      intro s m n hmn
      rcases cases3 hij hik hjk m with rfl | rfl | rfl <;>
        rcases cases3 hij hik hjk n with rfl | rfl | rfl <;>
        simp only [fi, fj, fk] <;>
        first
          | exact absurd rfl hmn
          | exact hoij s
          | exact hoik s
          | exact hojk s
          | (rw [dotProduct_comm]; first | exact hoij s | exact hoik s | exact hojk s))
    hmin
  filter_upwards [key] with s hs
  have hV : boxVolume K 1 = width K (e i) * width K (e j) * width K (e k) := by
    unfold boxVolume
    rw [prod3 hij hik hjk]
    simp only [axis_one]
  rw [prod3 hij hik hjk, prod3 hij hik hjk, hV] at hs
  simpa only [fi, fj, fk] using hs

end MinBox
