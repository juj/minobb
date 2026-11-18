import MinBox.Algebra
import MinBox.Motion

/-!
# The two motions that shrink the box

Everything here is in the frame of the box (orientation `1`), for three distinct coordinate
axes `i, j, k`.

* `caseA`: rotation about the axis `i`.  If the four faces of the axes `j` and `k` keep their
  contact sets under that rotation (they touch single vertices, or edges parallel to `eᵢ`),
  the box is not a local minimum.  This covers "all contacts on one pair of opposite faces" and
  the special two-edge configuration of the writeup.
* `caseB`: the curve keeping an edge contact on axis `i` and one on axis `j`, when neither edge
  is parallel to the box edge shared by the two faces.  The box is not a local minimum.
-/

open Filter Topology Matrix

noncomputable section

namespace MinBox

variable {K : Finset (Fin 3 → ℝ)}

/-- **Rotation in the coordinate plane `(j, k)`** (about the axis `i`), in the parametrisation
`N_j = e_j - s e_k`, `N_k = e_k + s e_j`.  Assume the two faces of axis `k` keep their contact
points (`Pk`, `Qk`) under this rotation.  Then local minimality gives, for small `s`, a pair of
contact vertices `P, Q` of the faces `±e_j` whose chord satisfies the displayed inequality. -/
theorem plane_rotation (hK : K.Nonempty) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hwi : 0 < width K (e i))
    (hmin : IsLocalMinOn (boxVolume K) SO3 1)
    {Pk Qk : Fin 3 → ℝ} (hPk : Pk ∈ contactSet K (e k)) (hQk : Qk ∈ contactSet K (-e k))
    (hkp : ∀ y ∈ contactSet K (e k), y j = Pk j)
    (hkm : ∀ y ∈ contactSet K (-e k), y j = Qk j) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∃ P ∈ contactSet K (e j), ∃ Q ∈ contactSet K (-e j),
      width K (e j) * width K (e k) * (1 + s ^ 2) ≤
        (width K (e j) - s * (P k - Q k)) * (width K (e k) + s * (Pk j - Qk j)) := by
  set Nj : ℝ → Fin 3 → ℝ := fun s => lin3 i j k 0 1 (-s) with hNj
  set Nk : ℝ → Fin 3 → ℝ := fun s => lin3 i j k 0 s 1 with hNk
  have cNj : ContinuousAt Nj 0 :=
    (continuous_lin3 i j k continuous_const continuous_const continuous_neg).continuousAt
  have cNk : ContinuousAt Nk 0 :=
    (continuous_lin3 i j k continuous_const continuous_id continuous_const).continuousAt
  have hNj0 : Nj 0 = e j := by simp [Nj, lin3_e_j]
  have hNk0 : Nk 0 = e k := by simp [Nk, lin3_e_k]
  have key := frame_eventually3 (K := K) hij hik hjk (Ni := fun _ => e i) continuousAt_const
    cNj cNk rfl hNj0 hNk0
    (fun s => by simp only [Nj, e_dot]; exact (lin3_apply hij hik hjk 0 1 (-s)).1)
    (fun s => by simp only [Nk, e_dot]; exact (lin3_apply hij hik hjk 0 s 1).1)
    (fun s => by simp only [Nj, Nk]; rw [lin3_dot_lin3 hij hik hjk]; ring)
    hmin
  -- the faces of axis `k` keep their contact points
  have hk_ev := eventually_width_eq hK cNk hNk0 (P := Pk) (Q := Qk)
    (fun s y hy => by
      simp only [Nk, dot_lin3]
      rw [hkp y hy, coord_eq_of_mem_pos hy hPk]; ring)
    (fun s y hy => by
      simp only [Nk, dot_lin3]
      rw [hkm y hy, coord_eq_of_mem_neg hy hQk]; ring)
  -- the faces of axis `j` are supported by some pair of their contact vertices
  have hj_ev := eventually_width_pair hK cNj hNj0
  filter_upwards [key, hk_ev, hj_ev] with s h1 h2 ⟨P, hP, Q, hQ, h3⟩
  refine ⟨P, hP, Q, hQ, ?_⟩
  have a1 : e i ⬝ᵥ e i = 1 := by simp [e_apply]
  have a2 : Nj s ⬝ᵥ Nj s = 1 + s ^ 2 := by
    simp only [Nj]; rw [lin3_dot_lin3 hij hik hjk]; ring
  have a3 : Nk s ⬝ᵥ Nk s = 1 + s ^ 2 := by
    simp only [Nk]; rw [lin3_dot_lin3 hij hik hjk]; ring
  have hs : √(e i ⬝ᵥ e i) * √(Nj s ⬝ᵥ Nj s) * √(Nk s ⬝ᵥ Nk s) = 1 + s ^ 2 := by
    rw [a1, a2, a3, Real.sqrt_one, one_mul, Real.mul_self_sqrt (by positivity)]
  have w2 : width K (Nk s) = width K (e k) + s * (Pk j - Qk j) := by
    rw [h2, width_e_eq hPk hQk]
    simp only [Nk, dot_lin3, Pi.sub_apply]; ring
  have w3 : width K (Nj s) = width K (e j) - s * (P k - Q k) := by
    rw [h3, width_e_eq hP hQ]
    simp only [Nj, dot_lin3, Pi.sub_apply]; ring
  rw [hs, w2, w3] at h1
  refine le_of_mul_le_mul_left ?_ hwi
  linarith

/-- **Case A: rotation about a box axis.**  If the faces of the axes `j` and `k` keep their
contact sets under rotation about `eᵢ` (every contact set of `±e_k` has constant `j`-coordinate
and every contact set of `±e_j` has constant `k`-coordinate), the identity orientation is not a
local minimum of the box volume. -/
theorem caseA (hK : K.Nonempty) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hwi : 0 < width K (e i)) (hwj : 0 < width K (e j)) (hwk : 0 < width K (e k))
    (hmin : IsLocalMinOn (boxVolume K) SO3 1)
    (hkp : ∀ y ∈ contactSet K (e k), ∀ y' ∈ contactSet K (e k), y j = y' j)
    (hkm : ∀ y ∈ contactSet K (-e k), ∀ y' ∈ contactSet K (-e k), y j = y' j)
    (hjp : ∀ y ∈ contactSet K (e j), ∀ y' ∈ contactSet K (e j), y k = y' k)
    (hjm : ∀ y ∈ contactSet K (-e j), ∀ y' ∈ contactSet K (-e j), y k = y' k) : False := by
  obtain ⟨Pk, hPk⟩ := contactSet_nonempty hK (e k)
  obtain ⟨Qk, hQk⟩ := contactSet_nonempty hK (-e k)
  obtain ⟨Pj, hPj⟩ := contactSet_nonempty hK (e j)
  obtain ⟨Qj, hQj⟩ := contactSet_nonempty hK (-e j)
  have h := plane_rotation hK hij hik hjk hwi hmin hPk hQk (fun y hy => hkp y hy Pk hPk)
    (fun y hy => hkm y hy Qk hQk)
  have h' : ∀ᶠ s in 𝓝 (0 : ℝ), width K (e j) * width K (e k) * (1 + s ^ 2) ≤
      (width K (e j) - s * (Pj k - Qj k)) * (width K (e k) + s * (Pk j - Qk j)) := by
    filter_upwards [h] with s ⟨P, hP, Q, hQ, hs⟩
    rwa [hjp P hP Pj hPj, hjm Q hQ Qj hQj] at hs
  generalize width K (e j) = wj at hwj h'
  generalize width K (e k) = wk at hwk h'
  generalize Pj k - Qj k = f at h'
  generalize Pk j - Qk j = g at h'
  -- first order: the two shear ratios agree
  have hfo : f * wk - g * wj = 0 := by
    refine first_order_zero (ρ := fun _ => f * g + wj * wk) continuousAt_const ?_
    filter_upwards [h'] with s hs
    linarith
  -- second order: the volume strictly decreases
  have hne : ∀ᶠ s in 𝓝[≠] (0 : ℝ), s ≠ 0 := self_mem_nhdsWithin
  obtain ⟨s, hs, hs0⟩ := ((h'.filter_mono nhdsWithin_le_nhds).and hne).exists
  have hs2 : 0 < s ^ 2 := by positivity
  have hfg : 0 ≤ f * g := by
    have h1 : f * g * wj = f ^ 2 * wk := by linear_combination (-f) * hfo
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hwj, mul_nonneg (sq_nonneg f) hwk.le]
  have h0 : s * (f * wk - g * wj) = 0 := by rw [hfo, mul_zero]
  nlinarith [mul_pos hs2 (mul_pos hwj hwk), mul_nonneg hs2.le hfg]

/-- **Case B: the curve keeping two edge contacts.**  Suppose the contact sets of the faces
`±eᵢ` are (at most) segments with direction `(0, α, 1)` in the coordinates `(i, j, k)`, those of
`±e_j` are segments with direction `(β, 0, 1)`, and the faces `±e_k` touch single vertices.
Then the identity orientation is not a local minimum of the box volume. -/
theorem caseB (hK : K.Nonempty) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hwi : 0 < width K (e i)) (hwj : 0 < width K (e j)) (hwk : 0 < width K (e k))
    (hmin : IsLocalMinOn (boxVolume K) SO3 1) {α β : ℝ}
    (hip : ∀ y ∈ contactSet K (e i), ∀ y' ∈ contactSet K (e i), y j - y' j = α * (y k - y' k))
    (him : ∀ y ∈ contactSet K (-e i), ∀ y' ∈ contactSet K (-e i),
      y j - y' j = α * (y k - y' k))
    (hjp : ∀ y ∈ contactSet K (e j), ∀ y' ∈ contactSet K (e j), y i - y' i = β * (y k - y' k))
    (hjm : ∀ y ∈ contactSet K (-e j), ∀ y' ∈ contactSet K (-e j),
      y i - y' i = β * (y k - y' k))
    (hkp : ∀ y ∈ contactSet K (e k), ∀ y' ∈ contactSet K (e k), y i = y' i ∧ y j = y' j)
    (hkm : ∀ y ∈ contactSet K (-e k), ∀ y' ∈ contactSet K (-e k), y i = y' i ∧ y j = y' j) :
    False := by
  obtain ⟨Pa, hPa⟩ := contactSet_nonempty hK (e i)
  obtain ⟨Qa, hQa⟩ := contactSet_nonempty hK (-e i)
  obtain ⟨Pj, hPj⟩ := contactSet_nonempty hK (e j)
  obtain ⟨Qj, hQj⟩ := contactSet_nonempty hK (-e j)
  obtain ⟨Pk, hPk⟩ := contactSet_nonempty hK (e k)
  obtain ⟨Qk, hQk⟩ := contactSet_nonempty hK (-e k)
  -- Step 1: first-order conditions from the rotations in the planes (i,k) and (j,k)
  have r1 := plane_rotation hK hij.symm hjk hik hwj hmin hPk hQk
    (fun y hy => (hkp y hy Pk hPk).1) (fun y hy => (hkm y hy Qk hQk).1)
  have b1 := first_order_bounds (contactSet K (e i) ×ˢ contactSet K (-e i))
    ⟨(Pa, Qa), Finset.mem_product.2 ⟨hPa, hQa⟩⟩ (fun pq => pq.1 k - pq.2 k) hwk
    (by
      filter_upwards [r1] with s ⟨P, hP, Q, hQ, hs⟩
      exact ⟨(P, Q), Finset.mem_product.2 ⟨hP, hQ⟩, hs⟩)
  obtain ⟨⟨⟨A, A'⟩, hA, hAlo⟩, ⟨⟨B, B'⟩, hB, hBhi⟩⟩ := b1
  obtain ⟨hA1, hA2⟩ := Finset.mem_product.1 hA
  obtain ⟨hB1, hB2⟩ := Finset.mem_product.1 hB
  have r2 := plane_rotation hK hij hik hjk hwi hmin hPk hQk
    (fun y hy => (hkp y hy Pk hPk).2) (fun y hy => (hkm y hy Qk hQk).2)
  have b2 := first_order_bounds (contactSet K (e j) ×ˢ contactSet K (-e j))
    ⟨(Pj, Qj), Finset.mem_product.2 ⟨hPj, hQj⟩⟩ (fun pq => pq.1 k - pq.2 k) hwk
    (by
      filter_upwards [r2] with s ⟨P, hP, Q, hQ, hs⟩
      exact ⟨(P, Q), Finset.mem_product.2 ⟨hP, hQ⟩, hs⟩)
  obtain ⟨⟨⟨C, C'⟩, hC, hClo⟩, ⟨⟨D, D'⟩, hD, hDhi⟩⟩ := b2
  obtain ⟨hC1, hC2⟩ := Finset.mem_product.1 hC
  obtain ⟨hD1, hD2⟩ := Finset.mem_product.1 hD
  simp only at hAlo hBhi hClo hDhi
  -- Step 2: the curve that keeps both edge contacts
  set Ni : ℝ → Fin 3 → ℝ := fun t => lin3 i j k 1 t (-(α * t)) with hNi
  set Nj : ℝ → Fin 3 → ℝ := fun t => lin3 i j k (-t) (1 + α * β * t) (β * t) with hNj
  set Nk : ℝ → Fin 3 → ℝ := fun t =>
    lin3 i j k (α * t + β * (1 + α ^ 2) * t ^ 2) (-(β * t) + α * t ^ 2)
      (1 + α * β * t + t ^ 2) with hNk
  have cNi : ContinuousAt Ni 0 :=
    (continuous_lin3 i j k (by fun_prop) (by fun_prop) (by fun_prop)).continuousAt
  have cNj : ContinuousAt Nj 0 :=
    (continuous_lin3 i j k (by fun_prop) (by fun_prop) (by fun_prop)).continuousAt
  have cNk : ContinuousAt Nk 0 :=
    (continuous_lin3 i j k (by fun_prop) (by fun_prop) (by fun_prop)).continuousAt
  have hNi0 : Ni 0 = e i := by simp [Ni, lin3_e_i]
  have hNj0 : Nj 0 = e j := by simp [Nj, lin3_e_j]
  have hNk0 : Nk 0 = e k := by simp [Nk, lin3_e_k]
  have key := frame_eventually3 (K := K) hij hik hjk cNi cNj cNk hNi0 hNj0 hNk0
    (fun t => by simp only [Ni, Nj]; rw [lin3_dot_lin3 hij hik hjk]; ring)
    (fun t => by simp only [Ni, Nk]; rw [lin3_dot_lin3 hij hik hjk]; ring)
    (fun t => by simp only [Nj, Nk]; rw [lin3_dot_lin3 hij hik hjk]; ring)
    hmin
  -- all six faces keep their contact sets along the curve
  have hi_ev := eventually_width_eq hK cNi hNi0 (P := Pa) (Q := Qa)
    (fun t y hy => by
      simp only [Ni, dot_lin3]
      linear_combination coord_eq_of_mem_pos hy hPa + t * hip y hy Pa hPa)
    (fun t y hy => by
      simp only [Ni, dot_lin3]
      linear_combination coord_eq_of_mem_neg hy hQa + t * him y hy Qa hQa)
  have hj_ev := eventually_width_eq hK cNj hNj0 (P := Pj) (Q := Qj)
    (fun t y hy => by
      simp only [Nj, dot_lin3]
      linear_combination (1 + α * β * t) * coord_eq_of_mem_pos hy hPj - t * hjp y hy Pj hPj)
    (fun t y hy => by
      simp only [Nj, dot_lin3]
      linear_combination (1 + α * β * t) * coord_eq_of_mem_neg hy hQj - t * hjm y hy Qj hQj)
  have hk_ev := eventually_width_eq hK cNk hNk0 (P := Pk) (Q := Qk)
    (fun t y hy => by
      simp only [Nk, dot_lin3]
      rw [(hkp y hy Pk hPk).1, (hkp y hy Pk hPk).2, coord_eq_of_mem_pos hy hPk])
    (fun t y hy => by
      simp only [Nk, dot_lin3]
      rw [(hkm y hy Qk hQk).1, (hkm y hy Qk hQk).2, coord_eq_of_mem_neg hy hQk])
  -- Step 3: reduce to real numbers
  have mem := fun {u : Fin 3 → ℝ} {x : Fin 3 → ℝ} (hx : x ∈ contactSet K u) =>
    contactSet_subset K u hx
  refine caseB_algebra hwi hwj hwk
    (dij := Pa j - Qa j) (dik := Pa k - Qa k) (dji := Pj i - Qj i) (djk := Pj k - Qj k)
    (dki := Pk i - Qk i) (dkj := Pk j - Qk j) (α := α) (β := β)
    (aj := A j - A' j) (ak := A k - A' k) (aj' := B j - B' j) (ak' := B k - B' k)
    hAlo hBhi
    (by linear_combination hip A hA1 Pa hPa - him A' hA2 Qa hQa)
    (by linear_combination hip B hB1 Pa hPa - him B' hB2 Qa hQa)
    (abs_coord_sub_le (mem hA1) (mem hA2) j) (abs_coord_sub_le (mem hB1) (mem hB2) j)
    (abs_coord_sub_le (mem hA1) (mem hA2) k) (abs_coord_sub_le (mem hB1) (mem hB2) k)
    (bi := C i - C' i) (bk := C k - C' k) (bi' := D i - D' i) (bk' := D k - D' k)
    hClo hDhi
    (by linear_combination hjp C hC1 Pj hPj - hjm C' hC2 Qj hQj)
    (by linear_combination hjp D hD1 Pj hPj - hjm D' hD2 Qj hQj)
    (abs_coord_sub_le (mem hC1) (mem hC2) i) (abs_coord_sub_le (mem hD1) (mem hD2) i)
    (abs_coord_sub_le (mem hC1) (mem hC2) k) (abs_coord_sub_le (mem hD1) (mem hD2) k)
    (abs_coord_sub_le (mem hPk) (mem hQk) i) (abs_coord_sub_le (mem hPk) (mem hQk) j)
    ?_
  filter_upwards [key, hi_ev, hj_ev, hk_ev] with t h0 h1 h2 h3
  have n1 : Ni t ⬝ᵥ Ni t = 1 + (1 + α ^ 2) * t ^ 2 := by
    simp only [Ni]; rw [lin3_dot_lin3 hij hik hjk]; ring
  have n2 : Nj t ⬝ᵥ Nj t = t ^ 2 + (1 + α * β * t) ^ 2 + β ^ 2 * t ^ 2 := by
    simp only [Nj]; rw [lin3_dot_lin3 hij hik hjk]; ring
  have n3 : Nk t ⬝ᵥ Nk t =
      (1 + (1 + α ^ 2) * t ^ 2) * (t ^ 2 + (1 + α * β * t) ^ 2 + β ^ 2 * t ^ 2) := by
    simp only [Nk]; rw [lin3_dot_lin3 hij hik hjk]; ring
  have p1 : (0 : ℝ) ≤ 1 + (1 + α ^ 2) * t ^ 2 := by positivity
  have p2 : (0 : ℝ) ≤ t ^ 2 + (1 + α * β * t) ^ 2 + β ^ 2 * t ^ 2 := by positivity
  have hsqrt : √(Ni t ⬝ᵥ Ni t) * √(Nj t ⬝ᵥ Nj t) * √(Nk t ⬝ᵥ Nk t) = polyA α β t := by
    rw [n1, n2, n3, Real.sqrt_mul p1]
    unfold polyA
    nlinarith [Real.mul_self_sqrt p1, Real.mul_self_sqrt p2]
  have w1 : width K (Ni t) = width K (e i) + t * ((Pa j - Qa j) - α * (Pa k - Qa k)) := by
    rw [h1, width_e_eq hPa hQa]
    simp only [Ni, dot_lin3, Pi.sub_apply]; ring
  have w2 : width K (Nj t) =
      width K (e j) + t * (-(Pj i - Qj i) + α * β * width K (e j) + β * (Pj k - Qj k)) := by
    rw [h2, width_e_eq hPj hQj]
    simp only [Nj, dot_lin3, Pi.sub_apply]; ring
  have w3 : width K (Nk t) =
      width K (e k) * (1 + α * β * t + t ^ 2)
        + (Pk i - Qk i) * (α * t + β * (1 + α ^ 2) * t ^ 2)
        + (Pk j - Qk j) * (-β * t + α * t ^ 2) := by
    rw [h3, width_e_eq hPk hQk]
    simp only [Nk, dot_lin3, Pi.sub_apply]; ring
  rw [hsqrt, w1, w2, w3] at h0
  exact h0

end MinBox
