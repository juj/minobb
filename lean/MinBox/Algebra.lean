import Mathlib

/-!
# Real-number lemmas behind the three-contact theorem

Everything in this file is about real numbers only.  It contains

* the quadratic form `hess` (the Hessian `H` of the writeup) and Lemma 3:
  it is negative semidefinite when the off-diagonal contact ratios satisfy `p², q², r² ≤ 1`,
  with the equality ("diagonal") case;
* the polynomials `polyA`, `polyB` that give the squared-length product and the six-point box
  volume along the curve that keeps two edge contacts, and their exact expansion;
* `quartic_core`: along that curve the six-point volume is strictly smaller for small `t ≠ 0`;
* the first-order lemmas used to extract the torque balance from local minimality.
-/

open Filter Topology

namespace MinBox

/-! ## The Hessian quadratic form -/

/-- The quadratic form `H(ω)` of the writeup, for a symmetric contact matrix with unit diagonal
and off-diagonal entries `p = X₁₂`, `q = X₁₃`, `r = X₂₃`, evaluated at `ω = (w1, w2, w3)`. -/
def hess (p q r w1 w2 w3 : ℝ) : ℝ :=
  -2 * (w1 ^ 2 + w2 ^ 2 + w3 ^ 2) + 2 * (p * w1 * w2 + q * w1 * w3 + r * w2 * w3)
    - (p * w3 - q * w2) ^ 2 - (r * w1 - p * w3) ^ 2 - (q * w2 - r * w1) ^ 2

/-- `H` written as minus a sum of terms that are non-negative when `p², q², r² ≤ 1`. -/
lemma hess_eq (p q r w1 w2 w3 : ℝ) :
    hess p q r w1 w2 w3 =
      -((w1 - p * w2) ^ 2 + (1 - p ^ 2) * w2 ^ 2 + (w1 - q * w3) ^ 2 + (1 - q ^ 2) * w3 ^ 2
        + (w2 - r * w3) ^ 2 + (1 - r ^ 2) * w3 ^ 2
        + (p * w3 - q * w2) ^ 2 + (r * w1 - p * w3) ^ 2 + (q * w2 - r * w1) ^ 2) := by
  unfold hess; ring

/-- **Lemma 3 (first half).** The Hessian is negative semidefinite. -/
theorem hess_nonpos {p q r : ℝ} (hp : p ^ 2 ≤ 1) (hq : q ^ 2 ≤ 1) (hr : r ^ 2 ≤ 1)
    (w1 w2 w3 : ℝ) : hess p q r w1 w2 w3 ≤ 0 := by
  rw [hess_eq]
  have h1 : 0 ≤ (1 - p ^ 2) * w2 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ (1 - q ^ 2) * w3 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 0 ≤ (1 - r ^ 2) * w3 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  linarith [sq_nonneg (w1 - p * w2), sq_nonneg (w1 - q * w3), sq_nonneg (w2 - r * w3),
    sq_nonneg (p * w3 - q * w2), sq_nonneg (r * w1 - p * w3), sq_nonneg (q * w2 - r * w1)]

/-- **Lemma 3 (axis directions).** `H(e_i) ≤ -2`, with no assumption on `p, q, r`. -/
theorem hess_axis_le (p q r : ℝ) :
    hess p q r 1 0 0 ≤ -2 ∧ hess p q r 0 1 0 ≤ -2 ∧ hess p q r 0 0 1 ≤ -2 := by
  unfold hess
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg p, sq_nonneg q, sq_nonneg r]

/-- **Lemma 3 (equality case).** If `H(ω) = 0` then every term of `hess_eq` vanishes. -/
theorem hess_eq_zero {p q r : ℝ} (hp : p ^ 2 ≤ 1) (hq : q ^ 2 ≤ 1) (hr : r ^ 2 ≤ 1)
    {w1 w2 w3 : ℝ} (h : hess p q r w1 w2 w3 = 0) :
    w1 = p * w2 ∧ w1 = q * w3 ∧ w2 = r * w3 ∧
      (1 - p ^ 2) * w2 ^ 2 = 0 ∧ (1 - q ^ 2) * w3 ^ 2 = 0 ∧ (1 - r ^ 2) * w3 ^ 2 = 0 := by
  rw [hess_eq] at h
  have h1 : 0 ≤ (1 - p ^ 2) * w2 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ (1 - q ^ 2) * w3 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 0 ≤ (1 - r ^ 2) * w3 ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have s1 := sq_nonneg (w1 - p * w2)
  have s2 := sq_nonneg (w1 - q * w3)
  have s3 := sq_nonneg (w2 - r * w3)
  have s4 := sq_nonneg (p * w3 - q * w2)
  have s5 := sq_nonneg (r * w1 - p * w3)
  have s6 := sq_nonneg (q * w2 - r * w1)
  have e1 : (w1 - p * w2) ^ 2 = 0 := by linarith
  have e2 : (w1 - q * w3) ^ 2 = 0 := by linarith
  have e3 : (w2 - r * w3) ^ 2 = 0 := by linarith
  refine ⟨?_, ?_, ?_, by linarith, by linarith, by linarith⟩
  · have := pow_eq_zero_iff (two_ne_zero) |>.1 e1; linarith
  · have := pow_eq_zero_iff (two_ne_zero) |>.1 e2; linarith
  · have := pow_eq_zero_iff (two_ne_zero) |>.1 e3; linarith

/-- The diagonal case in the normalisation `ω = (β, α, 1)` used below: the contact matrix is
`±` the all-ones pattern and `ω` is a space diagonal `(±1, ±1, 1)`. -/
lemma diag_of_hess_eq_zero {p q r α β : ℝ} (hp : p ^ 2 ≤ 1) (hq : q ^ 2 ≤ 1) (hr : r ^ 2 ≤ 1)
    (h : hess p q r β α 1 = 0) :
    α ^ 2 = 1 ∧ β ^ 2 = 1 ∧ q = β ∧ r = α ∧ p = α * β := by
  obtain ⟨h1, h2, h3, -, h5, h6⟩ := hess_eq_zero hp hq hr h
  have hβ : β = q := by linarith
  have hα : α = r := by linarith
  have hq1 : q ^ 2 = 1 := by linarith
  have hr1 : r ^ 2 = 1 := by linarith
  refine ⟨by rw [hα]; exact hr1, by rw [hβ]; exact hq1, hβ.symm, hα.symm, ?_⟩
  -- β = p α and α² = 1 give p = α β
  have : α * β = p * α ^ 2 := by rw [h1]; ring
  rw [this, hα, hr1, mul_one]

/-! ## The volume polynomials along the two-edge curve -/

/-- Product of the squared lengths of the first two frame vectors of the two-edge curve
(the third has squared length equal to this product). -/
def polyA (α β t : ℝ) : ℝ :=
  (1 + (1 + α ^ 2) * t ^ 2) * (t ^ 2 + (1 + α * β * t) ^ 2 + β ^ 2 * t ^ 2)

/-- Normalised six-point box volume `∏ (xₘ · Nₘ(t))` along the two-edge curve, for contact
ratios `X₁₂ = p1`, `X₂₁ = p2`, `X₁₃ = X₃₁ = q`, `X₂₃ = X₃₂ = r`. -/
def polyB (α β p1 p2 q r t : ℝ) : ℝ :=
  (1 + (p1 - α * q) * t) * (1 + (-p2 + α * β + β * r) * t) *
    (1 + (α * q - β * r + α * β) * t + (1 + q * β * (1 + α ^ 2) + r * α) * t ^ 2)

/-- Coefficient of `t²` in `polyA - polyB`. -/
def c2 (α β p1 p2 q r : ℝ) : ℝ :=
  α^2*q^2 + α^2 - 2*α*β*p1 + α*β*p2 - α*β*q*r - α*p1*q - α*r + β^2*r^2 + β^2 - β*p2*r - β*q
    + p1*p2 + 1

/-- Coefficient of `t³` in `polyA - polyB`. -/
def c3 (α β p1 p2 q r : ℝ) : ℝ :=
  2*α^3*β*q^2 + 2*α^3*β - α^2*β^2*p1 - α^2*β^2*q*r - 2*α^2*β*p1*q + α^2*β*q^2*r - α^2*β*r
    - α^2*p2*q^2 + α^2*q*r - α*β^2*q*r^2 - α*β^2*q + α*β*p1*p2 - α*β*p1*q*r + α*β*p2*q*r
    + α*β*q^2 - α*β*r^2 + α*β + α*p1*p2*q - α*p1*r + α*p2*r + α*q + β^2*p1*r^2 - β^2*q*r
    - β*p1*p2*r - β*p1*q + β*p2*q - β*r - p1 + p2

/-- Coefficient of `t⁴` in `polyA - polyB`. -/
def c4 (α β p1 p2 q r : ℝ) : ℝ :=
  α^4*β^2*q^2 + α^4*β^2 - α^3*β^2*p1*q + α^3*β^2*q^2*r - α^3*β*p2*q^2 + α^3*β*q*r
    - α^2*β^2*p1*q*r + α^2*β^2*q^2 + 2*α^2*β^2 + α^2*β*p1*p2*q - α^2*β*p1*r + α^2*β*q*r^2
    + α^2*β*q - α^2*p2*q*r + α^2 - α*β^2*p1*q + α*β^2*q^2*r - α*β*p1*r^2 - α*β*p1 - α*β*p2*q^2
    + α*β*q*r + α*p1*p2*r - α*p2*q - β^2*p1*q*r + β^2 + β*p1*p2*q - β*p1*r + p1*p2 + 1

/-- Exact expansion of `polyA - polyB`: it is a quartic in `t` without constant term. -/
lemma polyA_sub_polyB (α β p1 p2 q r t : ℝ) :
    polyA α β t - polyB α β p1 p2 q r t =
      t * (p2 - p1) +
        t ^ 2 * (c2 α β p1 p2 q r + t * (c3 α β p1 p2 q r + t * c4 α β p1 p2 q r)) := by
  unfold polyA polyB c2 c3 c4; ring

/-- With a symmetric contact matrix, the second-order coefficient along the curve with tangent
`ω = (β, α, 1)` is `-½ H(ω)`. -/
lemma c2_eq_hess (α β p q r : ℝ) : c2 α β p p q r = -(1 / 2) * hess p q r β α 1 := by
  unfold c2 hess; ring

/-! ## First-order lemmas -/

/-- If `t c + t² ρ(t) ≤ 0` for small `t > 0` then `c ≤ 0`. -/
lemma first_order_pos {c : ℝ} {ρ : ℝ → ℝ} (hρ : ContinuousAt ρ 0)
    (h : ∀ᶠ t in 𝓝[>] (0 : ℝ), t * c + t ^ 2 * ρ t ≤ 0) : c ≤ 0 := by
  have hlim : Tendsto (fun t : ℝ => c + t * ρ t) (𝓝[>] (0 : ℝ)) (𝓝 (c + 0 * ρ 0)) :=
    (tendsto_const_nhds.add (continuousAt_id.mul hρ)).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), c + t * ρ t ≤ 0 := by
    filter_upwards [h, self_mem_nhdsWithin] with t ht ht0
    have ht0' : (0 : ℝ) < t := ht0
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [mul_pos ht0' hcon]
  have := le_of_tendsto hlim hev
  simpa using this

/-- If `t c + t² ρ(t) ≤ 0` for small `t < 0` then `0 ≤ c`. -/
lemma first_order_neg {c : ℝ} {ρ : ℝ → ℝ} (hρ : ContinuousAt ρ 0)
    (h : ∀ᶠ t in 𝓝[<] (0 : ℝ), t * c + t ^ 2 * ρ t ≤ 0) : 0 ≤ c := by
  have hlim : Tendsto (fun t : ℝ => c + t * ρ t) (𝓝[<] (0 : ℝ)) (𝓝 (c + 0 * ρ 0)) :=
    (tendsto_const_nhds.add (continuousAt_id.mul hρ)).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[<] (0 : ℝ), 0 ≤ c + t * ρ t := by
    filter_upwards [h, self_mem_nhdsWithin] with t ht ht0
    have ht0' : t < (0 : ℝ) := ht0
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [mul_pos_of_neg_of_neg ht0' hcon]
  have := ge_of_tendsto hlim hev
  simpa using this

/-- If `t c + t² ρ(t) ≤ 0` for all small `t` then `c = 0`. -/
lemma first_order_zero {c : ℝ} {ρ : ℝ → ℝ} (hρ : ContinuousAt ρ 0)
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), t * c + t ^ 2 * ρ t ≤ 0) : c = 0 :=
  le_antisymm (first_order_pos hρ (h.filter_mono nhdsWithin_le_nhds))
    (first_order_neg hρ (h.filter_mono nhdsWithin_le_nhds))

/-- First-order condition along the two-edge curve: if the six-point volume does not drop below
the squared-length product for small `t`, then `X₁₂ = X₂₁`. -/
lemma first_order_p {α β p1 p2 q r : ℝ}
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), polyA α β t ≤ polyB α β p1 p2 q r t) : p1 = p2 := by
  have hρ : ContinuousAt
      (fun t : ℝ => c2 α β p1 p2 q r + t * (c3 α β p1 p2 q r + t * c4 α β p1 p2 q r)) 0 := by
    fun_prop
  have h0 : p2 - p1 = 0 := by
    refine first_order_zero hρ ?_
    filter_upwards [h] with t ht
    have := polyA_sub_polyB α β p1 p2 q r t
    linarith
  linarith

/-- **The core inequality.** For a symmetric contact matrix with `p², q², r² ≤ 1`, the
six-point volume along the two-edge curve is strictly below the squared-length product for some
arbitrarily small `t`; i.e. the box volume strictly decreases along the curve.

In the generic case this is `H(ω) < 0`; in the diagonal case `H(ω) = 0` the difference
`polyA - polyB` is exactly `6 t⁴`. -/
theorem quartic_core {α β p q r : ℝ} (hp : p ^ 2 ≤ 1) (hq : q ^ 2 ≤ 1) (hr : r ^ 2 ≤ 1) :
    ¬ ∀ᶠ t in 𝓝 (0 : ℝ), polyA α β t ≤ polyB α β p p q r t := by
  intro h
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := self_mem_nhdsWithin
  rcases (hess_nonpos hp hq hr β α 1).lt_or_eq with hlt | heq
  · -- strictly negative Hessian
    have hc2 : 0 < c2 α β p p q r := by rw [c2_eq_hess]; linarith
    have hcont : ContinuousAt
        (fun t : ℝ => c2 α β p p q r + t * (c3 α β p p q r + t * c4 α β p p q r)) 0 := by
      fun_prop
    have hpos : ∀ᶠ t in 𝓝 (0 : ℝ),
        0 < c2 α β p p q r + t * (c3 α β p p q r + t * c4 α β p p q r) := by
      refine hcont.eventually (lt_mem_nhds ?_)
      simpa using hc2
    obtain ⟨t, ⟨ht1, ht2⟩, ht0⟩ :=
      (((h.and hpos).filter_mono nhdsWithin_le_nhds).and hne).exists
    have hexp := polyA_sub_polyB α β p p q r t
    have ht : 0 < t ^ 2 := by positivity
    nlinarith [mul_pos ht ht2]
  · -- diagonal case: the difference is exactly 6 t⁴
    obtain ⟨hα, hβ, hq', hr', hp'⟩ := diag_of_hess_eq_zero hp hq hr heq
    obtain ⟨t, ht1, ht0⟩ := ((h.filter_mono nhdsWithin_le_nhds).and hne).exists
    have key : polyA α β t - polyB α β p p q r t = 6 * t ^ 4 := by
      rw [hq', hr', hp']
      unfold polyA polyB
      linear_combination
        (α^2*β^2*t^4 - α*β^3*t^3 + α*β*t^3 + 3*β^2*t^4 - β^2*t^2 + t^4) * hα
          + (-2*α*β*t^3 + 4*t^4 - t^2) * hβ
    have ht : 0 < t ^ 4 := by positivity
    linarith

/-! ## Bounds from first-order information -/

/-- From an "eventually one of finitely many branches does not shrink" statement for the
rotation in a coordinate plane, extract the two one-sided first-order conditions. -/
lemma first_order_bounds {ι : Type*} (T : Finset ι) (hT : T.Nonempty) (δ : ι → ℝ)
    {wj wk g : ℝ} (hwk : 0 < wk)
    (h : ∀ᶠ s in 𝓝 (0 : ℝ), ∃ τ ∈ T,
      wj * wk * (1 + s ^ 2) ≤ (wj - s * δ τ) * (wk + s * g)) :
    (∃ τ ∈ T, δ τ * wk ≤ g * wj) ∧ (∃ τ ∈ T, g * wj ≤ δ τ * wk) := by
  have hposk : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < wk + s * g := by
    have hc : ContinuousAt (fun s : ℝ => wk + s * g) 0 := by fun_prop
    refine hc.eventually (lt_mem_nhds ?_)
    simpa using hwk
  constructor
  · obtain ⟨τ0, hτ0, hmin⟩ := T.exists_min_image δ hT
    refine ⟨τ0, hτ0, ?_⟩
    have hc : δ τ0 * wk - g * wj ≤ 0 := by
      refine first_order_pos (ρ := fun _ => δ τ0 * g + wj * wk) continuousAt_const ?_
      filter_upwards [h.filter_mono nhdsWithin_le_nhds, hposk.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with s hs hk hs0
      have hs0' : (0 : ℝ) < s := hs0
      obtain ⟨τ, hτ, hτi⟩ := hs
      have h1 : (wj - s * δ τ) * (wk + s * g) ≤ (wj - s * δ τ0) * (wk + s * g) := by
        apply mul_le_mul_of_nonneg_right _ hk.le
        nlinarith [mul_le_mul_of_nonneg_left (hmin τ hτ) hs0'.le]
      nlinarith
    linarith
  · obtain ⟨τ0, hτ0, hmax⟩ := T.exists_max_image δ hT
    refine ⟨τ0, hτ0, ?_⟩
    have hc : 0 ≤ δ τ0 * wk - g * wj := by
      refine first_order_neg (ρ := fun _ => δ τ0 * g + wj * wk) continuousAt_const ?_
      filter_upwards [h.filter_mono nhdsWithin_le_nhds, hposk.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with s hs hk hs0
      have hs0' : s < (0 : ℝ) := hs0
      obtain ⟨τ, hτ, hτi⟩ := hs
      have h1 : (wj - s * δ τ) * (wk + s * g) ≤ (wj - s * δ τ0) * (wk + s * g) := by
        apply mul_le_mul_of_nonneg_right _ hk.le
        nlinarith [mul_le_mul_of_nonpos_left (hmax τ hτ) hs0'.le]
      nlinarith
    linarith

/-- A ratio bounded by `v/u` and by `u/v` has square at most one (Lemma 2 of the writeup). -/
lemma sq_le_one_of_abs {a u v : ℝ} (hu : 0 < u) (hv : 0 < v) (h1 : |a| * u ≤ v)
    (h2 : |a| * v ≤ u) : a ^ 2 ≤ 1 := by
  have ha : 0 ≤ |a| := abs_nonneg a
  have h : |a| ≤ 1 := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [mul_pos (sub_pos.2 hcon) hu, mul_pos (sub_pos.2 hcon) hv]
  calc a ^ 2 = |a| ^ 2 := (sq_abs a).symm
    _ ≤ 1 := by nlinarith

/-- A value between two values of absolute value at most `W` has absolute value at most `W`. -/
lemma abs_le_of_between {x lo hi W : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) (b1 : |lo| ≤ W)
    (b2 : |hi| ≤ W) : |x| ≤ W := by
  obtain ⟨l1, -⟩ := abs_le.1 b1
  obtain ⟨-, r2⟩ := abs_le.1 b2
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- The same along an affine image of an interval. -/
lemma abs_le_of_affine_between {x lo hi y ylo yhi α W : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi)
    (e1 : y - ylo = α * (x - lo)) (e2 : yhi - y = α * (hi - x)) (b1 : |ylo| ≤ W)
    (b2 : |yhi| ≤ W) : |y| ≤ W := by
  obtain ⟨l1, r1⟩ := abs_le.1 b1
  obtain ⟨l2, r2⟩ := abs_le.1 b2
  rcases le_total 0 α with hα | hα
  · have t1 := mul_nonneg hα (sub_nonneg.2 h1)
    have t2 := mul_nonneg hα (sub_nonneg.2 h2)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · have t1 := mul_nonpos_of_nonpos_of_nonneg hα (sub_nonneg.2 h1)
    have t2 := mul_nonpos_of_nonpos_of_nonneg hα (sub_nonneg.2 h2)
    exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **Algebraic heart of the two-edge case.**  All geometric input has been reduced to real
numbers: box widths `wi, wj, wk`; one chosen chord per axis with transverse components `d··`;
for each of the two edge axes a "low" and a "high" chord supplied by the first-order conditions
for the two coordinate-plane rotations; containment of all chords in the box; and the statement
`hev` that the volume does not decrease along the curve keeping both edge contacts. These are
contradictory. -/
theorem caseB_algebra {wi wj wk α β dij dik dji djk dki dkj : ℝ}
    (hwi : 0 < wi) (hwj : 0 < wj) (hwk : 0 < wk)
    {aj ak aj' ak' : ℝ}
    (h1 : ak * wk ≤ dki * wi) (h1' : dki * wi ≤ ak' * wk)
    (h2 : aj - dij = α * (ak - dik)) (h2' : aj' - dij = α * (ak' - dik))
    (h3 : |aj| ≤ wj) (h3' : |aj'| ≤ wj) (h4 : |ak| ≤ wk) (h4' : |ak'| ≤ wk)
    {bi bk bi' bk' : ℝ}
    (g1 : bk * wk ≤ dkj * wj) (g1' : dkj * wj ≤ bk' * wk)
    (g2 : bi - dji = β * (bk - djk)) (g2' : bi' - dji = β * (bk' - djk))
    (g3 : |bi| ≤ wi) (g3' : |bi'| ≤ wi) (g4 : |bk| ≤ wk) (g4' : |bk'| ≤ wk)
    (hki : |dki| ≤ wi) (hkj : |dkj| ≤ wj)
    (hev : ∀ᶠ t in 𝓝 (0 : ℝ),
      wi * wj * wk * polyA α β t ≤
        (wi + t * (dij - α * dik)) * (wj + t * (-dji + α * β * wj + β * djk)) *
          (wk * (1 + α * β * t + t ^ 2) + dki * (α * t + β * (1 + α ^ 2) * t ^ 2)
            + dkj * (-β * t + α * t ^ 2))) :
    False := by
  -- the symmetric contact matrix: q = X₁₃ = X₃₁, r = X₂₃ = X₃₂, and the two candidates for X₁₂
  set q := dki / wk with hq
  set r := dkj / wk with hr
  set p1 := (dij + α * (q * wi - dik)) / wi with hp1
  set p2 := (dji + β * (r * wj - djk)) / wj with hp2
  have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), polyA α β t ≤ polyB α β p1 p2 q r t := by
    filter_upwards [hev] with t ht
    have hrw : (wi + t * (dij - α * dik)) * (wj + t * (-dji + α * β * wj + β * djk)) *
          (wk * (1 + α * β * t + t ^ 2) + dki * (α * t + β * (1 + α ^ 2) * t ^ 2)
            + dkj * (-β * t + α * t ^ 2))
        = wi * wj * wk * polyB α β p1 p2 q r t := by
      simp only [polyB, hp1, hp2, hq, hr]
      field_simp
      ring
    rw [hrw] at ht
    exact le_of_mul_le_mul_left ht (by positivity)
  -- torque balance about the third axis
  have hp : p1 = p2 := first_order_p hev'
  -- Lemma 2: the three ratios are at most one in absolute value
  have hqwi : q * wi = dki * wi / wk := by rw [hq]; ring
  have hrwj : r * wj = dkj * wj / wk := by rw [hr]; ring
  have hqlo : ak ≤ q * wi := by rw [hqwi, le_div_iff₀ hwk]; exact h1
  have hqhi : q * wi ≤ ak' := by rw [hqwi, div_le_iff₀ hwk]; exact h1'
  have hrlo : bk ≤ r * wj := by rw [hrwj, le_div_iff₀ hwk]; exact g1
  have hrhi : r * wj ≤ bk' := by rw [hrwj, div_le_iff₀ hwk]; exact g1'
  have hq2 : q ^ 2 ≤ 1 := by
    refine sq_le_one_of_abs hwi hwk ?_ ?_
    · have := abs_le_of_between hqlo hqhi h4 h4'
      rwa [abs_mul, abs_of_pos hwi] at this
    · have : |q| * wk = |dki| := by
        rw [hq, abs_div, abs_of_pos hwk]; field_simp
      rw [this]; exact hki
  have hr2 : r ^ 2 ≤ 1 := by
    refine sq_le_one_of_abs hwj hwk ?_ ?_
    · have := abs_le_of_between hrlo hrhi g4 g4'
      rwa [abs_mul, abs_of_pos hwj] at this
    · have : |r| * wk = |dkj| := by
        rw [hr, abs_div, abs_of_pos hwk]; field_simp
      rw [this]; exact hkj
  have hp1wi : p1 * wi = dij + α * (q * wi - dik) := by rw [hp1]; field_simp
  have hp2wj : p2 * wj = dji + β * (r * wj - djk) := by rw [hp2]; field_simp
  have hp1b : |p1| * wi ≤ wj := by
    have := abs_le_of_affine_between (y := p1 * wi) (α := α) hqlo hqhi
      (by rw [hp1wi]; linarith) (by rw [hp1wi]; linarith) h3 h3'
    rwa [abs_mul, abs_of_pos hwi] at this
  have hp2b : |p2| * wj ≤ wi := by
    have := abs_le_of_affine_between (y := p2 * wj) (α := β) hrlo hrhi
      (by rw [hp2wj]; linarith) (by rw [hp2wj]; linarith) g3 g3'
    rwa [abs_mul, abs_of_pos hwj] at this
  have hp2 : p1 ^ 2 ≤ 1 := sq_le_one_of_abs hwi hwj hp1b (by rw [hp]; exact hp2b)
  -- the volume strictly decreases along the curve
  refine quartic_core (α := α) (β := β) hp2 hq2 hr2 ?_
  have : ∀ᶠ t in 𝓝 (0 : ℝ), polyA α β t ≤ polyB α β p1 p1 q r t := by
    filter_upwards [hev'] with t ht
    rw [← hp] at ht; exact ht
  exact this

end MinBox
