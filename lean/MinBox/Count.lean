import MinBox.Existence

/-!
# Counting edge–face contacts literally

`ThreeContacts` speaks about contact sets of box faces.  Here we turn it into the literal
statement of Conjecture 7.1: there are three distinct pairs (box face, polyhedron edge) with the
edge contained in the face, two of them on adjacent faces.

The extra ingredient is elementary polygon geometry: a face of a face is a face
(`contactSet_contactSet`), and a non-collinear planar point set has at least three edges
(`three_edges_planar`).
-/

open Filter Topology Matrix

open Classical

noncomputable section

namespace MinBox

local notation "V3" => Fin 3 → ℝ

variable {K : Finset V3}

/-- An edge of the polyhedron `conv K`: a face (contact set in some direction) that is a
segment, represented by the points of `K` on it. -/
def IsEdge (K : Finset V3) (E : Finset V3) : Prop :=
  (∃ v, E = contactSet K v) ∧ 1 < E.card ∧ Collinear ℝ (E : Set V3)

/-- An edge–face contact: the box face `f` (for orientation `R`) contains the polyhedron
edge `E`. -/
def IsContact (K : Finset V3) (R : Matrix (Fin 3) (Fin 3) ℝ) (f : Fin 3 × Bool)
    (E : Finset V3) : Prop :=
  IsEdge K E ∧ E ⊆ contactSet K (faceNormal R f)

/-! ## A face of a face is a face -/

lemma contactSet_contactSet (K : Finset V3) (u v : V3) :
    ∃ ε : ℝ, 0 < ε ∧ contactSet K (u + ε • v) = contactSet (contactSet K u) v := by
  have hcont : ∀ x : V3, Tendsto (fun ε : ℝ => x ⬝ᵥ (u + ε • v)) (𝓝 0) (𝓝 (x ⬝ᵥ u)) := by
    intro x
    have hc : Continuous fun ε : ℝ => x ⬝ᵥ u + ε * (x ⬝ᵥ v) := by fun_prop
    have h := hc.tendsto 0
    simp only [zero_mul, add_zero] at h
    refine h.congr fun ε => ?_
    simp [dotProduct_add, dotProduct_smul]
  have key : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ x ∈ K, x ∉ contactSet K u → ∀ y ∈ contactSet K u,
      x ⬝ᵥ (u + ε • v) < y ⬝ᵥ (u + ε • v) := by
    refine (Filter.eventually_all_finset K).2 fun x hx => ?_
    by_cases hxS : x ∈ contactSet K u
    · exact Eventually.of_forall fun ε h => absurd hxS h
    · have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ y ∈ contactSet K u,
          x ⬝ᵥ (u + ε • v) < y ⬝ᵥ (u + ε • v) := by
        refine (Filter.eventually_all_finset _).2 fun y hy => ?_
        have hlt : x ⬝ᵥ u < y ⬝ᵥ u := by
          by_contra hcon
          rw [not_lt] at hcon
          refine hxS (mem_contactSet.2 ⟨hx, fun z hz => ?_⟩)
          exact ((mem_contactSet.1 hy).2 z hz).trans hcon
        exact (hcont x).eventually_lt (hcont y) hlt
      exact h1.mono fun ε h _ => h
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (0 : ℝ) < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hε0⟩ := ((key.filter_mono nhdsWithin_le_nhds).and hpos).exists
  refine ⟨ε, hε0, ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨hzK, hzmax⟩ := mem_contactSet.1 hz
    have hzS : z ∈ contactSet K u := by
      by_contra hzS
      obtain ⟨y0, hy0⟩ := contactSet_nonempty ⟨z, hzK⟩ u
      have h1 := hε z hzK hzS y0 hy0
      have h2 := hzmax y0 (contactSet_subset K u hy0)
      linarith
    refine mem_contactSet.2 ⟨hzS, fun w hw => ?_⟩
    have h1 := hzmax w (contactSet_subset K u hw)
    have h2 := dot_eq_of_mem_contactSet hw hzS
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at h1
    have h3 : ε * (w ⬝ᵥ v) ≤ ε * (z ⬝ᵥ v) := by linarith
    exact le_of_mul_le_mul_left h3 hε0
  · intro hz
    obtain ⟨hzS, hzmax⟩ := mem_contactSet.1 hz
    refine mem_contactSet.2 ⟨contactSet_subset K u hzS, fun w hw => ?_⟩
    by_cases hwS : w ∈ contactSet K u
    · have h1 := hzmax w hwS
      have h2 := dot_eq_of_mem_contactSet hwS hzS
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      have h3 : ε * (w ⬝ᵥ v) ≤ ε * (z ⬝ᵥ v) := mul_le_mul_of_nonneg_left h1 hε0.le
      linarith
    · exact (hε w hw hwS z hzS).le

/-! ## Planar point sets -/

lemma sum3 {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (f : Fin 3 → ℝ) :
    ∑ m, f m = f i + f j + f k := by
  have h3 : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2 := by decide
  rw [Fin.sum_univ_three]
  rcases h3 i with rfl | rfl | rfl <;> rcases h3 j with rfl | rfl | rfl <;>
    rcases h3 k with rfl | rfl | rfl <;>
    first | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk | ring

lemma dot3 {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x u : V3) :
    x ⬝ᵥ u = x i * u i + x j * u j + x k * u k := by
  simp only [dotProduct]
  exact sum3 hij hik hjk _

/-- In a plane with normal `u`, `u m ≠ 0`, a point is determined by its other two
coordinates. -/
lemma eq_of_coords {u : V3} {a b m : Fin 3} (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m)
    (hum : u m ≠ 0) {x y : V3} (hxy : x ⬝ᵥ u = y ⬝ᵥ u) (ha : x a = y a) (hb : x b = y b) :
    x = y := by
  have hm : x m = y m := by
    rw [dot3 hab ham hbm, dot3 hab ham hbm, ha, hb] at hxy
    have h : (x m - y m) * u m = 0 := by linarith
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · exact absurd h hum
  funext i
  rcases cases3 hab ham hbm i with rfl | rfl | rfl <;> assumption

/-- Points of a plane whose `(a, b)`-coordinates lie on a line through `x0` are collinear. -/
lemma collinear_in_plane {u : V3} {a b m : Fin 3} (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m)
    (hum : u m ≠ 0) {T : Finset V3} {x0 : V3} (hplane : ∀ z ∈ T, z ⬝ᵥ u = x0 ⬝ᵥ u)
    (p q : ℝ) (r : V3 → ℝ) (h : ∀ z ∈ T, z a - x0 a = r z * p ∧ z b - x0 b = r z * q) :
    Collinear ℝ (T : Set V3) := by
  obtain ⟨d, hd⟩ : ∃ d : V3, d = lin3 a b m p q (-(p * u a + q * u b) / u m) := ⟨_, rfl⟩
  have da : d a = p := by rw [hd]; exact (lin3_apply hab ham hbm _ _ _).1
  have db : d b = q := by rw [hd]; exact (lin3_apply hab ham hbm _ _ _).2.1
  have hdu : d ⬝ᵥ u = 0 := by
    rw [hd, lin3_dot]; field_simp; ring
  refine (collinear_iff_exists_forall_eq_smul_vadd _).2 ⟨x0, d, fun z hz => ⟨r z, ?_⟩⟩
  obtain ⟨h1, h2⟩ := h z (Finset.mem_coe.1 hz)
  refine eq_of_coords hab ham hbm hum ?_ ?_ ?_
  · rw [hplane z (Finset.mem_coe.1 hz), vadd_eq_add, add_dotProduct, smul_dotProduct, hdu]
    simp
  · simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, da]; linarith
  · simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, db]; linarith

/-- Two segment faces through the same two distinct points coincide. -/
lemma contactSet_subset_of_two {S : Finset V3} {v1 v2 : V3}
    (h1 : Collinear ℝ (contactSet S v1 : Set V3)) {x y : V3} (hxy : x ≠ y)
    (hx1 : x ∈ contactSet S v1) (hy1 : y ∈ contactSet S v1)
    (hx2 : x ∈ contactSet S v2) (hy2 : y ∈ contactSet S v2) :
    contactSet S v1 ⊆ contactSet S v2 := by
  intro z hz
  obtain ⟨d, hd⟩ := (collinear_iff_of_mem (Finset.mem_coe.2 hx1)).1 h1
  obtain ⟨ry, hry⟩ := hd y (Finset.mem_coe.2 hy1)
  obtain ⟨rz, hrz⟩ := hd z (Finset.mem_coe.2 hz)
  have hyv : y ⬝ᵥ v2 = ry * (d ⬝ᵥ v2) + x ⬝ᵥ v2 := by
    rw [hry, vadd_eq_add, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hzv : z ⬝ᵥ v2 = rz * (d ⬝ᵥ v2) + x ⬝ᵥ v2 := by
    rw [hrz, vadd_eq_add, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have heq := dot_eq_of_mem_contactSet hy2 hx2
  have hry0 : ry ≠ 0 := by
    intro h0
    apply hxy
    rw [hry, h0]; simp
  have hdv : d ⬝ᵥ v2 = 0 := by
    have : ry * (d ⬝ᵥ v2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hry0
    · exact h
  refine mem_contactSet.2 ⟨contactSet_subset S v1 hz, fun w hw => ?_⟩
  rw [hzv, hdv, mul_zero, zero_add]
  exact (mem_contactSet.1 hx2).2 w hw

lemma contactSet_eq_of_two {S : Finset V3} {v1 v2 : V3}
    (h1 : Collinear ℝ (contactSet S v1 : Set V3)) (h2 : Collinear ℝ (contactSet S v2 : Set V3))
    {x y : V3} (hxy : x ≠ y) (hx1 : x ∈ contactSet S v1) (hy1 : y ∈ contactSet S v1)
    (hx2 : x ∈ contactSet S v2) (hy2 : y ∈ contactSet S v2) :
    contactSet S v1 = contactSet S v2 :=
  Finset.Subset.antisymm (contactSet_subset_of_two h1 hxy hx1 hy1 hx2 hy2)
    (contactSet_subset_of_two h2 hxy hx2 hy2 hx1 hy1)

/-- **Two edges at an extreme vertex.**  Let `S` be a non-collinear finite subset of a plane
with normal `u`, `u m ≠ 0`, and use the other two coordinates `(a, b)` as coordinates on the
plane.  At the lexicographically smallest point `x0` of `S` for `(s·x_a, s·x_b)` there are two
different segment faces of `S` (the "lower" and the "upper" edge at `x0`). -/
lemma two_edges_at_lexmin {S : Finset V3} {u : V3} {a b m : Fin 3} (hab : a ≠ b) (ham : a ≠ m)
    (hbm : b ≠ m) (hum : u m ≠ 0) (hplane : ∀ x ∈ S, ∀ y ∈ S, x ⬝ᵥ u = y ⬝ᵥ u)
    (hS : ¬ Collinear ℝ (S : Set V3)) {s : ℝ} (hs : s ≠ 0) :
    ∃ x0 ∈ S, (∀ y ∈ S, s * x0 a ≤ s * y a) ∧ (∀ y ∈ S, y a = x0 a → s * x0 b ≤ s * y b) ∧
      ∃ v1 v2 : V3, x0 ∈ contactSet S v1 ∧ x0 ∈ contactSet S v2 ∧
        Collinear ℝ (contactSet S v1 : Set V3) ∧ Collinear ℝ (contactSet S v2 : Set V3) ∧
        1 < (contactSet S v1).card ∧ 1 < (contactSet S v2).card ∧
        contactSet S v1 ≠ contactSet S v2 := by
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    exact hS (by rw [h]; simpa using collinear_empty ℝ V3)
  -- the lexicographically smallest point
  obtain ⟨xa, hxa, hmina⟩ := S.exists_min_image (fun x => s * x a) hSne
  have hS0ne : (S.filter (fun x => x a = xa a)).Nonempty :=
    ⟨xa, Finset.mem_filter.2 ⟨hxa, rfl⟩⟩
  obtain ⟨x0, hx0S0, hminb⟩ :=
    (S.filter (fun x => x a = xa a)).exists_min_image (fun x => s * x b) hS0ne
  have hx0 : x0 ∈ S := (Finset.mem_filter.1 hx0S0).1
  have hx0a : x0 a = xa a := (Finset.mem_filter.1 hx0S0).2
  have L1 : ∀ y ∈ S, s * x0 a ≤ s * y a := fun y hy => by rw [hx0a]; exact hmina y hy
  have L2 : ∀ y ∈ S, y a = x0 a → s * x0 b ≤ s * y b := fun y hy hya =>
    hminb y (Finset.mem_filter.2 ⟨hy, by rw [hya, hx0a]⟩)
  refine ⟨x0, hx0, L1, L2, ?_⟩
  have plane0 : ∀ z ∈ S, z ⬝ᵥ u = x0 ⬝ᵥ u := fun z hz => hplane z hz x0 hx0
  -- the points strictly beyond `x0` in the first coordinate
  obtain ⟨T, hT⟩ : ∃ T : Finset V3, T = S.filter (fun z => s * x0 a < s * z a) := ⟨_, rfl⟩
  have hTS : ∀ z ∈ T, z ∈ S := fun z hz => by rw [hT] at hz; exact (Finset.mem_filter.1 hz).1
  have hTpos : ∀ z ∈ T, 0 < s * (z a - x0 a) := fun z hz => by
    rw [hT] at hz
    have := (Finset.mem_filter.1 hz).2
    rw [mul_sub]; linarith
  have hnotT : ∀ z ∈ S, z ∉ T → z a = x0 a := by
    intro z hz hzT
    have h1 : ¬ s * x0 a < s * z a := fun h => hzT (by rw [hT]; exact Finset.mem_filter.2 ⟨hz, h⟩)
    have h2 := L1 z hz
    exact mul_left_cancel₀ hs (le_antisymm (not_lt.1 h1) h2)
  have hTne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hS
    refine collinear_in_plane hab ham hbm hum plane0 0 1 (fun z => z b - x0 b) fun z hz => ?_
    have := hnotT z hz (by rw [h]; exact Finset.notMem_empty z)
    constructor <;> linarith
  -- slopes seen from `x0`
  obtain ⟨σ, hσ⟩ : ∃ σ : V3 → ℝ, σ = fun z => (z b - x0 b) / (z a - x0 a) := ⟨_, rfl⟩
  have hTne0 : ∀ z ∈ T, z a - x0 a ≠ 0 := fun z hz h0 => by
    have := hTpos z hz
    rw [h0, mul_zero] at this
    exact lt_irrefl _ this
  have hσmul : ∀ z ∈ T, σ z * (z a - x0 a) = z b - x0 b := fun z hz => by
    have := hTne0 z hz
    rw [hσ]; field_simp
  -- the lower edge: smallest slope
  obtain ⟨y1, hy1T, hy1min⟩ := T.exists_min_image σ hTne
  have hy1S : y1 ∈ S := hTS y1 hy1T
  obtain ⟨v1, hv1⟩ : ∃ v1 : V3, v1 = s • (σ y1 • e a - e b) := ⟨_, rfl⟩
  have dv1 : ∀ z : V3, z ⬝ᵥ v1 = s * (σ y1 * z a - z b) := fun z => by
    rw [hv1]; simp [dotProduct_smul, dotProduct_sub]
  have hmax1 : ∀ z ∈ S, z ⬝ᵥ v1 ≤ x0 ⬝ᵥ v1 := by
    intro z hz
    rw [dv1, dv1]
    by_cases hzT : z ∈ T
    · have h1 := mul_nonneg (sub_nonneg.2 (hy1min z hzT)) (hTpos z hzT).le
      have h3 : s * (σ z * (z a - x0 a)) = s * (z b - x0 b) := by rw [hσmul z hzT]
      linarith
    · have h1 := hnotT z hz hzT
      have h2 := L2 z hz h1
      rw [h1]; linarith
  have hx0E1 : x0 ∈ contactSet S v1 := mem_contactSet.2 ⟨hx0, hmax1⟩
  have hy1E1 : y1 ∈ contactSet S v1 := by
    refine mem_contactSet.2 ⟨hy1S, fun z hz => (hmax1 z hz).trans (le_of_eq ?_)⟩
    rw [dv1, dv1]
    linear_combination (-s) * hσmul y1 hy1T
  have hne01 : x0 ≠ y1 := fun h => by
    have := hTpos y1 hy1T
    rw [← h, sub_self, mul_zero] at this
    exact lt_irrefl _ this
  have hline : ∀ (v : V3) (τ : ℝ), (∀ z : V3, z ⬝ᵥ v = s * (τ * z a - z b)) →
      x0 ∈ contactSet S v → Collinear ℝ (contactSet S v : Set V3) := by
    intro v τ dv hx0E
    refine collinear_in_plane hab ham hbm hum
      (fun z hz => plane0 z (contactSet_subset S v hz)) 1 τ (fun z => z a - x0 a)
      fun z hz => ⟨by ring, ?_⟩
    have h := dot_eq_of_mem_contactSet hz hx0E
    rw [dv, dv] at h
    have := mul_left_cancel₀ hs h
    linarith
  have col1 := hline v1 (σ y1) dv1 hx0E1
  have card1 : 1 < (contactSet S v1).card := Finset.one_lt_card.2 ⟨x0, hx0E1, y1, hy1E1, hne01⟩
  -- the upper edge
  by_cases hV : ∃ z ∈ S, z a = x0 a ∧ z ≠ x0
  · -- a second point with the same first coordinate: the edge `x_a = const`
    obtain ⟨zv, hzvS, hzva, hzvne⟩ := hV
    obtain ⟨v2, hv2⟩ : ∃ v2 : V3, v2 = (-s) • e a := ⟨_, rfl⟩
    have dv2 : ∀ z : V3, z ⬝ᵥ v2 = -(s * z a) := fun z => by
      rw [hv2]; simp [dotProduct_smul]
    have hx0E2 : x0 ∈ contactSet S v2 :=
      mem_contactSet.2 ⟨hx0, fun z hz => by rw [dv2, dv2]; linarith [L1 z hz]⟩
    have hzvE2 : zv ∈ contactSet S v2 :=
      mem_contactSet.2 ⟨hzvS, fun z hz => by rw [dv2, dv2, hzva]; linarith [L1 z hz]⟩
    have col2 : Collinear ℝ (contactSet S v2 : Set V3) := by
      refine collinear_in_plane hab ham hbm hum
        (fun z hz => plane0 z (contactSet_subset S v2 hz)) 0 1 (fun z => z b - x0 b)
        fun z hz => ?_
      have h := dot_eq_of_mem_contactSet hz hx0E2
      rw [dv2, dv2] at h
      have := mul_left_cancel₀ hs (neg_injective h)
      constructor <;> linarith
    refine ⟨v1, v2, hx0E1, hx0E2, col1, col2, card1,
      Finset.one_lt_card.2 ⟨x0, hx0E2, zv, hzvE2, hzvne.symm⟩, fun heq => ?_⟩
    have hy1E2 : y1 ∈ contactSet S v2 := heq ▸ hy1E1
    have h := dot_eq_of_mem_contactSet hy1E2 hx0E2
    rw [dv2, dv2] at h
    have h' := hTpos y1 hy1T
    rw [mul_sub] at h'
    linarith
  · -- otherwise: largest slope
    have hV' : ∀ z ∈ S, z a = x0 a → z = x0 := by
      intro z hz hza
      by_contra hne
      exact hV ⟨z, hz, hza, hne⟩
    obtain ⟨y2, hy2T, hy2max⟩ := T.exists_max_image σ hTne
    have hy2S : y2 ∈ S := hTS y2 hy2T
    obtain ⟨v2, hv2⟩ : ∃ v2 : V3, v2 = (-s) • (σ y2 • e a - e b) := ⟨_, rfl⟩
    have dv2 : ∀ z : V3, z ⬝ᵥ v2 = -s * (σ y2 * z a - z b) := fun z => by
      rw [hv2]; simp [dotProduct_smul, dotProduct_sub]
    have hmax2 : ∀ z ∈ S, z ⬝ᵥ v2 ≤ x0 ⬝ᵥ v2 := by
      intro z hz
      rw [dv2, dv2]
      by_cases hzT : z ∈ T
      · have h1 := mul_nonneg (sub_nonneg.2 (hy2max z hzT)) (hTpos z hzT).le
        have h3 : s * (σ z * (z a - x0 a)) = s * (z b - x0 b) := by rw [hσmul z hzT]
        linarith
      · rw [hV' z hz (hnotT z hz hzT)]
    have hx0E2 : x0 ∈ contactSet S v2 := mem_contactSet.2 ⟨hx0, hmax2⟩
    have hy2E2 : y2 ∈ contactSet S v2 := by
      refine mem_contactSet.2 ⟨hy2S, fun z hz => (hmax2 z hz).trans (le_of_eq ?_)⟩
      rw [dv2, dv2]
      linear_combination s * hσmul y2 hy2T
    have hne02 : x0 ≠ y2 := fun h => by
      have := hTpos y2 hy2T
      rw [← h, sub_self, mul_zero] at this
      exact lt_irrefl _ this
    have col2 : Collinear ℝ (contactSet S v2 : Set V3) := by
      refine collinear_in_plane hab ham hbm hum
        (fun z hz => plane0 z (contactSet_subset S v2 hz)) 1 (σ y2) (fun z => z a - x0 a)
        fun z hz => ⟨by ring, ?_⟩
      have h := dot_eq_of_mem_contactSet hz hx0E2
      rw [dv2, dv2] at h
      have := mul_left_cancel₀ (neg_ne_zero.2 hs) h
      linarith
    refine ⟨v1, v2, hx0E1, hx0E2, col1, col2, card1,
      Finset.one_lt_card.2 ⟨x0, hx0E2, y2, hy2E2, hne02⟩, fun heq => ?_⟩
    -- equal edges would force all slopes to agree, hence `S` collinear
    have hy2E1 : y2 ∈ contactSet S v1 := heq ▸ hy2E2
    have h := dot_eq_of_mem_contactSet hy2E1 hx0E1
    rw [dv1, dv1] at h
    have h' := mul_left_cancel₀ hs h
    have hσeq : σ y1 = σ y2 := by
      have h2 := hσmul y2 hy2T
      have h3 : (σ y1 - σ y2) * (y2 a - x0 a) = 0 := by linarith
      rcases mul_eq_zero.1 h3 with h4 | h4
      · linarith
      · exact absurd h4 (hTne0 y2 hy2T)
    apply hS
    refine collinear_in_plane hab ham hbm hum plane0 1 (σ y1) (fun z => z a - x0 a)
      fun z hz => ⟨by ring, ?_⟩
    by_cases hzT : z ∈ T
    · have h1 := hy1min z hzT
      have h2 := hy2max z hzT
      have h3 : σ z = σ y1 := le_antisymm (hσeq ▸ h2) h1
      rw [← h3, mul_comm]
      exact (hσmul z hzT).symm
    · rw [hV' z hz (hnotT z hz hzT)]; ring

/-- **A polygon has at least three edges.**  A non-collinear finite subset `S` of a plane has
three pairwise different segment faces. -/
theorem three_edges_planar {S : Finset V3} {u : V3} (hu : u ≠ 0)
    (hplane : ∀ x ∈ S, ∀ y ∈ S, x ⬝ᵥ u = y ⬝ᵥ u) (hS : ¬ Collinear ℝ (S : Set V3)) :
    ∃ v1 v2 v3 : V3,
      (Collinear ℝ (contactSet S v1 : Set V3) ∧ 1 < (contactSet S v1).card) ∧
      (Collinear ℝ (contactSet S v2 : Set V3) ∧ 1 < (contactSet S v2).card) ∧
      (Collinear ℝ (contactSet S v3 : Set V3) ∧ 1 < (contactSet S v3).card) ∧
      contactSet S v1 ≠ contactSet S v2 ∧ contactSet S v1 ≠ contactSet S v3 ∧
      contactSet S v2 ≠ contactSet S v3 := by
  obtain ⟨m, hm⟩ := Function.ne_iff.1 hu
  have hum : u m ≠ 0 := by simpa using hm
  obtain ⟨a, b, hma, hmb, hab⟩ := exists_other m
  have ham := hma.symm
  have hbm := hmb.symm
  obtain ⟨x0, hx0, L1, L2, v1, v2, hx01, hx02, c1, c2, k1, k2, hne12⟩ :=
    two_edges_at_lexmin hab ham hbm hum hplane hS (s := 1) one_ne_zero
  obtain ⟨x1, hx1, M1, M2, v3, v4, hx13, hx14, c3, c4, k3, k4, hne34⟩ :=
    two_edges_at_lexmin hab ham hbm hum hplane hS (s := -1) (by norm_num)
  have hx01ne : x0 ≠ x1 := by
    intro h
    rw [← h] at M1 M2
    apply hS
    have hall : ∀ z ∈ S, z = x0 := by
      intro z hz
      have ha : z a = x0 a := by
        have := L1 z hz
        have := M1 z hz
        linarith
      have hb : z b = x0 b := by
        have := L2 z hz ha
        have := M2 z hz ha
        linarith
      exact eq_of_coords hab ham hbm hum (hplane z hz x0 hx0) ha hb
    refine collinear_in_plane hab ham hbm hum (fun z hz => hplane z hz x0 hx0) 0 0
      (fun _ => 0) fun z hz => ?_
    rw [hall z hz]; simp
  by_cases h3 : contactSet S v3 = contactSet S v1 ∨ contactSet S v3 = contactSet S v2
  · by_cases h4 : contactSet S v4 = contactSet S v1 ∨ contactSet S v4 = contactSet S v2
    · -- both edges at `x1` are edges at `x0`: then the two edges at `x0` coincide
      exfalso
      have hx1E1 : x1 ∈ contactSet S v1 := by
        rcases h3 with h3 | h3
        · exact h3 ▸ hx13
        · rcases h4 with h4 | h4
          · exact h4 ▸ hx14
          · exact absurd (h3.trans h4.symm) hne34
      have hx1E2 : x1 ∈ contactSet S v2 := by
        rcases h3 with h3 | h3
        · rcases h4 with h4 | h4
          · exact absurd (h3.trans h4.symm) hne34
          · exact h4 ▸ hx14
        · exact h3 ▸ hx13
      exact hne12 (contactSet_eq_of_two c1 c2 hx01ne hx01 hx1E1 hx02 hx1E2)
    · rw [not_or] at h4
      exact ⟨v1, v2, v4, ⟨c1, k1⟩, ⟨c2, k2⟩, ⟨c4, k4⟩, hne12, fun h => h4.1 h.symm,
        fun h => h4.2 h.symm⟩
  · rw [not_or] at h3
    exact ⟨v1, v2, v3, ⟨c1, k1⟩, ⟨c2, k2⟩, ⟨c3, k3⟩, hne12, fun h => h3.1 h.symm,
      fun h => h3.2 h.symm⟩

/-! ## Edges of the polyhedron inside a box face -/

/-- A polygonal face of `K` (non-collinear contact set in a direction `u ≠ 0`) contains three
different edges of `K`. -/
theorem three_edges_of_face {u : V3} (hu : u ≠ 0)
    (h : ¬ Collinear ℝ (contactSet K u : Set V3)) :
    ∃ E₁ E₂ E₃ : Finset V3, IsEdge K E₁ ∧ IsEdge K E₂ ∧ IsEdge K E₃ ∧
      E₁ ⊆ contactSet K u ∧ E₂ ⊆ contactSet K u ∧ E₃ ⊆ contactSet K u ∧
      E₁ ≠ E₂ ∧ E₁ ≠ E₃ ∧ E₂ ≠ E₃ := by
  obtain ⟨v1, v2, v3, ⟨c1, k1⟩, ⟨c2, k2⟩, ⟨c3, k3⟩, n12, n13, n23⟩ :=
    three_edges_planar hu (fun x hx y hy => dot_eq_of_mem_contactSet hx hy) h
  have edge : ∀ v : V3, Collinear ℝ (contactSet (contactSet K u) v : Set V3) →
      1 < (contactSet (contactSet K u) v).card → IsEdge K (contactSet (contactSet K u) v) := by
    intro v c k
    obtain ⟨ε, -, hε⟩ := contactSet_contactSet K u v
    exact ⟨⟨u + ε • v, hε.symm⟩, k, c⟩
  exact ⟨_, _, _, edge v1 c1 k1, edge v2 c2 k2, edge v3 c3 k3, contactSet_subset _ v1,
    contactSet_subset _ v2, contactSet_subset _ v3, n12, n13, n23⟩

lemma faceNormal_ne_zero {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) (f : Fin 3 × Bool) :
    faceNormal R f ≠ 0 := by
  have h1 : axis R f.1 ≠ 0 := fun h0 => by
    have := axis_dot_self hR f.1
    rw [h0] at this
    simp at this
  unfold faceNormal
  split_ifs
  · exact h1
  · exact neg_ne_zero.2 h1

/-- A box face whose contact set has two points contains a polyhedron edge. -/
lemma exists_contact_of_hasEdge {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3)
    {f : Fin 3 × Bool} (h : HasEdge K R f) : ∃ E, IsContact K R f E := by
  by_cases hcol : Collinear ℝ (contactSet K (faceNormal R f) : Set V3)
  · exact ⟨_, ⟨⟨_, rfl⟩, h, hcol⟩, Finset.Subset.refl _⟩
  · obtain ⟨E, -, -, hE, -, -, hsub, -⟩ := three_edges_of_face (faceNormal_ne_zero hR f) hcol
    exact ⟨E, hE, hsub⟩

/-! ## The literal statement -/

/-- **Conjecture 7.1, literally.**  At a local minimum of the volume of the enclosing box there
are three distinct edge–face contacts — pairs (box face, polyhedron edge) with the edge
contained in the face — and the first two of them lie on faces of different axes, i.e. on
adjacent faces of the box. -/
theorem three_edge_face_contacts (K : Finset V3) (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ SO3)
    (hpos : 0 < boxVolume K R) (hmin : IsLocalMinOn (boxVolume K) SO3 R) :
    ∃ (f₁ f₂ f₃ : Fin 3 × Bool) (E₁ E₂ E₃ : Finset V3),
      IsContact K R f₁ E₁ ∧ IsContact K R f₂ E₂ ∧ IsContact K R f₃ E₃ ∧
      (f₁, E₁) ≠ (f₂, E₂) ∧ (f₁, E₁) ≠ (f₃, E₃) ∧ (f₂, E₂) ≠ (f₃, E₃) ∧ f₁.1 ≠ f₂.1 := by
  obtain ⟨⟨f, g, hfg, hf, hg⟩, h2⟩ := three_contacts K R hR hpos hmin
  rcases h2 with ⟨f0, hf0⟩ | ⟨f', g', h', n1, n2, n3, hf', hg', hh'⟩
  · -- a box face flush with a polygonal face: three edges there, plus an edge on another axis
    obtain ⟨E₁, E₂, -, hE₁, hE₂, -, s₁, s₂, -, n12, -, -⟩ :=
      three_edges_of_face (faceNormal_ne_zero hR f0) hf0
    have other : ∃ g0 : Fin 3 × Bool, f0.1 ≠ g0.1 ∧ HasEdge K R g0 := by
      by_cases hf0f : f0.1 = f.1
      · exact ⟨g, fun h => hfg (hf0f.symm.trans h), hg⟩
      · exact ⟨f, hf0f, hf⟩
    obtain ⟨g0, hg0, hg0E⟩ := other
    obtain ⟨Eg, hEg⟩ := exists_contact_of_hasEdge hR hg0E
    have hfg0 : f0 ≠ g0 := fun h => hg0 (congrArg Prod.fst h)
    refine ⟨f0, g0, f0, E₁, Eg, E₂, ⟨hE₁, s₁⟩, hEg, ⟨hE₂, s₂⟩, ?_, ?_, ?_, hg0⟩
    · exact fun h => hfg0 (congrArg Prod.fst h)
    · exact fun h => n12 (congrArg Prod.snd h)
    · exact fun h => hfg0 (congrArg Prod.fst h).symm
  · -- three different box faces, each containing an edge
    obtain ⟨Ef, hEf⟩ := exists_contact_of_hasEdge hR hf'
    obtain ⟨Eg, hEg⟩ := exists_contact_of_hasEdge hR hg'
    obtain ⟨Eh, hEh⟩ := exists_contact_of_hasEdge hR hh'
    have bool3 : ∀ x y z : Bool, x ≠ y → z = x ∨ z = y := by decide
    by_cases h12 : f'.1 = g'.1
    · -- `f'` and `g'` are opposite, so `h'` is on another axis
      have hh1 : f'.1 ≠ h'.1 := by
        intro h13
        have hb : f'.2 ≠ g'.2 := fun hb => n1 (Prod.ext h12 hb)
        rcases bool3 f'.2 g'.2 h'.2 hb with h | h
        · exact n2 (Prod.ext h13 h.symm)
        · exact n3 (Prod.ext (h12.symm.trans h13) h.symm)
      refine ⟨f', h', g', Ef, Eh, Eg, hEf, hEh, hEg, ?_, ?_, ?_, hh1⟩
      · exact fun h => n2 (congrArg Prod.fst h)
      · exact fun h => n1 (congrArg Prod.fst h)
      · exact fun h => n3 (congrArg Prod.fst h).symm
    · refine ⟨f', g', h', Ef, Eg, Eh, hEf, hEg, hEh, ?_, ?_, ?_, h12⟩
      · exact fun h => n1 (congrArg Prod.fst h)
      · exact fun h => n2 (congrArg Prod.fst h)
      · exact fun h => n3 (congrArg Prod.fst h)

/-- A box of minimal volume exists and has three distinct edge–face contacts, two of them on
adjacent faces. -/
theorem exists_minimal_box_with_three_contacts (K : Finset V3)
    (hK : ∀ u : V3, u ≠ 0 → 0 < width K u) :
    ∃ R ∈ SO3, IsMinOn (boxVolume K) SO3 R ∧
      ∃ (f₁ f₂ f₃ : Fin 3 × Bool) (E₁ E₂ E₃ : Finset V3),
        IsContact K R f₁ E₁ ∧ IsContact K R f₂ E₂ ∧ IsContact K R f₃ E₃ ∧
        (f₁, E₁) ≠ (f₂, E₂) ∧ (f₁, E₁) ≠ (f₃, E₃) ∧ (f₂, E₂) ≠ (f₃, E₃) ∧ f₁.1 ≠ f₂.1 := by
  obtain ⟨R, hR, hmin, -⟩ := exists_minimal_box K hK
  exact ⟨R, hR, hmin,
    three_edge_face_contacts K R hR (boxVolume_pos hK hR) hmin.isLocalMinOn⟩

end MinBox
