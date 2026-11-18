import MinBox.Cases

/-!
# Conjecture 7.1: a locally minimal bounding box has three edge contacts

`three_contacts` is the main theorem.  It is first proved in the frame of the box
(`three_contacts_one`) by the case analysis of the writeup, and then transported to an
arbitrary orientation by expressing the point set in box coordinates.
-/

open Filter Topology Matrix

open Classical

noncomputable section

namespace MinBox

variable {K : Finset (Fin 3 → ℝ)}

/-- **The conclusion of the theorem** for the box with orientation `R`:

1. two box faces on different axes (hence adjacent) each contain a polyhedron edge, and
2. either some box face is flush with a polygonal face of the polyhedron (which contributes at
   least three edge–face contacts on its own), or three different box faces each contain a
   polyhedron edge.

Together: at least three edge–face contacts, at least two of them on adjacent faces. -/
def ThreeContacts (K : Finset (Fin 3 → ℝ)) (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  (∃ f g : Fin 3 × Bool, f.1 ≠ g.1 ∧ HasEdge K R f ∧ HasEdge K R g) ∧
    ((∃ f, HasFace K R f) ∨
      ∃ f g h : Fin 3 × Bool, f ≠ g ∧ f ≠ h ∧ g ≠ h ∧
        HasEdge K R f ∧ HasEdge K R g ∧ HasEdge K R h)

/-! ## The theorem in the frame of the box -/

lemma faceNormal_one_true (m : Fin 3) : faceNormal 1 (m, true) = e m := by
  simp [faceNormal, axis_one]

lemma faceNormal_one_false (m : Fin 3) : faceNormal 1 (m, false) = -e m := by
  simp [faceNormal, axis_one]

lemma exists_other (i : Fin 3) : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  revert i; decide

lemma exists_third {i j : Fin 3} (h : i ≠ j) : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
  revert i j; decide

/-- A box face that contains no edge touches the polyhedron in a single vertex. -/
lemma eq_of_not_hasEdge {R : Matrix (Fin 3) (Fin 3) ℝ} {f : Fin 3 × Bool}
    (h : ¬ HasEdge K R f) :
    ∀ y ∈ contactSet K (faceNormal R f), ∀ y' ∈ contactSet K (faceNormal R f), y = y' :=
  Finset.card_le_one.1 (not_lt.1 h)

/-- A collinear set that is not contained in a plane `x_k = const` has a slope: the `n`-th
coordinate is an affine function of the `k`-th coordinate along it. -/
lemma exists_slope {S : Finset (Fin 3 → ℝ)} (hcol : Collinear ℝ (S : Set (Fin 3 → ℝ)))
    (n : Fin 3) {k : Fin 3} (hne : ∃ x ∈ S, ∃ y ∈ S, x k ≠ y k) :
    ∃ α : ℝ, ∀ y ∈ S, ∀ y' ∈ S, y n - y' n = α * (y k - y' k) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hne
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (Finset.mem_coe.2 hx)).1 hcol
  have hvk : v k ≠ 0 := by
    obtain ⟨r, hr⟩ := hv y (Finset.mem_coe.2 hy)
    intro h0
    apply hxy
    have := congrFun hr k
    simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0, mul_zero,
      zero_add] at this
    exact this.symm
  refine ⟨v n / v k, fun p hp p' hp' => ?_⟩
  obtain ⟨r, hr⟩ := hv p (Finset.mem_coe.2 hp)
  obtain ⟨r', hr'⟩ := hv p' (Finset.mem_coe.2 hp')
  have e1 := congrFun hr n
  have e2 := congrFun hr k
  have e3 := congrFun hr' n
  have e4 := congrFun hr' k
  simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4
  rw [e1, e2, e3, e4]
  field_simp
  ring

/-- **The theorem in the frame of the box.** -/
theorem three_contacts_one (hpos : 0 < boxVolume K 1)
    (hmin : IsLocalMinOn (boxVolume K) SO3 1) : ThreeContacts K 1 := by
  have hK := nonempty_of_boxVolume_pos hpos
  have hw : ∀ m, 0 < width K (e m) := fun m => by
    simpa [axis_one] using width_pos_of_boxVolume_pos hpos m
  -- restating a property of both faces of an axis in terms of `±eₘ`
  have split : ∀ (m : Fin 3) (Φ : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Prop),
      (∀ b, ∀ y ∈ contactSet K (faceNormal 1 (m, b)),
        ∀ y' ∈ contactSet K (faceNormal 1 (m, b)), Φ y y') →
      (∀ y ∈ contactSet K (e m), ∀ y' ∈ contactSet K (e m), Φ y y') ∧
        (∀ y ∈ contactSet K (-e m), ∀ y' ∈ contactSet K (-e m), Φ y y') := by
    intro m Φ h
    have hT := h true
    have hF := h false
    rw [faceNormal_one_true] at hT
    rw [faceNormal_one_false] at hF
    exact ⟨hT, hF⟩
  -- Step 4 of the writeup: contacts cannot all lie on one pair of opposite faces
  have part1 : ∃ f g : Fin 3 × Bool, f.1 ≠ g.1 ∧ HasEdge K 1 f ∧ HasEdge K 1 g := by
    by_contra hcon
    have hax : ∃ i : Fin 3, ∀ g : Fin 3 × Bool, g.1 ≠ i → ¬ HasEdge K 1 g := by
      by_cases hE : ∃ f, HasEdge K 1 f
      · obtain ⟨f, hf⟩ := hE
        exact ⟨f.1, fun g hg hgE => hcon ⟨f, g, hg.symm, hf, hgE⟩⟩
      · exact ⟨0, fun g _ hgE => hE ⟨g, hgE⟩⟩
    obtain ⟨i, hi⟩ := hax
    obtain ⟨j, k, hij, hik, hjk⟩ := exists_other i
    -- the faces of the axes `j` and `k` touch single vertices: rotate about `eᵢ`
    obtain ⟨hkp, hkm⟩ := split k (fun y y' => y j = y' j) fun b y hy y' hy' => by
      rw [eq_of_not_hasEdge (hi (k, b) hik.symm) y hy y' hy']
    obtain ⟨hjp, hjm⟩ := split j (fun y y' => y k = y' k) fun b y hy y' hy' => by
      rw [eq_of_not_hasEdge (hi (j, b) hij.symm) y hy y' hy']
    exact caseA hK hij hik hjk (hw i) (hw j) (hw k) hmin hkp hkm hjp hjm
  refine ⟨part1, ?_⟩
  -- Step 3 of the writeup: at most two contacts is impossible
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnoface, hno3⟩ := hcon
  have hcol : ∀ f, Collinear ℝ (contactSet K (faceNormal 1 f) : Set (Fin 3 → ℝ)) := fun f => by
    by_contra h
    exact hnoface ⟨f, h⟩
  obtain ⟨⟨i, bf⟩, ⟨j, bg⟩, hfg, hf, hg⟩ := part1
  have hij : i ≠ j := hfg
  have hother : ∀ h : Fin 3 × Bool, h ≠ (i, bf) → h ≠ (j, bg) → ¬ HasEdge K 1 h :=
    fun h hhf hhg hh =>
      hno3 ⟨(i, bf), (j, bg), h, fun heq => hij (congrArg Prod.fst heq), hhf.symm, hhg.symm,
        hf, hg, hh⟩
  obtain ⟨k, hik, hjk⟩ := exists_third hij
  -- the two faces of the third axis touch single vertices
  have single_k : ∀ b, ∀ y ∈ contactSet K (faceNormal 1 (k, b)),
      ∀ y' ∈ contactSet K (faceNormal 1 (k, b)), y = y' := fun b =>
    eq_of_not_hasEdge (hother (k, b) (by simp [hik.symm]) (by simp [hjk.symm]))
  -- the face opposite to an edge face touches a single vertex
  have single_i : ∀ b, b ≠ bf → ∀ y ∈ contactSet K (faceNormal 1 (i, b)),
      ∀ y' ∈ contactSet K (faceNormal 1 (i, b)), y = y' := fun b hb =>
    eq_of_not_hasEdge (hother (i, b) (by simp [hb]) (by simp [hij]))
  have single_j : ∀ b, b ≠ bg → ∀ y ∈ contactSet K (faceNormal 1 (j, b)),
      ∀ y' ∈ contactSet K (faceNormal 1 (j, b)), y = y' := fun b hb =>
    eq_of_not_hasEdge (hother (j, b) (by simp [hij.symm]) (by simp [hb]))
  by_cases hfk : ∀ y ∈ contactSet K (faceNormal 1 (i, bf)),
      ∀ y' ∈ contactSet K (faceNormal 1 (i, bf)), y k = y' k
  · -- the edge on axis `i` is parallel to `e_j`: rotate about `e_j`
    obtain ⟨hkp, hkm⟩ := split k (fun y y' => y i = y' i) fun b y hy y' hy' => by
      rw [single_k b y hy y' hy']
    obtain ⟨hip, him⟩ := split i (fun y y' => y k = y' k) fun b => by
      by_cases hb : b = bf
      · subst hb; exact hfk
      · intro y hy y' hy'; rw [single_i b hb y hy y' hy']
    exact caseA hK hij.symm hjk hik (hw j) (hw i) (hw k) hmin hkp hkm hip him
  by_cases hgk : ∀ y ∈ contactSet K (faceNormal 1 (j, bg)),
      ∀ y' ∈ contactSet K (faceNormal 1 (j, bg)), y k = y' k
  · -- the edge on axis `j` is parallel to `eᵢ`: rotate about `eᵢ`
    obtain ⟨hkp, hkm⟩ := split k (fun y y' => y j = y' j) fun b y hy y' hy' => by
      rw [single_k b y hy y' hy']
    obtain ⟨hjp, hjm⟩ := split j (fun y y' => y k = y' k) fun b => by
      by_cases hb : b = bg
      · subst hb; exact hgk
      · intro y hy y' hy'; rw [single_j b hb y hy y' hy']
    exact caseA hK hij hik hjk (hw i) (hw j) (hw k) hmin hkp hkm hjp hjm
  -- generic position: follow the curve that keeps both edge contacts
  · have hfk' : ∃ x ∈ contactSet K (faceNormal 1 (i, bf)),
        ∃ y ∈ contactSet K (faceNormal 1 (i, bf)), x k ≠ y k := by
      by_contra h
      exact hfk fun y hy y' hy' => by
        by_contra hne
        exact h ⟨y, hy, y', hy', hne⟩
    have hgk' : ∃ x ∈ contactSet K (faceNormal 1 (j, bg)),
        ∃ y ∈ contactSet K (faceNormal 1 (j, bg)), x k ≠ y k := by
      by_contra h
      exact hgk fun y hy y' hy' => by
        by_contra hne
        exact h ⟨y, hy, y', hy', hne⟩
    obtain ⟨α, hα⟩ := exists_slope (hcol (i, bf)) j hfk'
    obtain ⟨β, hβ⟩ := exists_slope (hcol (j, bg)) i hgk'
    obtain ⟨hip, him⟩ := split i (fun y y' => y j - y' j = α * (y k - y' k)) fun b => by
      by_cases hb : b = bf
      · subst hb; exact hα
      · intro y hy y' hy'; rw [single_i b hb y hy y' hy']; ring
    obtain ⟨hjp, hjm⟩ := split j (fun y y' => y i - y' i = β * (y k - y' k)) fun b => by
      by_cases hb : b = bg
      · subst hb; exact hβ
      · intro y hy y' hy'; rw [single_j b hb y hy y' hy']; ring
    obtain ⟨hkp, hkm⟩ := split k (fun y y' => y i = y' i ∧ y j = y' j) fun b y hy y' hy' => by
      rw [single_k b y hy y' hy']; exact ⟨rfl, rfl⟩
    exact caseB hK hij hik hjk (hw i) (hw j) (hw k) hmin hip him hjp hjm hkp hkm

/-! ## Transport to an arbitrary orientation -/

/-- Coordinates of a point in the frame `R`. -/
def toFrame (R : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ := Rᵀ *ᵥ x

lemma toFrame_dot (R : Matrix (Fin 3) (Fin 3) ℝ) (x v : Fin 3 → ℝ) :
    toFrame R x ⬝ᵥ v = x ⬝ᵥ (R *ᵥ v) := by
  unfold toFrame
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]

lemma supp_image (R : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    supp (K.image (toFrame R)) v = supp K (R *ᵥ v) := by
  by_cases hK : K.Nonempty
  · have hK' : (K.image (toFrame R)).Nonempty := hK.image _
    apply le_antisymm
    · obtain ⟨x', hx', h⟩ := exists_eq_supp hK' v
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
      rw [h, toFrame_dot]
      exact le_supp hx _
    · obtain ⟨x, hx, h⟩ := exists_eq_supp hK (R *ᵥ v)
      rw [h, ← toFrame_dot]
      exact le_supp (Finset.mem_image_of_mem _ hx) _
  · have : K = ∅ := Finset.not_nonempty_iff_eq_empty.1 hK
    subst this
    simp [supp]

lemma width_image (R : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    width (K.image (toFrame R)) v = width K (R *ᵥ v) := by
  unfold width
  rw [supp_image, supp_image, Matrix.mulVec_neg]

lemma axis_mul (R Q : Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3) :
    axis (R * Q) m = R *ᵥ axis Q m := by
  funext a
  simp [axis, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- The box volume of the point set in frame coordinates. -/
lemma boxVolume_image (R Q : Matrix (Fin 3) (Fin 3) ℝ) :
    boxVolume (K.image (toFrame R)) Q = boxVolume K (R * Q) := by
  unfold boxVolume
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [width_image, axis_mul]

lemma faceNormal_mul (R Q : Matrix (Fin 3) (Fin 3) ℝ) (f : Fin 3 × Bool) :
    faceNormal (R * Q) f = R *ᵥ faceNormal Q f := by
  unfold faceNormal
  split_ifs <;> simp [axis_mul, Matrix.mulVec_neg]

lemma contactSet_image_subset (R : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    contactSet (K.image (toFrame R)) v ⊆ (contactSet K (R *ᵥ v)).image (toFrame R) := by
  intro x' hx'
  obtain ⟨hx'K, hmax⟩ := mem_contactSet.1 hx'
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'K
  refine Finset.mem_image_of_mem _ (mem_contactSet.2 ⟨hx, fun y hy => ?_⟩)
  have := hmax (toFrame R y) (Finset.mem_image_of_mem _ hy)
  rwa [toFrame_dot, toFrame_dot] at this

lemma hasEdge_of_image {R : Matrix (Fin 3) (Fin 3) ℝ} {f : Fin 3 × Bool}
    (h : HasEdge (K.image (toFrame R)) 1 f) : HasEdge K R f := by
  unfold HasEdge at *
  have h1 := Finset.card_le_card (contactSet_image_subset (K := K) R (faceNormal 1 f))
  have h2 := Finset.card_image_le (s := contactSet K (R *ᵥ faceNormal 1 f)) (f := toFrame R)
  have h3 : R *ᵥ faceNormal 1 f = faceNormal R f := by rw [← faceNormal_mul, mul_one]
  rw [h3] at h1 h2
  omega

lemma hasFace_of_image {R : Matrix (Fin 3) (Fin 3) ℝ} {f : Fin 3 × Bool}
    (h : HasFace (K.image (toFrame R)) 1 f) : HasFace K R f := by
  unfold HasFace at *
  intro hcol
  apply h
  have h3 : R *ᵥ faceNormal 1 f = faceNormal R f := by rw [← faceNormal_mul, mul_one]
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).1 hcol
  refine (collinear_iff_exists_forall_eq_smul_vadd _).2 ⟨toFrame R p₀, toFrame R v, ?_⟩
  intro x' hx'
  have hx'' := contactSet_image_subset (K := K) R (faceNormal 1 f) (Finset.mem_coe.1 hx')
  rw [h3] at hx''
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx''
  obtain ⟨r, hr⟩ := hv x (Finset.mem_coe.2 hx)
  refine ⟨r, ?_⟩
  rw [hr]
  simp only [toFrame, vadd_eq_add, Matrix.mulVec_add, Matrix.mulVec_smul]

lemma isLocalMinOn_image {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3)
    (hmin : IsLocalMinOn (boxVolume K) SO3 R) :
    IsLocalMinOn (boxVolume (K.image (toFrame R))) SO3 1 := by
  have hcont : Continuous fun Q : Matrix (Fin 3) (Fin 3) ℝ => R * Q :=
    continuous_const.matrix_mul continuous_id
  have hmaps : Set.MapsTo (fun Q : Matrix (Fin 3) (Fin 3) ℝ => R * Q) SO3 SO3 := by
    intro Q hQ
    refine ⟨?_, ?_⟩
    · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ, hR.1, Matrix.one_mul,
        hQ.1]
    · rw [Matrix.det_mul, hR.2, hQ.2, one_mul]
  have ht : Tendsto (fun Q : Matrix (Fin 3) (Fin 3) ℝ => R * Q) (𝓝[SO3] 1) (𝓝[SO3] (R * 1)) :=
    hcont.continuousWithinAt.tendsto_nhdsWithin hmaps
  rw [mul_one] at ht
  have hev : ∀ᶠ Q in 𝓝[SO3] (1 : Matrix (Fin 3) (Fin 3) ℝ),
      boxVolume K R ≤ boxVolume K (R * Q) := ht.eventually hmin
  change ∀ᶠ Q in 𝓝[SO3] (1 : Matrix (Fin 3) (Fin 3) ℝ),
    boxVolume (K.image (toFrame R)) 1 ≤ boxVolume (K.image (toFrame R)) Q
  filter_upwards [hev] with Q hQ
  rw [boxVolume_image, boxVolume_image, mul_one]
  exact hQ

/-! ## The main theorem -/

/-- **Conjecture 7.1 (Jylänki 2015), in the stronger form for local minima.**

Let `K` be a finite point set in `ℝ³` (the vertices of a convex polyhedron), and let the
orientation `R ∈ SO(3)` be a local minimum of the volume of the enclosing box, with positive
volume.  Then two adjacent faces of that box each contain an edge of the polyhedron, and
altogether there are at least three edge–face contacts: either a box face is flush with a
polygonal face of the polyhedron, or three different box faces each contain an edge. -/
theorem three_contacts (K : Finset (Fin 3 → ℝ)) (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R ∈ SO3)
    (hpos : 0 < boxVolume K R) (hmin : IsLocalMinOn (boxVolume K) SO3 R) :
    ThreeContacts K R := by
  have hpos' : 0 < boxVolume (K.image (toFrame R)) 1 := by
    rw [boxVolume_image, mul_one]; exact hpos
  obtain ⟨⟨f, g, hfg, hf, hg⟩, h2⟩ := three_contacts_one hpos' (isLocalMinOn_image hR hmin)
  refine ⟨⟨f, g, hfg, hasEdge_of_image hf, hasEdge_of_image hg⟩, ?_⟩
  rcases h2 with ⟨f, hf⟩ | ⟨f, g, h, h1, h2, h3, hf, hg, hh⟩
  · exact Or.inl ⟨f, hasFace_of_image hf⟩
  · exact Or.inr ⟨f, g, h, h1, h2, h3, hasEdge_of_image hf, hasEdge_of_image hg,
      hasEdge_of_image hh⟩

/-- **Conjecture 7.1 as stated**: a box of minimal volume (a global minimum over all
orientations) has the three contacts. -/
theorem three_contacts_of_isMinOn (K : Finset (Fin 3 → ℝ)) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : R ∈ SO3) (hpos : 0 < boxVolume K R) (hmin : IsMinOn (boxVolume K) SO3 R) :
    ThreeContacts K R :=
  three_contacts K R hR hpos hmin.isLocalMinOn

/-- `SO3` is Mathlib's special orthogonal group. -/
lemma mem_SO3_iff (R : Matrix (Fin 3) (Fin 3) ℝ) :
    R ∈ SO3 ↔ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  rfl

end MinBox
