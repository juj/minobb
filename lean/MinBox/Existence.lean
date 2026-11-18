import MinBox.Main

/-!
# A minimal box exists

`SO(3)` is compact and the box volume is continuous, so a box of minimal volume exists; by the
main theorem it has the three contacts.  This makes the statement of Conjecture 7.1
("a box of minimal volume circumscribing a convex polyhedron has …") non-vacuous.
-/

open Filter Topology Matrix

noncomputable section

namespace MinBox

variable {K : Finset (Fin 3 → ℝ)}

lemma one_mem_SO3 : (1 : Matrix (Fin 3) (Fin 3) ℝ) ∈ SO3 := by
  refine ⟨?_, ?_⟩ <;> simp

/-- The columns of a rotation matrix are unit vectors. -/
lemma axis_dot_self {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) (m : Fin 3) :
    axis R m ⬝ᵥ axis R m = 1 := by
  have := congrFun (congrFun hR.1 m) m
  simpa [Matrix.mul_apply, Matrix.transpose_apply, axis, dotProduct] using this

lemma isCompact_SO3 : IsCompact SO3 := by
  have hclosed : IsClosed SO3 := by
    have h1 : IsClosed {R : Matrix (Fin 3) (Fin 3) ℝ | Rᵀ * R = 1} :=
      isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id) continuous_const
    have h2 : IsClosed {R : Matrix (Fin 3) (Fin 3) ℝ | R.det = 1} :=
      isClosed_eq continuous_id.matrix_det continuous_const
    exact h1.inter h2
  have hsub : SO3 ⊆ Set.pi Set.univ
      (fun _ : Fin 3 => Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1)) := by
    intro R hR a _ m _
    have h : ∑ b, R b m * R b m = 1 := by
      simpa [axis, dotProduct] using axis_dot_self hR m
    have hle : R a m * R a m ≤ 1 := by
      rw [← h]
      exact Finset.single_le_sum (f := fun b => R b m * R b m)
        (fun b _ => mul_self_nonneg _) (Finset.mem_univ a)
    exact ⟨by nlinarith, by nlinarith⟩
  exact IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc) hclosed hsub

lemma continuous_supp (K : Finset (Fin 3 → ℝ)) : Continuous (supp K) := by
  by_cases hK : K.Nonempty
  · have h : supp K = fun u => K.sup' hK (fun x => x ⬝ᵥ u) := funext (supp_of_nonempty hK)
    rw [h]
    refine Continuous.finset_sup'_apply hK fun x _ => ?_
    change Continuous fun u : Fin 3 → ℝ => ∑ i, x i * u i
    fun_prop
  · have h : supp K = fun _ => 0 := by
      funext u; simp [supp, hK]
    rw [h]
    exact continuous_const

lemma continuous_width (K : Finset (Fin 3 → ℝ)) : Continuous (width K) := by
  unfold width
  exact (continuous_supp K).add ((continuous_supp K).comp continuous_neg)

lemma continuous_boxVolume (K : Finset (Fin 3 → ℝ)) : Continuous (boxVolume K) := by
  unfold boxVolume
  refine continuous_finsetProd _ fun m _ => (continuous_width K).comp ?_
  exact continuous_pi fun a => (continuous_apply m).comp (continuous_apply a)

/-- If `K` has positive width in every direction (it is not contained in a plane), every
enclosing box has positive volume. -/
lemma boxVolume_pos (hK : ∀ u : Fin 3 → ℝ, u ≠ 0 → 0 < width K u)
    {R : Matrix (Fin 3) (Fin 3) ℝ} (hR : R ∈ SO3) : 0 < boxVolume K R := by
  refine Finset.prod_pos fun m _ => hK _ fun h0 => ?_
  have := axis_dot_self hR m
  rw [h0] at this
  simp at this

/-- **Existence.**  A finite point set not contained in a plane has an enclosing box of minimal
volume, and every such box has the three contacts of Conjecture 7.1. -/
theorem exists_minimal_box (K : Finset (Fin 3 → ℝ))
    (hK : ∀ u : Fin 3 → ℝ, u ≠ 0 → 0 < width K u) :
    ∃ R ∈ SO3, IsMinOn (boxVolume K) SO3 R ∧ ThreeContacts K R := by
  obtain ⟨R, hR, hmin⟩ := isCompact_SO3.exists_isMinOn ⟨1, one_mem_SO3⟩
    (continuous_boxVolume K).continuousOn
  exact ⟨R, hR, hmin, three_contacts_of_isMinOn K R hR (boxVolume_pos hK hR) hmin⟩

end MinBox
