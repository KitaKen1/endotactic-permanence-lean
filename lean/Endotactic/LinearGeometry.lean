import Endotactic.AffinePlateau
import Endotactic.EssentialSource

/-! # Conserved affine branches cannot obstruct ascent outside the plateau -/

namespace Endotactic

def dotLinear {d : ℕ} (r : State d) : State d →ₗ[ℝ] ℝ where
  toFun := dot r
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem dot_eq_of_zero_projections {d : ℕ} {E : Type*} (N : Network d E)
    (r : State d) {x c : State d} (hx : x - c ∈ N.stoichiometricSubspace)
    (hzero : ∀ e, N.projection r e = 0) : dot r x = dot r c := by
  have hsub : N.stoichiometricSubspace ≤ (dotLinear r).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, rfl⟩
    exact hzero e
  have hh : dot r (x - c) = 0 := hsub hx
  rw [dot_sub] at hh
  linarith

theorem active_direction_has_nonzero_projection {d m : ℕ} {E : Type*}
    (N : Network d E) (A : AffineFamily d m) {x c : State d} {i : Fin m} {M : ℝ}
    (hx : x ∈ N.positiveClass c) (hi : A.Active i x)
    (hout : x ∉ A.plateau M) (hc : c ∈ A.plateau M) :
    ∃ e : E, N.projection (A.slope i) e ≠ 0 := by
  by_contra h
  have hzero : ∀ e, N.projection (A.slope i) e = 0 := by
    simpa only [not_exists, not_not] using h
  have heq := dot_eq_of_zero_projections N (A.slope i) hx.2 hzero
  apply A.active_value_ne_at_class_representative hi hout hc
  simp only [AffineFamily.value]
  rw [heq]

theorem active_direction_has_positive_essential_source {d m : ℕ} {E : Type*}
    [Fintype E] (N : Network d E) (hN : N.IsEndotactic) (A : AffineFamily d m)
    {x c : State d} {i : Fin m} {M : ℝ}
    (hx : x ∈ N.positiveClass c) (hi : A.Active i x)
    (hout : x ∉ A.plateau M) (hc : c ∈ A.plateau M) :
    ∃ e : E, 0 < N.projection (A.slope i) e ∧
      ∀ f : E, N.projection (A.slope i) f < 0 →
        N.sourceLevel (A.slope i) e < N.sourceLevel (A.slope i) f :=
  exists_positive_essential_source N hN
    (active_direction_has_nonzero_projection N A hx hi hout hc)

end Endotactic
