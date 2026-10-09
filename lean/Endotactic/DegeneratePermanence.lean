import Endotactic.Stoichiometry
import Endotactic.IntegralUniqueness

/-!
# Permanence when every reaction vector vanishes

This includes empty reaction sets. Each positive class is the singleton `{c}`,
and the integral equation forces every solution to be constant. No lower-rate
bound or endotacticity hypothesis is needed for this degenerate case.
-/

namespace Endotactic

open Set MeasureTheory

variable {d : ℕ} {E : Type*}

theorem Network.stoichiometricSubspace_eq_bot_of_vectors_zero (N : Network d E)
    (hzero : ∀ e, N.vector e = 0) : N.stoichiometricSubspace = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  rintro v ⟨e, rfl⟩
  rw [hzero e]
  exact Submodule.zero_mem _

variable [Fintype E]

theorem Network.rhs_eq_zero_of_vectors_zero (N : Network d E)
    (hzero : ∀ e, N.vector e = 0) (k : E → ℝ) (x : State d) : N.rhs k x = 0 := by
  simp [Network.rhs, hzero]

omit [Fintype E] in
theorem Network.positiveClass_eq_singleton_of_vectors_zero (N : Network d E)
    (hzero : ∀ e, N.vector e = 0) {c : State d} (hc : Positive c) :
    N.positiveClass c = {c} := by
  ext x
  simp only [Network.positiveClass, mem_ofPred_eq, mem_singleton_iff]
  rw [N.stoichiometricSubspace_eq_bot_of_vectors_zero hzero, Submodule.mem_bot,
    sub_eq_zero]
  constructor
  · exact fun h => h.2
  · rintro rfl
    exact ⟨hc, rfl⟩

theorem Network.constant_integralSolution_of_vectors_zero (N : Network d E)
    (hzero : ∀ e, N.vector e = 0) (k : E → ℝ → ℝ) (z : State d) :
    N.IsIntegralSolution k z (fun _ => z) := by
  refine ⟨continuous_const.continuousOn, rfl, ?_, ?_⟩
  · intro T _
    simp only [N.rhs_eq_zero_of_vectors_zero hzero]
    exact intervalIntegrable_const
  · intro t _
    simp [N.rhs_eq_zero_of_vectors_zero hzero]

theorem Network.integralSolution_eq_initial_of_vectors_zero (N : Network d E)
    (hzero : ∀ e, N.vector e = 0) {k : E → ℝ → ℝ} {z : State d}
    {x : ℝ → State d} (hx : N.IsIntegralSolution k z x) {t : ℝ} (ht : 0 ≤ t) :
    x t = z := by
  simpa [N.rhs_eq_zero_of_vectors_zero hzero] using hx.2.2.2 t ht

theorem Network.positiveWellPosed_of_vectors_zero (N : Network d E)
    (hzero : ∀ e, N.vector e = 0) (k : E → ℝ → ℝ) {z : State d} (hz : Positive z) :
    N.PositiveWellPosed k z := by
  refine ⟨fun _ => z, ⟨N.constant_integralSolution_of_vectors_zero hzero k z,
    fun _ _ => hz⟩, ?_⟩
  intro y hy t ht
  exact N.integralSolution_eq_initial_of_vectors_zero hzero hy.1 ht

theorem Network.uniformPermanent_of_vectors_zero (N : Network d E)
    (hzero : ∀ e, N.vector e = 0) (ℓ u : ℝ) {c : State d} (hc : Positive c)
    (regular : (E → ℝ → ℝ) → Prop) : N.UniformPermanent ℓ u c regular := by
  refine ⟨{c}, singleton_nonempty c, isCompact_singleton, ?_, ?_⟩
  · rw [N.positiveClass_eq_singleton_of_vectors_zero hzero hc]
  · intro k _ _
    refine ⟨fun z hz => N.positiveWellPosed_of_vectors_zero hzero k hz.1, ?_⟩
    intro z hz x hx
    have hzc : z = c := by
      rw [N.positiveClass_eq_singleton_of_vectors_zero hzero hc] at hz
      exact hz
    refine ⟨0, le_rfl, ?_⟩
    intro t ht
    exact (N.integralSolution_eq_initial_of_vectors_zero hzero hx.1 ht).trans hzc

end Endotactic
