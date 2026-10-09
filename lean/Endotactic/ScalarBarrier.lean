import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Scalar growth implies finite-time absorption

These lemmas isolate the final analytic step. In the general permanence proof,
the function is the finite affine minimum along a trajectory. Proving the
appropriate one-sided derivative or absolutely-continuous growth estimate for
that minimum remains a separate obligation.
-/

namespace Endotactic

open Set

set_option backward.isDefEq.respectTransparency false in
theorem growth_of_right_derivative_lower_bound (g g' : ℝ → ℝ) {s t δ : ℝ}
    (hst : s ≤ t) (hg : ContinuousOn g (Icc s t))
    (hg' : ∀ z ∈ Ico s t, HasDerivWithinAt g (g' z) (Ici z) z)
    (hδ : ∀ z ∈ Ico s t, δ ≤ g' z) :
    δ * (t - s) ≤ g t - g s := by
  let : NormedSpace ℝ ℝ := NormedField.toNormedSpace
  have hbound := image_le_of_deriv_right_le_deriv_boundary
    (f := fun z => -g z) (f' := fun z => -g' z) hg.neg
    (fun z hz => (hg' z hz).neg)
    (B := fun z => -g s - δ * (z - s)) (B' := fun _ => -δ)
    (by simp) (by fun_prop)
    (fun z _ => by
      convert ((hasDerivAt_const z (-g s)).sub
        (((hasDerivAt_id z).sub_const s).const_mul δ)).hasDerivWithinAt (s := Ici z)
        using 1 <;> first | rfl | simp)
    (fun z hz => by linarith [hδ z hz])
    (x := t) ⟨hst, le_rfl⟩
  linarith

theorem finite_entry_of_growth (g : ℝ → ℝ) {s M δ : ℝ}
    (hδ : 0 < δ) (hupper : ∀ t, s ≤ t → g t ≤ M)
    (hgrowth : ∀ t, s ≤ t → (∀ z ∈ Icc s t, g z < M) →
      δ * (t - s) ≤ g t - g s) :
    ∃ t : ℝ, s ≤ t ∧ g t = M := by
  by_contra h
  have hlt : ∀ t, s ≤ t → g t < M := by
    intro t ht
    exact lt_of_le_of_ne (hupper t ht) (fun he => h ⟨t, ht, he⟩)
  let t := s + (M - g s + 1) / δ
  have hst : s ≤ t := by
    dsimp [t]
    have hnum : 0 ≤ M - g s + 1 := by linarith [hupper s le_rfl]
    exact le_add_of_nonneg_right (div_nonneg hnum hδ.le)
  have hh := hgrowth t hst (fun z hz => hlt z hz.1)
  have hidentity : δ * (t - s) = M - g s + 1 := by
    dsimp [t]
    rw [add_sub_cancel_left, mul_div_cancel₀ _ hδ.ne']
  rw [hidentity] at hh
  linarith [hupper t hst]

theorem eventual_plateau_of_growth (g : ℝ → ℝ) {s M δ : ℝ}
    (hs : 0 ≤ s) (hδ : 0 < δ) (hupper : ∀ t, s ≤ t → g t ≤ M)
    (hgrowth : ∀ t, s ≤ t → (∀ z ∈ Icc s t, g z < M) →
      δ * (t - s) ≤ g t - g s)
    (hinvariant : ∀ a, s ≤ a → g a = M → ∀ t, a ≤ t → g t = M) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → g t = M := by
  obtain ⟨T, hT, heq⟩ := finite_entry_of_growth g hδ hupper hgrowth
  exact ⟨T, hs.trans hT, hinvariant T hT heq⟩

end Endotactic
