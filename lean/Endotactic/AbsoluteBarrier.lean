import Endotactic.FiniteMinimum
import Endotactic.ScalarBarrier

/-!
# A capped absolutely continuous observable reaches and stays on its plateau

The cap makes its derivative zero almost everywhere on the plateau by Fermat's
theorem. A nonnegative derivative below the cap therefore gives monotonicity;
no separate invariance assumption is needed. A strictly positive lower bound
below the cap then gives finite entry.
-/

namespace Endotactic

open MeasureTheory Set Filter
open scoped Topology

theorem ac_monotone_of_below_cap_deriv_nonneg (g : ℝ → ℝ) {s M : ℝ}
    (hg : ∀ T, s ≤ T → AbsolutelyContinuousOnInterval g s T)
    (hupper : ∀ t, s ≤ t → g t ≤ M)
    (hbelow : ∀ T, s ≤ T → ∀ᵐ t ∂volume,
      t ∈ Icc s T → g t < M → 0 ≤ deriv g t) :
    ∀ a b, s ≤ a → a ≤ b → g a ≤ g b := by
  intro a b hsa hab
  have hsb := hsa.trans hab
  have hac : AbsolutelyContinuousOnInterval g a b := by
    apply (hg b hsb).mono
    simpa only [uIcc_of_le hab, uIcc_of_le hsb] using
      (show Icc a b ⊆ Icc s b from fun _ ht => ⟨hsa.trans ht.1, ht.2⟩)
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ s := by simp [ae_iff, measure_singleton]
  have hd : ∀ᵐ t ∂volume, t ∈ Icc a b → 0 ≤ deriv g t := by
    filter_upwards [hac.ae_differentiableAt, hbelow b hsb, hne]
      with t hdiff hb hts ht
    have hst : s ≤ t := hsa.trans ht.1
    rcases lt_or_eq_of_le (hupper t hst) with hlt | heq
    · exact hb ⟨hst, ht.2⟩ hlt
    · have hmax : IsLocalMax g t := by
        filter_upwards [Ioi_mem_nhds (lt_of_le_of_ne hst hts.symm)] with z hz
        rw [heq]
        exact hupper z hz.le
      rw [hmax.hasDerivAt_eq_zero (hdiff (by simpa only [uIcc_of_le hab] using ht)).hasDerivAt]
  have hh := growth_of_ac_deriv_lower_bound hab hac hd
  linarith

theorem eventual_plateau_of_ac (g : ℝ → ℝ) {s M δ : ℝ}
    (hs : 0 ≤ s) (hδ : 0 < δ)
    (hg : ∀ T, s ≤ T → AbsolutelyContinuousOnInterval g s T)
    (hupper : ∀ t, s ≤ t → g t ≤ M)
    (hbelow : ∀ T, s ≤ T → ∀ᵐ t ∂volume,
      t ∈ Icc s T → g t < M → δ ≤ deriv g t) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t → g t = M := by
  have hmono := ac_monotone_of_below_cap_deriv_nonneg g hg hupper (by
    intro T hT
    filter_upwards [hbelow T hT] with t ht hmem hlt
    exact hδ.le.trans (ht hmem hlt))
  apply eventual_plateau_of_growth g hs hδ hupper
  · intro T hT hlt
    apply growth_of_ac_deriv_lower_bound hT (hg T hT)
    filter_upwards [hbelow T hT] with t ht hmem
    exact ht hmem (hlt t hmem)
  · intro a ha heq t hat
    exact le_antisymm (hupper t (ha.trans hat)) (heq ▸ hmono a t ha hat)

end Endotactic
