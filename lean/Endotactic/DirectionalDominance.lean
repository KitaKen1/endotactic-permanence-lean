import Endotactic.MonomialOrder
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Eventual positive flux along any fixed nonconserved exponent ray

The threshold is uniform over all coefficients in the box, but depends on the
direction. Uniform control over ALL active plateau directions remains the hard
geometric step of the general theorem.
-/

namespace Endotactic

open Filter Topology

theorem fixed_direction_eventual_positive_flux {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (r : State d) (hnonzero : ∃ e : E, N.projection r e ≠ 0)
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hlu : ℓ ≤ u) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
        0 < dot r (N.rhs k (exponentialPoint h r)) := by
  obtain ⟨a, ha⟩ := exists_essentialMinimum N hnonzero
  obtain ⟨H, hH, hgap⟩ := exists_positive_negative_source_gap N hN ha
  have hpositive : 0 < ℓ * N.projection r a :=
    mul_pos hℓ (essentialMinimum_projection_pos N hN ha)
  have hlimit : Tendsto (fun h : ℝ => u * h ^ H * negativeMass (N.projection r))
      (𝓝 0) (𝓝 0) := by
    have hr : Tendsto (fun h : ℝ => h ^ H) (𝓝 0) (𝓝 0) := by
      simpa only [Real.zero_rpow hH.ne'] using
        (Real.continuousAt_rpow_const 0 H (.inr hH.le)).tendsto
    simpa only [mul_zero, zero_mul] using
      (hr.const_mul u).mul_const (negativeMass (N.projection r))
  have hevent : ∀ᶠ h : ℝ in 𝓝 0,
      u * h ^ H * negativeMass (N.projection r) < ℓ * N.projection r a :=
    hlimit.eventually (eventually_lt_nhds hpositive)
  obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨min ε 1, lt_min hε (by norm_num), ?_⟩
  intro h hh hh₀ k hk
  have hhε : h < ε := lt_of_lt_of_le hh₀ (min_le_left _ _)
  have hh1 : h ≤ 1 := (lt_of_lt_of_le hh₀ (min_le_right _ _)).le
  apply exponentialPoint_flux_pos N hN r r k a ℓ u h H hℓ
    (hℓ.le.trans hlu) hh hh1 hk ha
  · simpa only [Network.sourceLevel] using hgap
  · exact hsmall (by simpa [Real.dist_eq, abs_of_pos hh] using hhε)

end Endotactic
