import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# Finite termination of square-root scale enlargement

This proves the numerical part only. The implication from one plateau's bounds
to the next plateau's entry still requires the geometric construction.
-/

namespace Endotactic

open Filter Topology

noncomputable def rootScale (h : ℝ) (n : ℕ) : ℝ := h ^ ((1 / 2 : ℝ) ^ n)

theorem rootScale_zero (h : ℝ) : rootScale h 0 = h := by
  simp [rootScale]

theorem rootScale_succ {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    rootScale h (n + 1) = Real.sqrt (rootScale h n) := by
  rw [Real.sqrt_eq_rpow]
  unfold rootScale
  rw [← Real.rpow_mul hh, pow_succ]

theorem rootScale_pos {h : ℝ} (hh : 0 < h) (n : ℕ) : 0 < rootScale h n :=
  Real.rpow_pos_of_pos hh _

theorem rootScale_tendsto_one {h : ℝ} (hh : 0 < h) :
    Tendsto (rootScale h) atTop (𝓝 1) := by
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hr : Tendsto (fun y : ℝ => h ^ y) (𝓝 (0 : ℝ)) (𝓝 (h ^ (0 : ℝ))) :=
    (Real.continuousAt_const_rpow (a := h) (b := 0) hh.ne').tendsto
  change Tendsto (fun n : ℕ => h ^ ((1 / 2 : ℝ) ^ n)) atTop (𝓝 1)
  simpa only [Function.comp_def, Real.rpow_zero] using hr.comp hp

theorem rootScale_crosses_threshold {h target : ℝ} (hh : 0 < h)
    (htarget : target < 1) : ∃ n : ℕ, target < rootScale h n := by
  have hevent : ∀ᶠ n : ℕ in atTop, target < rootScale h n :=
    (rootScale_tendsto_one hh).eventually (eventually_gt_nhds htarget)
  exact hevent.exists

theorem capped_rootScale_reaches_threshold {h target : ℝ} (hh : 0 < h)
    (htarget : target < 1) : ∃ n : ℕ, min (rootScale h n) target = target := by
  obtain ⟨n, hn⟩ := rootScale_crosses_threshold hh htarget
  exact ⟨n, min_eq_right hn.le⟩

end Endotactic
