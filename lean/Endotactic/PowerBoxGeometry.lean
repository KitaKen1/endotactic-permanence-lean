import Endotactic.LogarithmicBox
import Endotactic.ScaleIteration

/-!
# Narrow power boxes and capped square-root scales
-/

namespace Endotactic

noncomputable def powerBox {d : ℕ} (h β : ℝ) : Set (State d) :=
  Set.Icc (fun _ => h ^ β) (fun _ => (h ^ β)⁻¹)

theorem powerBox_positive {d : ℕ} {h β : ℝ} (hh : 0 < h) :
    powerBox (d := d) h β ⊆ {x | Positive x} :=
  fun _ hx j => (Real.rpow_pos_of_pos hh β).trans_le (hx.1 j)

theorem logarithmicExponent_power_scale {d : ℕ} {h β : ℝ}
    (hh : 0 < h) (hβ : β ≠ 0) (x : State d) :
    logarithmicExponent h x = β • logarithmicExponent (h ^ β) x := by
  ext j
  simp only [logarithmicExponent, Pi.smul_apply, smul_eq_mul, Real.log_rpow hh]
  by_cases hl : Real.log h = 0
  · simp [hl]
  · field_simp

theorem logarithmicExponent_mem_power_cube {d : ℕ} {h β : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hβ : 0 < β) {x : State d}
    (hx : x ∈ powerBox h β) :
    logarithmicExponent h x ∈ Set.Icc (fun _ => -β) (fun _ => β) := by
  have hg := Real.rpow_pos_of_pos hh β
  have hg1 := Real.rpow_lt_one hh.le hh1 hβ
  have hp := logarithmicExponent_mem_cube hg hg1 hx
  rw [logarithmicExponent_power_scale hh hβ.ne' x]
  constructor
  · intro j
    simpa only [Pi.smul_apply, smul_eq_mul, mul_neg_one] using
      mul_le_mul_of_nonneg_left (hp.1 j) hβ.le
  · intro j
    simpa only [Pi.smul_apply, smul_eq_mul, mul_one] using
      mul_le_mul_of_nonneg_left (hp.2 j) hβ.le

theorem logarithmicExponent_power_boundary_norm {d : ℕ} {h β : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hβ : 0 < β) {x : State d}
    (hx : x ∈ powerBox h β)
    (hboundary : x ∉ openCoordinateBox (fun _ => h ^ β) (fun _ => (h ^ β)⁻¹)) :
    β ≤ ‖logarithmicExponent h x‖ := by
  have hg := Real.rpow_pos_of_pos hh β
  have hg1 := Real.rpow_lt_one hh.le hh1 hβ
  have hn := logarithmicExponent_boundary_norm hg hg1 hx hboundary
  rw [logarithmicExponent_power_scale hh hβ.ne' x, norm_smul, Real.norm_eq_abs,
    abs_of_pos hβ]
  nlinarith

theorem logarithmicExponent_norm_lt_mem_open_power_box {d : ℕ} {h β : ℝ}
    (hh : 0 < h) (hh1 : h < 1) {x : State d} (hx : Positive x)
    (hp : ‖logarithmicExponent h x‖ < β) :
    x ∈ openCoordinateBox (fun _ => h ^ β) (fun _ => (h ^ β)⁻¹) := by
  have hpow := exponentialPoint_logarithmicExponent hh hh1 hx
  intro j
  have hb : |logarithmicExponent h x j| < β :=
    (show |logarithmicExponent h x j| ≤ ‖logarithmicExponent h x‖ by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (logarithmicExponent h x) j).trans_lt hp
  have hr := abs_lt.mp hb
  have hlo := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hr.2
  have hhi := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hr.1
  have heq : h ^ logarithmicExponent h x j = x j := congrFun hpow j
  simpa only [heq, Real.rpow_neg hh.le] using And.intro hlo hhi

theorem powerBox_subset_unit_box {d : ℕ} {h β g : ℝ}
    (hh : 0 < h) (hg : 0 < g) (hgh : g ≤ h ^ β) :
    powerBox (d := d) h β ⊆ Set.Icc (fun _ => g) (fun _ => g⁻¹) := by
  intro x hx
  refine ⟨fun j => hgh.trans (hx.1 j), fun j => (hx.2 j).trans ?_⟩
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hh β) hg).mpr hgh

theorem capped_sqrt_le_quarter_power {h H : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    min (Real.sqrt h) H ≤ h ^ (1 / 4 : ℝ) := by
  apply (min_le_left _ _).trans
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_ge hh hh1 (by norm_num)

end Endotactic
