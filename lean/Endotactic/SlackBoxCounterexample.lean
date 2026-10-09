import Endotactic.SlackBoxPermanence
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Strict exterior signs do not imply finite entry into the unrelaxed target

At the admissible endpoint rates `(1,2,1,1)`, the positive trajectory
`x(t) = (1/2 - exp(-2t)/4, 1)` approaches the tight target `[1/2,2]^2`
from below and never enters it at a finite time. The path is an actual global
positive integral solution of the two-species endotactic network.

This refutes only absorption into this specified tight set, not permanence:
every positive relaxation is absorbing by `SlackBoxPermanence`.
-/

namespace Endotactic.SlackBox

open Set MeasureTheory

def endpointRates (e : Fin 4) (_t : ℝ) : ℝ := ![1, 2, 1, 1] e

noncomputable def approachingPath (t : ℝ) : State 2 :=
  ![1 / 2 - Real.exp (-2 * t) / 4, 1]

theorem endpointRates_admissible : AdmissibleRates endpointRates 1 2 := by
  constructor
  · intro e; exact measurable_const
  · intro e _ _; fin_cases e <;> norm_num [endpointRates]

theorem approachingPath_continuous : Continuous approachingPath := by
  unfold approachingPath
  fun_prop

theorem approachingPath_positive {t : ℝ} (ht : 0 ≤ t) : Positive (approachingPath t) := by
  have he : Real.exp (-2 * t) ≤ 1 := by
    have hh := Real.exp_le_exp.mpr (by linarith : -2 * t ≤ 0)
    simpa only [Real.exp_zero] using hh
  intro i
  fin_cases i
  · change 0 < 1 / 2 - Real.exp (-2 * t) / 4
    linarith
  · change 0 < (1 : ℝ)
    norm_num

set_option backward.isDefEq.respectTransparency false in
theorem approachingPath_hasDerivAt (t : ℝ) :
    HasDerivAt approachingPath (network.rhs (fun e => endpointRates e t) (approachingPath t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun s => 1 / 2 - Real.exp (-2 * s) / 4)
      (network.rhs (fun e => endpointRates e t) (approachingPath t) 0) t
    rw [(rhs_at _ _).1]
    change HasDerivAt (fun s => 1 / 2 - Real.exp (-2 * s) / 4)
      (1 - 2 * (1 / 2 - Real.exp (-2 * t) / 4)) t
    have hd := (((hasDerivAt_id t).const_mul (-2)).exp.div_const 4).const_sub (1 / 2)
    convert hd using 1 <;> first | rfl | (simp only [id_eq]; ring)
  · change HasDerivAt (fun _ : ℝ => (1 : ℝ))
      (network.rhs (fun e => endpointRates e t) (approachingPath t) 1) t
    rw [(rhs_at _ _).2]
    simpa [endpointRates, approachingPath] using hasDerivAt_const t (1 : ℝ)

theorem approachingPath_integralSolution :
    network.IsIntegralSolution endpointRates (approachingPath 0) approachingPath := by
  have hc : Continuous (fun t => network.rhs (fun e => endpointRates e t) (approachingPath t)) :=
    network.rhs_joint_contDiff.continuous.comp
      (continuous_const.prodMk approachingPath_continuous)
  refine ⟨approachingPath_continuous.continuousOn, rfl,
    fun T _ => hc.intervalIntegrable 0 T, ?_⟩
  intro t _
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_hs : s ∈ uIcc 0 t) => approachingPath_hasDerivAt s) (hc.intervalIntegrable 0 t)
  rw [heq, add_sub_cancel]

theorem approachingPath_globalPositive :
    network.IsGlobalPositiveSolution endpointRates (approachingPath 0) approachingPath :=
  ⟨approachingPath_integralSolution, fun _ ht => approachingPath_positive ht⟩

theorem approachingPath_outside_tight_target (t : ℝ) :
    approachingPath t ∉ targetFamily.plateau 0 := by
  intro hp
  have hh := hp 0
  have hlow : 0 ≤ approachingPath t 0 - 1 / 2 := by
    simpa [targetFamily_value] using hh
  simp only [approachingPath, Matrix.cons_val_zero] at hlow
  linarith [Real.exp_pos (-2 * t)]

theorem approachingPath_not_eventuallyIn_tight_target :
    ¬ EventuallyIn approachingPath (targetFamily.plateau 0) := by
  rintro ⟨T, _, hstay⟩
  exact approachingPath_outside_tight_target T (hstay T le_rfl)

end Endotactic.SlackBox
