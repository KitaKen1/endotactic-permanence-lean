/-
The interval clamping and continuous extension are adapted from LeanPool:
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0; see licenses/LeanPool-Apache-2.0.txt.
Changes: finite-dimensional nonlinear field, direct short-time contraction,
and integral-solution predicates. See THIRD_PARTY_NOTICES.txt.
-/
import Endotactic.Network
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Short-interval integral solutions with bounded measurable nonlinear kinetics

The continuous-path construction and clamping extension are adapted from
Scott Armstrong and Vlad Vicol's LeanPool linear Volterra implementation
(Apache-2.0, 2026), at commit bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8.
Here the field is nonlinear. A sufficiently short interval makes the Volterra
map itself contractive, so no factorial estimate for iterates is needed.

This module proves a fixed point, not merely measurability or regularity.
Applying it to mass action requires a bounded globally Lipschitz cutoff.
-/

namespace Endotactic

open MeasureTheory Set
open scoped Topology NNReal

def intervalClamp {a b : ℝ} (hab : a ≤ b) (t : ℝ) : Icc a b :=
  ⟨max a (min b t), le_max_left _ _, max_le hab (min_le_left _ _)⟩

def extendIntervalCurve {d : ℕ} {a b : ℝ} (hab : a ≤ b)
    (u : C(Icc a b, State d)) : ℝ → State d := fun t => u (intervalClamp hab t)

theorem continuous_extendIntervalCurve {d : ℕ} {a b : ℝ} (hab : a ≤ b)
    (u : C(Icc a b, State d)) : Continuous (extendIntervalCurve hab u) := by
  apply u.continuous.comp
  exact (show Continuous (fun t : ℝ => max a (min b t)) by fun_prop).subtype_mk _

theorem extendIntervalCurve_eq_of_mem {d : ℕ} {a b : ℝ} (hab : a ≤ b)
    (u : C(Icc a b, State d)) {t : ℝ} (ht : t ∈ Icc a b) :
    extendIntervalCurve hab u t = u ⟨t, ht⟩ := by
  simp [extendIntervalCurve, intervalClamp, max_eq_right ht.1, min_eq_right ht.2]

structure BoundedMeasurableODE (d : ℕ) where
  field : ℝ → State d → State d
  initial : State d
  normBound : ℝ
  lipschitzConstant : ℝ≥0
  measurable : Measurable (fun p : ℝ × State d => field p.1 p.2)
  norm_le : ∀ t z, ‖field t z‖ ≤ normBound
  lipschitz : ∀ t, LipschitzWith lipschitzConstant (field t)

variable {d : ℕ} {a b : ℝ}

def BoundedMeasurableODE.curveRhs (D : BoundedMeasurableODE d) (hab : a ≤ b)
    (u : C(Icc a b, State d)) (t : ℝ) : State d := D.field t (extendIntervalCurve hab u t)

theorem BoundedMeasurableODE.curveRhs_intervalIntegrable (D : BoundedMeasurableODE d)
    (hab : a ≤ b) (u : C(Icc a b, State d)) :
    IntervalIntegrable (D.curveRhs hab u) volume a b := by
  have hm : Measurable (D.curveRhs hab u) :=
    D.measurable.comp (measurable_id.prodMk (continuous_extendIntervalCurve hab u).measurable)
  apply intervalIntegrable_iff.mpr
  apply IntegrableOn.of_bound (s := uIoc a b) (μ := volume)
    (by rw [uIoc_of_le hab]; exact measure_Ioc_lt_top)
    (hm.aestronglyMeasurable.mono_measure Measure.restrict_le_self) D.normBound
  exact Filter.Eventually.of_forall fun t => D.norm_le t _

noncomputable def BoundedMeasurableODE.volterra (D : BoundedMeasurableODE d)
    (hab : a ≤ b) : C(Icc a b, State d) → C(Icc a b, State d) := fun u =>
  ⟨fun t => D.initial + ∫ s in a..(t : ℝ), D.curveRhs hab u s, by
    have hp := intervalIntegral.continuousOn_primitive_interval'
      (D.curveRhs_intervalIntegrable hab u) left_mem_uIcc
    have hsum := (continuousOn_const (c := D.initial)).add hp
    exact continuousOn_iff_continuous_domRestrict.mp
      (show ContinuousOn (fun t : ℝ => D.initial + ∫ s in a..t, D.curveRhs hab u s)
        (Icc a b) by simpa only [Pi.add_def, uIcc_of_le hab] using hsum)⟩

theorem BoundedMeasurableODE.dist_volterra_apply_le (D : BoundedMeasurableODE d)
    (hab : a ≤ b) (u v : C(Icc a b, State d)) (t : Icc a b) :
    dist (D.volterra hab u t) (D.volterra hab v t) ≤
      (D.lipschitzConstant : ℝ) * ((t : ℝ) - a) * dist u v := by
  have hsub : uIcc a (t : ℝ) ⊆ uIcc a b := by
    simpa only [uIcc_of_le hab, uIcc_of_le t.property.1] using
      (show Icc a (t : ℝ) ⊆ Icc a b from fun _ hs => ⟨hs.1, hs.2.trans t.property.2⟩)
  change ‖(D.initial + ∫ s in a..(t : ℝ), D.curveRhs hab u s) -
    (D.initial + ∫ s in a..(t : ℝ), D.curveRhs hab v s)‖ ≤ _
  rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
    ((D.curveRhs_intervalIntegrable hab u).mono_set hsub)
    ((D.curveRhs_intervalIntegrable hab v).mono_set hsub)]
  have hb : ∀ s ∈ uIoc a (t : ℝ),
      ‖D.curveRhs hab u s - D.curveRhs hab v s‖ ≤ (D.lipschitzConstant : ℝ) * dist u v := by
    intro s _
    rw [← dist_eq_norm]
    exact ((D.lipschitz s).dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist (intervalClamp hab s))
        D.lipschitzConstant.coe_nonneg)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [abs_of_nonneg (sub_nonneg.mpr t.property.1)] at hh
  convert hh using 1; ring

theorem BoundedMeasurableODE.volterra_lipschitz (D : BoundedMeasurableODE d)
    (hab : a ≤ b) :
    LipschitzWith (D.lipschitzConstant * ⟨b - a, sub_nonneg.mpr hab⟩) (D.volterra hab) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change dist (D.volterra hab u) (D.volterra hab v) ≤
    (D.lipschitzConstant : ℝ) * (b - a) * dist u v
  have hnonneg : 0 ≤ (D.lipschitzConstant : ℝ) * (b - a) * dist u v := by positivity
  rw [ContinuousMap.dist_le hnonneg]
  intro t
  exact (D.dist_volterra_apply_le hab u v t).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_sub_right t.property.2 a)
        D.lipschitzConstant.coe_nonneg) dist_nonneg)

theorem BoundedMeasurableODE.existsUnique_fixedPoint (D : BoundedMeasurableODE d)
    (hab : a ≤ b) (hshort : (D.lipschitzConstant : ℝ) * (b - a) < 1) :
    ∃! u : C(Icc a b, State d), D.volterra hab u = u := by
  have hc : ContractingWith (D.lipschitzConstant * ⟨b - a, sub_nonneg.mpr hab⟩)
      (D.volterra hab) := ⟨hshort, D.volterra_lipschitz hab⟩
  exact ⟨hc.fixedPoint, hc.fixedPoint_isFixedPt,
    fun v hv => hc.fixedPoint_unique hv⟩

/-- An integral solution on one compact time interval. -/
def IntegralSolutionOn (F : ℝ → State d → State d) (z : State d) (a b : ℝ)
    (x : ℝ → State d) : Prop :=
  ContinuousOn x (Icc a b) ∧ x a = z ∧
    IntervalIntegrable (fun t => F t (x t)) volume a b ∧
    ∀ t ∈ Icc a b, x t = z + ∫ s in a..t, F s (x s)

theorem BoundedMeasurableODE.fixedPoint_integralSolution (D : BoundedMeasurableODE d)
    (hab : a ≤ b) (u : C(Icc a b, State d)) (hu : D.volterra hab u = u) :
    IntegralSolutionOn D.field D.initial a b (extendIntervalCurve hab u) := by
  have heq : ∀ t ∈ Icc a b, extendIntervalCurve hab u t =
      D.initial + ∫ s in a..t, D.field s (extendIntervalCurve hab u s) := by
    intro t ht
    have hh := congrArg (fun w : C(Icc a b, State d) => w ⟨t, ht⟩) hu
    rw [extendIntervalCurve_eq_of_mem hab u ht]
    exact hh.symm
  refine ⟨(continuous_extendIntervalCurve hab u).continuousOn, ?_,
    D.curveRhs_intervalIntegrable hab u, heq⟩
  simpa using heq a ⟨le_rfl, hab⟩

theorem BoundedMeasurableODE.exists_integralSolution (D : BoundedMeasurableODE d)
    (hab : a ≤ b) (hshort : (D.lipschitzConstant : ℝ) * (b - a) < 1) :
    ∃ x : ℝ → State d, Continuous x ∧ IntegralSolutionOn D.field D.initial a b x := by
  obtain ⟨u, hu, _⟩ := D.existsUnique_fixedPoint hab hshort
  exact ⟨extendIntervalCurve hab u, continuous_extendIntervalCurve hab u,
    D.fixedPoint_integralSolution hab u hu⟩

end Endotactic
