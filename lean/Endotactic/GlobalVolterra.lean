import Endotactic.IntegralUniqueness
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Global bounded-field solutions by an exponentially weighted Volterra map

On bounded continuous paths over `[0,∞)`, conjugate the Volterra map by
`u(t) ↦ exp(c*t) • u(t)`, with `c = L+1`. Its Lipschitz constant is at most
`L/c < 1`, independently of the time horizon. Boundedness of the field makes
the weighted output uniformly bounded. This avoids countable time-step gluing.

The theorem concerns the bounded cutoff field. Recovering the original
mass-action field still requires a proved trapping condition.
-/

namespace Endotactic

open Set MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

variable {d : ℕ}

def nonnegativeClamp (t : ℝ) : Ici (0 : ℝ) :=
  ⟨max 0 t, show 0 ≤ max 0 t from le_max_left _ _⟩

theorem continuous_nonnegativeClamp : Continuous nonnegativeClamp :=
  (show Continuous (fun t : ℝ => max 0 t) by fun_prop).subtype_mk _

def BoundedMeasurableODE.weightRate (D : BoundedMeasurableODE d) : ℝ :=
  (D.lipschitzConstant : ℝ) + 1

theorem BoundedMeasurableODE.weightRate_ge_one (D : BoundedMeasurableODE d) :
    1 ≤ D.weightRate := by dsimp [weightRate]; linarith [D.lipschitzConstant.coe_nonneg]

theorem BoundedMeasurableODE.weightRate_pos (D : BoundedMeasurableODE d) :
    0 < D.weightRate := lt_of_lt_of_le zero_lt_one D.weightRate_ge_one

theorem BoundedMeasurableODE.normBound_nonneg (D : BoundedMeasurableODE d) :
    0 ≤ D.normBound := (norm_nonneg (D.field 0 0)).trans (D.norm_le 0 0)

noncomputable def BoundedMeasurableODE.inflate (D : BoundedMeasurableODE d)
    (u : Ici (0 : ℝ) →ᵇ State d) (t : ℝ) : State d :=
  Real.exp (D.weightRate * t) • u (nonnegativeClamp t)

theorem BoundedMeasurableODE.continuous_inflate (D : BoundedMeasurableODE d)
    (u : Ici (0 : ℝ) →ᵇ State d) : Continuous (D.inflate u) := by
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    (u.continuous.comp continuous_nonnegativeClamp)

theorem BoundedMeasurableODE.path_intervalIntegrable (D : BoundedMeasurableODE d)
    {x : ℝ → State d} (hx : Continuous x) (a b : ℝ) :
    IntervalIntegrable (fun t => D.field t (x t)) volume a b := by
  have hm := D.measurable.comp (measurable_id.prodMk hx.measurable)
  apply intervalIntegrable_iff.mpr
  apply IntegrableOn.of_bound (s := uIoc a b) (μ := volume)
    (show volume (uIoc a b) < ⊤ from measure_Ioc_lt_top)
    (hm.aestronglyMeasurable.mono_measure Measure.restrict_le_self) D.normBound
  exact Filter.Eventually.of_forall fun t => D.norm_le t _

noncomputable def BoundedMeasurableODE.weightedValue (D : BoundedMeasurableODE d)
    (u : Ici (0 : ℝ) →ᵇ State d) (t : ℝ) : State d :=
  Real.exp (-D.weightRate * t) •
    (D.initial + ∫ s in (0 : ℝ)..t, D.field s (D.inflate u s))

theorem BoundedMeasurableODE.continuous_weightedValue (D : BoundedMeasurableODE d)
    (u : Ici (0 : ℝ) →ᵇ State d) : Continuous (D.weightedValue u) := by
  have hp := intervalIntegral.continuous_primitive
    (D.path_intervalIntegrable (D.continuous_inflate u)) 0
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    (continuous_const.add hp)

theorem exp_weight_mul_time_le_one {c t : ℝ} (hc : 1 ≤ c) (ht : 0 ≤ t) :
    Real.exp (-c * t) * t ≤ 1 := by
  have hh : t ≤ Real.exp (c * t) := by
    have hct : t ≤ c * t := by simpa using mul_le_mul_of_nonneg_right hc ht
    have he := Real.add_one_le_exp (c * t)
    linarith
  calc
    Real.exp (-c * t) * t ≤ Real.exp (-c * t) * Real.exp (c * t) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem BoundedMeasurableODE.weightedValue_norm_le (D : BoundedMeasurableODE d)
    (u : Ici (0 : ℝ) →ᵇ State d) {t : ℝ} (ht : 0 ≤ t) :
    ‖D.weightedValue u t‖ ≤ ‖D.initial‖ + D.normBound := by
  have hi : ‖∫ s in (0 : ℝ)..t, D.field s (D.inflate u s)‖ ≤ D.normBound * t := by
    simpa only [sub_zero, abs_of_nonneg ht] using
      intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun s => D.field s (D.inflate u s)) (a := 0) (b := t)
        (fun s _ => D.norm_le s _)
  have he : Real.exp (-D.weightRate * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr D.weightRate_pos.le) ht)
  rw [weightedValue, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-D.weightRate * t) * ‖D.initial + ∫ s in 0..t, D.field s (D.inflate u s)‖ ≤
        Real.exp (-D.weightRate * t) * (‖D.initial‖ + D.normBound * t) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add_right hi _))
        (Real.exp_pos _).le
    _ = Real.exp (-D.weightRate * t) * ‖D.initial‖ +
        D.normBound * (Real.exp (-D.weightRate * t) * t) := by ring
    _ ≤ 1 * ‖D.initial‖ + D.normBound * 1 := add_le_add
      (mul_le_mul_of_nonneg_right he (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (exp_weight_mul_time_le_one D.weightRate_ge_one ht)
        D.normBound_nonneg)
    _ = ‖D.initial‖ + D.normBound := by ring

noncomputable def BoundedMeasurableODE.weightedVolterra (D : BoundedMeasurableODE d) :
    (Ici (0 : ℝ) →ᵇ State d) → (Ici (0 : ℝ) →ᵇ State d) := fun u =>
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => D.weightedValue u t)
    ((D.continuous_weightedValue u).comp continuous_subtype_val)
    (‖D.initial‖ + D.normBound) (fun t => D.weightedValue_norm_le u t.property)

theorem integral_exp_mul_real {c t : ℝ} (hc : c ≠ 0) :
    (∫ s in (0 : ℝ)..t, Real.exp (c * s)) = (Real.exp (c * t) - 1) / c := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp hc]
  simp only [mul_zero, integral_exp, Real.exp_zero, smul_eq_mul]
  ring

theorem BoundedMeasurableODE.dist_weightedVolterra_apply_le (D : BoundedMeasurableODE d)
    (u v : Ici (0 : ℝ) →ᵇ State d) (t : Ici (0 : ℝ)) :
    dist (D.weightedVolterra u t) (D.weightedVolterra v t) ≤
      ((D.lipschitzConstant : ℝ) / D.weightRate) * dist u v := by
  have hu := D.path_intervalIntegrable (D.continuous_inflate u) 0 t
  have hv := D.path_intervalIntegrable (D.continuous_inflate v) 0 t
  have hd : ∀ s ∈ Icc (0 : ℝ) t,
      ‖D.field s (D.inflate u s) - D.field s (D.inflate v s)‖ ≤
        ((D.lipschitzConstant : ℝ) * dist u v) * Real.exp (D.weightRate * s) := by
    intro s _
    rw [← dist_eq_norm]
    have hh := (D.lipschitz s).dist_le_mul (D.inflate u s) (D.inflate v s)
    unfold inflate at hh
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hh
    calc
      _ ≤ (D.lipschitzConstant : ℝ) *
          (Real.exp (D.weightRate * s) * dist (u (nonnegativeClamp s)) (v (nonnegativeClamp s))) := hh
      _ ≤ (D.lipschitzConstant : ℝ) * (Real.exp (D.weightRate * s) * dist u v) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (BoundedContinuousFunction.dist_coe_le_dist _)
            (Real.exp_pos _).le) D.lipschitzConstant.coe_nonneg
      _ = _ := by ring
  have hexp : Continuous (fun s : ℝ => Real.exp (D.weightRate * s)) := by fun_prop
  have hint : ‖∫ s in (0 : ℝ)..(t : ℝ),
      D.field s (D.inflate u s) - D.field s (D.inflate v s)‖ ≤
        ((D.lipschitzConstant : ℝ) * dist u v) *
          ((Real.exp (D.weightRate * t) - 1) / D.weightRate) := by
    calc
      _ ≤ ∫ s in (0 : ℝ)..(t : ℝ), ‖D.field s (D.inflate u s) - D.field s (D.inflate v s)‖ :=
        intervalIntegral.norm_integral_le_integral_norm t.property
      _ ≤ ∫ s in (0 : ℝ)..(t : ℝ),
          ((D.lipschitzConstant : ℝ) * dist u v) * Real.exp (D.weightRate * s) :=
        intervalIntegral.integral_mono_on t.property (hu.sub hv).norm
          ((hexp.intervalIntegrable 0 t).const_mul _) hd
      _ = _ := by rw [intervalIntegral.integral_const_mul, integral_exp_mul_real D.weightRate_pos.ne']
  change dist (D.weightedValue u t) (D.weightedValue v t) ≤ _
  rw [weightedValue, weightedValue, dist_smul₀, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), dist_eq_norm, add_sub_add_left_eq_sub,
    ← intervalIntegral.integral_sub hu hv]
  have he : Real.exp (-D.weightRate * (t : ℝ)) * Real.exp (D.weightRate * (t : ℝ)) = 1 := by
    rw [← Real.exp_add]; simp
  have hc := D.weightRate_pos
  calc
    _ ≤ Real.exp (-D.weightRate * (t : ℝ)) *
        (((D.lipschitzConstant : ℝ) * dist u v) *
          ((Real.exp (D.weightRate * t) - 1) / D.weightRate)) :=
      mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le
    _ ≤ Real.exp (-D.weightRate * (t : ℝ)) *
        (((D.lipschitzConstant : ℝ) * dist u v) *
          (Real.exp (D.weightRate * t) / D.weightRate)) := by gcongr; linarith
    _ = _ := by
      calc
        _ = ((D.lipschitzConstant : ℝ) / D.weightRate) * dist u v *
            (Real.exp (-D.weightRate * (t : ℝ)) * Real.exp (D.weightRate * (t : ℝ))) := by ring
        _ = _ := by rw [he, mul_one]

noncomputable def BoundedMeasurableODE.weightContraction (D : BoundedMeasurableODE d) : ℝ≥0 :=
  ⟨(D.lipschitzConstant : ℝ) / D.weightRate,
    div_nonneg D.lipschitzConstant.coe_nonneg D.weightRate_pos.le⟩

theorem BoundedMeasurableODE.weightedVolterra_contracting (D : BoundedMeasurableODE d) :
    ContractingWith D.weightContraction D.weightedVolterra := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  · change (D.lipschitzConstant : ℝ) / D.weightRate < 1
    rw [div_lt_one D.weightRate_pos]
    dsimp [weightRate]; linarith
  · apply (BoundedContinuousFunction.dist_le (mul_nonneg D.weightContraction.coe_nonneg dist_nonneg)).mpr
    exact D.dist_weightedVolterra_apply_le u v

/-- An integral solution on all nonnegative times, without a positivity claim. -/
def GlobalIntegralSolution (F : ℝ → State d → State d) (z : State d)
    (x : ℝ → State d) : Prop :=
  ContinuousOn x (Ici 0) ∧ x 0 = z ∧
    (∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun t => F t (x t)) volume 0 T) ∧
    ∀ t : ℝ, 0 ≤ t → x t = z + ∫ s in (0 : ℝ)..t, F s (x s)

theorem GlobalIntegralSolution.on_interval {F : ℝ → State d → State d}
    {z : State d} {x : ℝ → State d} (hx : GlobalIntegralSolution F z x)
    {T : ℝ} (hT : 0 ≤ T) : IntegralSolutionOn F z 0 T x :=
  ⟨hx.1.mono (fun _ ht => ht.1), hx.2.1, hx.2.2.1 T hT,
    fun t ht => hx.2.2.2 t ht.1⟩

theorem BoundedMeasurableODE.exists_global_integralSolution (D : BoundedMeasurableODE d) :
    ∃ x : ℝ → State d, Continuous x ∧ GlobalIntegralSolution D.field D.initial x := by
  let hc := D.weightedVolterra_contracting
  let u : Ici (0 : ℝ) →ᵇ State d := hc.fixedPoint
  have hu : D.weightedVolterra u = u := hc.fixedPoint_isFixedPt
  refine ⟨D.inflate u, D.continuous_inflate u, ?_⟩
  have heq : ∀ t : ℝ, 0 ≤ t → D.inflate u t =
      D.initial + ∫ s in (0 : ℝ)..t, D.field s (D.inflate u s) := by
    intro t ht
    have hh := congrArg (fun w : Ici (0 : ℝ) →ᵇ State d => w ⟨t, ht⟩) hu
    change Real.exp (-D.weightRate * t) •
      (D.initial + ∫ s in (0 : ℝ)..t, D.field s (D.inflate u s)) = u ⟨t, ht⟩ at hh
    unfold inflate
    have hclamp : nonnegativeClamp t = ⟨t, ht⟩ := by
      apply Subtype.ext; exact max_eq_right ht
    rw [hclamp, ← hh, smul_smul]
    have he : Real.exp (D.weightRate * t) * Real.exp (-D.weightRate * t) = 1 := by
      rw [← Real.exp_add]; simp
    rw [he, one_smul]
    rfl
  exact ⟨(D.continuous_inflate u).continuousOn, by simpa using heq 0 le_rfl,
    fun T _ => D.path_intervalIntegrable (D.continuous_inflate u) 0 T, heq⟩

theorem BoundedMeasurableODE.global_integralSolution_unique (D : BoundedMeasurableODE d)
    {x y : ℝ → State d} (hx : GlobalIntegralSolution D.field D.initial x)
    (hy : GlobalIntegralSolution D.field D.initial y) : EqOn x y (Ici 0) := by
  intro t ht
  exact (hx.on_interval ht).eqOn_of_lipschitzOn ht (hy.on_interval ht)
    (B := univ) (L := D.lipschitzConstant)
    (fun s _ => lipschitzOnWith_iff_dist_le_mul.mpr
      (fun z _ w _ => (D.lipschitz s).dist_le_mul z w))
    (fun _ _ => mem_univ _) (fun _ _ => mem_univ _) ⟨ht, le_rfl⟩

end Endotactic
