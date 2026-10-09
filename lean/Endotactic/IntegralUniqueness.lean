import Endotactic.LocalExistence
import Mathlib.Analysis.ODE.Gronwall

/-!
# Uniqueness of measurable mass-action integral solutions

The distance of two trajectories is continuous. Apply the differentiable
Grönwall theorem to its integral, rather than to the trajectories themselves.
Thus no pointwise differentiability of the measurable-time field is assumed.
-/

namespace Endotactic

open Set MeasureTheory
open scoped Topology NNReal

variable {d : ℕ} {E : Type*} [Fintype E]

theorem continuous_eq_zero_of_le_integral {u : ℝ → ℝ} {a b L : ℝ}
    (hu : Continuous u) (hn : ∀ t ∈ Icc a b, 0 ≤ u t)
    (hi : ∀ t ∈ Icc a b, u t ≤ L * ∫ s in a..t, u s) :
    ∀ t ∈ Icc a b, u t = 0 := by
  let G : ℝ → ℝ := fun t => ∫ s in a..t, u s
  have hGc : Continuous G := intervalIntegral.continuous_primitive
    (fun s t => hu.intervalIntegrable s t) a
  have hGn : ∀ t ∈ Icc a b, 0 ≤ G t := by
    intro t ht
    apply intervalIntegral.integral_nonneg ht.1
    intro s hs
    exact hn s ⟨hs.1, hs.2.trans ht.2⟩
  have hGzero : ∀ t ∈ Icc a b, G t = 0 :=
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hGc.continuousOn
      (fun t _ => (intervalIntegral.integral_hasDerivAt_right
        (hu.intervalIntegrable a t) (hu.stronglyMeasurableAtFilter volume (𝓝 t))
        hu.continuousAt).hasDerivWithinAt)
      (by simp [G]) (by
        intro t ht
        have ht' : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hn t ht'),
          abs_of_nonneg (hGn t ht')] using hi t ht')
  intro t ht
  apply le_antisymm _ (hn t ht)
  have hh : u t ≤ L * G t := hi t ht
  simpa only [hGzero t ht, mul_zero] using hh

theorem IntegralSolutionOn.eqOn_of_lipschitzOn {F : ℝ → State d → State d}
    {z : State d} {a b : ℝ} (hab : a ≤ b) {x y : ℝ → State d}
    (hx : IntegralSolutionOn F z a b x) (hy : IntegralSolutionOn F z a b y)
    {B : Set (State d)} {L : ℝ≥0}
    (hL : ∀ t ∈ Icc a b, LipschitzOnWith L (F t) B)
    (hxB : MapsTo x (Icc a b) B) (hyB : MapsTo y (Icc a b) B) :
    EqOn x y (Icc a b) := by
  let ux : C(Icc a b, State d) :=
    ⟨fun t => x t, continuousOn_iff_continuous_domRestrict.mp hx.1⟩
  let uy : C(Icc a b, State d) :=
    ⟨fun t => y t, continuousOn_iff_continuous_domRestrict.mp hy.1⟩
  let U : ℝ → ℝ := fun t => dist (extendIntervalCurve hab ux t) (extendIntervalCurve hab uy t)
  have hUc : Continuous U := (continuous_extendIntervalCurve hab ux).dist
    (continuous_extendIntervalCurve hab uy)
  have hUeq : ∀ t ∈ Icc a b, U t = dist (x t) (y t) := by
    intro t ht
    dsimp [U]
    rw [extendIntervalCurve_eq_of_mem hab ux ht, extendIntervalCurve_eq_of_mem hab uy ht]
    rfl
  have hineq : ∀ t ∈ Icc a b, U t ≤ (L : ℝ) * ∫ s in a..t, U s := by
    intro t ht
    have hsub : uIcc a t ⊆ uIcc a b := by
      simpa only [uIcc_of_le hab, uIcc_of_le ht.1] using
        (show Icc a t ⊆ Icc a b from fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩)
    have hf := (hx.2.2.1.mono_set hsub).sub (hy.2.2.1.mono_set hsub)
    rw [hUeq t ht, hx.2.2.2 t ht, hy.2.2.2 t ht, dist_eq_norm,
      add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
        (hx.2.2.1.mono_set hsub) (hy.2.2.1.mono_set hsub)]
    calc
      ‖∫ s in a..t, F s (x s) - F s (y s)‖ ≤
          ∫ s in a..t, ‖F s (x s) - F s (y s)‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in a..t, (L : ℝ) * U s := by
        apply intervalIntegral.integral_mono_on ht.1 hf.norm
          ((hUc.intervalIntegrable a t).const_mul (L : ℝ))
        intro s hs
        have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
        rw [← dist_eq_norm, hUeq s hs']
        exact (hL s hs').dist_le_mul _ (hxB hs') _ (hyB hs')
      _ = (L : ℝ) * ∫ s in a..t, U s := intervalIntegral.integral_const_mul _ _
  have hzero := continuous_eq_zero_of_le_integral hUc
    (fun _ _ => dist_nonneg) hineq
  intro t ht
  exact dist_eq_zero.mp ((hUeq t ht).symm.trans (hzero t ht))

theorem Network.integralSolutionOn_unique (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u T : ℝ} (hk : AdmissibleRates k ℓ u) (hT : 0 ≤ T)
    {z : State d} {x y : ℝ → State d}
    (hx : IntegralSolutionOn (fun t v => N.rhs (fun e => k e t) v) z 0 T x)
    (hy : IntegralSolutionOn (fun t v => N.rhs (fun e => k e t) v) z 0 T y) :
    EqOn x y (Icc 0 T) := by
  obtain ⟨Rx, hRx⟩ := isCompact_Icc.exists_bound_of_continuousOn hx.1
  obtain ⟨Ry, hRy⟩ := isCompact_Icc.exists_bound_of_continuousOn hy.1
  let R : ℝ := max Rx Ry
  have hB : ∀ (v : ℝ → State d), (∀ t ∈ Icc 0 T, ‖v t‖ ≤ R) →
      MapsTo v (Icc 0 T) (Icc (fun _ => -R) (fun _ => R)) := by
    intro v hv t ht
    have hb : ∀ i, |v t i| ≤ ‖v t‖ := fun i => by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (v t) i
    have hh : ∀ i, |v t i| ≤ R := fun i => (hb i).trans (hv t ht)
    exact ⟨fun i => (abs_le.mp (hh i)).1, fun i => (abs_le.mp (hh i)).2⟩
  obtain ⟨L, hL⟩ := N.rhs_uniform_lipschitzOn_box
    (fun _ => ℓ) (fun _ => u) (fun _ => -R) (fun _ => R)
  exact hx.eqOn_of_lipschitzOn hT hy
    (fun t ht => hL _ ⟨fun e => (hk.2 e t ht.1).1, fun e => (hk.2 e t ht.1).2⟩)
    (hB x (fun t ht => (hRx t ht).trans (le_max_left _ _)))
    (hB y (fun t ht => (hRy t ht).trans (le_max_right _ _)))

theorem Network.IsIntegralSolution.eqOn_nonnegative (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    {z : State d} {x y : ℝ → State d}
    (hx : N.IsIntegralSolution k z x) (hy : N.IsIntegralSolution k z y) :
    EqOn x y (Ici 0) := by
  intro t ht
  have hx' : IntegralSolutionOn (fun s v => N.rhs (fun e => k e s) v) z 0 t x :=
    ⟨hx.1.mono (fun _ hs => hs.1), hx.2.1, hx.2.2.1 t ht,
      fun s hs => hx.2.2.2 s hs.1⟩
  have hy' : IntegralSolutionOn (fun s v => N.rhs (fun e => k e s) v) z 0 t y :=
    ⟨hy.1.mono (fun _ hs => hs.1), hy.2.1, hy.2.2.1 t ht,
      fun s hs => hy.2.2.2 s hs.1⟩
  exact N.integralSolutionOn_unique hk ht hx' hy' ⟨ht, le_rfl⟩

theorem Network.positiveWellPosed_of_exists (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u) {z : State d}
    (h : ∃ x, N.IsGlobalPositiveSolution k z x) : N.PositiveWellPosed k z := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hx, fun y hy t ht => Network.IsIntegralSolution.eqOn_nonnegative N hk hy.1 hx.1 ht⟩

theorem Network.exists_unique_positive_local_integralSolution (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (z : State d) (hz : Positive z) :
    ∃ T : ℝ, 0 < T ∧ ∃ x : ℝ → State d, Continuous x ∧
      IntegralSolutionOn (fun t v => N.rhs (fun e => k e t) v) z 0 T x ∧
      (∀ t ∈ Icc 0 T, Positive (x t)) ∧
      ∀ y, IntegralSolutionOn (fun t v => N.rhs (fun e => k e t) v) z 0 T y →
        EqOn y x (Icc 0 T) := by
  obtain ⟨T, hT, x, hxc, hx, hp⟩ := N.exists_positive_local_integralSolution hk z hz
  exact ⟨T, hT, x, hxc, hx, hp, fun y hy => N.integralSolutionOn_unique hk hT.le hy hx⟩

end Endotactic
