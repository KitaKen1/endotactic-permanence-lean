import Endotactic.BoxKinetics
import Mathlib.Algebra.Order.Field.Pi

/-!
# Positive local integral solutions of measurable mass action

A bounded, globally Lipschitz cutoff has a short-interval Volterra fixed point.
Its displacement bound keeps it inside the cutoff box, so it is an actual
solution of the original mass-action equation. This construction proves local
positivity. It does not establish global positivity or rule out finite escape.
-/

namespace Endotactic

open Set MeasureTheory
open scoped NNReal

variable {d : ℕ} {E : Type*} [Fintype E]

theorem IntegralSolutionOn.dist_initial_le {F : ℝ → State d → State d}
    {z : State d} {a b R : ℝ} {x : ℝ → State d}
    (hx : IntegralSolutionOn F z a b x) (hR : ∀ t y, ‖F t y‖ ≤ R)
    {t : ℝ} (ht : t ∈ Icc a b) : dist (x t) z ≤ R * (t - a) := by
  rw [hx.2.2.2 t ht, dist_eq_norm, add_sub_cancel_left]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s => F s (x s)) (a := a) (b := t) (fun s _ => hR s (x s))
  simpa only [abs_of_nonneg (sub_nonneg.mpr ht.1)] using hh

theorem IntegralSolutionOn.increment_eq {F : ℝ → State d → State d}
    {z : State d} {a b : ℝ} {x : ℝ → State d}
    (hx : IntegralSolutionOn F z a b x) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    x t - x s = ∫ r in s..t, F r (x r) := by
  have hab := hs.1.trans hs.2
  have hint : ∀ r ∈ Icc a b, IntervalIntegrable (fun q => F q (x q)) volume a r := by
    intro r hr
    apply hx.2.2.1.mono_set
    rw [uIcc_of_le hab]
    exact uIcc_subset_Icc ⟨le_rfl, hab⟩ hr
  rw [hx.2.2.2 t ht, hx.2.2.2 s hs, add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left (hint t ht) (hint s hs)

theorem IntegralSolutionOn.dist_le_time {F : ℝ → State d → State d}
    {z : State d} {a b R : ℝ} {x : ℝ → State d}
    (hx : IntegralSolutionOn F z a b x)
    (hR : ∀ r ∈ Icc a b, ‖F r (x r)‖ ≤ R) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    dist (x t) (x s) ≤ R * |t - s| := by
  rw [dist_eq_norm, hx.increment_eq hs ht]
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun r hr => hR r (uIcc_subset_Icc hs ht (uIoc_subset_uIcc hr)))

theorem IntegralSolutionOn.restart {F : ℝ → State d → State d}
    {z : State d} {a b : ℝ} {x : ℝ → State d}
    (hx : IntegralSolutionOn F z a b x) {s : ℝ} (hs : s ∈ Icc a b) :
    IntegralSolutionOn F (x s) s b x := by
  have hab := hs.1.trans hs.2
  have hsub : Icc s b ⊆ Icc a b := fun _ ht => ⟨hs.1.trans ht.1, ht.2⟩
  refine ⟨hx.1.mono hsub, rfl, ?_, ?_⟩
  · apply hx.2.2.1.mono_set
    rw [uIcc_of_le hab, uIcc_of_le hs.2]
    exact hsub
  · intro t ht
    exact (sub_eq_iff_eq_add.mp (hx.increment_eq hs (hsub ht))).trans (add_comm _ _)

theorem exists_short_positive_time (L R ε : ℝ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hε : 0 < ε) : ∃ T : ℝ, 0 < T ∧ L * T < 1 ∧ R * T < ε := by
  obtain ⟨T₁, hT₁, hL₁⟩ := exists_pos_mul_lt (show (0 : ℝ) < 1 by norm_num) L
  obtain ⟨T₂, hT₂, hR₂⟩ := exists_pos_mul_lt hε R
  refine ⟨min T₁ T₂, lt_min hT₁ hT₂, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hL).trans_lt hL₁
  · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hR).trans_lt hR₂

theorem BoundedMeasurableODE.unique_integralSolution (D : BoundedMeasurableODE d)
    {a b : ℝ} (hab : a ≤ b) (hshort : (D.lipschitzConstant : ℝ) * (b - a) < 1)
    {x y : ℝ → State d} (hx : IntegralSolutionOn D.field D.initial a b x)
    (hy : IntegralSolutionOn D.field D.initial a b y) : EqOn x y (Icc a b) := by
  let ux : C(Icc a b, State d) :=
    ⟨fun t => x t, continuousOn_iff_continuous_domRestrict.mp hx.1⟩
  let uy : C(Icc a b, State d) :=
    ⟨fun t => y t, continuousOn_iff_continuous_domRestrict.mp hy.1⟩
  have hfixed : ∀ (z : ℝ → State d) (hz : IntegralSolutionOn D.field D.initial a b z)
      (uz : C(Icc a b, State d)), (∀ t, uz t = z t) → D.volterra hab uz = uz := by
    intro z hz uz huz
    apply ContinuousMap.ext
    intro t
    change D.initial + (∫ s in a..(t : ℝ), D.curveRhs hab uz s) = uz t
    rw [huz, hz.2.2.2 t t.property]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans t.property.2⟩
    unfold BoundedMeasurableODE.curveRhs
    rw [extendIntervalCurve_eq_of_mem hab uz hs', huz]
  obtain ⟨u, _, hu⟩ := D.existsUnique_fixedPoint hab hshort
  have hux : ux = u := hu ux (hfixed x hx ux (fun _ => rfl))
  have huy : uy = u := hu uy (hfixed y hy uy (fun _ => rfl))
  intro t ht
  exact congrArg (fun w : C(Icc a b, State d) => w ⟨t, ht⟩) (hux.trans huy.symm)

theorem Network.exists_positive_local_integralSolution (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (z : State d) (hz : Positive z) :
    ∃ T : ℝ, 0 < T ∧ ∃ x : ℝ → State d, Continuous x ∧
      IntegralSolutionOn (fun t y => N.rhs (fun e => k e t) y) z 0 T x ∧
      ∀ t ∈ Icc 0 T, Positive (x t) := by
  obtain ⟨ε, hε, hεz⟩ := Pi.exists_forall_pos_add_lt (x := fun _ : Fin d => (0 : ℝ)) hz
  have hεz : ∀ i, ε < z i := by simpa using hεz
  let lo : State d := fun i => z i - ε
  let hi : State d := fun i => z i + ε
  have hbox : lo ≤ hi := fun i => by dsimp [lo, hi]; linarith
  obtain ⟨D, hDF, hDz⟩ := N.exists_cutoffODE hk lo hi hbox z
  obtain ⟨T, hT, hLT, hRT⟩ := exists_short_positive_time (D.lipschitzConstant : ℝ)
    (max D.normBound 0) ε D.lipschitzConstant.coe_nonneg (le_max_right _ _) hε
  obtain ⟨x, hxc, hx⟩ := D.exists_integralSolution (a := 0) (b := T) hT.le
    (by simpa using hLT)
  have hclose : ∀ t ∈ Icc 0 T, dist (x t) z < ε := by
    intro t ht
    have hb := hx.dist_initial_le D.norm_le ht
    rw [hDz] at hb
    calc
      dist (x t) z ≤ D.normBound * (t - 0) := hb
      _ ≤ max D.normBound 0 * T := by
        simp only [sub_zero]
        exact mul_le_mul (le_max_left _ _) ht.2 ht.1 (le_max_right _ _)
      _ < ε := hRT
  have hmem : ∀ t ∈ Icc 0 T, x t ∈ Icc lo hi := by
    intro t ht
    have hc : ∀ i, |x t i - z i| < ε := fun i => by
      simpa only [Real.dist_eq] using (dist_le_pi_dist (x t) z i).trans_lt (hclose t ht)
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hh := (abs_lt.mp (hc i)).1
      dsimp [lo]; linarith
    · have hh := (abs_lt.mp (hc i)).2
      dsimp [hi]; linarith
  have hfield : ∀ t ∈ Icc 0 T, D.field t (x t) = N.rhs (fun e => k e t) (x t) := by
    intro t ht
    rw [hDF]
    exact N.cutoffRhs_eq k lo hi ht.1 (hmem t ht)
  refine ⟨T, hT, x, hxc, ?_, ?_⟩
  · refine ⟨hx.1, hDz ▸ hx.2.1, ?_, ?_⟩
    · apply hx.2.2.1.congr
      intro t ht
      apply hfield t
      rw [uIoc_of_le hT.le] at ht
      exact Ioc_subset_Icc_self ht
    · intro t ht
      rw [hx.2.2.2 t ht, hDz]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      exact hfield s ⟨hs.1, hs.2.trans ht.2⟩
  · intro t ht i
    have hh := (hmem t ht).1 i
    dsimp [lo] at hh
    exact (sub_pos.mpr (hεz i)).trans_le hh

end Endotactic
