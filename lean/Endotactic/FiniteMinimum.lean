import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Finite minima along absolutely continuous paths

At every point where the minimum and an active branch are differentiable,
their derivatives agree: their difference is nonnegative and vanishes there,
so Fermat's theorem applies. Absolute continuity makes these points full measure.
This avoids a case-by-case derivative formula at ties.
-/

namespace Endotactic

open MeasureTheory Set Filter
open scoped Topology

theorem ac_congrOn {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (heq : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  have hevent : ∀ᶠ E in AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
      𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  apply hf.congr'
  filter_upwards [hevent] with E hE
  apply Finset.sum_congr rfl
  intro i hi
  rw [heq (hE.1 i hi).1, heq (hE.1 i hi).2]

theorem ac_const (c a b : ℝ) : AbsolutelyContinuousOnInterval (fun _ => c) a b := by
  unfold AbsolutelyContinuousOnInterval
  simp only [dist_self, Finset.sum_const_zero]
  exact tendsto_const_nhds

theorem ac_min {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => min (f t) (g t)) a b := by
  have hdist (s t : ℝ) :
      dist (min (f s) (g s)) (min (f t) (g t)) ≤ dist (f s) (f t) + dist (g s) (g t) := by
    have h := lipschitzWith_min.dist_le_mul (f s, g s) (f t, g t)
    simp only [NNReal.coe_one, one_mul, Prod.dist_eq] at h
    exact h.trans (max_le (le_add_of_nonneg_right dist_nonneg)
      (le_add_of_nonneg_left dist_nonneg))
  apply squeeze_zero (fun E => Finset.sum_nonneg fun _ _ => dist_nonneg)
    (fun E => ?_) (by simpa using Tendsto.add hf hg)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => hdist (E.2 i).1 (E.2 i).2

theorem ac_finset_inf {I : Type*} [DecidableEq I] (s : Finset I) (hs : s.Nonempty)
    (f : I → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => s.inf' hs (fun i => f i t)) a b := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hf i (by simp)
  | cons i s hi hs ih =>
    have htail : ∀ j ∈ s, AbsolutelyContinuousOnInterval (f j) a b :=
      fun j hj => hf j (Finset.mem_cons.mpr (Or.inr hj))
    simpa only [Finset.inf'_cons hs] using
      ac_min (hf i (Finset.mem_cons.mpr (Or.inl rfl))) (ih htail)

noncomputable def finiteMinimum {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty f

theorem finiteMinimum_le {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) (i : I) :
    finiteMinimum f ≤ f i :=
  Finset.inf'_le f (Finset.mem_univ i)

theorem finiteMinimum_attained {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) :
    ∃ i, finiteMinimum f = f i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty f
  exact ⟨i, hi⟩

theorem finiteMinimum_ac {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => finiteMinimum (fun i => f i t)) a b := by
  classical
  exact ac_finset_inf Finset.univ Finset.univ_nonempty f (fun i _ => hf i)

theorem finiteMinimum_deriv_eq_active {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) {t : ℝ} {i : I}
    (hF : DifferentiableAt ℝ (fun s => finiteMinimum (fun j => f j s)) t)
    (hi : DifferentiableAt ℝ (f i) t)
    (hactive : finiteMinimum (fun j => f j t) = f i t) :
    deriv (fun s => finiteMinimum (fun j => f j s)) t = deriv (f i) t := by
  have hmin : IsLocalMin (fun s => f i s - finiteMinimum (fun j => f j s)) t := by
    apply Filter.Eventually.of_forall
    intro s
    change f i t - finiteMinimum (fun j => f j t) ≤
      f i s - finiteMinimum (fun j => f j s)
    rw [hactive, sub_self]
    exact sub_nonneg.mpr (finiteMinimum_le (fun j => f j s) i)
  have hz := hmin.hasDerivAt_eq_zero (hi.hasDerivAt.sub hF.hasDerivAt)
  linarith

theorem finiteMinimum_ae_deriv_lower_bound {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) {a b δ : ℝ}
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) a b)
    (hbound : ∀ᵐ t ∂volume, t ∈ uIcc a b → ∀ i,
      finiteMinimum (fun j => f j t) = f i t → δ ≤ deriv (f i) t) :
    ∀ᵐ t ∂volume, t ∈ uIcc a b →
      δ ≤ deriv (fun s => finiteMinimum (fun j => f j s)) t := by
  have hbranches : ∀ᵐ t ∂volume, ∀ i, t ∈ uIcc a b → DifferentiableAt ℝ (f i) t :=
    ae_all_iff.mpr fun i => (hf i).ae_differentiableAt
  filter_upwards [(finiteMinimum_ac f hf).ae_differentiableAt, hbranches, hbound]
    with t hF hi hb ht
  obtain ⟨i, hactive⟩ := finiteMinimum_attained (fun j => f j t)
  rw [finiteMinimum_deriv_eq_active f (hF ht) (hi i ht) hactive]
  exact hb ht i hactive

theorem finiteMinimum_ae_deriv_lower_bound_on {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) (P : ℝ → Prop) {a b δ : ℝ}
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) a b)
    (hbound : ∀ᵐ t ∂volume, t ∈ uIcc a b → P t → ∀ i,
      finiteMinimum (fun j => f j t) = f i t → δ ≤ deriv (f i) t) :
    ∀ᵐ t ∂volume, t ∈ uIcc a b → P t →
      δ ≤ deriv (fun s => finiteMinimum (fun j => f j s)) t := by
  have hbranches : ∀ᵐ t ∂volume, ∀ i, t ∈ uIcc a b → DifferentiableAt ℝ (f i) t :=
    ae_all_iff.mpr fun i => (hf i).ae_differentiableAt
  filter_upwards [(finiteMinimum_ac f hf).ae_differentiableAt, hbranches, hbound]
    with t hF hi hb ht hP
  obtain ⟨i, hactive⟩ := finiteMinimum_attained (fun j => f j t)
  rw [finiteMinimum_deriv_eq_active f (hF ht) (hi i ht) hactive]
  exact hb ht hP i hactive

theorem growth_of_ac_deriv_lower_bound {g : ℝ → ℝ} {a b δ : ℝ}
    (hab : a ≤ b) (hg : AbsolutelyContinuousOnInterval g a b)
    (hbound : ∀ᵐ t ∂volume, t ∈ Icc a b → δ ≤ deriv g t) :
    δ * (b - a) ≤ g b - g a := by
  have hb : (fun _ : ℝ => δ) ≤ᵐ[volume.restrict (Icc a b)] deriv g := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hbound] with t ht hb
    exact hb ht
  have hh := intervalIntegral.integral_mono_ae_restrict hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => δ) volume a b)
    hg.intervalIntegrable_deriv hb
  rw [hg.integral_deriv_eq_sub, intervalIntegral.integral_const, smul_eq_mul] at hh
  simpa only [mul_comm] using hh

theorem finiteMinimum_growth {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) {a b δ : ℝ} (hab : a ≤ b)
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) a b)
    (hbound : ∀ᵐ t ∂volume, t ∈ Icc a b → ∀ i,
      finiteMinimum (fun j => f j t) = f i t → δ ≤ deriv (f i) t) :
    δ * (b - a) ≤ finiteMinimum (fun i => f i b) - finiteMinimum (fun i => f i a) := by
  apply growth_of_ac_deriv_lower_bound hab (finiteMinimum_ac f hf)
  simpa only [uIcc_of_le hab] using
    finiteMinimum_ae_deriv_lower_bound f hf (by simpa only [uIcc_of_le hab] using hbound)

end Endotactic
