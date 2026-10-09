import Endotactic.BoxInvariance

/-!
# Positive global solutions trapped by finite affine inequalities

A derivative sign is needed only in a thin strip below the target level.
Clamping an absolutely continuous scalar at the bottom of that strip makes
its derivative zero at the bottom, by Fermat. The existing negative-part
barrier then rules out crossing the target level.

Applied to a finite affine minimum of a global cutoff trajectory, this proves
polyhedral trapping, including tilted faces. An enlarged plateau contained
in a positive coordinate box makes the cutoff agree with the original field
throughout the strip. The strip flux signs are explicit hypotheses here.
-/

namespace Endotactic

open Set MeasureTheory Filter
open scoped Topology

theorem ac_max {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => max (f t) (g t)) a b := by
  have hdist (s t : ℝ) :
      dist (max (f s) (g s)) (max (f t) (g t)) ≤ dist (f s) (f t) + dist (g s) (g t) := by
    have h := lipschitzWith_max.dist_le_mul (f s, g s) (f t, g t)
    simp only [NNReal.coe_one, one_mul, Prod.dist_eq] at h
    exact h.trans (max_le (le_add_of_nonneg_right dist_nonneg)
      (le_add_of_nonneg_left dist_nonneg))
  apply squeeze_zero (fun E => Finset.sum_nonneg fun _ _ => dist_nonneg)
    (fun E => ?_) (by simpa using Tendsto.add hf hg)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => hdist (E.2 i).1 (E.2 i).2

theorem ac_nonnegative_of_deriv_in_strip (f : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hAC : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T) (h0 : 0 ≤ f 0)
    (hderiv : ∀ T, 0 ≤ T → ∀ᵐ t ∂volume,
      t ∈ Icc 0 T → -ε < f t → f t < 0 → 0 ≤ deriv f t) :
    ∀ t, 0 ≤ t → 0 ≤ f t := by
  let g : ℝ → ℝ := fun t => max (f t) (-ε)
  have hg : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval g 0 T :=
    fun T hT => ac_max (hAC T hT) (ac_const (-ε) 0 T)
  have hnonneg := ac_nonnegative_of_deriv_on_negative g hg
    (h0.trans (le_max_left _ _)) (by
      intro T hT
      filter_upwards [(hAC T hT).ae_differentiableAt, (hg T hT).ae_differentiableAt,
        hderiv T hT] with t hdf hdg hd ht hneg
      have ht' : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hT] using ht
      by_cases hf : -ε < f t
      · have hlocal : ∀ᶠ s in 𝓝 t, -ε < f s :=
          (hdf ht').continuousAt.eventually (Ioi_mem_nhds hf)
        have hh : HasDerivAt g (deriv f t) t := (hdf ht').hasDerivAt.congr_of_eventuallyEq
          (hlocal.mono fun s hs => max_eq_left hs.le)
        rw [hh.deriv]
        exact hd ht hf ((le_max_left _ _).trans_lt hneg)
      · have heq : g t = -ε := max_eq_right (le_of_not_gt hf)
        have hmin : IsLocalMin g t := Filter.Eventually.of_forall (fun s => by
          rw [heq]; exact le_max_right _ _)
        rw [hmin.hasDerivAt_eq_zero (hdg ht').hasDerivAt])
  intro t ht
  have hh := hnonneg t ht
  exact (le_max_iff.mp hh).resolve_right (by linarith)

variable {d m : ℕ}
variable {F : ℝ → State d → State d} {z : State d} {x : ℝ → State d}

theorem GlobalIntegralSolution.affine_branch_ac (hx : GlobalIntegralSolution F z x)
    (A : AffineFamily d m) (i : Fin m) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => A.value i (x t)) 0 T :=
  (hx.clm_ac (dotCLM (A.slope i)) hT).add (ac_const (A.offset i) 0 T)

theorem GlobalIntegralSolution.affine_branch_ae_hasDerivAt
    (hx : GlobalIntegralSolution F z x) (A : AffineFamily d m) (i : Fin m)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt (fun s => A.value i (x s))
      (dot (A.slope i) (F t (x t))) t := by
  filter_upwards [hx.clm_ae_hasDerivAt (dotCLM (A.slope i)) hT] with t hd ht
  exact (hd ht).add_const (A.offset i)

variable [Nonempty (Fin m)]

theorem GlobalIntegralSolution.affine_minimum_ac (hx : GlobalIntegralSolution F z x)
    (A : AffineFamily d m) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => A.minimum (x t)) 0 T :=
  finiteMinimum_ac (fun i t => A.value i (x t)) (fun i => hx.affine_branch_ac A i hT)

theorem GlobalIntegralSolution.affine_minimum_ae_deriv_nonneg_on
    (hx : GlobalIntegralSolution F z x) (A : AffineFamily d m) (P : ℝ → Prop)
    {T : ℝ} (hT : 0 ≤ T)
    (hb : ∀ t ∈ Icc 0 T, P t → ∀ i, A.Active i (x t) →
      0 ≤ dot (A.slope i) (F t (x t))) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T → P t → 0 ≤ deriv (fun s => A.minimum (x s)) t := by
  have hd : ∀ᵐ t ∂volume, ∀ i, t ∈ Icc 0 T → HasDerivAt (fun s => A.value i (x s))
      (dot (A.slope i) (F t (x t))) t :=
    ae_all_iff.mpr fun i => hx.affine_branch_ae_hasDerivAt A i hT
  have hbound : ∀ᵐ t ∂volume, t ∈ uIcc 0 T → P t → ∀ i,
      finiteMinimum (fun j => A.value j (x t)) = A.value i (x t) →
        0 ≤ deriv (fun s => A.value i (x s)) t := by
    filter_upwards [hd] with t hds ht hp i hi
    have ht' : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
    rw [(hds i ht').deriv]
    exact hb t ht' hp i ((A.active_iff_minimum_eq i (x t)).mpr hi)
  simpa only [AffineFamily.minimum, uIcc_of_le hT] using
    finiteMinimum_ae_deriv_lower_bound_on (fun i t => A.value i (x t)) P
      (fun i => hx.affine_branch_ac A i hT) hbound

theorem GlobalIntegralSolution.mem_affine_plateau_of_strip
    (hx : GlobalIntegralSolution F z x) (A : AffineFamily d m) {M ε : ℝ}
    (hε : 0 < ε) (hz : z ∈ A.plateau M)
    (hb : ∀ t, 0 ≤ t → M - ε < A.minimum (x t) → A.minimum (x t) < M →
      ∀ i, A.Active i (x t) → 0 ≤ dot (A.slope i) (F t (x t))) :
    ∀ t, 0 ≤ t → x t ∈ A.plateau M := by
  have hn := ac_nonnegative_of_deriv_in_strip (fun t => A.minimum (x t) - M) hε
    (fun T hT => (hx.affine_minimum_ac A hT).sub (ac_const M 0 T))
    (by rw [hx.2.1]; exact sub_nonneg.mpr ((A.mem_plateau_iff_minimum_ge z M).mp hz)) (by
      intro T hT
      have hd := hx.affine_minimum_ae_deriv_nonneg_on A
        (fun t => M - ε < A.minimum (x t) ∧ A.minimum (x t) < M) hT
        (fun t ht hp => hb t ht.1 hp.1 hp.2)
      filter_upwards [hd, (hx.affine_minimum_ac A hT).ae_differentiableAt]
        with t hds hdiff ht hl hu
      have hh := (hdiff (by simpa only [uIcc_of_le hT] using ht)).hasDerivAt.sub_const M
      rw [hh.deriv]
      exact hds ht ⟨by linarith, by linarith⟩)
  exact fun t ht => (A.mem_plateau_iff_minimum_ge (x t) M).mpr (sub_nonneg.mp (hn t ht))

variable {E : Type*} [Fintype E]

theorem Network.exists_global_positive_in_affine_strip (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M ε : ℝ} (hε : 0 < ε)
    (lo hi : State d) (hbox : lo ≤ hi) (hlo : Positive lo)
    (hsub : A.plateau (M - ε) ⊆ Icc lo hi) {z : State d} (hz : z ∈ A.plateau M)
    (hflux : ∀ t, 0 ≤ t → ∀ y, M - ε < A.minimum y → A.minimum y < M →
      ∀ i, A.Active i y → 0 ≤ dot (A.slope i) (N.rhs (fun e => k e t) y)) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧ ∀ t, 0 ≤ t → x t ∈ A.plateau M := by
  obtain ⟨x, _, hx⟩ := N.exists_global_cutoff_integralSolution hk lo hi hbox z
  have hstay := hx.mem_affine_plateau_of_strip A hε hz (by
    intro t ht hl hu i ha
    have hy : x t ∈ Icc lo hi := hsub
      ((A.mem_plateau_iff_minimum_ge (x t) (M - ε)).mpr hl.le)
    rw [N.cutoffRhs_eq k lo hi ht hy]
    exact hflux t ht (x t) hl hu i ha)
  have hxbox : ∀ t, 0 ≤ t → x t ∈ Icc lo hi := by
    intro t ht
    apply hsub
    exact fun i => (sub_le_self M hε.le).trans (hstay t ht i)
  have hactual : N.IsIntegralSolution k z x := hx.congr_field
    (fun t ht => N.cutoffRhs_eq k lo hi ht (hxbox t ht))
  exact ⟨x, ⟨hactual, fun t ht i => (hlo i).trans_le ((hxbox t ht).1 i)⟩, hstay⟩

end Endotactic
