import Endotactic.PolyhedralInvariance
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Linear deficit bounds preserve absolutely continuous barriers

An inward sign on the boundary need not extend as a nonnegative sign outside.
The weaker estimate `C * f ≤ f'` on `f < 0` still prevents crossing zero.
Multiplication by `exp(-C*t)` reduces this to the existing negative-part barrier.
No pointwise differentiability of the measurable-time trajectory is assumed.
-/

namespace Endotactic

open Set MeasureTheory Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false in
theorem ac_nonnegative_of_linear_deficit (f : ℝ → ℝ) (C : ℝ)
    (hAC : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T) (h0 : 0 ≤ f 0)
    (hderiv : ∀ T, 0 ≤ T → ∀ᵐ t ∂volume,
      t ∈ Icc 0 T → f t < 0 → C * f t ≤ deriv f t) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ f t := by
  let g : ℝ → ℝ := fun t => Real.exp (-C * t) * f t
  have he : ∀ T : ℝ, AbsolutelyContinuousOnInterval (fun t => Real.exp (-C * t)) 0 T := by
    intro T
    have hc : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-C * t)) := by fun_prop
    exact hc.contDiffOn.absolutelyContinuousOnInterval
  have hg : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval g 0 T :=
    fun T hT => (he T).mul (hAC T hT)
  have hstay := ac_nonnegative_of_deriv_on_negative g hg
    (by simpa [g] using h0) (by
      intro T hT
      filter_upwards [(hAC T hT).ae_differentiableAt, hderiv T hT] with t hd hb ht hn
      have hfn : f t < 0 := by
        by_contra h
        exact not_lt_of_ge (mul_nonneg (Real.exp_pos _).le (le_of_not_gt h)) hn
      have hf := (hd (by simpa only [uIcc_of_le hT] using ht)).hasDerivAt
      have hex := ((hasDerivAt_id t).const_mul (-C)).exp
      have hprod : HasDerivAt g
          (Real.exp (-C * t) * (deriv f t - C * f t)) t := by
        convert hex.mul hf using 1 <;> first | rfl | (simp only [id_eq]; ring)
      rw [hprod.deriv]
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hb ht hfn)))
  intro t ht
  exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp (hstay t ht)

theorem ac_nonnegative_of_linear_deficit_in_strip (f : ℝ → ℝ) {C ε : ℝ}
    (hC : 0 ≤ C) (hε : 0 < ε)
    (hAC : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T) (h0 : 0 ≤ f 0)
    (hderiv : ∀ T, 0 ≤ T → ∀ᵐ t ∂volume,
      t ∈ Icc 0 T → -ε < f t → f t < 0 → C * f t ≤ deriv f t) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ f t := by
  let g : ℝ → ℝ := fun t => max (f t) (-ε)
  have hg : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval g 0 T :=
    fun T hT => ac_max (hAC T hT) (ac_const (-ε) 0 T)
  have hstay := ac_nonnegative_of_linear_deficit g C hg (h0.trans (le_max_left _ _)) (by
    intro T hT
    filter_upwards [(hAC T hT).ae_differentiableAt, (hg T hT).ae_differentiableAt,
      hderiv T hT] with t hdf hdg hb ht hn
    have ht' : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hT] using ht
    by_cases hf : -ε < f t
    · have hl : ∀ᶠ s in 𝓝 t, -ε < f s :=
        (hdf ht').continuousAt.eventually (Ioi_mem_nhds hf)
      have hd : HasDerivAt g (deriv f t) t := (hdf ht').hasDerivAt.congr_of_eventuallyEq
        (hl.mono fun s hs => max_eq_left hs.le)
      rw [hd.deriv]
      change C * max (f t) (-ε) ≤ deriv f t
      rw [max_eq_left hf.le]
      exact hb ht hf ((le_max_left _ _).trans_lt hn)
    · have heq : g t = -ε := max_eq_right (le_of_not_gt hf)
      have hmin : IsLocalMin g t := Filter.Eventually.of_forall (fun s => by
        rw [heq]; exact le_max_right _ _)
      rw [hmin.hasDerivAt_eq_zero (hdg ht').hasDerivAt, heq]
      exact mul_nonpos_of_nonneg_of_nonpos hC (by linarith))
  intro t ht
  exact (le_max_iff.mp (hstay t ht)).resolve_right (by linarith)

variable {d m : ℕ} [Nonempty (Fin m)]
variable {F : ℝ → State d → State d} {z : State d} {x : ℝ → State d}

theorem GlobalIntegralSolution.mem_affine_plateau_of_linear_deficit
    (hx : GlobalIntegralSolution F z x) (A : AffineFamily d m) {M C ε : ℝ}
    (hC : 0 ≤ C) (hε : 0 < ε) (hz : z ∈ A.plateau M)
    (hb : ∀ t, 0 ≤ t → M - ε < A.minimum (x t) → A.minimum (x t) < M →
      ∀ i, A.Active i (x t) →
        C * (A.minimum (x t) - M) ≤ dot (A.slope i) (F t (x t))) :
    ∀ t, 0 ≤ t → x t ∈ A.plateau M := by
  have hstay := ac_nonnegative_of_linear_deficit_in_strip
    (fun t => A.minimum (x t) - M) hC hε
    (fun T hT => (hx.affine_minimum_ac A hT).sub (ac_const M 0 T))
    (by rw [hx.2.1]; exact sub_nonneg.mpr ((A.mem_plateau_iff_minimum_ge z M).mp hz)) (by
      intro T hT
      have hds : ∀ᵐ t ∂volume, ∀ i, t ∈ Icc 0 T →
          HasDerivAt (fun s => A.value i (x s)) (dot (A.slope i) (F t (x t))) t :=
        ae_all_iff.mpr fun i => hx.affine_branch_ae_hasDerivAt A i hT
      filter_upwards [hds, (hx.affine_minimum_ac A hT).ae_differentiableAt]
        with t hd hmin ht hl hu
      have ht' : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hT] using ht
      obtain ⟨i, hi⟩ := finiteMinimum_attained (fun j => A.value j (x t))
      have heq := finiteMinimum_deriv_eq_active (fun j s => A.value j (x s))
        (hmin ht') (hd i ht).differentiableAt hi
      change deriv (fun s => A.minimum (x s)) t = deriv (fun s => A.value i (x s)) t at heq
      have hsub := (hmin ht').hasDerivAt.sub_const M
      rw [hsub.deriv, heq, (hd i ht).deriv]
      exact hb t ht.1 (by linarith) (by linarith) i
        ((A.active_iff_minimum_eq i (x t)).mpr hi))
  exact fun t ht => (A.mem_plateau_iff_minimum_ge (x t) M).mpr (sub_nonneg.mp (hstay t ht))

end Endotactic
