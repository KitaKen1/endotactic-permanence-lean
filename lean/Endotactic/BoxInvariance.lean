import Endotactic.GlobalVolterra
import Endotactic.IntegralTrajectory

/-!
# Box invariance and positive global mass-action solutions

For an absolutely continuous coordinate, cap its negative part at zero.
Nonnegative derivative below zero implies that a nonnegative initial coordinate
stays nonnegative. Applied to both faces, this gives box invariance without
pointwise differentiability of the rate path.

Clamping sends a state outside a coordinate face to that face. Inward face
inequalities therefore imply the required derivative signs everywhere outside
the box. The global cutoff solution is then a positive global solution of the
original field. The face inequalities are explicit hypotheses, not consequences
of general endotacticity proved here.
-/

namespace Endotactic

open Set MeasureTheory Filter
open scoped Topology

variable {d : ℕ} {E : Type*} [Fintype E]

theorem ac_nonnegative_of_deriv_on_negative (f : ℝ → ℝ)
    (hAC : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T) (h0 : 0 ≤ f 0)
    (hderiv : ∀ T, 0 ≤ T → ∀ᵐ t ∂volume,
      t ∈ Icc 0 T → f t < 0 → 0 ≤ deriv f t) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ f t := by
  let g : ℝ → ℝ := fun t => min (f t) 0
  have hg : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval g 0 T :=
    fun T hT => ac_min (hAC T hT) (ac_const 0 0 T)
  have hbelow : ∀ T, 0 ≤ T → ∀ᵐ t ∂volume,
      t ∈ Icc 0 T → g t < 0 → 0 ≤ deriv g t := by
    intro T hT
    filter_upwards [(hAC T hT).ae_differentiableAt, hderiv T hT] with t hdiff hd ht hneg
    have hfneg : f t < 0 := (min_lt_iff.mp hneg).resolve_right (lt_irrefl 0)
    have hdf := (hdiff (by simpa only [uIcc_of_le hT] using ht)).hasDerivAt
    have hlocal : ∀ᶠ s in 𝓝 t, f s < 0 := hdf.continuousAt.eventually (Iio_mem_nhds hfneg)
    have hmin : HasDerivAt g (deriv f t) t :=
      hdf.congr_of_eventuallyEq (hlocal.mono fun s hs => min_eq_left hs.le)
    rw [hmin.deriv]
    exact hd ht hfneg
  have hmono := ac_monotone_of_below_cap_deriv_nonneg g hg
    (fun _ _ => min_le_right _ _) hbelow
  intro t ht
  have hh := hmono 0 t le_rfl ht
  have hg0 : g 0 = 0 := min_eq_right h0
  rw [hg0] at hh
  exact hh.trans (min_le_left _ _)

theorem GlobalIntegralSolution.clm_integral_eq {F : ℝ → State d → State d}
    {z : State d} {x : ℝ → State d} (hx : GlobalIntegralSolution F z x)
    (L : State d →L[ℝ] ℝ) {t : ℝ} (ht : 0 ≤ t) :
    L (x t) = L z + ∫ s in (0 : ℝ)..t, L (F s (x s)) := by
  have hh := congrArg L (hx.2.2.2 t ht)
  rw [map_add, ← L.intervalIntegral_comp_comm (hx.2.2.1 t ht)] at hh
  exact hh

theorem GlobalIntegralSolution.clm_ac {F : ℝ → State d → State d}
    {z : State d} {x : ℝ → State d} (hx : GlobalIntegralSolution F z x)
    (L : State d →L[ℝ] ℝ) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => L (x t)) 0 T := by
  have hp := (clm_intervalIntegrable L (hx.2.2.1 T hT)).absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) (by simp)
  apply ac_congrOn ((ac_const (L z) 0 T).add hp)
  intro t ht
  have ht' : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
  exact (hx.clm_integral_eq L ht'.1).symm

theorem GlobalIntegralSolution.clm_ae_hasDerivAt {F : ℝ → State d → State d}
    {z : State d} {x : ℝ → State d} (hx : GlobalIntegralSolution F z x)
    (L : State d →L[ℝ] ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt (fun s => L (x s)) (L (F t (x t))) t := by
  have hzero : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have htop : ∀ᵐ t : ℝ ∂volume, t ≠ T := by simp [ae_iff, measure_singleton]
  filter_upwards [(clm_intervalIntegrable L (hx.2.2.1 T hT)).ae_hasDerivAt_integral, hzero, htop]
    with t hp hz ht hmem
  have hlt0 : 0 < t := lt_of_le_of_ne hmem.1 hz.symm
  have hltT : t < T := lt_of_le_of_ne hmem.2 ht
  have hp' := (hp (by simpa only [uIcc_of_le hT] using hmem) 0 (by simp)).const_add (L z)
  apply hp'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hlt0 hltT] with s hs
  exact hx.clm_integral_eq L hs.1.le

theorem GlobalIntegralSolution.mem_box_of_outside_sign {F : ℝ → State d → State d}
    {z lo hi : State d} {x : ℝ → State d} (hx : GlobalIntegralSolution F z x)
    (hz : z ∈ Icc lo hi)
    (hlower : ∀ t, 0 ≤ t → ∀ y i, y i < lo i → 0 ≤ F t y i)
    (hupper : ∀ t, 0 ≤ t → ∀ y i, hi i < y i → F t y i ≤ 0) :
    ∀ t, 0 ≤ t → x t ∈ Icc lo hi := by
  have hlow : ∀ i t, 0 ≤ t → 0 ≤ x t i - lo i := by
    intro i
    let L : State d →L[ℝ] ℝ := ContinuousLinearMap.proj i
    apply ac_nonnegative_of_deriv_on_negative
    · intro T hT
      exact (hx.clm_ac L hT).sub (ac_const (lo i) 0 T)
    · rw [hx.2.1]; exact sub_nonneg.mpr (hz.1 i)
    · intro T hT
      filter_upwards [hx.clm_ae_hasDerivAt L hT] with t hd ht hneg
      have hh : HasDerivAt (fun s => x s i - lo i) (F t (x t) i) t := (hd ht).sub_const (lo i)
      rw [hh.deriv]
      exact hlower t ht.1 (x t) i (sub_neg.mp hneg)
  have hhigh : ∀ i t, 0 ≤ t → 0 ≤ hi i - x t i := by
    intro i
    let L : State d →L[ℝ] ℝ := ContinuousLinearMap.proj i
    apply ac_nonnegative_of_deriv_on_negative
    · intro T hT
      exact (ac_const (hi i) 0 T).sub (hx.clm_ac L hT)
    · rw [hx.2.1]; exact sub_nonneg.mpr (hz.2 i)
    · intro T hT
      filter_upwards [hx.clm_ae_hasDerivAt L hT] with t hd ht hneg
      have hh : HasDerivAt (fun s => hi i - x s i) (-F t (x t) i) t := (hd ht).const_sub (hi i)
      rw [hh.deriv]
      exact neg_nonneg.mpr (hupper t ht.1 (x t) i (sub_neg.mp hneg))
  exact fun t ht => ⟨fun i => sub_nonneg.mp (hlow i t ht), fun i => sub_nonneg.mp (hhigh i t ht)⟩

theorem boxClamp_lower_face {lo hi : State d} (hbox : lo ≤ hi) {y : State d}
    (i : Fin d) (hy : y i ≤ lo i) : boxClamp lo hi y i = lo i := by
  simp only [boxClamp, min_eq_right (hy.trans (hbox i)), max_eq_left hy]

theorem boxClamp_upper_face {lo hi : State d} (hbox : lo ≤ hi) {y : State d}
    (i : Fin d) (hy : hi i ≤ y i) : boxClamp lo hi y i = hi i := by
  simp only [boxClamp, min_eq_left hy, max_eq_right (hbox i)]

theorem GlobalIntegralSolution.congr_field {F G : ℝ → State d → State d}
    {z : State d} {x : ℝ → State d} (hx : GlobalIntegralSolution F z x)
    (hFG : ∀ t, 0 ≤ t → F t (x t) = G t (x t)) : GlobalIntegralSolution G z x := by
  refine ⟨hx.1, hx.2.1, ?_, ?_⟩
  · intro T hT
    apply (hx.2.2.1 T hT).congr
    intro t ht
    rw [uIoc_of_le hT] at ht
    exact hFG t ht.1.le
  · intro t ht
    rw [hx.2.2.2 t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact hFG s hs.1

theorem Network.exists_global_cutoff_integralSolution (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (lo hi : State d) (hbox : lo ≤ hi) (z : State d) :
    ∃ x : ℝ → State d, Continuous x ∧ GlobalIntegralSolution (N.cutoffRhs k lo hi) z x := by
  obtain ⟨D, hDF, hDz⟩ := N.exists_cutoffODE hk lo hi hbox z
  obtain ⟨x, hc, hx⟩ := D.exists_global_integralSolution
  rw [hDF, hDz] at hx
  exact ⟨x, hc, hx⟩

theorem Network.exists_global_positive_in_box (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (lo hi : State d) (hbox : lo ≤ hi) (hlo : Positive lo) {z : State d} (hz : z ∈ Icc lo hi)
    (hlower : ∀ t, 0 ≤ t → ∀ y ∈ Icc lo hi, ∀ i, y i = lo i →
      0 ≤ N.rhs (fun e => k e t) y i)
    (hupper : ∀ t, 0 ≤ t → ∀ y ∈ Icc lo hi, ∀ i, y i = hi i →
      N.rhs (fun e => k e t) y i ≤ 0) :
    ∃ x : ℝ → State d, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ Icc lo hi := by
  obtain ⟨x, _, hx⟩ := N.exists_global_cutoff_integralSolution hk lo hi hbox z
  have hstay := hx.mem_box_of_outside_sign hz
    (by
      intro t ht y i hy
      unfold Network.cutoffRhs
      rw [max_eq_right ht]
      exact hlower t ht _ (boxClamp_mem lo hi hbox y) i (boxClamp_lower_face hbox i hy.le))
    (by
      intro t ht y i hy
      unfold Network.cutoffRhs
      rw [max_eq_right ht]
      exact hupper t ht _ (boxClamp_mem lo hi hbox y) i (boxClamp_upper_face hbox i hy.le))
  have hactual : N.IsIntegralSolution k z x := hx.congr_field
    (fun t ht => N.cutoffRhs_eq k lo hi ht (hstay t ht))
  exact ⟨x, ⟨hactual, fun t ht i => (hlo i).trans_le ((hstay t ht).1 i)⟩, hstay⟩

end Endotactic
