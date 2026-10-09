import Endotactic.NarrowZeroCap
import Endotactic.LateCompactAbsorption
import Endotactic.CompactTrapPermanence
import Endotactic.ActivityFluxBridge

/-!
# A fixed scale family reaches a common compact target

Quarter-power boxes fit in the next capped square-root scale's exponent box.
Late compact absorption connects the plateaux without assuming nestedness.
The final set is chosen before both rate paths and positive initial states.
-/

namespace Endotactic

open Set

structure ScaleTrapFamily {d m : ℕ} {E : Type*} [Fintype E]
    (N : Network d E) (ℓ u : ℝ) (c : State d) where
  family : ScaledAffineFamily d m
  threshold : ℝ
  threshold_pos : 0 < threshold
  threshold_lt_one : threshold < 1
  level : ℝ → ℝ
  relaxed : ℝ → ℝ
  reference : ∀ h ∈ Ioc 0 threshold, c ∈ (family.atScale h).plateau (level h)
  gap : ∀ h ∈ Ioc 0 threshold, relaxed h < level h
  compact : ∀ h ∈ Ioc 0 threshold, IsCompact ((family.atScale h).plateau (relaxed h))
  box : ∀ h ∈ Ioc 0 threshold,
    (family.atScale h).plateau (relaxed h) ⊆ powerBox h (1 / 4 : ℝ)
  capture : ∀ z : State d, Positive z → ∃ h ∈ Ioc 0 threshold,
    z ∈ (family.atScale h).plateau (relaxed h)
  flux : ∀ h ∈ Ioc 0 threshold,
    ∀ y ∈ Icc (fun _ => h) (fun _ => h⁻¹), ∀ i : Fin m,
      (family.atScale h).Active i y → (∃ e, N.projection (family.slope i) e ≠ 0) →
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
        0 < dot (family.slope i) (N.rhs a y)

theorem capped_rootScale_succ {h H : ℝ} (hh : 0 < h) (hH1 : H ≤ 1) (n : ℕ) :
    min (rootScale h (n + 1)) H = Real.sqrt (min (rootScale h n) H) ⊓ H := by
  rw [rootScale_succ hh.le]
  by_cases hu : rootScale h n ≤ H
  · rw [min_eq_left hu]
  · have hHu := le_of_not_ge hu
    have hHH : H ≤ Real.sqrt H := Real.le_sqrt_self_iff.mpr hH1
    have hHs : H ≤ Real.sqrt (rootScale h n) := hHH.trans (Real.sqrt_le_sqrt hHu)
    rw [min_eq_right hHu, min_eq_right hHs]
    exact (min_eq_right hHH).symm

variable {d m : ℕ} {E : Type*} [Fintype E]
variable {N : Network d E} {ℓ u : ℝ} {c : State d}

theorem ScaleTrapFamily.faceCertificate (D : ScaleTrapFamily (m := m) N ℓ u c)
    {h : ℝ} (hh : h ∈ Ioc 0 D.threshold) :
    N.AffineFaceCertificate (D.family.atScale h) ℓ u (D.relaxed h) := by
  classical
  apply N.affineFaceCertificate_of_projections
  intro i
  by_cases hi : ∀ e, N.projection (D.family.slope i) e = 0
  · exact Or.inl hi
  · push Not at hi
    refine Or.inr ?_
    intro a ha y hy heq
    have hbox := D.box h hh hy
    have hsmall : h ≤ h ^ (1 / 4 : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge hh.1 (hh.2.trans D.threshold_lt_one.le)
          (by norm_num : (1 / 4 : ℝ) ≤ 1)
    have hunit := powerBox_subset_unit_box hh.1 hh.1 hsmall hbox
    have hactive : (D.family.atScale h).Active i y := fun j => heq ▸ hy j
    exact D.flux h hh y hunit i hactive hi a ha

theorem ScaleTrapFamily.eventual_step [Nonempty (Fin m)]
    (D : ScaleTrapFamily (m := m) N ℓ u c) {h : ℝ} (hh : h ∈ Ioc 0 D.threshold)
    {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u) {z : State d}
    (hz : z ∈ N.positiveClass c) {x : ℝ → State d} (hx : N.IsGlobalPositiveSolution k z x)
    (hstay : EventuallyIn x ((D.family.atScale h).plateau (D.relaxed h))) :
    EventuallyIn x ((D.family.atScale (min (Real.sqrt h) D.threshold)).plateau
      (D.relaxed (min (Real.sqrt h) D.threshold))) := by
  let g := min (Real.sqrt h) D.threshold
  have hg : g ∈ Ioc 0 D.threshold :=
    ⟨lt_min (Real.sqrt_pos.mpr hh.1) D.threshold_pos, min_le_right _ _⟩
  let B := (D.family.atScale h).plateau (D.relaxed h) ∩ N.stoichiometricClass c
  have hB : IsCompact B := (D.compact h hh).inter_right (N.stoichiometricClass_isClosed c)
  have hstayB : EventuallyIn x B := by
    obtain ⟨T, hT, hb⟩ := hstay
    exact ⟨T, hT, fun t ht => ⟨hb t ht, (hx.mem_positiveClass hz (hT.trans ht)).2⟩⟩
  have hgh : g ≤ h ^ (1 / 4 : ℝ) :=
    capped_sqrt_le_quarter_power hh.1 (hh.2.trans D.threshold_lt_one.le)
  have hcarrier : ((D.family.atScale g).plateau (D.level g) ∩
      N.stoichiometricClass c).Nonempty :=
    ⟨c, D.reference g hg, by change c - c ∈ N.stoichiometricSubspace; simp⟩
  apply (D.family.atScale g).eventuallyIn_plateau_of_eventual_compact_strict_exterior
    hk hx.1 hB hstayB (D.gap g hg)
  intro a ha y hy hmin i hi
  have hpower := D.box h hh hy.1
  have hypos := powerBox_positive hh.1 hpower
  have hunit := powerBox_subset_unit_box hh.1 hg.1 hgh hpower
  have hout : y ∉ (D.family.atScale g).plateau (D.level g) := by
    rw [(D.family.atScale g).mem_plateau_iff_minimum_ge]
    exact not_le.mpr hmin
  have hnonzero := active_direction_has_nonzero_projection_of_carrier_nonempty N
    (D.family.atScale g) ⟨hypos, hy.2⟩ hi hout hcarrier
  exact D.flux g hg y hunit i hi hnonzero a ha

theorem ScaleTrapFamily.uniformPermanent [Nonempty (Fin m)]
    (D : ScaleTrapFamily (m := m) N ℓ u c) : N.UniformPermanent ℓ u c (fun _ => True) := by
  let K := (D.family.atScale D.threshold).plateau (D.relaxed D.threshold) ∩
    N.stoichiometricClass c
  have hH : D.threshold ∈ Ioc 0 D.threshold := ⟨D.threshold_pos, le_rfl⟩
  have hpos : ∀ h ∈ Ioc 0 D.threshold,
      (D.family.atScale h).plateau (D.relaxed h) ⊆ {y | Positive y} :=
    fun h hh y hy => powerBox_positive hh.1 (D.box h hh hy)
  have hc : c ∈ K := ⟨fun i => (D.gap _ hH).le.trans (D.reference _ hH i),
    by change c - c ∈ N.stoichiometricSubspace; simp⟩
  refine ⟨K, ⟨c, hc⟩, (D.compact _ hH).inter_right (N.stoichiometricClass_isClosed c),
    (fun y hy => ⟨hpos _ hH hy.1, hy.2⟩), ?_⟩
  intro k hk _
  have htrap : ∀ z ∈ N.positiveClass c, ∃ h ∈ Ioc 0 D.threshold,
      ∃ x, N.IsGlobalPositiveSolution k z x ∧
        ∀ t, 0 ≤ t → x t ∈ (D.family.atScale h).plateau (D.relaxed h) := by
    intro z hz
    obtain ⟨h, hh, hzh⟩ := D.capture z hz.1
    exact ⟨h, hh, N.exists_global_positive_of_compact_affine_face_certificate hk
      (D.family.atScale h) (D.compact h hh) (hpos h hh) (D.faceCertificate hh) hzh⟩
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨h, hh, x, hx, _⟩ := htrap z hz
    exact N.positiveWellPosed_of_exists hk ⟨x, hx⟩
  · intro z hz x hx
    obtain ⟨h, hh, y, hy, hstay⟩ := htrap z hz
    have hinitial : EventuallyIn x ((D.family.atScale h).plateau (D.relaxed h)) :=
      ⟨0, le_rfl, fun t ht => by
        rw [Network.IsIntegralSolution.eqOn_nonnegative N hk hx.1 hy.1 ht]
        exact hstay t ht⟩
    have hiter : ∀ n : ℕ, EventuallyIn x
        ((D.family.atScale (min (rootScale h n) D.threshold)).plateau
          (D.relaxed (min (rootScale h n) D.threshold))) := by
      intro n
      induction n with
      | zero => simpa only [rootScale_zero, min_eq_left hh.2] using hinitial
      | succ n ih =>
        have hn : min (rootScale h n) D.threshold ∈ Ioc 0 D.threshold :=
          ⟨lt_min (rootScale_pos hh.1 n) D.threshold_pos, min_le_right _ _⟩
        simpa only [capped_rootScale_succ hh.1 D.threshold_lt_one.le n] using
          D.eventual_step hn hk hz hx ih
    obtain ⟨n, hn⟩ := capped_rootScale_reaches_threshold hh.1 D.threshold_lt_one
    have hfinal := hiter n
    rw [hn] at hfinal
    obtain ⟨T, hT, hentry⟩ := hfinal
    exact ⟨T, hT, fun t ht => ⟨hentry t ht, (hx.mem_positiveClass hz (hT.trans ht)).2⟩⟩

end Endotactic
