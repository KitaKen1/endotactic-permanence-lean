import Endotactic.ZeroSlopeActivity
import Endotactic.LogarithmicBox
import Endotactic.IntegralTrajectory

/-!
# Compact positive plateaux from a zero branch

The constant active branch caps the whole affine minimum. Uniform exclusion
of this branch on the exponent-box boundary, convexity and one interior point
put its entire maximal plateau inside the positive box.
-/

namespace Endotactic

open Filter Topology

theorem AffineFamily.exists_active {d m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (x : State d) : ∃ i, A.Active i x := by
  obtain ⟨i, hi⟩ := finiteMinimum_attained (fun j => A.value j x)
  exact ⟨i, (A.active_iff_minimum_eq i x).mpr hi⟩

theorem ScaledAffineFamily.zero_cap_plateau_subset_open_box {d m : ℕ}
    (A : ScaledAffineFamily d m) {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (i₀ : Fin m) (hi₀ : A.slope i₀ = 0) {z : State d}
    (hz : (A.atScale h).Active i₀ z)
    (hzbox : z ∈ openCoordinateBox (fun _ => h) (fun _ => h⁻¹))
    (hactive : ∀ p ∈ Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
      (A.atScale h).Active i₀ (exponentialPoint h p) → ‖p‖ < 1) :
    (A.atScale h).plateau (A.offset i₀ h) ⊆
      openCoordinateBox (fun _ => h) (fun _ => h⁻¹) := by
  have hslope : ∀ j, (A.atScale h).slope i₀ j = 0 :=
    fun j => congrFun hi₀ j
  have hzK := ((A.atScale h).constant_active_iff_mem_plateau i₀ hslope z).mp hz
  apply convex_subset_open_box_of_no_boundary ((A.atScale h).plateau_convex _) hzK hzbox
  intro x hx hbox
  by_contra hboundary
  have hxpos : Positive x := fun j => hh.trans_le (hbox.1 j)
  have hpow := exponentialPoint_logarithmicExponent hh hh1 hxpos
  have hi := ((A.atScale h).constant_active_iff_mem_plateau i₀ hslope x).mpr hx
  have hp := logarithmicExponent_mem_cube hh hh1 hbox
  have hlt := hactive (logarithmicExponent h x) hp (hpow.symm ▸ hi)
  exact (not_lt_of_ge (logarithmicExponent_boundary_norm hh hh1 hbox hboundary)) hlt

theorem ScaledAffineFamily.zero_cap_plateau_compact_positive {d m : ℕ}
    (A : ScaledAffineFamily d m) {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (i₀ : Fin m) (hi₀ : A.slope i₀ = 0) {z : State d}
    (hz : (A.atScale h).Active i₀ z)
    (hzbox : z ∈ openCoordinateBox (fun _ => h) (fun _ => h⁻¹))
    (hactive : ∀ p ∈ Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
      (A.atScale h).Active i₀ (exponentialPoint h p) → ‖p‖ < 1) :
    IsCompact ((A.atScale h).plateau (A.offset i₀ h)) ∧
      (A.atScale h).plateau (A.offset i₀ h) ⊆ {x | Positive x} ∧
      (A.atScale h).plateau (A.offset i₀ h) ⊆ Set.Icc (fun _ => h) (fun _ => h⁻¹) := by
  have hsub := A.zero_cap_plateau_subset_open_box hh hh1 i₀ hi₀ hz hzbox hactive
  have hbox : (A.atScale h).plateau (A.offset i₀ h) ⊆
      Set.Icc (fun _ => h) (fun _ => h⁻¹) :=
    fun x hx => ⟨fun j => (hsub hx j).1.le, fun j => (hsub hx j).2.le⟩
  exact ⟨(A.atScale h).plateau_isCompact_of_subset _ isCompact_Icc hbox,
    fun x hx j => hh.trans (hsub hx j).1, hbox⟩

/-- A fixed finite family works for every positive reference point. The scale
threshold is allowed to depend on that point; this is not common absorption. -/
theorem ScaledAffineFamily.exists_small_scale_zero_cap {d m : ℕ}
    [Nonempty (Fin m)] (A : ScaledAffineFamily d m) (ε : State d → ℝ)
    (hseq : A.HasSequentialActivityBound
      (Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
      (fun i => zeroForcingTolerance ε (A.slope i)))
    {z : State d} (hz : Positive z) :
    ∃ H : ℝ, 0 < H ∧ H ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < H →
      ∃ i₀ : Fin m, A.slope i₀ = 0 ∧
        z ∈ (A.atScale h).plateau (A.offset i₀ h) ∧
        IsCompact ((A.atScale h).plateau (A.offset i₀ h)) ∧
        (A.atScale h).plateau (A.offset i₀ h) ⊆ {x | Positive x} ∧
        (A.atScale h).plateau (A.offset i₀ h) ⊆ Set.Icc (fun _ => h) (fun _ => h⁻¹) := by
  have hzero : (0 : State d) ∈ Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) :=
    ⟨fun _ => by norm_num, fun _ => by norm_num⟩
  obtain ⟨δ, hδ, hnear⟩ := A.exists_zero_active_neighborhood hzero _ hseq
    (fun i hi => zeroForcingTolerance_nonzero ε hi)
  obtain ⟨H₁, hH₁, hH₁1, huniform⟩ := A.uniformActivityBound_of_sequential _
    isCompact_Icc _ hseq
  have hevent : ∀ᶠ h in 𝓝[>] (0 : ℝ), ‖logarithmicExponent h z‖ < min δ 1 :=
    (tendsto_logarithmicExponent z).norm.eventually
      (by simpa only [norm_zero] using
        (gt_mem_nhds (lt_min hδ (by norm_num)) :
          ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), x < min δ 1))
  obtain ⟨H₂, hH₂, hlog⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  refine ⟨min H₁ (min δ (min H₂ 1)), lt_min hH₁ (lt_min hδ (lt_min hH₂ (by norm_num))),
    (min_le_left _ _).trans hH₁1, ?_⟩
  intro h hh hlt
  have hlt₁ : h < H₁ := hlt.trans_le (min_le_left _ _)
  have hrest : h < min δ (min H₂ 1) := hlt.trans_le (min_le_right _ _)
  have hltδ : h < δ := hrest.trans_le (min_le_left _ _)
  have hrest₂ : h < min H₂ 1 := hrest.trans_le (min_le_right _ _)
  have hlt₂ : h < H₂ := hrest₂.trans_le (min_le_left _ _)
  have hh1 : h < 1 := hrest₂.trans_le (min_le_right _ _)
  have hnorm := hlog ⟨hh, hlt₂⟩
  have hpδ : ‖logarithmicExponent h z‖ < δ := hnorm.trans_le (min_le_left _ _)
  have hp1 : ‖logarithmicExponent h z‖ < 1 := hnorm.trans_le (min_le_right _ _)
  have hpow := exponentialPoint_logarithmicExponent hh hh1 hz
  obtain ⟨i₀, hi₀⟩ := (A.atScale h).exists_active z
  have hslope := hnear h hh hltδ _ hpδ i₀ (hpow.symm ▸ hi₀)
  have hslope' : ∀ j, (A.atScale h).slope i₀ j = 0 := fun j => congrFun hslope j
  have hzK := ((A.atScale h).constant_active_iff_mem_plateau i₀ hslope' z).mp hi₀
  have hzbox : z ∈ openCoordinateBox (fun _ => h) (fun _ => h⁻¹) := by
    intro j
    have hb : |logarithmicExponent h z j| < 1 :=
      (show |logarithmicExponent h z j| ≤ ‖logarithmicExponent h z‖ by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (logarithmicExponent h z) j).trans_lt hp1
    have hp := abs_lt.mp hb
    have hlower := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hp.2
    have hupper := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hp.1
    have heqj : h ^ logarithmicExponent h z j = z j := congrFun hpow j
    simpa only [Real.rpow_one, Real.rpow_neg_one, heqj] using
      (show h ^ (1 : ℝ) < h ^ logarithmicExponent h z j ∧
        h ^ logarithmicExponent h z j < h ^ (-1 : ℝ) from ⟨hlower, hupper⟩)
  have hactive : ∀ p ∈ Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
      (A.atScale h).Active i₀ (exponentialPoint h p) → ‖p‖ < 1 := by
    intro p hp hi
    have hb := huniform h hh hlt₁ p hp i₀ hi
    rw [hslope, sub_zero] at hb
    exact hb.trans_le (zeroForcingTolerance_zero ε) |>.trans (by norm_num)
  obtain ⟨hcompact, hpos, hbox⟩ :=
    A.zero_cap_plateau_compact_positive hh hh1 i₀ hslope hi₀ hzbox hactive
  exact ⟨i₀, hslope, hzK, hcompact, hpos, hbox⟩

end Endotactic
