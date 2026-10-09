import Endotactic.ScaleTrapPermanence
import Endotactic.AffineApproximationExistence

/-!
# General endotactic scale-trap family construction

Tolerance is selected before the finite family. Each scale gets a positive
relaxation staying in its quarter-power box. No offset continuity, common
positive tolerance infimum, nestedness or carrier oracle is assumed.
-/

namespace Endotactic

open Set Filter Topology

theorem Network.exists_scaleTrapFamily {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (hd : 0 < d) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    {c : State d} (hc : Positive c) :
    ∃ m : ℕ, 0 < m ∧ Nonempty (ScaleTrapFamily (m := m) N ℓ u c) := by
  classical
  obtain ⟨εN, hεN⟩ := N.exists_slopeTolerance hN
  let η : State d → ℝ := fun r => min (εN r) (1 / 8 : ℝ)
  have hη : ∀ r, 0 < η r := fun r => lt_min (hεN r).1 (by norm_num)
  obtain ⟨m, hm, A, _, _, hseq⟩ := finiteAffineApproximation d hd (-1) 1 (by norm_num)
    (zeroForcingTolerance η) (fun r _ => zeroForcingTolerance_pos hη r)
  let : NeZero m := ⟨by omega⟩
  have hseqN := A.sequentialActivityBound_tolerance_mono hseq
    (fun i => (zeroForcingTolerance_le η (A.slope i)).trans (min_le_left _ _))
  obtain ⟨F, hF, _, hflux⟩ := N.uniform_active_flux_of_sequentialActivityBound
    A _ isCompact_Icc εN hεN hseqN hℓ hu
  obtain ⟨C, hC, _, hcapc⟩ := A.exists_small_scale_zero_cap η hseq hc
  obtain ⟨U, hU, _, huniform⟩ := A.uniformActivityBound_of_sequential _ isCompact_Icc _ hseq
  have hevent : ∀ᶠ h in 𝓝[>] (0 : ℝ), ‖logarithmicExponent h c‖ < (1 / 4 : ℝ) :=
    (tendsto_logarithmicExponent c).norm.eventually
      (by simpa only [norm_zero] using
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4) :
          ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), x < 1 / 4))
  obtain ⟨L, hL, hlog⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  let H : ℝ := min F (min C (min U (min L 1))) / 2
  have hbase : 0 < min F (min C (min U (min L 1))) :=
    lt_min hF (lt_min hC (lt_min hU (lt_min hL (by norm_num))))
  have hH : 0 < H := div_pos hbase (by norm_num)
  have hHlt : H < min F (min C (min U (min L 1))) := by dsimp [H]; linarith
  have hHF : H < F := hHlt.trans_le (min_le_left _ _)
  have hrest := hHlt.trans_le (min_le_right _ _)
  have hHC : H < C := hrest.trans_le (min_le_left _ _)
  have hrestU := hrest.trans_le (min_le_right _ _)
  have hHU : H < U := hrestU.trans_le (min_le_left _ _)
  have hrestL := hrestU.trans_le (min_le_right _ _)
  have hHL : H < L := hrestL.trans_le (min_le_left _ _)
  have hH1 : H < 1 := hrestL.trans_le (min_le_right _ _)
  let M : ℝ → ℝ := fun h => (A.atScale h).minimum c
  have hgeom : ∀ h ∈ Ioc 0 H,
      c ∈ (A.atScale h).plateau (M h) ∧ IsCompact ((A.atScale h).plateau (M h)) ∧
      (A.atScale h).plateau (M h) ⊆
        openCoordinateBox (fun _ => h ^ (1 / 4 : ℝ)) (fun _ => (h ^ (1 / 4 : ℝ))⁻¹) := by
    intro h hh
    have hh1 := hh.2.trans_lt hH1
    obtain ⟨i₀, hi₀, hcK, hcompact, _, _⟩ := hcapc h hh.1 (hh.2.trans_lt hHC)
    have hslope : ∀ j, (A.atScale h).slope i₀ j = 0 := fun j => congrFun hi₀ j
    have hactive := ((A.atScale h).constant_active_iff_mem_plateau i₀ hslope c).mpr hcK
    have hM : M h = A.offset i₀ h := by
      change (A.atScale h).minimum c = _
      rw [((A.atScale h).active_iff_minimum_eq i₀ c).mp hactive,
        (A.atScale h).constant_value i₀ hslope c]
      rfl
    have hcbox := logarithmicExponent_norm_lt_mem_open_power_box hh.1 hh1 hc
      (hlog ⟨hh.1, hh.2.trans_lt hHL⟩)
    have hsmall : ∀ p ∈ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
        (A.atScale h).Active i₀ (exponentialPoint h p) → ‖p‖ < (1 / 4 : ℝ) := by
      intro p hp hi
      have hb := huniform h hh.1 (hh.2.trans_lt hHU) p hp i₀ hi
      rw [hi₀, sub_zero] at hb
      have he : zeroForcingTolerance η 0 ≤ (1 / 8 : ℝ) :=
        (zeroForcingTolerance_le η 0).trans (min_le_right _ _)
      exact (hb.trans_le he).trans (by norm_num)
    have hsub := A.zero_cap_plateau_subset_open_power_box hh.1 hh1
      (by norm_num) (by norm_num) i₀ hi₀ hactive hcbox hsmall
    rw [hM]
    exact ⟨hcK, hcompact, hsub⟩
  have hrelax : ∀ h : ℝ, ∃ δ : ℝ, 0 < δ ∧ (h ∈ Ioc 0 H →
      (A.atScale h).plateau (M h - δ) ⊆
        openCoordinateBox (fun _ => h ^ (1 / 4 : ℝ)) (fun _ => (h ^ (1 / 4 : ℝ))⁻¹)) := by
    intro h
    by_cases hh : h ∈ Ioc 0 H
    · obtain ⟨hcK, hcompact, hsub⟩ := hgeom h hh
      obtain ⟨δ, hδ, hδsub⟩ := (A.atScale h).exists_relaxed_plateau_subset_open
        ⟨c, hcK⟩ hcompact (isOpen_openCoordinateBox _ _) hsub
      exact ⟨δ, hδ, fun _ => hδsub⟩
    · exact ⟨1, by norm_num, fun hs => (hh hs).elim⟩
  choose δ hδ hδsub using hrelax
  let Q : ℝ → ℝ := fun h => M h - δ h
  have hbox : ∀ h ∈ Ioc 0 H, (A.atScale h).plateau (Q h) ⊆ powerBox h (1 / 4 : ℝ) :=
    fun h hh y hy => ⟨fun j => (hδsub h hh hy j).1.le, fun j => (hδsub h hh hy j).2.le⟩
  refine ⟨m, hm, ⟨{
    family := A
    threshold := H
    threshold_pos := hH
    threshold_lt_one := hH1
    level := M
    relaxed := Q
    reference := fun h hh => (hgeom h hh).1
    gap := fun h _ => sub_lt_self (M h) (hδ h)
    compact := fun h hh => (A.atScale h).plateau_isCompact_of_subset (Q h)
      isCompact_Icc (hbox h hh)
    box := hbox
    capture := ?_
    flux := ?_
  }⟩⟩
  · intro z hz
    obtain ⟨Z, hZ, _, hcapz⟩ := A.exists_small_scale_zero_cap η hseq hz
    let h : ℝ := min Z H / 2
    have hh : 0 < h := div_pos (lt_min hZ hH) (by norm_num)
    have hlt : h < min Z H := by dsimp [h]; linarith [lt_min hZ hH]
    have hhH : h ∈ Ioc 0 H := ⟨hh, (hlt.trans_le (min_le_right _ _)).le⟩
    obtain ⟨i, hi, hcK, _, _, _⟩ := hcapc h hh (hhH.2.trans_lt hHC)
    obtain ⟨j, hj, hzK, _, _, _⟩ := hcapz h hh (hlt.trans_le (min_le_left _ _))
    have hi' : ∀ k, (A.atScale h).slope i k = 0 := fun k => congrFun hi k
    have hj' : ∀ k, (A.atScale h).slope j k = 0 := fun k => congrFun hj k
    have hic := ((A.atScale h).constant_active_iff_mem_plateau i hi' c).mpr hcK
    have hjz := ((A.atScale h).constant_active_iff_mem_plateau j hj' z).mpr hzK
    have hiz := (A.atScale h).active_zero_transfer hi' hj' hic hjz
    have hM : M h = A.offset i h := by
      change (A.atScale h).minimum c = _
      rw [((A.atScale h).active_iff_minimum_eq i c).mp hic,
        (A.atScale h).constant_value i hi' c]
      rfl
    have hzM : z ∈ (A.atScale h).plateau (M h) := by
      rw [hM]
      exact ((A.atScale h).constant_active_iff_mem_plateau i hi' z).mp hiz
    exact ⟨h, hhH, fun i => (sub_le_self (M h) (hδ h).le).trans (hzM i)⟩
  · intro h hh y hy i hi hnonzero a ha
    have hypos : Positive y := fun j => hh.1.trans_le (hy.1 j)
    have hh1 := hh.2.trans_lt hH1
    have hpow := exponentialPoint_logarithmicExponent hh.1 hh1 hypos
    have hp := logarithmicExponent_mem_cube hh.1 hh1 hy
    have hb := hflux h hh.1 (hh.2.trans_lt hHF) (logarithmicExponent h y) hp i
      (hpow.symm ▸ hi) hnonzero a (fun e => ⟨ha.1 e, ha.2 e⟩)
    simpa only [hpow] using hb

end Endotactic
