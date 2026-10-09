import Endotactic.MovingPowerAsymptotics
import Endotactic.ExponentMinimum

/-!
# Improve offset decay by shrinking a minimum neighborhood

Offsets bounded by powers with exponents strictly above the fixed minimum are
little-o of a common slightly raised power. All label thresholds are finite;
no continuity or globally uniform tolerance is required.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem shifted_power_offset_isBigO {c : ℝ → ℝ} {β : ℝ}
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β)) :
    IsBigO (𝓝[>] (0 : ℝ)) (fun h => -(h ^ β) + c h) (fun h => h ^ β) :=
  (isBigO_refl (fun h : ℝ => h ^ β) _).neg_left.add hc.isBigO

theorem offset_isLittleO_of_powerBound {c : ℝ → ℝ} {q β : ℝ}
    (hc : IsBigO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β)) (hq : q < β) :
    IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ q) :=
  hc.trans_isLittleO (rpow_isLittleO_nhdsGT_zero hq)

/-- The empty-label case is included. In nonempty families the radius is
bounded by half the smallest strictly positive exponent gap. -/
theorem exists_common_offset_decay {I : Type*} [Fintype I]
    (c : I → ℝ → ℝ) (β : I → ℝ) (t : ℝ) {R : ℝ} (hR : 0 < R)
    (hβ : ∀ i, t < β i)
    (hc : ∀ i, IsBigO (𝓝[>] (0 : ℝ)) (c i) (fun h => h ^ β i)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      ∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (c i) (fun h => h ^ (t + ρ)) := by
  classical
  by_cases hI : Nonempty I
  · let : Nonempty I := hI
    let s := Finset.univ.image (fun i => β i - t)
    have hs : s.Nonempty := Finset.univ_nonempty.image _
    have hmin : 0 < s.min' hs := by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (s.min'_mem hs)
      rw [← hi]
      exact sub_pos.mpr (hβ i)
    refine ⟨min R (s.min' hs / 2), lt_min hR (by positivity), min_le_left _ _, ?_⟩
    intro i
    apply offset_isLittleO_of_powerBound (hc i)
    have hi : s.min' hs ≤ β i - t :=
      s.min'_le _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hρ := min_le_right R (s.min' hs / 2)
    linarith
  · exact ⟨R, hR, le_rfl, fun i => (hI ⟨i⟩).elim⟩

theorem ScaledAffineFamily.sequentialActivityBound_mono {d m : ℕ}
    (A : ScaledAffineFamily d m) {K L : Set (State d)} {ε : Fin m → ℝ}
    (hL : A.HasSequentialActivityBound L ε) (hKL : K ⊆ L) :
    A.HasSequentialActivityBound K ε := by
  intro i h p q hh hhlim hplim hq hi
  exact hL i h p q hh hhlim hplim (hKL hq) hi

/-- Both sequential approximation and improved offset decay hold on the same
closed band after shrinking it. The family and slopes are retained. -/
theorem ScaledAffineFamily.sequentialActivityBound_near_level_with_decay
    {d m : ℕ} (A : ScaledAffineFamily d m) (K : Set (State d)) (hK : IsCompact K)
    (ε : Fin m → ℝ) (f : State d → ℝ) (hf : Continuous f) (t : ℝ)
    (hfixed : A.HasSequentialActivityBound (K ∩ {q | f q = t}) ε)
    (β : Fin m → ℝ) (hβ : ∀ i, t < β i)
    (hc : ∀ i, IsBigO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ β i)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ (t + ρ))) ∧
      A.HasSequentialActivityBound (K ∩ {q | |f q - t| ≤ ρ}) ε := by
  obtain ⟨R, hR, hseq⟩ := A.sequentialActivityBound_near_level K hK ε f hf t hfixed
  obtain ⟨ρ, hρ, hρR, hdecay⟩ := exists_common_offset_decay A.offset β t hR hβ hc
  refine ⟨ρ, hρ, hdecay, A.sequentialActivityBound_mono hseq ?_⟩
  rintro q ⟨hq, hband⟩
  exact ⟨hq, hband.trans hρR⟩

theorem ScaledAffineFamily.sequentialActivityBound_near_minimum_with_decay
    {d m : ℕ} [NeZero d] (A : ScaledAffineFamily d m) (a b : ℝ)
    (ε : Fin m → ℝ) (t : ℝ)
    (hfixed : A.HasSequentialActivityBound
      (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = t}) ε)
    (β : Fin m → ℝ) (hβ : ∀ i, t < β i)
    (hc : ∀ i, IsBigO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ β i)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ (t + ρ))) ∧
      A.HasSequentialActivityBound
        (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | |exponentMinimum q - t| ≤ ρ}) ε :=
  A.sequentialActivityBound_near_level_with_decay _ isCompact_Icc ε exponentMinimum
    continuous_exponentMinimum t hfixed β hβ hc

end Endotactic
