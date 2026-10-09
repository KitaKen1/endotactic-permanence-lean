import Endotactic.ActivityLimitNeighborhood
import Endotactic.FiniteMinimum

/-!
# Zero slopes near the zero exponent

A pointwise tolerance below half the norm of every nonzero slope forces
all labels active sufficiently near the zero exponent to have zero slope.
The labels are fixed and finite; neither offsets nor tolerance are continuous.
-/

namespace Endotactic

open Filter Topology

noncomputable def zeroForcingTolerance {d : ℕ} (ε : State d → ℝ)
    (r : State d) : ℝ := min (ε r) (if r = 0 then 1 / 2 else ‖r‖ / 2)

theorem zeroForcingTolerance_pos {d : ℕ} {ε : State d → ℝ}
    (hε : ∀ r, 0 < ε r) (r : State d) : 0 < zeroForcingTolerance ε r := by
  classical
  unfold zeroForcingTolerance
  apply lt_min (hε r)
  split_ifs with hr
  · norm_num
  · exact div_pos (norm_pos_iff.mpr hr) (by norm_num)

theorem zeroForcingTolerance_le {d : ℕ} (ε : State d → ℝ) (r : State d) :
    zeroForcingTolerance ε r ≤ ε r := min_le_left _ _

theorem zeroForcingTolerance_zero {d : ℕ} (ε : State d → ℝ) :
    zeroForcingTolerance ε 0 ≤ 1 / 2 := by
  simp [zeroForcingTolerance]

theorem zeroForcingTolerance_nonzero {d : ℕ} (ε : State d → ℝ)
    {r : State d} (hr : r ≠ 0) : zeroForcingTolerance ε r ≤ ‖r‖ / 2 := by
  simpa only [zeroForcingTolerance, if_neg hr] using
    (min_le_right (ε r) (‖r‖ / 2))

theorem ScaledAffineFamily.sequentialActivityBound_tolerance_mono {d m : ℕ}
    (A : ScaledAffineFamily d m) {K : Set (State d)} {ε η : Fin m → ℝ}
    (hseq : A.HasSequentialActivityBound K ε) (hle : ∀ i, ε i ≤ η i) :
    A.HasSequentialActivityBound K η := by
  intro i h p q hh hlim hplim hq hi
  exact (hseq i h p q hh hlim hplim hq hi).trans_le (hle i)

/-- The exponent points in this neighborhood need not belong to `K`. -/
theorem ScaledAffineFamily.exists_zero_active_neighborhood {d m : ℕ}
    [Nonempty (Fin m)] (A : ScaledAffineFamily d m) {K : Set (State d)}
    (hzero : (0 : State d) ∈ K) (ε : Fin m → ℝ)
    (hseq : A.HasSequentialActivityBound K ε)
    (hsmall : ∀ i, A.slope i ≠ 0 → ε i ≤ ‖A.slope i‖ / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ p : State d, ‖p‖ < δ → ∀ i,
        (A.atScale h).Active i (exponentialPoint h p) → A.slope i = 0 := by
  classical
  have hex : ∀ i : Fin m, ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ p : State d, ‖p‖ < δ →
        (A.atScale h).Active i (exponentialPoint h p) → A.slope i = 0 := by
    intro i
    by_cases hi : A.slope i = 0
    · exact ⟨1, by norm_num, fun _ _ _ _ _ _ => hi⟩
    · have hnot : (0 : State d) ∉ A.activityLimit i := by
        intro hlim
        have hb := (A.sequentialActivityBound_iff_limits K ε).mp hseq i 0 hzero hlim
        simp only [zero_sub, norm_neg] at hb
        have hn := norm_nonneg (A.slope i)
        have he := hsmall i hi
        linarith
      by_contra hbad
      push Not at hbad
      apply hnot
      apply mem_scaleLimit_iff_small_witness.mpr
      intro δ hδ
      obtain ⟨h, hh, hlt, p, hp, hactive, hne⟩ := hbad δ hδ
      exact ⟨h, hh, hlt, p, by simpa only [dist_zero_right] using hp, hactive⟩
  choose δ hδ hgood using hex
  have hmin : 0 < finiteMinimum δ := by
    obtain ⟨i, hi⟩ := finiteMinimum_attained δ
    rw [hi]
    exact hδ i
  refine ⟨finiteMinimum δ, hmin, ?_⟩
  intro h hh hlt p hp i hactive
  exact hgood i h hh (hlt.trans_le (finiteMinimum_le δ i)) p
    (hp.trans_le (finiteMinimum_le δ i)) hactive

end Endotactic
