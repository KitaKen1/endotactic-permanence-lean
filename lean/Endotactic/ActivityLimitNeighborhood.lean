import Endotactic.ScaledAffineActivity
import Endotactic.ScaleLimits

/-!
# Fixed-level activity bounds extend to nearby levels

The finite union of bad activity-limit sets is compact inside the given
compact exponent domain. A continuous level function separates this bad set
from a level where all labels are already known to satisfy their tolerance.
This proves the nearby-level step, but does not construct the fixed-level
families or their offset shifts in affine approximation A.
-/

namespace Endotactic

open Filter Topology

def ScaledAffineFamily.activityLimit {d m : ℕ}
    (A : ScaledAffineFamily d m) (i : Fin m) : Set (State d) :=
  scaleLimit (fun h p => (A.atScale h).Active i (exponentialPoint h p))

theorem ScaledAffineFamily.isClosed_activityLimit {d m : ℕ}
    (A : ScaledAffineFamily d m) (i : Fin m) : IsClosed (A.activityLimit i) :=
  isClosed_scaleLimit _

theorem ScaledAffineFamily.isCompact_activityLimit_inter {d m : ℕ}
    (A : ScaledAffineFamily d m) (i : Fin m) {K : Set (State d)} (hK : IsCompact K) :
    IsCompact (K ∩ A.activityLimit i) :=
  hK.inter_right (A.isClosed_activityLimit i)

/-- Exact equivalence: approaching exponent points remain unrestricted, and
every fixed active label, including ties, occurs in its own limit set. -/
theorem ScaledAffineFamily.sequentialActivityBound_iff_limits {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (ε : Fin m → ℝ) :
    A.HasSequentialActivityBound K ε ↔
      ∀ i : Fin m, ∀ q ∈ K, q ∈ A.activityLimit i → ‖q - A.slope i‖ < ε i := by
  constructor
  · intro hseq i q hq
    rintro ⟨h, p, hh, hhlim, hplim, hactive⟩
    exact hseq i h p q hh hhlim hplim hq hactive
  · intro hlimits i h p q hh hhlim hplim hq hactive
    exact hlimits i q hq ⟨h, p, hh, hhlim, hplim, hactive⟩

def ScaledAffineFamily.badActivityLimits {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (ε : Fin m → ℝ) :
    Set (State d) := K ∩ {q | ∃ i : Fin m,
      q ∈ A.activityLimit i ∧ ε i ≤ ‖q - A.slope i‖}

theorem ScaledAffineFamily.isCompact_badActivityLimits {d m : ℕ}
    (A : ScaledAffineFamily d m) {K : Set (State d)} (hK : IsCompact K)
    (ε : Fin m → ℝ) : IsCompact (A.badActivityLimits K ε) := by
  apply hK.inter_right
  have hclosed : ∀ i : Fin m,
      IsClosed (A.activityLimit i ∩ {q | ε i ≤ ‖q - A.slope i‖}) := by
    intro i
    exact (A.isClosed_activityLimit i).inter
      (isClosed_le continuous_const ((continuous_id.sub continuous_const).norm))
  convert isClosed_iUnion_of_finite hclosed using 1
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]

theorem ScaledAffineFamily.sequentialActivityBound_iff_bad_empty {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (ε : Fin m → ℝ) :
    A.HasSequentialActivityBound K ε ↔ A.badActivityLimits K ε = ∅ := by
  rw [A.sequentialActivityBound_iff_limits]
  constructor
  · intro hgood
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro q ⟨hq, i, hi, hbad⟩
    exact (not_lt_of_ge hbad) (hgood i q hq hi)
  · intro hempty i q hq hi
    apply lt_of_not_ge
    intro hbad
    have hmem : q ∈ A.badActivityLimits K ε := ⟨hq, i, hi, hbad⟩
    rw [hempty] at hmem
    exact hmem

/-- The fixed finite family is retained. Neither offset nor tolerance needs
continuity. The level function alone is assumed continuous. -/
theorem ScaledAffineFamily.activityLimits_near_level {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (hK : IsCompact K)
    (ε : Fin m → ℝ) (f : State d → ℝ) (hf : Continuous f) (t : ℝ)
    (hfixed : ∀ i : Fin m, ∀ q ∈ K, q ∈ A.activityLimit i → f q = t →
      ‖q - A.slope i‖ < ε i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ K, |f q - t| < ρ →
      ∀ i : Fin m, q ∈ A.activityLimit i → ‖q - A.slope i‖ < ε i := by
  have hlevel : ∀ q ∈ A.badActivityLimits K ε, f q ≠ t := by
    rintro q ⟨hq, i, hi, hbad⟩ heq
    exact (not_lt_of_ge hbad) (hfixed i q hq hi heq)
  obtain ⟨ρ, hρ, hsep⟩ := compact_avoids_level_band
    (A.isCompact_badActivityLimits hK ε) f hf t hlevel
  refine ⟨ρ, hρ, ?_⟩
  intro q hq hnear i hi
  apply lt_of_not_ge
  intro hbad
  exact (not_lt_of_ge (hsep q ⟨hq, i, hi, hbad⟩)) hnear

/-- A narrower closed band is compact and preserves the strict bound. -/
theorem ScaledAffineFamily.sequentialActivityBound_near_level {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (hK : IsCompact K)
    (ε : Fin m → ℝ) (f : State d → ℝ) (hf : Continuous f) (t : ℝ)
    (hfixed : A.HasSequentialActivityBound (K ∩ {q | f q = t}) ε) :
    ∃ ρ : ℝ, 0 < ρ ∧
      A.HasSequentialActivityBound (K ∩ {q | |f q - t| ≤ ρ}) ε := by
  obtain ⟨ρ, hρ, hnear⟩ := A.activityLimits_near_level K hK ε f hf t
    (fun i q hq hi heq =>
      (A.sequentialActivityBound_iff_limits _ _).mp hfixed i q ⟨hq, heq⟩ hi)
  refine ⟨ρ / 2, by positivity, (A.sequentialActivityBound_iff_limits _ _).mpr ?_⟩
  rintro i q ⟨hq, hband⟩ hi
  exact hnear q hq (hband.trans_lt (by linarith)) i hi

/-- Fixed-level sequential approximation now yields one scale threshold on a
nontrivial closed neighborhood of that level, for every active label. -/
theorem ScaledAffineFamily.uniformActivityBound_near_level {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (hK : IsCompact K)
    (ε : Fin m → ℝ) (f : State d → ℝ) (hf : Continuous f) (t : ℝ)
    (hfixed : A.HasSequentialActivityBound (K ∩ {q | f q = t}) ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ → ∀ q ∈ K, |f q - t| ≤ ρ →
        ∀ i : Fin m, (A.atScale h).Active i (exponentialPoint h q) →
          ‖q - A.slope i‖ < ε i := by
  obtain ⟨ρ, hρ, hseq⟩ := A.sequentialActivityBound_near_level K hK ε f hf t hfixed
  have hband : IsCompact (K ∩ {q | |f q - t| ≤ ρ}) :=
    hK.inter_right (isClosed_le ((hf.sub continuous_const).abs) continuous_const)
  obtain ⟨h₀, hh₀, hh₀1, hgood⟩ := A.uniformActivityBound_of_sequential _ hband ε hseq
  exact ⟨ρ, hρ, h₀, hh₀, hh₀1, fun h hh hsmall q hq hnear =>
    hgood h hh hsmall q ⟨hq, hnear⟩⟩

end Endotactic
