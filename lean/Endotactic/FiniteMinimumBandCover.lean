import Endotactic.MinimumBandReduction
import Mathlib.Data.Finset.Sort

/-!
# Compact finite band covers and pruning by minimum cardinality

Every center lies in the original interval. Pointwise positivity alone gives
an open cover. A cover of minimum finite cardinality cannot contain a band
contained in another band. No radius continuity or uniform lower bound is used.
-/

namespace Endotactic

open Filter Topology

def CoversMinimumBands (a b : ℝ) (ρ : ℝ → ℝ) (s : Finset ℝ) : Prop :=
  (∀ t ∈ s, t ∈ Set.Icc a b) ∧
    ∀ x ∈ Set.Icc a b, ∃ t ∈ s, t - ρ t < x ∧ x < t + ρ t

theorem exists_finite_minimum_band_cover {a b : ℝ} (ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) :
    ∃ s : Finset ℝ, CoversMinimumBands a b ρ s := by
  classical
  let U : Set.Icc a b → Set ℝ := fun t => Set.Ioo (t.val - ρ t.val) (t.val + ρ t.val)
  have hcover : Set.Icc a b ⊆ ⋃ t, U t := by
    intro x hx
    apply Set.mem_iUnion.mpr
    exact ⟨⟨x, hx⟩, ⟨by dsimp [U]; linarith [hρ x hx],
      by dsimp [U]; linarith [hρ x hx]⟩⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover U (fun _ => isOpen_Ioo) hcover
  refine ⟨s.image Subtype.val, ?_, ?_⟩
  · intro t ht
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ht
    exact u.property
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := (by simpa only [Set.mem_iUnion, exists_prop] using hs hx :
      ∃ t : Set.Icc a b, t ∈ s ∧ x ∈ U t)
    exact ⟨t.val, Finset.mem_image.mpr ⟨t, ht, rfl⟩, hxt⟩

theorem CoversMinimumBands.nonempty {a b : ℝ} {ρ : ℝ → ℝ} {s : Finset ℝ}
    (hs : CoversMinimumBands a b ρ s) (hab : a ≤ b) : s.Nonempty := by
  obtain ⟨t, ht, _⟩ := hs.2 a ⟨le_rfl, hab⟩
  exact ⟨t, ht⟩

theorem exists_pruned_minimum_band_cover {a b : ℝ} (ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) :
    ∃ s : Finset ℝ, CoversMinimumBands a b ρ s ∧
      ∀ t ∈ s, ∀ u ∈ s, t ≠ u → ¬ (u - ρ u ≤ t - ρ t ∧ t + ρ t ≤ u + ρ u) := by
  classical
  obtain ⟨s₀, hs₀⟩ := exists_finite_minimum_band_cover ρ hρ
  have hex : ∃ k : ℕ, ∃ s : Finset ℝ, s.card = k ∧ CoversMinimumBands a b ρ s :=
    ⟨s₀.card, s₀, rfl, hs₀⟩
  obtain ⟨s, hcard, hs⟩ := Nat.find_spec hex
  refine ⟨s, hs, ?_⟩
  intro t ht u hu htu hcontained
  have herase : CoversMinimumBands a b ρ (s.erase t) := by
    refine ⟨fun v hv => hs.1 v (Finset.mem_of_mem_erase hv), ?_⟩
    intro x hx
    obtain ⟨v, hv, hleft, hright⟩ := hs.2 x hx
    by_cases hvt : v = t
    · subst v
      exact ⟨u, Finset.mem_erase.mpr ⟨htu.symm, hu⟩,
        hcontained.1.trans_lt hleft, hright.trans_le hcontained.2⟩
    · exact ⟨v, Finset.mem_erase.mpr ⟨hvt, hv⟩, hleft, hright⟩
  have hmin : Nat.find hex ≤ (s.erase t).card :=
    Nat.find_min' hex ⟨s.erase t, rfl, herase⟩
  have hsmall := Finset.card_erase_lt_of_mem ht
  omega

theorem minimum_band_endpoints_strict_of_noncontainment (ρ : ℝ → ℝ)
    {t u : ℝ} (htu : t < u)
    (hforward : ¬ (u - ρ u ≤ t - ρ t ∧ t + ρ t ≤ u + ρ u))
    (hbackward : ¬ (t - ρ t ≤ u - ρ u ∧ u + ρ u ≤ t + ρ t)) :
    t - ρ t < u - ρ u ∧ t + ρ t < u + ρ u := by
  constructor
  · by_contra hbad
    apply hforward
    exact ⟨le_of_not_gt hbad, by linarith⟩
  · by_contra hbad
    apply hbackward
    exact ⟨by linarith, le_of_not_gt hbad⟩

end Endotactic
