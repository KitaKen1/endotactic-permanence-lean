import Endotactic.OrderedMinimumBandCover

/-!
# Pointwise positive bands admit the required ordered cuts

The compact cover/pruning/order proof closes the pure interval obligation.
Its cut construction includes the one-band case without special assumptions.
The exact full affine existence statement then follows by the checked strong
induction and actual shifted-family construction.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem OrderedOpenMinimumBandCover.exists_ordered_chain {n : ℕ} {a b : ℝ} {ρ : ℝ → ℝ}
    (D : OrderedOpenMinimumBandCover n a b ρ) (hab : a ≤ b)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) : Nonempty (OrderedMinimumBandChain n a b ρ) := by
  classical
  have hex := fun k : Fin n => D.exists_adjacent_cut hρ k.val k.isLt
  choose cut hcl hcu hbl hbu using hex
  let q : ℕ → ℝ := fun k => if hk : k < n then cut ⟨k, hk⟩ else b
  refine ⟨{ center := D.center
            center_mem := D.center_mem
            cut := q
            cut_between := ?_
            band_left := ?_
            band_right := ?_ }⟩
  · intro k hk
    dsimp only [q]
    rw [dif_pos hk]
    exact ⟨hcl ⟨k, hk⟩, hcu ⟨k, hk⟩⟩
  · intro j
    by_cases hj : j.val = 0
    · rw [if_pos hj]
      have heq : j = 0 := Fin.ext hj
      rw [heq]
      exact (D.first_contains_left hab).le
    · have hk : j.val - 1 < n := by omega
      have hpred : j.val - 1 + 1 = j.val := by omega
      rw [if_neg hj]
      dsimp only [q]
      rw [dif_pos hk]
      have h := hbl ⟨j.val - 1, hk⟩
      simpa only [hpred] using h.le
  · intro j
    by_cases hj : j.val = n
    · rw [if_pos hj]
      have heq : j = Fin.last n := Fin.ext hj
      rw [heq]
      exact (D.last_contains_right hab).le
    · have hk : j.val < n := by omega
      rw [if_neg hj]
      dsimp only [q]
      rw [dif_pos hk]
      exact (hbu ⟨j.val, hk⟩).le

theorem minimumBandSelection : MinimumBandSelectionStatement := by
  intro a b hab ρ hρ
  obtain ⟨n, ⟨D⟩⟩ := exists_ordered_open_minimum_band_cover hab.le ρ hρ
  exact ⟨n, D.exists_ordered_chain hab.le hρ⟩

theorem affineMinimumCombination : AffineMinimumCombinationStatement :=
  affineMinimumCombination_of_bandSelection minimumBandSelection

theorem finiteAffineApproximation : FiniteAffineApproximationStatement :=
  finiteAffineApproximation_of_minimumBandSelection minimumBandSelection

end Endotactic
