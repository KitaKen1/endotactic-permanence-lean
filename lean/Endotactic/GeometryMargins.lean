import Endotactic.MonomialOrder

/-! # Transfer of strict source gaps from an active slope to exponent space -/

namespace Endotactic

def l1 {d : ℕ} (v : State d) : ℝ := ∑ i, |v i|

theorem dot_error_le {d : ℕ} (p r v : State d) {ε : ℝ}
    (hclose : ∀ i, |p i - r i| ≤ ε) :
    |dot p v - dot r v| ≤ ε * l1 v := by
  have heq : dot p v - dot r v = ∑ i, (p i - r i) * v i := by
    simp [dot, sub_mul, Finset.sum_sub_distrib]
  rw [heq]
  calc
    |∑ i, (p i - r i) * v i| ≤ ∑ i, |(p i - r i) * v i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ε * |v i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hclose i) (abs_nonneg _)
    _ = ε * l1 v := by rw [← Finset.mul_sum]; rfl

theorem dot_gap_transfer {d : ℕ} (p r v : State d) {ε H : ℝ}
    (hclose : ∀ i, |p i - r i| ≤ ε)
    (herror : ε * l1 v ≤ dot r v / 2)
    (hH : H ≤ dot r v / 2) : H ≤ dot p v := by
  have h := dot_error_le p r v hclose
  have := (abs_le.mp h).1
  linarith

theorem source_gap_transfer {d : ℕ} {E : Type*} (N : Network d E)
    (p r : State d) (a e : E) {ε H : ℝ}
    (hclose : ∀ i, |p i - r i| ≤ ε)
    (herror : ε * l1 (realComplex (N.source e) - realComplex (N.source a)) ≤
      (N.sourceLevel r e - N.sourceLevel r a) / 2)
    (hH : H ≤ (N.sourceLevel r e - N.sourceLevel r a) / 2) :
    H ≤ N.sourceLevel p e - N.sourceLevel p a := by
  have h := dot_gap_transfer p r
    (realComplex (N.source e) - realComplex (N.source a)) hclose
    (by simpa [dot_sub, Network.sourceLevel] using herror)
    (by simpa [dot_sub, Network.sourceLevel] using hH)
  simpa [dot_sub, Network.sourceLevel] using h

end Endotactic
