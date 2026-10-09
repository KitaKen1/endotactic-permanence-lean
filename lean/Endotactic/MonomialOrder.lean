import Endotactic.FluxBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Monomial comparison in logarithmic coordinates

For `0 < h < 1`, lower exponent level means a larger monomial. This order
reversal is essential; exchanging it makes the permanence argument false.
-/

namespace Endotactic

noncomputable def exponentialPoint {d : ℕ} (h : ℝ) (p : State d) : State d :=
  fun i => h ^ p i

theorem exponentialPoint_positive {d : ℕ} {h : ℝ} (hh : 0 < h) (p : State d) :
    Positive (exponentialPoint h p) := by
  intro i
  exact Real.rpow_pos_of_pos hh _

theorem monomial_exponentialPoint {d : ℕ} {h : ℝ} (hh : 0 < h)
    (p : State d) (a : Complex d) :
    monomial (exponentialPoint h p) a = h ^ (dot p (realComplex a)) := by
  unfold monomial exponentialPoint dot realComplex
  rw [Real.rpow_sum_of_pos hh]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.rpow_mul hh.le, Real.rpow_natCast]

theorem monomial_domination_of_exponent_gap {d : ℕ} {h H : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (p : State d) (a b : Complex d)
    (hgap : H ≤ dot p (realComplex b) - dot p (realComplex a)) :
    monomial (exponentialPoint h p) b ≤
      h ^ H * monomial (exponentialPoint h p) a := by
  rw [monomial_exponentialPoint hh, monomial_exponentialPoint hh]
  rw [← Real.rpow_add hh]
  exact Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)

/-- A positive flux at an exponential point, under the explicit geometric gaps.
This theorem is conditional on those gaps, not on the general permanence claim. -/
theorem exponentialPoint_flux_pos {d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (N : Network d E) (hN : N.IsEndotactic) (r p : State d) (k : E → ℝ)
    (a : E) (ℓ u h H : ℝ) (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    (hh : 0 < h) (hh1 : h ≤ 1) (hk : ∀ e, ℓ ≤ k e ∧ k e ≤ u)
    (ha : N.IsEssentialMinimum r a)
    (hgap : ∀ e, N.projection r e < 0 →
      H ≤ dot p (realComplex (N.source e)) - dot p (realComplex (N.source a)))
    (hsmall : u * h ^ H * negativeMass (N.projection r) <
      ℓ * N.projection r a) :
    0 < dot r (N.rhs k (exponentialPoint h p)) := by
  apply network_flux_pos N hN r (exponentialPoint h p) k a ℓ u (h ^ H)
    hℓ hu (exponentialPoint_positive hh p) hk ha
  · intro e he
    exact monomial_domination_of_exponent_gap hh hh1 p (N.source a) (N.source e)
      (hgap e he)
  · exact hsmall

end Endotactic
