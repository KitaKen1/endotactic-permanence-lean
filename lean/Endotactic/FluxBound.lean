import Endotactic.EssentialSource

/-!
# A single positive source dominates all negative fluxes

The generic finite-sum lemma separates the ordered reaction geometry from the
analytic monomial comparison. In particular, it holds for every coefficient
vector in a prescribed box, not just sampled coefficient values.
-/

namespace Endotactic

def negativeMass {E : Type*} [Fintype E] (p : E → ℝ) : ℝ :=
  ∑ e, max (-(p e)) 0

theorem weighted_sum_lower_bound {E : Type*} [Fintype E] [DecidableEq E]
    (p μ k : E → ℝ) (a : E) (ℓ u ρ : ℝ)
    (hu : 0 ≤ u) (hμ : ∀ e, 0 ≤ μ e)
    (hk : ∀ e, ℓ ≤ k e ∧ k e ≤ u) (hk0 : ∀ e, 0 ≤ k e)
    (ha : 0 ≤ p a) (hdom : ∀ e, p e < 0 → μ e ≤ ρ * μ a) :
    μ a * (ℓ * p a - u * ρ * negativeMass p) ≤ ∑ e, k e * μ e * p e := by
  have hpoint : ∀ e : E,
      (if e = a then ℓ * μ a * p a else 0) -
        (u * (ρ * μ a)) * max (-(p e)) 0 ≤ k e * μ e * p e := by
    intro e
    by_cases hea : e = a
    · subst e
      have hmul := mul_le_mul_of_nonneg_right (hk a).1
        (mul_nonneg (hμ a) ha)
      simpa [max_eq_right (neg_nonpos.mpr ha), mul_assoc] using hmul
    · simp only [if_neg hea]
      by_cases hpe : p e < 0
      · have hw : k e * μ e ≤ u * (ρ * μ a) := by
          calc
            k e * μ e ≤ u * μ e := mul_le_mul_of_nonneg_right (hk e).2 (hμ e)
            _ ≤ u * (ρ * μ a) := mul_le_mul_of_nonneg_left (hdom e hpe) hu
        have hm := mul_le_mul_of_nonpos_right hw (le_of_lt hpe)
        rw [max_eq_left (neg_nonneg.mpr (le_of_lt hpe))]
        nlinarith only [hm]
      · have hp : 0 ≤ p e := le_of_not_gt hpe
        simp only [max_eq_right (neg_nonpos.mpr hp), mul_zero, sub_zero]
        exact mul_nonneg (mul_nonneg (hk0 e) (hμ e)) hp
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hpoint e)
  have heq : (∑ e : E, ((if e = a then ℓ * μ a * p a else 0) -
      (u * (ρ * μ a)) * max (-(p e)) 0)) =
      μ a * (ℓ * p a - u * ρ * negativeMass p) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.mul_sum]
    unfold negativeMass
    ring
  rwa [heq] at hsum

theorem weighted_sum_pos {E : Type*} [Fintype E] [DecidableEq E]
    (p μ k : E → ℝ) (a : E) (ℓ u ρ : ℝ)
    (hu : 0 ≤ u) (hμ : ∀ e, 0 ≤ μ e)
    (hk : ∀ e, ℓ ≤ k e ∧ k e ≤ u) (hk0 : ∀ e, 0 ≤ k e)
    (ha : 0 ≤ p a) (hμa : 0 < μ a)
    (hdom : ∀ e, p e < 0 → μ e ≤ ρ * μ a)
    (hgap : u * ρ * negativeMass p < ℓ * p a) :
    0 < ∑ e, k e * μ e * p e := by
  exact lt_of_lt_of_le (mul_pos hμa (sub_pos.mpr hgap))
    (weighted_sum_lower_bound p μ k a ℓ u ρ hu hμ hk hk0 ha hdom)

theorem dot_rhs {d : ℕ} {E : Type*} [Fintype E]
    (N : Network d E) (r x : State d) (k : E → ℝ) :
    dot r (N.rhs k x) = ∑ e, k e * monomial x (N.source e) * N.projection r e := by
  simp only [dot, Network.rhs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Network.projection, dot]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem network_flux_pos {d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (N : Network d E) (hN : N.IsEndotactic) (r x : State d) (k : E → ℝ)
    (a : E) (ℓ u ρ : ℝ) (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    (hx : Positive x) (hk : ∀ e, ℓ ≤ k e ∧ k e ≤ u)
    (ha : N.IsEssentialMinimum r a)
    (hdom : ∀ e, N.projection r e < 0 →
      monomial x (N.source e) ≤ ρ * monomial x (N.source a))
    (hgap : u * ρ * negativeMass (N.projection r) < ℓ * N.projection r a) :
    0 < dot r (N.rhs k x) := by
  rw [dot_rhs]
  exact weighted_sum_pos (N.projection r) (fun e => monomial x (N.source e))
    k a ℓ u ρ hu (fun e => (monomial_pos hx _).le) hk
    (fun e => le_trans hℓ.le (hk e).1)
    (essentialMinimum_projection_pos N hN ha).le (monomial_pos hx _)
    hdom hgap

end Endotactic
