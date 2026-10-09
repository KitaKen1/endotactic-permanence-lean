import Endotactic.FiniteDirectionalCover

/-!
# The bridge from finite active-slope approximation to uniform flux

Each nonconserved slope has a positive tolerance for perturbing the exponent
point. For any fixed finite set of slopes these tolerances give one common
scale threshold. Constructing an affine family with the required activity
approximation is still a separate, unproved geometric step.
-/

namespace Endotactic

theorem l1_nonneg {d : ℕ} (v : State d) : 0 ≤ l1 v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem exists_directional_exponent_tolerance {d : ℕ} {E : Type*}
    [Fintype E] {N : Network d E} {r : State d} {H B : ℝ}
    (C : N.DirectionalCertificate r r H B) (hH : 0 < H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : State d, (∀ i, |p i - r i| ≤ ε) →
      Nonempty (N.DirectionalCertificate r p (H / 2) B) := by
  classical
  let L := ∑ e : E, l1 (realComplex (N.source e) - realComplex (N.source C.pivot))
  have hL : 0 ≤ L := Finset.sum_nonneg fun _ _ => l1_nonneg _
  let ε := H / (2 * (L + 1))
  have hden : 0 < 2 * (L + 1) := by positivity
  have hε : 0 < ε := div_pos hH hden
  have heq : ε * (2 * (L + 1)) = H := div_mul_cancel₀ H hden.ne'
  have hsmall : ε * L ≤ H / 2 := by nlinarith only [heq, hε]
  refine ⟨ε, hε, ?_⟩
  intro p hclose
  refine ⟨C.transfer_exponent hclose ?_⟩
  intro e _
  have heL : l1 (realComplex (N.source e) - realComplex (N.source C.pivot)) ≤ L :=
    Finset.single_le_sum (fun f _ => l1_nonneg
      (realComplex (N.source f) - realComplex (N.source C.pivot))) (Finset.mem_univ e)
  exact (mul_le_mul_of_nonneg_left heL hε.le).trans hsmall

/-- These tolerances can be selected pointwise before an affine family is
constructed. No continuity in the slope, nor positive infimum, is claimed. -/
theorem exists_fixed_slope_tolerantCertificate {d : ℕ} {E : Type*}
    [Fintype E] (N : Network d E) (hN : N.IsEndotactic) (r : State d)
    (hnonzero : ∃ e : E, N.projection r e ≠ 0) :
    ∃ ε H B : ℝ, 0 < ε ∧ 0 < H ∧ 0 ≤ B ∧
      ∀ p : State d, (∀ i, |p i - r i| ≤ ε) →
        Nonempty (N.DirectionalCertificate r p H B) := by
  obtain ⟨H, B, hH, hB, ⟨C⟩⟩ := exists_fixed_directionalCertificate N hN r hnonzero
  obtain ⟨ε, hε, hC⟩ := exists_directional_exponent_tolerance C hH
  exact ⟨ε, H / 2, B, hε, by positivity, hB, hC⟩

/-- Fixed finite slopes, moving exponent points, and all coefficients share
one threshold once every relevant point stays within its slope's tolerance. -/
theorem finite_slopes_tolerant_eventual_flux {d : ℕ} {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I] [Nonempty I]
    (N : Network d E) (hN : N.IsEndotactic) (r : I → State d)
    (hnonzero : ∀ i, ∃ e : E, N.projection (r i) e ≠ 0)
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ ε : I → ℝ, (∀ i, 0 < ε i) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ i : I, ∀ p : State d, (∀ j, |p j - r i j| ≤ ε i) →
          ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
            0 < dot (r i) (N.rhs k (exponentialPoint h p)) := by
  classical
  choose ε H B hε hH hB hC using
    fun i => exists_fixed_slope_tolerantCertificate N hN (r i) (hnonzero i)
  let Q : Set (State d × State d) :=
    {q | ∃ i : I, q.1 = r i ∧ ∀ j, |q.2 j - r i j| ≤ ε i}
  have hcover : ∀ q ∈ Q, ∃ i, Nonempty (N.DirectionalCertificate q.1 q.2 (H i) (B i)) := by
    rintro q ⟨i, hi, hp⟩
    exact ⟨i, hi.symm ▸ hC i q.2 hp⟩
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ :=
    finite_directional_cover_eventual_flux N Q H B hH hℓ hu hcover
  refine ⟨ε, hε, h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall i p hp k hk
  exact hflux h hh hsmall (r i, p) ⟨i, rfl, hp⟩ k hk

end Endotactic
