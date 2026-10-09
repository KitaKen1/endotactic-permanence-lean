import Endotactic.MinimumBandSelection

/-!
# Unconditional affine approximation and endotactic active-flux families

The exact affine theorem is now proved, so no affine-existence oracle is an
input to these APIs. Compact positive class carriers and exterior geometry
are still separate requirements of the eventual permanence theorem.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem exists_uniform_affine_approximation {d : ℕ} (hd : 0 < d)
    {a b : ℝ} (hab : a < b) (E : State d → ℝ)
    (hE : ∀ r ∈ Set.Icc (fun _ => a) (fun _ => b), 0 < E r) :
    ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily d m,
      (∀ i, A.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) ∧
      A.HasSequentialActivityBound (Set.Icc (fun _ => a) (fun _ => b))
        (fun i => E (A.slope i)) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ p ∈ Set.Icc (fun _ => a) (fun _ => b), ∀ i,
          (A.atScale h).Active i (exponentialPoint h p) → ‖p - A.slope i‖ < E (A.slope i) := by
  obtain ⟨m, hm, A, hcube, hdecay, hseq⟩ := finiteAffineApproximation d hd a b hab E hE
  exact ⟨m, hm, A, hcube, hdecay, hseq,
    A.uniformActivityBound_of_sequential _ isCompact_Icc _ hseq⟩

theorem Network.exists_uniform_active_flux_family {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (hd : 0 < d) {a b ℓ u : ℝ} (hab : a < b) (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily d m,
      (∀ i, A.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ p ∈ Set.Icc (fun _ => a) (fun _ => b), ∀ i,
          (A.atScale h).Active i (exponentialPoint h p) →
          (∃ e, N.projection (A.slope i) e ≠ 0) →
          ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
            0 < dot (A.slope i) (N.rhs k (exponentialPoint h p)) :=
  N.uniform_active_flux_of_affineApproximation hN finiteAffineApproximation hd hab hℓ hu

theorem Network.exists_uniform_exterior_active_flux_family {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (hd : 0 < d) {a b ℓ u : ℝ} (hab : a < b) (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily d m,
      (∀ i, A.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ p ∈ Set.Icc (fun _ => a) (fun _ => b), ∀ c : State d, ∀ M : ℝ,
          exponentialPoint h p ∈ N.positiveClass c →
          exponentialPoint h p ∉ (A.atScale h).plateau M →
          ((A.atScale h).plateau M ∩ N.stoichiometricClass c).Nonempty →
          ∀ i, (A.atScale h).Active i (exponentialPoint h p) →
            ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
              0 < dot (A.slope i) (N.rhs k (exponentialPoint h p)) := by
  obtain ⟨ε, hε⟩ := N.exists_slopeTolerance hN
  obtain ⟨m, hm, A, hcube, hdecay, hseq⟩ := finiteAffineApproximation d hd a b hab ε
    (fun r _ => (hε r).1)
  exact ⟨m, hm, A, hcube, hdecay,
    N.uniform_exterior_active_flux_of_sequentialActivityBound A _ isCompact_Icc ε hε hseq hℓ hu⟩

end Endotactic
