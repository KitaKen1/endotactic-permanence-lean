import Endotactic.ActivityLimitNeighborhood
import Endotactic.ActivityFluxBridge
import Endotactic.FiniteMinimum
import Mathlib.Topology.Order.Lattice

/-!
# Continuous minimum exponent and the nearby-minimum activity theorem

The cube includes its boundary. In a positive dimension, the minimum of its
coordinates is continuous and the top minimum stratum is a singleton.
-/

namespace Endotactic

noncomputable def exponentMinimum {d : ℕ} [NeZero d] (p : State d) : ℝ :=
  finiteMinimum p

theorem exponentMinimum_le_coordinate {d : ℕ} [NeZero d] (p : State d) (i : Fin d) :
    exponentMinimum p ≤ p i := finiteMinimum_le p i

theorem exponentMinimum_attained {d : ℕ} [NeZero d] (p : State d) :
    ∃ i : Fin d, exponentMinimum p = p i := finiteMinimum_attained p

theorem continuous_exponentMinimum {d : ℕ} [NeZero d] :
    Continuous (exponentMinimum : State d → ℝ) := by
  apply Continuous.finset_inf'_apply Finset.univ_nonempty
  intro i _
  exact continuous_apply i

theorem exponentMinimum_mem_interval {d : ℕ} [NeZero d] {a b : ℝ} {p : State d}
    (hp : p ∈ Set.Icc (fun _ => a) (fun _ => b)) :
    exponentMinimum p ∈ Set.Icc a b := by
  obtain ⟨i, hi⟩ := exponentMinimum_attained p
  rw [hi]
  exact ⟨hp.1 i, hp.2 i⟩

theorem exponentMinimum_eq_top_iff {d : ℕ} [NeZero d] {b : ℝ} {p : State d}
    (hp : p ≤ fun _ => b) : exponentMinimum p = b ↔ p = fun _ => b := by
  constructor
  · intro heq
    funext i
    apply le_antisymm (hp i)
    rw [← heq]
    exact exponentMinimum_le_coordinate p i
  · rintro rfl
    obtain ⟨i, hi⟩ := exponentMinimum_attained (fun _ : Fin d => b)
    exact hi

/-- This is the original fixed-minimum-to-neighborhood step with the closed
cube and a common scale threshold. Its fixed-stratum guarantee is an explicit
input; constructing those families and combining them remains separate. -/
theorem ScaledAffineFamily.uniformActivityBound_near_minimum {d m : ℕ} [NeZero d]
    (A : ScaledAffineFamily d m) (a b : ℝ) (ε : Fin m → ℝ) (t : ℝ)
    (hfixed : A.HasSequentialActivityBound
      (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = t}) ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => a) (fun _ => b), |exponentMinimum q - t| ≤ ρ →
          ∀ i : Fin m, (A.atScale h).Active i (exponentialPoint h q) →
            ‖q - A.slope i‖ < ε i :=
  A.uniformActivityBound_near_level _ isCompact_Icc ε exponentMinimum
    continuous_exponentMinimum t hfixed

/-- Pass the extended fixed-minimum family directly to the checked flux API.
The tolerance must already be the one certifying this network's fixed slopes. -/
theorem Network.uniform_active_flux_near_minimum {d m : ℕ} [NeZero d] {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (A : ScaledAffineFamily d m)
    (a b : ℝ) (ε : State d → ℝ) (hε : N.IsSlopeTolerance ε) (t : ℝ)
    (hfixed : A.HasSequentialActivityBound
      (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = t})
      (fun i => ε (A.slope i))) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => a) (fun _ => b), |exponentMinimum q - t| ≤ ρ →
          ∀ i : Fin m, (A.atScale h).Active i (exponentialPoint h q) →
            (∃ e, N.projection (A.slope i) e ≠ 0) →
            ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
              0 < dot (A.slope i) (N.rhs k (exponentialPoint h q)) := by
  obtain ⟨ρ, hρ, hseq⟩ := A.sequentialActivityBound_near_level _ isCompact_Icc
    (fun i => ε (A.slope i)) exponentMinimum continuous_exponentMinimum t hfixed
  have hband : IsCompact (Set.Icc (fun _ : Fin d => a) (fun _ => b) ∩
      {q | |exponentMinimum q - t| ≤ ρ}) :=
    isCompact_Icc.inter_right (isClosed_le
      ((continuous_exponentMinimum.sub continuous_const).abs) continuous_const)
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ :=
    N.uniform_active_flux_of_sequentialActivityBound A _ hband ε hε hseq hℓ hu
  exact ⟨ρ, hρ, h₀, hh₀, hh₀1, fun h hh hsmall q hq hnear =>
    hflux h hh hsmall q ⟨hq, hnear⟩⟩

/-- On a nonempty original class carrier, conservation eliminates every
exterior zero-projection active label after nearby-minimum extension. -/
theorem Network.uniform_exterior_active_flux_near_minimum
    {d m : ℕ} [NeZero d] {E : Type*} [Fintype E] [DecidableEq E]
    (N : Network d E) (A : ScaledAffineFamily d m) (a b : ℝ)
    (ε : State d → ℝ) (hε : N.IsSlopeTolerance ε) (t : ℝ)
    (hfixed : A.HasSequentialActivityBound
      (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = t})
      (fun i => ε (A.slope i))) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => a) (fun _ => b), |exponentMinimum q - t| ≤ ρ →
          ∀ c : State d, ∀ M : ℝ,
            exponentialPoint h q ∈ N.positiveClass c →
            exponentialPoint h q ∉ (A.atScale h).plateau M →
            ((A.atScale h).plateau M ∩ N.stoichiometricClass c).Nonempty →
            ∀ i : Fin m, (A.atScale h).Active i (exponentialPoint h q) →
              ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
                0 < dot (A.slope i) (N.rhs k (exponentialPoint h q)) := by
  obtain ⟨ρ, hρ, h₀, hh₀, hh₀1, hflux⟩ :=
    N.uniform_active_flux_near_minimum A a b ε hε t hfixed hℓ hu
  refine ⟨ρ, hρ, h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall q hq hnear c M hx hout hne i hi k hk
  exact hflux h hh hsmall q hq hnear i hi
    (active_direction_has_nonzero_projection_of_carrier_nonempty N (A.atScale h)
      hx hi hout hne) k hk

end Endotactic
