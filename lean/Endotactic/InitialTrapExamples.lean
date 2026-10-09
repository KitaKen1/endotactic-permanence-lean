import Endotactic.EndotacticInitialTrap
import Endotactic.DirectionalWallCounterexample
import Endotactic.ConversionPermanence

/-!
# General initial traps on nonlinear and conserved examples

The nonlinear network has no uniform fixed-ray flux threshold, yet the
zero-cap construction gives a rate-uniform positive compact initial trap.
The conservative conversion also instantiates the ambient compact route
without a full-dimensional stoichiometric-class assumption.
-/

namespace Endotactic.InitialTrapExamples

theorem nonlinear_uniform_initial_trap {z : State 2} (hz : Positive z) :
    ∃ K : Set (State 2), z ∈ K ∧ IsCompact K ∧ K ⊆ {x | Positive x} ∧
      ∀ k : Fin 4 → ℝ → ℝ, AdmissibleRates k 1 3 →
        DirectionalWall.network.PositiveWellPosed k z ∧ ∀ x : ℝ → State 2,
          DirectionalWall.network.IsGlobalPositiveSolution k z x →
            ∀ t : ℝ, 0 ≤ t → x t ∈ K :=
  DirectionalWall.network.exists_uniform_compact_initial_trap
    DirectionalWall.network_endotactic (by norm_num) (by norm_num) (by norm_num) hz

theorem nonlinear_constant_rates_wellPosed {z : State 2} (hz : Positive z) :
    DirectionalWall.network.PositiveWellPosed (fun e _ => DirectionalWall.rates e) z := by
  apply DirectionalWall.network.positiveWellPosed_of_endotactic
    DirectionalWall.network_endotactic (by norm_num) (ℓ := 1) (u := 3)
    (by norm_num) (by norm_num) _ hz
  exact ⟨fun _ => measurable_const, fun e _ _ => DirectionalWall.rates_mem_box e⟩

theorem conserved_uniform_positive_box {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : ℓ ≤ u)
    {z : State 2} (hz : Positive z) :
    ∃ lo hi : State 2, lo ≤ hi ∧ Positive lo ∧
      ∀ k : Fin 2 → ℝ → ℝ, AdmissibleRates k ℓ u →
        Conversion.conversion.PositiveWellPosed k z ∧ ∀ x : ℝ → State 2,
          Conversion.conversion.IsGlobalPositiveSolution k z x →
            ∀ t : ℝ, 0 ≤ t → x t ∈ Set.Icc lo hi :=
  Conversion.conversion.exists_uniform_positive_trajectory_box Conversion.isEndotactic
    (by norm_num) hℓ ((hℓ.trans_le hu).le) hz

end Endotactic.InitialTrapExamples
