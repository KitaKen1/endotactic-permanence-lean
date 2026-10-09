import EndotacticPublication.Statement
import Endotactic.GeneralPermanence

/-!
# Compact-set permanence targets

These targets use the proof-library compact-set definitions.
CoordinateBounds proves equivalence with positive coordinate bounds;
FCPresentation proves the independently written FC targets.
The answer is outside every quantifier. Global positive existence and
uniqueness are included in the permanence definitions.
-/

namespace EndotacticPublication

/-- The natural-exponent Extended Permanence Conjecture of [CNP11, Section 4],
with the explicit locally finite piecewise differentiability convention.
For each admissible rate path and positive stoichiometric class, is there a
compact positive set absorbing every positive trajectory in that class?
The answer for the displayed model is positive. The rate path precedes the
compact set; the entry time may depend on the trajectory. -/
theorem extended_permanence :
    answer(True) ↔
      ∀ (d m : ℕ), 0 < d → ∀ N : Endotactic.Network d (Fin m),
        N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
          ∀ k : Fin m → ℝ → ℝ, Endotactic.AdmissibleRates k ℓ u →
            Endotactic.LocallyPiecewiseDifferentiableRates k →
              ∀ c : Endotactic.State d, Endotactic.Positive c →
                N.PermanentForRates k c := by
  exact ⟨fun _ => Endotactic.original_extended_permanence, fun _ => True.intro⟩

/-- A measurable-rate, common-coefficient-box strengthening of [CNP11].
For each finite endotactic network, positive coefficient box and positive
class, is there one compact positive set absorbing all positive trajectories
for every bounded measurable rate path in that box? The answer is positive.
The compact set precedes both the rate path and the initial state. -/
theorem measurable_extended_permanence :
    answer(True) ↔
      ∀ (d m : ℕ), 0 < d → ∀ N : Endotactic.Network d (Fin m),
        N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
          ∀ c : Endotactic.State d, Endotactic.Positive c →
            N.UniformPermanent ℓ u c (fun _ => True) := by
  exact ⟨fun _ => Endotactic.measurable_extended_permanence, fun _ => True.intro⟩

/-- The common-rate-box statement restricted to the displayed piecewise rates. -/
theorem uniform_piecewise_extended_permanence :
    Endotactic.ExtendedPermanenceConjecture :=
  Endotactic.extended_permanence

#print axioms extended_permanence
#print axioms measurable_extended_permanence
#print axioms uniform_piecewise_extended_permanence

end EndotacticPublication
