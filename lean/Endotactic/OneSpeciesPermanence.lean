import Endotactic.ScalarTrapPermanence
import Endotactic.DegeneratePermanence

/-!
# Complete permanence for arbitrary one-species endotactic networks

Any finite reaction set and any natural source/target degrees are allowed.
Rates are measurable and range in an arbitrary box `0 < ℓ ≤ u`. There is one
compact positive absorbing set for the whole box, before selecting rates or
initial states. Global positive existence and uniqueness are part of the result.

The zero-vector case uses a singleton class; the nonzero case uses the two
exponent rays and scalar trapping. This proves the one-species specialization
of the measurable strengthening. The arbitrary-dimensional conjecture remains
unproved.
-/

namespace Endotactic

variable {E : Type*} [Fintype E]

theorem Network.oneSpecies_uniformPermanent (N : Network 1 E) (hN : N.IsEndotactic)
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hlu : ℓ ≤ u) {c : State 1} (hc : Positive c)
    (regular : (E → ℝ → ℝ) → Prop) : N.UniformPermanent ℓ u c regular := by
  classical
  by_cases hzero : ∀ e, N.vector e 0 = 0
  · have hzero' : ∀ e, N.vector e = 0 := by
      intro e
      ext i
      fin_cases i
      exact hzero e
    exact N.uniformPermanent_of_vectors_zero hzero' ℓ u hc regular
  · have hnonzero : ∃ e, N.vector e 0 ≠ 0 := by simpa only [not_forall] using hzero
    obtain ⟨T⟩ := N.exists_scalarTrap_of_oneSpecies_endotactic hN hnonzero hℓ hlu
    exact T.uniformPermanent hnonzero c regular

theorem Network.oneSpecies_positiveWellPosed (N : Network 1 E) (hN : N.IsEndotactic)
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hlu : ℓ ≤ u) {k : E → ℝ → ℝ}
    (hk : AdmissibleRates k ℓ u) {z : State 1} (hz : Positive z) :
    N.PositiveWellPosed k z := by
  obtain ⟨_, _, _, _, hK⟩ := N.oneSpecies_uniformPermanent hN hℓ hlu hz (fun _ => True)
  exact (hK k hk trivial).1 z ⟨hz, by rw [sub_self]; exact Submodule.zero_mem _⟩

theorem Network.oneSpecies_permanentForRates (N : Network 1 E) (hN : N.IsEndotactic)
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hlu : ℓ ≤ u) {k : E → ℝ → ℝ}
    (hk : AdmissibleRates k ℓ u) {c : State 1} (hc : Positive c) :
    N.PermanentForRates k c :=
  UniformPermanent.implies_permanentForRates N
    (N.oneSpecies_uniformPermanent hN hℓ hlu hc (fun _ => True)) hk trivial

/-- The `d = 1` part of `MeasurableExtendedPermanenceConjecture`, with the
same rate/compact-set quantifiers and the same solution predicate. -/
theorem oneSpecies_measurable_permanence :
    ∀ (m : ℕ) (N : Network 1 (Fin m)), N.IsEndotactic →
      ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u → ∀ c : State 1, Positive c →
        N.UniformPermanent ℓ u c (fun _ => True) := by
  intro m N hN ℓ u hℓ hlu c hc
  exact N.oneSpecies_uniformPermanent hN hℓ hlu hc (fun _ => True)

end Endotactic
