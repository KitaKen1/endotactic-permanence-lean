import Endotactic.Network
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Precise permanence statements

Solutions are continuous integral solutions on nonnegative time. Interval
integrability is explicit, so Lean's default value for a nonintegrable integral
cannot accidentally satisfy the solution predicate.

The absorbing compact set is chosen BEFORE the rate path and initial state.
The entry time is chosen AFTER them. We do not require one common entry time
over the entire, possibly unbounded positive stoichiometric class.
-/

namespace Endotactic

open MeasureTheory Set

variable {d : ℕ} {E : Type*} [Fintype E]

def AdmissibleRates (k : E → ℝ → ℝ) (ℓ u : ℝ) : Prop :=
  (∀ e, Measurable (k e)) ∧ ∀ e t, 0 ≤ t → ℓ ≤ k e t ∧ k e t ≤ u

/-- A concrete locally finite piecewise differentiability condition. -/
def LocallyPiecewiseDifferentiableRates (k : E → ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ cuts : Finset ℝ,
    ∀ e t, t ∈ Ioo 0 T → t ∉ cuts → DifferentiableAt ℝ (k e) t

def Network.IsIntegralSolution (N : Network d E) (k : E → ℝ → ℝ)
    (x₀ : State d) (x : ℝ → State d) : Prop :=
  ContinuousOn x (Ici 0) ∧ x 0 = x₀ ∧
    (∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun t => N.rhs (fun e => k e t) (x t))
      volume 0 T) ∧
    ∀ t : ℝ, 0 ≤ t →
      x t = x₀ + ∫ s in (0 : ℝ)..t, N.rhs (fun e => k e s) (x s)

def Network.IsGlobalPositiveSolution (N : Network d E) (k : E → ℝ → ℝ)
    (x₀ : State d) (x : ℝ → State d) : Prop :=
  N.IsIntegralSolution k x₀ x ∧ ∀ t : ℝ, 0 ≤ t → Positive (x t)

def Network.PositiveWellPosed (N : Network d E) (k : E → ℝ → ℝ)
    (x₀ : State d) : Prop :=
  ∃ x : ℝ → State d, N.IsGlobalPositiveSolution k x₀ x ∧
    ∀ y : ℝ → State d, N.IsGlobalPositiveSolution k x₀ y →
      ∀ t : ℝ, 0 ≤ t → y t = x t

def EventuallyIn {α : Type*} (x : ℝ → α) (K : Set α) : Prop :=
  ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → x t ∈ K

/-- Common compact absorption for a specified class and a specified rate box.
`regular` allows the original piecewise differentiable formulation and its
measurable-coefficient strengthening to share exactly the same quantifiers. -/
def Network.UniformPermanent (N : Network d E) (ℓ u : ℝ) (c : State d)
    (regular : (E → ℝ → ℝ) → Prop) : Prop :=
  ∃ K : Set (State d), K.Nonempty ∧ IsCompact K ∧ K ⊆ N.positiveClass c ∧
    ∀ k : E → ℝ → ℝ, AdmissibleRates k ℓ u → regular k →
      (∀ x₀ ∈ N.positiveClass c, N.PositiveWellPosed k x₀) ∧
      ∀ x₀ ∈ N.positiveClass c, ∀ x : ℝ → State d,
        N.IsGlobalPositiveSolution k x₀ x → EventuallyIn x K

/-- Permanence for one fixed coefficient path. The compact set is common to
initial points in the class, but may depend on this path, as in CNP Definitions
2.9--2.10. Global positive well-posedness is made explicit here. -/
def Network.PermanentForRates (N : Network d E) (k : E → ℝ → ℝ) (c : State d) : Prop :=
  ∃ K : Set (State d), K.Nonempty ∧ IsCompact K ∧ K ⊆ N.positiveClass c ∧
    (∀ x₀ ∈ N.positiveClass c, N.PositiveWellPosed k x₀) ∧
    ∀ x₀ ∈ N.positiveClass c, ∀ x : ℝ → State d,
      N.IsGlobalPositiveSolution k x₀ x → EventuallyIn x K

/-- The natural-exponent CNP formulation, with the rate path fixed before K.
The rate predicate spells out the chosen locally finite interpretation of
piecewise differentiability; the broader real-exponent formulation is separate. -/
def OriginalExtendedPermanenceConjecture : Prop :=
  ∀ (d m : ℕ), 0 < d → ∀ N : Network d (Fin m),
    N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
      ∀ k : Fin m → ℝ → ℝ, AdmissibleRates k ℓ u →
        LocallyPiecewiseDifferentiableRates k →
          ∀ c : State d, Positive c → N.PermanentForRates k c

/-- A stronger, common-rate-box version of the CNP conjecture. -/
def ExtendedPermanenceConjecture : Prop :=
  ∀ (d m : ℕ), 0 < d → ∀ N : Network d (Fin m),
    N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
      ∀ c : State d, Positive c →
        N.UniformPermanent ℓ u c LocallyPiecewiseDifferentiableRates

/-- This strengthens the regularity assumption in the original CNP formulation.
It is not labelled as an established theorem. -/
def MeasurableExtendedPermanenceConjecture : Prop :=
  ∀ (d m : ℕ), 0 < d → ∀ N : Network d (Fin m),
    N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
      ∀ c : State d, Positive c → N.UniformPermanent ℓ u c (fun _ => True)

theorem UniformPermanent.mono_regularity (N : Network d E) {ℓ u : ℝ} {c : State d}
    {regular₁ regular₂ : (E → ℝ → ℝ) → Prop}
    (h : N.UniformPermanent ℓ u c regular₁)
    (hreg : ∀ k, regular₂ k → regular₁ k) : N.UniformPermanent ℓ u c regular₂ := by
  obtain ⟨K, hKne, hKcompact, hKclass, hK⟩ := h
  exact ⟨K, hKne, hKcompact, hKclass, fun k hk hr => hK k hk (hreg k hr)⟩

theorem measurable_conjecture_implies_extended
    (h : MeasurableExtendedPermanenceConjecture) : ExtendedPermanenceConjecture := by
  intro d m hd N hN ℓ u hℓ hlu c hc
  exact UniformPermanent.mono_regularity N (h d m hd N hN ℓ u hℓ hlu c hc)
    (fun _ _ => trivial)

theorem UniformPermanent.implies_permanentForRates (N : Network d E)
    {ℓ u : ℝ} {c : State d} {regular : (E → ℝ → ℝ) → Prop}
    (h : N.UniformPermanent ℓ u c regular) {k : E → ℝ → ℝ}
    (hk : AdmissibleRates k ℓ u) (hr : regular k) : N.PermanentForRates k c := by
  obtain ⟨K, hKne, hKcompact, hKclass, hK⟩ := h
  exact ⟨K, hKne, hKcompact, hKclass, hK k hk hr⟩

theorem uniform_extended_conjecture_implies_original
    (h : ExtendedPermanenceConjecture) : OriginalExtendedPermanenceConjecture := by
  intro d m hd N hN ℓ u hℓ hlu k hk hr c hc
  exact UniformPermanent.implies_permanentForRates N (h d m hd N hN ℓ u hℓ hlu c hc) hk hr

end Endotactic
