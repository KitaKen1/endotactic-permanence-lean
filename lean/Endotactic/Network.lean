import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

/-!
# Finite reaction networks and endotacticity

Natural exponents are used for ordinary mass-action kinetics. Reaction vectors
are formed AFTER casting both complexes to real vectors; natural subtraction
would incorrectly erase negative coordinates.

The direction convention is: a negative projected reaction must have a positive
projected reaction with a strictly lower source. Sources of zero projected
reactions do not enter the essential-source minimum.
-/

namespace Endotactic

abbrev State (d : ℕ) := Fin d → ℝ
abbrev Complex (d : ℕ) := Fin d → ℕ

def realComplex {d : ℕ} (a : Complex d) : State d := fun i => a i

def dot {d : ℕ} (r x : State d) : ℝ := ∑ i, r i * x i

structure Network (d : ℕ) (E : Type*) where
  source : E → Complex d
  target : E → Complex d

def Network.vector {d : ℕ} {E : Type*} (N : Network d E) (e : E) : State d :=
  realComplex (N.target e) - realComplex (N.source e)

def Network.projection {d : ℕ} {E : Type*} (N : Network d E)
    (r : State d) (e : E) : ℝ := dot r (N.vector e)

def Network.sourceLevel {d : ℕ} {E : Type*} (N : Network d E)
    (r : State d) (e : E) : ℝ := dot r (realComplex (N.source e))

def Network.IsEndotactic {d : ℕ} {E : Type*} (N : Network d E) : Prop :=
  ∀ (r : State d) (e : E), N.projection r e < 0 →
    ∃ f : E, 0 < N.projection r f ∧ N.sourceLevel r f < N.sourceLevel r e

def Network.stoichiometricSubspace {d : ℕ} {E : Type*} (N : Network d E) :
    Submodule ℝ (State d) := Submodule.span ℝ (Set.range N.vector)

def Positive {d : ℕ} (x : State d) : Prop := ∀ i, 0 < x i

def Network.positiveClass {d : ℕ} {E : Type*} (N : Network d E)
    (c : State d) : Set (State d) :=
  {x | Positive x ∧ x - c ∈ N.stoichiometricSubspace}

def monomial {d : ℕ} (x : State d) (a : Complex d) : ℝ := ∏ i, x i ^ a i

def Network.rhs {d : ℕ} {E : Type*} [Fintype E] (N : Network d E)
    (k : E → ℝ) (x : State d) : State d :=
  ∑ e, (k e * monomial x (N.source e)) • N.vector e

theorem dot_sub {d : ℕ} (r x y : State d) : dot r (x - y) = dot r x - dot r y := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

theorem monomial_pos {d : ℕ} {x : State d} (hx : Positive x) (a : Complex d) :
    0 < monomial x a := by
  exact Finset.prod_pos fun i _ => pow_pos (hx i) _

theorem rhs_mem_stoichiometricSubspace {d : ℕ} {E : Type*} [Fintype E]
    (N : Network d E) (k : E → ℝ) (x : State d) :
    N.rhs k x ∈ N.stoichiometricSubspace := by
  apply Submodule.sum_mem
  intro e _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)

end Endotactic
