import Endotactic.IntegralTrajectory
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Stoichiometric-class conservation for integral solutions

Apply the quotient map by the reaction subspace to the integral equation.
The projected right-hand side is identically zero. This avoids having to assume
integrability of each individual reaction summand.
-/

namespace Endotactic

open MeasureTheory Set

theorem intervalIntegral_mem_subspace {d : ℕ} (S : Submodule ℝ (State d))
    {f : ℝ → State d} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (hmem : ∀ t ∈ uIcc a b, f t ∈ S) :
    (∫ t in a..b, f t) ∈ S := by
  let : IsClosed (S : Set (State d)) := S.closed_of_finiteDimensional
  apply (Submodule.Quotient.mk_eq_zero S).mp
  change S.mkQL (∫ t in a..b, f t) = 0
  rw [← S.mkQL.intervalIntegral_comp_comm hf]
  have heq : EqOn (fun t => S.mkQL (f t)) (fun _ => 0) (uIcc a b) := by
    intro t ht
    exact (Submodule.Quotient.mk_eq_zero S).mpr (hmem t ht)
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]

variable {d : ℕ} {E : Type*} [Fintype E]
variable {N : Network d E} {k : E → ℝ → ℝ} {x₀ : State d} {x : ℝ → State d}

theorem Network.IsIntegralSolution.sub_initial_mem
    (hx : N.IsIntegralSolution k x₀ x) {t : ℝ} (ht : 0 ≤ t) :
    x t - x₀ ∈ N.stoichiometricSubspace := by
  rw [hx.2.2.2 t ht, add_sub_cancel_left]
  exact intervalIntegral_mem_subspace N.stoichiometricSubspace (hx.2.2.1 t ht)
    (fun s _ => rhs_mem_stoichiometricSubspace N (fun e => k e s) (x s))

theorem Network.IsGlobalPositiveSolution.mem_positiveClass
    (hx : N.IsGlobalPositiveSolution k x₀ x) {c : State d}
    (h₀ : x₀ ∈ N.positiveClass c) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ N.positiveClass c := by
  refine ⟨hx.2 t ht, ?_⟩
  have hh := N.stoichiometricSubspace.add_mem (hx.1.sub_initial_mem ht) h₀.2
  simpa only [sub_add_sub_cancel] using hh

/-- A conditional assembly theorem. The plateau is chosen before rates and
initial points; the positive growth margin may depend on the trajectory.
Constructing this geometry and proving positive well-posedness remain open. -/
theorem Network.uniformPermanent_of_affine_plateau {m : ℕ} [Nonempty (Fin m)]
    (N : Network d E) (A : AffineFamily d m) (ℓ u M : ℝ) (c : State d)
    (regular : (E → ℝ → ℝ) → Prop)
    (hKne : (A.plateau M ∩ N.positiveClass c).Nonempty)
    (hKcompact : IsCompact (A.plateau M ∩ N.positiveClass c))
    (hcap : ∀ z ∈ N.positiveClass c, A.minimum z ≤ M)
    (hwell : ∀ k, AdmissibleRates k ℓ u → regular k →
      ∀ x₀ ∈ N.positiveClass c, N.PositiveWellPosed k x₀)
    (hflux : ∀ k, AdmissibleRates k ℓ u → regular k →
      ∀ x₀ ∈ N.positiveClass c, ∀ x, N.IsGlobalPositiveSolution k x₀ x →
        ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 ≤ t → A.minimum (x t) < M → ∀ i,
          A.Active i (x t) → δ ≤ dot (A.slope i) (N.rhs (fun e => k e t) (x t))) :
    N.UniformPermanent ℓ u c regular := by
  refine ⟨A.plateau M ∩ N.positiveClass c, hKne, hKcompact,
    fun _ hz => hz.2, ?_⟩
  intro k hk hr
  refine ⟨hwell k hk hr, ?_⟩
  intro x₀ h₀ x hx
  obtain ⟨δ, hδ, hb⟩ := hflux k hk hr x₀ h₀ x hx
  obtain ⟨T, hT, hstay⟩ := A.eventuallyIn_plateau hx.1 hδ
    (fun t ht => hcap (x t) (hx.mem_positiveClass h₀ ht)) hb
  exact ⟨T, hT, fun t ht => ⟨hstay t ht, hx.mem_positiveClass h₀ (hT.trans ht)⟩⟩

end Endotactic
