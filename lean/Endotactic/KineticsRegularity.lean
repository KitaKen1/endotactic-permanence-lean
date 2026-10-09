import Endotactic.Network
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Elementary regularity of mass-action kinetics

The finite polynomial formula directly gives state smoothness and measurable
composition, without importing a general Nemytskii theorem. These conditions do
not by themselves provide a nonlinear time-dependent existence theorem.
-/

namespace Endotactic

open scoped ContDiff

variable {d : ℕ} {E : Type*} [Fintype E]

theorem Network.rhs_contDiff (N : Network d E) (k : E → ℝ) :
    ContDiff ℝ ∞ (N.rhs k) := by
  unfold Network.rhs monomial
  fun_prop

theorem Network.rhs_locallyLipschitzOn (N : Network d E) (k : E → ℝ) :
    LocallyLipschitzOn Set.univ (N.rhs k) := by
  exact ContDiffOn.locallyLipschitzOn convex_univ
    ((N.rhs_contDiff k).of_le (by norm_num)).contDiffOn

theorem Network.rhs_measurable (N : Network d E) (k : E → ℝ → ℝ)
    (x : ℝ → State d) (hk : ∀ e, Measurable (k e)) (hx : Measurable x) :
    Measurable (fun t => N.rhs (fun e => k e t) (x t)) := by
  unfold Network.rhs monomial
  fun_prop

end Endotactic
