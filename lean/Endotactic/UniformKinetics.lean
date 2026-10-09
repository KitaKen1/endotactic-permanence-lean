import Endotactic.KineticsRegularity

/-!
# Lipschitz constants uniform over compact coefficient sets

Treating coefficients and state as one polynomial map provides a common state
Lipschitz constant on any compact convex product. This is the uniform local
estimate needed by the time-dependent Volterra construction; existence of its
fixed point is a separate obligation.
-/

namespace Endotactic

open Set
open scoped ContDiff NNReal

variable {d : ℕ} {E : Type*} [Fintype E]

theorem Network.rhs_joint_contDiff (N : Network d E) :
    ContDiff ℝ ∞ (fun p : (E → ℝ) × State d => N.rhs p.1 p.2) := by
  unfold Network.rhs monomial
  fun_prop

theorem Network.rhs_uniform_lipschitzOn (N : Network d E)
    {K : Set (E → ℝ)} {B : Set (State d)}
    (hK : IsCompact K) (hB : IsCompact B) (hKconv : Convex ℝ K) (hBconv : Convex ℝ B) :
    ∃ L : ℝ≥0, ∀ k ∈ K, LipschitzOnWith L (N.rhs k) B := by
  obtain ⟨L, hL⟩ := (N.rhs_joint_contDiff.contDiffOn).exists_lipschitzOnWith
    (by simp) (hKconv.prod hBconv) (hK.prod hB)
  refine ⟨L, fun k hk => lipschitzOnWith_iff_dist_le_mul.mpr ?_⟩
  intro x hx y hy
  have hh := hL.dist_le_mul (k, x) (show (k, x) ∈ K ×ˢ B from ⟨hk, hx⟩)
    (k, y) (show (k, y) ∈ K ×ˢ B from ⟨hk, hy⟩)
  simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hh

theorem Network.rhs_uniform_lipschitzOn_box (N : Network d E)
    (klo khi : E → ℝ) (xlo xhi : State d) :
    ∃ L : ℝ≥0, ∀ k ∈ Icc klo khi,
      LipschitzOnWith L (N.rhs k) (Icc xlo xhi) :=
  N.rhs_uniform_lipschitzOn isCompact_Icc isCompact_Icc
    (convex_Icc _ _) (convex_Icc _ _)

end Endotactic
