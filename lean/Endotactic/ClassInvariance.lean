import Endotactic.Stoichiometry
import Endotactic.PolyhedralInvariance
import Endotactic.RelativeAffineRobustness

/-!
# Stoichiometric classes are preserved even before removing the cutoff

Clamping the state need not preserve its class, but the mass-action velocity
always belongs to the reaction span. Applying the quotient map to the cutoff
integral equation therefore preserves the affine class. No state projection,
orthogonal norm, or individual reaction-term integrability is needed.
-/

namespace Endotactic

open Set MeasureTheory

variable {d : ℕ} {E : Type*}

def Network.stoichiometricClass (N : Network d E) (c : State d) : Set (State d) :=
  {y | y - c ∈ N.stoichiometricSubspace}

theorem Network.stoichiometricClass_isClosed (N : Network d E) (c : State d) :
    IsClosed (N.stoichiometricClass c) :=
  N.stoichiometricSubspace.closed_of_finiteDimensional.preimage
    (continuous_id.sub continuous_const)

theorem Network.stoichiometricClass_convex (N : Network d E) (c : State d) :
    Convex ℝ (N.stoichiometricClass c) := by
  intro x hx y hy a b _ _ hab
  change (a • x + b • y) - c ∈ N.stoichiometricSubspace
  have heq : (a • x + b • y) - c = a • (x - c) + b • (y - c) := by
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun z : ℝ => z * c i) hab]
  rw [heq]
  exact N.stoichiometricSubspace.add_mem
    (N.stoichiometricSubspace.smul_mem a hx) (N.stoichiometricSubspace.smul_mem b hy)

theorem Network.positiveClass_eq (N : Network d E) (c : State d) :
    N.positiveClass c = {x | Positive x} ∩ N.stoichiometricClass c := rfl

variable [Fintype E]

theorem Network.cutoffRhs_mem_stoichiometricSubspace (N : Network d E)
    (k : E → ℝ → ℝ) (lo hi : State d) (t : ℝ) (y : State d) :
    N.cutoffRhs k lo hi t y ∈ N.stoichiometricSubspace :=
  rhs_mem_stoichiometricSubspace N _ _

theorem GlobalIntegralSolution.sub_initial_mem {F : ℝ → State d → State d}
    {z : State d} {x : ℝ → State d} (hx : GlobalIntegralSolution F z x)
    (S : Submodule ℝ (State d)) (hF : ∀ t, 0 ≤ t → ∀ y, F t y ∈ S)
    {t : ℝ} (ht : 0 ≤ t) : x t - z ∈ S := by
  rw [hx.2.2.2 t ht, add_sub_cancel_left]
  exact intervalIntegral_mem_subspace S (hx.2.2.1 t ht) (by
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact hF s hs.1 (x s))

omit [Fintype E] in
theorem GlobalIntegralSolution.mem_stoichiometricClass
    {F : ℝ → State d → State d} {z c : State d} {x : ℝ → State d}
    (hx : GlobalIntegralSolution F z x) (N : Network d E)
    (hF : ∀ t, 0 ≤ t → ∀ y, F t y ∈ N.stoichiometricSubspace)
    (hz : z ∈ N.stoichiometricClass c) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ N.stoichiometricClass c := by
  have hh := N.stoichiometricSubspace.add_mem (hx.sub_initial_mem _ hF ht) hz
  change x t - c ∈ N.stoichiometricSubspace
  simpa only [sub_add_sub_cancel] using hh

variable {m : ℕ} [Nonempty (Fin m)]

theorem Network.exists_global_positive_in_class_affine_strip (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M ε : ℝ} (hε : 0 < ε)
    (c lo hi : State d) (hbox : lo ≤ hi) (hlo : Positive lo)
    (hsub : A.plateau (M - ε) ∩ N.stoichiometricClass c ⊆ Icc lo hi)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c)
    (hflux : ∀ t, 0 ≤ t → ∀ y ∈ N.stoichiometricClass c,
      M - ε < A.minimum y → A.minimum y < M → ∀ i, A.Active i y →
        0 ≤ dot (A.slope i) (N.rhs (fun e => k e t) y)) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ A.plateau M ∩ N.stoichiometricClass c := by
  obtain ⟨x, _, hx⟩ := N.exists_global_cutoff_integralSolution hk lo hi hbox z
  have hclass : ∀ t, 0 ≤ t → x t ∈ N.stoichiometricClass c :=
    fun t ht => hx.mem_stoichiometricClass N
      (fun s _ y => N.cutoffRhs_mem_stoichiometricSubspace k lo hi s y) hz.2 ht
  have hstay := hx.mem_affine_plateau_of_strip A hε hz.1 (by
    intro t ht hl hu i ha
    have hy : x t ∈ Icc lo hi := hsub
      ⟨(A.mem_plateau_iff_minimum_ge (x t) (M - ε)).mpr hl.le, hclass t ht⟩
    rw [N.cutoffRhs_eq k lo hi ht hy]
    exact hflux t ht (x t) (hclass t ht) hl hu i ha)
  have hxbox : ∀ t, 0 ≤ t → x t ∈ Icc lo hi := by
    intro t ht
    exact hsub ⟨fun i => (sub_le_self M hε.le).trans (hstay t ht i), hclass t ht⟩
  have hactual : N.IsIntegralSolution k z x := hx.congr_field
    (fun t ht => N.cutoffRhs_eq k lo hi ht (hxbox t ht))
  exact ⟨x, ⟨hactual, fun t ht i => (hlo i).trans_le ((hxbox t ht).1 i)⟩,
    fun t ht => ⟨hstay t ht, hclass t ht⟩⟩

end Endotactic
