import Endotactic.CompactAbsorption
import Endotactic.ClassFaceTrap
import Endotactic.IntegralUniqueness

/-!
# Pointwise exterior signs and compact initial traps imply permanence

Choose a slightly relaxed target once, using relative affine robustness to
preserve positivity and compactness in the stoichiometric class. Each initial
point may have its own compact invariant trap. Pointwise strict flux outside
the original target then supplies a common positive margin on each trap below
the relaxed level, without any numerical margin or global upper-cap hypothesis.

The final certificate theorem constructs actual positive global solutions
from class-restricted strict/conserved face certificates. General endotacticity
has not yet been shown to construct the target and these traps.
-/

namespace Endotactic

open Set

variable {d m : ℕ} [Nonempty (Fin m)] {E : Type*} [Fintype E]

theorem Network.integralSolution_mem_of_trapped_solution (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    {z : State d} {x : ℝ → State d} (hx : N.IsIntegralSolution k z x)
    {B : Set (State d)} (htrap : ∃ y, N.IsIntegralSolution k z y ∧
      ∀ t, 0 ≤ t → y t ∈ B) {t : ℝ} (ht : 0 ≤ t) : x t ∈ B := by
  obtain ⟨y, hy, hstay⟩ := htrap
  rw [hx.eqOn_nonnegative N hk hy ht]
  exact hstay t ht

theorem Network.uniformPermanent_of_compact_strict_exterior (N : Network d E)
    (A : AffineFamily d m) (ℓ u M : ℝ) (c : State d)
    (regular : (E → ℝ → ℝ) → Prop)
    (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (hwell : ∀ k, AdmissibleRates k ℓ u → regular k →
      ∀ z ∈ N.positiveClass c, N.PositiveWellPosed k z)
    (htraps : ∀ z ∈ N.positiveClass c, ∃ B : Set (State d), IsCompact B ∧
      (∀ k, AdmissibleRates k ℓ u → regular k →
        ∀ x, N.IsGlobalPositiveSolution k z x → ∀ t, 0 ≤ t → x t ∈ B) ∧
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
        ∀ y ∈ B, A.minimum y < M → ∀ i, A.Active i y →
          0 < dot (A.slope i) (N.rhs a y)) : N.UniformPermanent ℓ u c regular := by
  obtain ⟨ε, lo, hi, hε, _, hlo, hsub⟩ :=
    A.exists_enlarged_positive_box_inter (N.stoichiometricClass_isClosed c)
      (N.stoichiometricClass_convex c) hne hK hpos
  let Q : ℝ := M - ε
  let K : Set (State d) := A.plateau Q ∩ N.stoichiometricClass c
  have hQ : Q < M := sub_lt_self M hε
  have hne' : K.Nonempty := by
    obtain ⟨y, hy, hyC⟩ := hne
    exact ⟨y, (fun i => (sub_le_self M hε.le).trans (hy i)), hyC⟩
  have hcompact : IsCompact K := isCompact_Icc.of_isClosed_subset
    ((A.plateau_isClosed Q).inter (N.stoichiometricClass_isClosed c)) hsub
  have hclass : K ⊆ N.positiveClass c := by
    intro y hy
    exact ⟨fun i => (hlo i).trans_le ((hsub hy).1 i), hy.2⟩
  refine ⟨K, hne', hcompact, hclass, ?_⟩
  intro k hk hr
  refine ⟨hwell k hk hr, ?_⟩
  intro z hz x hx
  obtain ⟨B, hB, hstay, hstrict⟩ := htraps z hz
  obtain ⟨T, hT, hentry⟩ := A.eventuallyIn_plateau_of_compact_strict_exterior hk hx.1 hB
    (hstay k hk hr x hx) hQ hstrict
  exact ⟨T, hT, fun t ht => ⟨hentry t ht,
    (hx.mem_positiveClass hz (hT.trans ht)).2⟩⟩

theorem Network.uniformPermanent_of_compact_affine_traps {n : ℕ} [Nonempty (Fin n)]
    (N : Network d E) (A : AffineFamily d m) (ℓ u M : ℝ) (c : State d)
    (regular : (E → ℝ → ℝ) → Prop)
    (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (htraps : ∀ z ∈ N.positiveClass c,
      ∃ (B : AffineFamily d n) (L : ℝ),
        z ∈ B.plateau L ∩ N.stoichiometricClass c ∧
        IsCompact (B.plateau L ∩ N.stoichiometricClass c) ∧
        (B.plateau L ∩ N.stoichiometricClass c ⊆ {y | Positive y}) ∧
        N.ClassAffineFaceCertificate B ℓ u L c ∧
        ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
          ∀ y ∈ B.plateau L ∩ N.stoichiometricClass c,
            A.minimum y < M → ∀ i, A.Active i y →
              0 < dot (A.slope i) (N.rhs a y)) : N.UniformPermanent ℓ u c regular := by
  apply N.uniformPermanent_of_compact_strict_exterior A ℓ u M c regular hne hK hpos
  · intro k hk _ z hz
    obtain ⟨B, L, hzB, hB, hBp, hfaces, _⟩ := htraps z hz
    exact N.positiveWellPosed_of_class_affine_face_certificate hk B c hB hBp hfaces hzB
  · intro z hz
    obtain ⟨B, L, hzB, hB, hBp, hfaces, hstrict⟩ := htraps z hz
    refine ⟨B.plateau L ∩ N.stoichiometricClass c, hB, ?_, hstrict⟩
    intro k hk _ x hx t ht
    obtain ⟨y, hy, hstay⟩ := N.exists_global_positive_of_class_affine_face_certificate hk
      B c hB hBp hfaces hzB
    exact N.integralSolution_mem_of_trapped_solution hk hx.1 ⟨y, hy.1, hstay⟩ ht

end Endotactic
