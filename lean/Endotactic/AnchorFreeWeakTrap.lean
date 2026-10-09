import Endotactic.WeakFaceRigidity

/-!
# Weak trapping without a supplied anchor, for distinct rate endpoints

Nonempty compact positive class carriers and nonnegative original face fluxes
are sufficient when `ell < u`. The relative anchor is constructed, rather than
assumed. Original integral solutions stay in the original carrier. The finite
certificate still permits a different face count for each initial state.

Permanence needs separate common-target geometry and strict exterior signs.
This module does not prove those certificates exist for every endotactic network.
-/

namespace Endotactic

open Set

variable {d : ℕ} {E : Type*} [Fintype E]

structure Network.AnchorFreeWeakFiniteClassTrap (N : Network d E) (ℓ u : ℝ)
    (c z : State d) where
  branchCount : ℕ
  nonemptyBranches : Nonempty (Fin branchCount)
  family : AffineFamily d branchCount
  level : ℝ
  initial_mem : z ∈ family.plateau level ∩ N.stoichiometricClass c
  compact : IsCompact (family.plateau level ∩ N.stoichiometricClass c)
  positive : family.plateau level ∩ N.stoichiometricClass c ⊆ {y | Positive y}
  faces : N.ClassWeakAffineFaceCertificate family ℓ u level c

def Network.AnchorFreeWeakFiniteClassTrap.carrier {N : Network d E} {ℓ u : ℝ}
    {c z : State d} (T : N.AnchorFreeWeakFiniteClassTrap ℓ u c z) : Set (State d) :=
  T.family.plateau T.level ∩ N.stoichiometricClass c

noncomputable def Network.anchorFreeWeakFiniteClassTrap_of_dual_certificate {n : ℕ}
    [Nonempty (Fin n)] (N : Network d E) (A : AffineFamily d n)
    {ℓ u M : ℝ} {c z lo hi : State d} (C : N.ClassBoxCertificate A M c lo hi)
    (hlo : Positive lo) (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u M c)
    (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    N.AnchorFreeWeakFiniteClassTrap ℓ u c z where
  branchCount := n
  nonemptyBranches := inferInstance
  family := A
  level := M
  initial_mem := hz
  compact := C.isCompact N A
  positive := C.positive N A hlo
  faces := hfaces

namespace Network.AnchorFreeWeakFiniteClassTrap

variable {N : Network d E} {ℓ u : ℝ} {c z : State d}

noncomputable def toRelativeTrap (T : N.AnchorFreeWeakFiniteClassTrap ℓ u c z)
    (hgap : ℓ < u) : N.RelativeWeakFiniteClassTrap ℓ u c z := by
  let hex := N.exists_classRelativeAnchor_of_weak_faces T.family hgap
    ⟨z, T.initial_mem⟩ T.positive T.faces
  exact {
    branchCount := T.branchCount
    nonemptyBranches := T.nonemptyBranches
    family := T.family
    level := T.level
    anchor := Classical.choose hex
    anchor_relative := (Classical.choose_spec hex).2
    initial_mem := T.initial_mem
    compact := T.compact
    positive := T.positive
    faces := T.faces }

theorem toRelativeTrap_carrier (T : N.AnchorFreeWeakFiniteClassTrap ℓ u c z)
    (hgap : ℓ < u) : (T.toRelativeTrap hgap).carrier = T.carrier := rfl

theorem exists_global_positive (T : N.AnchorFreeWeakFiniteClassTrap ℓ u c z)
    (hgap : ℓ < u) {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧ ∀ t, 0 ≤ t → x t ∈ T.carrier :=
  (T.toRelativeTrap hgap).exists_global_positive hk

theorem positiveWellPosed (T : N.AnchorFreeWeakFiniteClassTrap ℓ u c z)
    (hgap : ℓ < u) {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u) :
    N.PositiveWellPosed k z := (T.toRelativeTrap hgap).positiveWellPosed hk

theorem integralSolution_mem (T : N.AnchorFreeWeakFiniteClassTrap ℓ u c z)
    (hgap : ℓ < u) {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u)
    {x : ℝ → State d} (hx : N.IsIntegralSolution k z x) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ T.carrier := (T.toRelativeTrap hgap).integralSolution_mem hk hx ht

end Network.AnchorFreeWeakFiniteClassTrap

variable {m : ℕ} [Nonempty (Fin m)]

theorem Network.exists_global_positive_of_anchor_free_weak_class_faces (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u M : ℝ} (hk : AdmissibleRates k ℓ u) (hgap : ℓ < u)
    (A : AffineFamily d m) (c : State d)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u M c)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ A.plateau M ∩ N.stoichiometricClass c := by
  obtain ⟨p, _, hp⟩ := N.exists_classRelativeAnchor_of_weak_faces A hgap ⟨z, hz⟩ hpos hfaces
  exact N.exists_global_positive_of_relative_weak_class_faces hk A c p hp hK hpos hfaces hz

theorem Network.positiveWellPosed_of_anchor_free_weak_class_faces (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u M : ℝ} (hk : AdmissibleRates k ℓ u) (hgap : ℓ < u)
    (A : AffineFamily d m) (c : State d)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u M c)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    N.PositiveWellPosed k z := by
  obtain ⟨x, hx, _⟩ := N.exists_global_positive_of_anchor_free_weak_class_faces hk hgap
    A c hK hpos hfaces hz
  exact N.positiveWellPosed_of_exists hk ⟨x, hx⟩

theorem Network.uniformPermanent_of_anchor_free_weak_finite_class_traps
    (N : Network d E) (A : AffineFamily d m) (ℓ u M : ℝ) (c : State d)
    (regular : (E → ℝ → ℝ) → Prop) (hgap : ℓ < u)
    (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (htraps : ∀ z ∈ N.positiveClass c, ∃ T : N.AnchorFreeWeakFiniteClassTrap ℓ u c z,
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
        ∀ y ∈ T.carrier, A.minimum y < M → ∀ i, A.Active i y →
          0 < dot (A.slope i) (N.rhs a y)) : N.UniformPermanent ℓ u c regular := by
  apply N.uniformPermanent_of_relative_weak_finite_class_traps A ℓ u M c regular hne hK hpos
  intro z hz
  obtain ⟨T, hstrict⟩ := htraps z hz
  exact ⟨T.toRelativeTrap hgap, hstrict⟩

end Endotactic
