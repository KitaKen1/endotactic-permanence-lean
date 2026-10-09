import Endotactic.ConservedNormalization
import Endotactic.WeakFiniteClassTrap

/-!
# Relative weak finite traps retain conserved equality faces

The anchor is strict only on moving branches. Conserved branches are checked
by finite reaction projections and replaced by constant one within the class.
The carrier is unchanged, so the existing weak finite trap and permanence
assembly apply. A coordinate dual certificate can still use the original faces.

General endotacticity has not been shown to supply these finite certificates.
-/

namespace Endotactic

open Set

variable {d : ℕ} {E : Type*} [Fintype E]

structure Network.RelativeWeakFiniteClassTrap (N : Network d E) (ℓ u : ℝ)
    (c z : State d) where
  branchCount : ℕ
  nonemptyBranches : Nonempty (Fin branchCount)
  family : AffineFamily d branchCount
  level : ℝ
  anchor : State d
  anchor_relative : N.ClassRelativeAnchor family level c anchor
  initial_mem : z ∈ family.plateau level ∩ N.stoichiometricClass c
  compact : IsCompact (family.plateau level ∩ N.stoichiometricClass c)
  positive : family.plateau level ∩ N.stoichiometricClass c ⊆ {y | Positive y}
  faces : N.ClassWeakAffineFaceCertificate family ℓ u level c

def Network.RelativeWeakFiniteClassTrap.carrier {N : Network d E} {ℓ u : ℝ}
    {c z : State d} (T : N.RelativeWeakFiniteClassTrap ℓ u c z) : Set (State d) :=
  T.family.plateau T.level ∩ N.stoichiometricClass c

noncomputable def Network.relativeWeakFiniteClassTrap_of_dual_certificate {n : ℕ}
    [Nonempty (Fin n)] (N : Network d E) (A : AffineFamily d n)
    {ℓ u M : ℝ} {c z p lo hi : State d} (C : N.ClassBoxCertificate A M c lo hi)
    (hlo : Positive lo) (hp : N.ClassRelativeAnchor A M c p)
    (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u M c)
    (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    N.RelativeWeakFiniteClassTrap ℓ u c z where
  branchCount := n
  nonemptyBranches := inferInstance
  family := A
  level := M
  anchor := p
  anchor_relative := hp
  initial_mem := hz
  compact := C.isCompact N A
  positive := C.positive N A hlo
  faces := hfaces

noncomputable def Network.relativeWeakFiniteClassTrap_of_face_witnesses {n : ℕ}
    [Nonempty (Fin n)] (N : Network d E) (A : AffineFamily d n)
    {ℓ u M : ℝ} {c z lo hi : State d} (C : N.ClassBoxCertificate A M c lo hi)
    (hlo : Positive lo) (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u M c)
    (hw : ∀ i, (∀ e, N.projection (A.slope i) e = 0) ∨
      ∃ y ∈ A.plateau M ∩ N.stoichiometricClass c, M < A.value i y)
    (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    N.RelativeWeakFiniteClassTrap ℓ u c z := by
  let hex := N.exists_classRelativeAnchor_of_face_witnesses A ⟨z, hz⟩ hw
  let p := Classical.choose hex
  have hp : N.ClassRelativeAnchor A M c p := (Classical.choose_spec hex).2
  exact N.relativeWeakFiniteClassTrap_of_dual_certificate A C hlo hp hfaces hz

namespace Network.RelativeWeakFiniteClassTrap

variable {N : Network d E} {ℓ u : ℝ} {c z : State d}

noncomputable def toWeakTrap (T : N.RelativeWeakFiniteClassTrap ℓ u c z) :
    N.WeakFiniteClassTrap ℓ u c z := by
  have hne : (T.family.plateau T.level ∩ N.stoichiometricClass c).Nonempty := ⟨z, T.initial_mem⟩
  have heq := N.classNormalizeAt_class_plateau T.family T.anchor_relative hne
  exact {
    branchCount := T.branchCount
    nonemptyBranches := T.nonemptyBranches
    family := N.classNormalizeAt T.family T.level T.anchor
    level := 0
    anchor := T.anchor
    anchor_class := T.anchor_relative.1
    anchor_strict := fun i => by rw [N.classNormalizeAt_anchor T.family T.anchor_relative i]; norm_num
    initial_mem := by rw [heq]; exact T.initial_mem
    compact := by rw [heq]; exact T.compact
    positive := by rw [heq]; exact T.positive
    faces := N.classWeakAffineFaceCertificate_classNormalizeAt T.family T.anchor_relative hne T.faces }

theorem toWeakTrap_carrier (T : N.RelativeWeakFiniteClassTrap ℓ u c z) :
    T.toWeakTrap.carrier = T.carrier := by
  change (N.classNormalizeAt T.family T.level T.anchor).plateau 0 ∩ N.stoichiometricClass c = _
  exact N.classNormalizeAt_class_plateau T.family T.anchor_relative ⟨z, T.initial_mem⟩

theorem exists_global_positive (T : N.RelativeWeakFiniteClassTrap ℓ u c z)
    {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧ ∀ t, 0 ≤ t → x t ∈ T.carrier := by
  simpa only [T.toWeakTrap_carrier] using T.toWeakTrap.exists_global_positive hk

theorem positiveWellPosed (T : N.RelativeWeakFiniteClassTrap ℓ u c z)
    {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u) : N.PositiveWellPosed k z :=
  T.toWeakTrap.positiveWellPosed hk

theorem integralSolution_mem (T : N.RelativeWeakFiniteClassTrap ℓ u c z)
    {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u)
    {x : ℝ → State d} (hx : N.IsIntegralSolution k z x) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ T.carrier := by
  simpa only [T.toWeakTrap_carrier] using T.toWeakTrap.integralSolution_mem hk hx ht

end Network.RelativeWeakFiniteClassTrap

theorem Network.uniformPermanent_of_relative_weak_finite_class_traps
    {m : ℕ} [Nonempty (Fin m)] (N : Network d E) (A : AffineFamily d m)
    (ℓ u M : ℝ) (c : State d) (regular : (E → ℝ → ℝ) → Prop)
    (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (htraps : ∀ z ∈ N.positiveClass c, ∃ T : N.RelativeWeakFiniteClassTrap ℓ u c z,
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
        ∀ y ∈ T.carrier, A.minimum y < M → ∀ i, A.Active i y →
          0 < dot (A.slope i) (N.rhs a y)) : N.UniformPermanent ℓ u c regular := by
  apply N.uniformPermanent_of_weak_finite_class_traps A ℓ u M c regular hne hK hpos
  intro z hz
  obtain ⟨T, hstrict⟩ := htraps z hz
  refine ⟨T.toWeakTrap, ?_⟩
  simpa only [T.toWeakTrap_carrier] using hstrict

end Endotactic
