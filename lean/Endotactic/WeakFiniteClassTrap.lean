import Endotactic.WeakClassFaceTrap
import Endotactic.CompactTrapPermanence
import Endotactic.ClassDualBounds

/-!
# Finite class traps with nonstrict faces and an interior anchor

Each initial state may choose its face count, affine family and strictly feasible
anchor in the class. Nonstrict inward faces suffice. A finite dual witness can
supply positive compactness. Combined with the separate common-target exterior
signs, these initial certificates construct global solutions and permanence.

Existence of these certificates for every endotactic network remains unproved.
-/

namespace Endotactic

open Set

variable {d : ℕ} {E : Type*} [Fintype E]

structure Network.WeakFiniteClassTrap (N : Network d E) (ℓ u : ℝ) (c z : State d) where
  branchCount : ℕ
  nonemptyBranches : Nonempty (Fin branchCount)
  family : AffineFamily d branchCount
  level : ℝ
  anchor : State d
  anchor_class : anchor ∈ N.stoichiometricClass c
  anchor_strict : ∀ i, level < family.value i anchor
  initial_mem : z ∈ family.plateau level ∩ N.stoichiometricClass c
  compact : IsCompact (family.plateau level ∩ N.stoichiometricClass c)
  positive : family.plateau level ∩ N.stoichiometricClass c ⊆ {y | Positive y}
  faces : N.ClassWeakAffineFaceCertificate family ℓ u level c

def Network.WeakFiniteClassTrap.carrier {N : Network d E} {ℓ u : ℝ} {c z : State d}
    (T : N.WeakFiniteClassTrap ℓ u c z) : Set (State d) :=
  T.family.plateau T.level ∩ N.stoichiometricClass c

noncomputable def Network.weakFiniteClassTrap_of_dual_certificate {n : ℕ}
    [Nonempty (Fin n)] (N : Network d E) (A : AffineFamily d n)
    {ℓ u M : ℝ} {c z p lo hi : State d} (C : N.ClassBoxCertificate A M c lo hi)
    (hlo : Positive lo) (hpC : p ∈ N.stoichiometricClass c) (hp : ∀ i, M < A.value i p)
    (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u M c)
    (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) : N.WeakFiniteClassTrap ℓ u c z where
  branchCount := n
  nonemptyBranches := inferInstance
  family := A
  level := M
  anchor := p
  anchor_class := hpC
  anchor_strict := hp
  initial_mem := hz
  compact := C.isCompact N A
  positive := C.positive N A hlo
  faces := hfaces

namespace Network.WeakFiniteClassTrap

variable {N : Network d E} {ℓ u : ℝ} {c z : State d} (T : N.WeakFiniteClassTrap ℓ u c z)

include T

theorem exists_global_positive {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧ ∀ t, 0 ≤ t → x t ∈ T.carrier := by
  let : Nonempty (Fin T.branchCount) := T.nonemptyBranches
  exact N.exists_global_positive_of_weak_class_faces hk T.family c T.anchor
    T.anchor_strict T.anchor_class T.compact T.positive T.faces T.initial_mem

theorem positiveWellPosed {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u) :
    N.PositiveWellPosed k z := by
  obtain ⟨x, hx, _⟩ := T.exists_global_positive hk
  exact N.positiveWellPosed_of_exists hk ⟨x, hx⟩

theorem integralSolution_mem {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u)
    {x : ℝ → State d} (hx : N.IsIntegralSolution k z x) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ T.carrier := by
  obtain ⟨y, hy, hstay⟩ := T.exists_global_positive hk
  exact N.integralSolution_mem_of_trapped_solution hk hx ⟨y, hy.1, hstay⟩ ht

end Network.WeakFiniteClassTrap

theorem Network.uniformPermanent_of_weak_finite_class_traps {m : ℕ} [Nonempty (Fin m)]
    (N : Network d E) (A : AffineFamily d m) (ℓ u M : ℝ) (c : State d)
    (regular : (E → ℝ → ℝ) → Prop)
    (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (htraps : ∀ z ∈ N.positiveClass c, ∃ T : N.WeakFiniteClassTrap ℓ u c z,
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
        ∀ y ∈ T.carrier, A.minimum y < M → ∀ i, A.Active i y →
          0 < dot (A.slope i) (N.rhs a y)) : N.UniformPermanent ℓ u c regular := by
  apply N.uniformPermanent_of_compact_strict_exterior A ℓ u M c regular hne hK hpos
  · intro k hk _ z hz
    obtain ⟨T, _⟩ := htraps z hz
    exact T.positiveWellPosed hk
  · intro z hz
    obtain ⟨T, hstrict⟩ := htraps z hz
    exact ⟨T.carrier, T.compact,
      fun k hk _ x hx t ht => T.integralSolution_mem hk hx.1 ht, hstrict⟩

end Endotactic
