import Endotactic.CompactTrapPermanence
import Endotactic.ClassDualBounds

/-!
# Finite initial-trap certificates with a variable number of faces

Each initial state may choose a different finite affine family and face count.
The certificate contains the original class trap, positivity, compactness and
strict/conserved face signs. A finite conserved-direction dual witness can
supply positivity and compactness. The trap constructs actual global solutions;
uniqueness puts all original integral solutions in its carrier.

Together with a common positive compact target and pointwise strict exterior
signs on these carriers, the certificates prove common-rate-box permanence.
Existence of such certificates for arbitrary endotactic networks is not proved.
-/

namespace Endotactic

open Set

variable {d : ℕ} {E : Type*} [Fintype E]

structure Network.FiniteClassTrap (N : Network d E) (ℓ u : ℝ) (c z : State d) where
  branchCount : ℕ
  nonemptyBranches : Nonempty (Fin branchCount)
  family : AffineFamily d branchCount
  level : ℝ
  initial_mem : z ∈ family.plateau level ∩ N.stoichiometricClass c
  compact : IsCompact (family.plateau level ∩ N.stoichiometricClass c)
  positive : family.plateau level ∩ N.stoichiometricClass c ⊆ {y | Positive y}
  faces : N.ClassAffineFaceCertificate family ℓ u level c

def Network.FiniteClassTrap.carrier {N : Network d E} {ℓ u : ℝ} {c z : State d}
    (T : N.FiniteClassTrap ℓ u c z) : Set (State d) :=
  T.family.plateau T.level ∩ N.stoichiometricClass c

noncomputable def Network.finiteClassTrap_of_dual_certificate {n : ℕ}
    [Nonempty (Fin n)] (N : Network d E) (B : AffineFamily d n)
    {ℓ u L : ℝ} {c z lo hi : State d} (C : N.ClassBoxCertificate B L c lo hi)
    (hlo : Positive lo) (hfaces : N.ClassAffineFaceCertificate B ℓ u L c)
    (hz : z ∈ B.plateau L ∩ N.stoichiometricClass c) : N.FiniteClassTrap ℓ u c z where
  branchCount := n
  nonemptyBranches := inferInstance
  family := B
  level := L
  initial_mem := hz
  compact := C.isCompact N B
  positive := C.positive N B hlo
  faces := hfaces

namespace Network.FiniteClassTrap

variable {N : Network d E} {ℓ u : ℝ} {c z : State d} (T : N.FiniteClassTrap ℓ u c z)

include T

theorem exists_global_positive {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧ ∀ t, 0 ≤ t → x t ∈ T.carrier := by
  let : Nonempty (Fin T.branchCount) := T.nonemptyBranches
  exact N.exists_global_positive_of_class_affine_face_certificate hk T.family c
    T.compact T.positive T.faces T.initial_mem

theorem positiveWellPosed {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u) :
    N.PositiveWellPosed k z := by
  obtain ⟨x, hx, _⟩ := T.exists_global_positive hk
  exact N.positiveWellPosed_of_exists hk ⟨x, hx⟩

theorem integralSolution_mem {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u)
    {x : ℝ → State d} (hx : N.IsIntegralSolution k z x) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ T.carrier := by
  obtain ⟨y, hy, hstay⟩ := T.exists_global_positive hk
  exact N.integralSolution_mem_of_trapped_solution hk hx ⟨y, hy.1, hstay⟩ ht

end Network.FiniteClassTrap

theorem Network.uniformPermanent_of_finite_class_traps {m : ℕ} [Nonempty (Fin m)]
    (N : Network d E) (A : AffineFamily d m) (ℓ u M : ℝ) (c : State d)
    (regular : (E → ℝ → ℝ) → Prop)
    (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (htraps : ∀ z ∈ N.positiveClass c, ∃ T : N.FiniteClassTrap ℓ u c z,
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
