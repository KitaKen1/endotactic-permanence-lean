import Endotactic.ClassFaceTrap
import Endotactic.AffineDualBounds
import Endotactic.LinearGeometry

/-!
# Coordinate dual certificates modulo conserved linear observables

Within a stoichiometric class, a conserved linear observable has the value at
the class representative. A nonnegative combination of plateau slopes may
therefore reconstruct a coordinate up to a conserved direction. This proves
relative coordinate bounds even when all plateau slopes point into a cone
and the ambient plateau is unbounded.

Conservation is checked by the finite reaction-projection equations. Candidate
weights and conserved directions can be discovered externally; the full
coordinate containment, compactness, positivity and global trapping below
are verified by Lean under the explicit face certificate.
-/

namespace Endotactic

open Set

variable {d m : ℕ} {E : Type*}

theorem dot_add_left (r s x : State d) : dot (r + s) x = dot r x + dot s x := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem Network.dot_eq_in_stoichiometricClass (N : Network d E) (r : State d)
    {x c : State d} (hx : x ∈ N.stoichiometricClass c)
    (hzero : ∀ e, N.projection r e = 0) : dot r x = dot r c :=
  dot_eq_of_zero_projections N r hx hzero

structure Network.ClassBoxCertificate (N : Network d E) (A : AffineFamily d m)
    (M : ℝ) (c lo hi : State d) where
  lowerWeight : Fin d → Fin m → ℝ
  upperWeight : Fin d → Fin m → ℝ
  lowerConserved : Fin d → State d
  upperConserved : Fin d → State d
  lower_nonneg : ∀ j i, 0 ≤ lowerWeight j i
  upper_nonneg : ∀ j i, 0 ≤ upperWeight j i
  lower_zero : ∀ j e, N.projection (lowerConserved j) e = 0
  upper_zero : ∀ j e, N.projection (upperConserved j) e = 0
  lower_coordinate : ∀ j k, (∑ i, lowerWeight j i * A.slope i k) =
    (if k = j then 1 else 0) + lowerConserved j k
  upper_coordinate : ∀ j k, (∑ i, upperWeight j i * A.slope i k) =
    (if k = j then -1 else 0) + upperConserved j k
  lower_bound : ∀ j, lo j ≤ M * (∑ i, lowerWeight j i) -
    (∑ i, lowerWeight j i * A.offset i) - dot (lowerConserved j) c
  upper_bound : ∀ j, (∑ i, upperWeight j i * A.offset i) +
    dot (upperConserved j) c - M * (∑ i, upperWeight j i) ≤ hi j

theorem Network.ClassBoxCertificate.class_plateau_subset_box (N : Network d E)
    (A : AffineFamily d m) {M : ℝ} {c lo hi : State d}
    (C : N.ClassBoxCertificate A M c lo hi) :
    A.plateau M ∩ N.stoichiometricClass c ⊆ Icc lo hi := by
  rintro x ⟨hx, hxC⟩
  constructor
  · intro j
    have hb := A.weighted_plateau_bound (C.lowerWeight j) (C.lower_nonneg j) hx
    rw [A.weighted_value_eq] at hb
    have heq : (fun k => ∑ i, C.lowerWeight j i * A.slope i k) =
        (fun k => if k = j then 1 else 0) + C.lowerConserved j :=
      funext (C.lower_coordinate j)
    rw [heq, dot_add_left, dot_coordinate_mask, one_mul,
      N.dot_eq_in_stoichiometricClass _ hxC (C.lower_zero j)] at hb
    linarith [C.lower_bound j]
  · intro j
    have hb := A.weighted_plateau_bound (C.upperWeight j) (C.upper_nonneg j) hx
    rw [A.weighted_value_eq] at hb
    have heq : (fun k => ∑ i, C.upperWeight j i * A.slope i k) =
        (fun k => if k = j then -1 else 0) + C.upperConserved j :=
      funext (C.upper_coordinate j)
    rw [heq, dot_add_left, dot_coordinate_mask, neg_one_mul,
      N.dot_eq_in_stoichiometricClass _ hxC (C.upper_zero j)] at hb
    linarith [C.upper_bound j]

theorem Network.ClassBoxCertificate.isCompact (N : Network d E)
    (A : AffineFamily d m) {M : ℝ} {c lo hi : State d}
    (C : N.ClassBoxCertificate A M c lo hi) :
    IsCompact (A.plateau M ∩ N.stoichiometricClass c) :=
  isCompact_Icc.of_isClosed_subset
    ((A.plateau_isClosed M).inter (N.stoichiometricClass_isClosed c))
    (C.class_plateau_subset_box N A)

theorem Network.ClassBoxCertificate.positive (N : Network d E)
    (A : AffineFamily d m) {M : ℝ} {c lo hi : State d}
    (C : N.ClassBoxCertificate A M c lo hi) (hlo : Positive lo) :
    A.plateau M ∩ N.stoichiometricClass c ⊆ {x | Positive x} :=
  fun _ hx j => (hlo j).trans_le ((C.class_plateau_subset_box N A hx).1 j)

variable [Fintype E] [Nonempty (Fin m)]

theorem Network.exists_global_positive_of_class_affine_certificates (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} {c lo hi : State d}
    (C : N.ClassBoxCertificate A M c lo hi) (hlo : Positive lo)
    (hfaces : N.ClassAffineFaceCertificate A ℓ u M c)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ A.plateau M ∩ N.stoichiometricClass c :=
  N.exists_global_positive_of_class_affine_face_certificate hk A c (C.isCompact N A)
    (C.positive N A hlo) hfaces hz

theorem Network.positiveWellPosed_of_class_affine_certificates (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} {c lo hi : State d}
    (C : N.ClassBoxCertificate A M c lo hi) (hlo : Positive lo)
    (hfaces : N.ClassAffineFaceCertificate A ℓ u M c)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    N.PositiveWellPosed k z :=
  N.positiveWellPosed_of_class_affine_face_certificate hk A c (C.isCompact N A)
    (C.positive N A hlo) hfaces hz

end Endotactic
