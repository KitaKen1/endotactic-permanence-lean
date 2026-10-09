import Endotactic.AffineRobustness

/-!
# Finite dual certificates for affine coordinate bounds

Nonnegative combinations of plateau inequalities that reconstruct a coordinate
or its negative certify lower and upper coordinate bounds. A rational LP solver
may discover these weights externally; Lean checks the identities and bounds
for every state. Neither solver correctness nor termination is assumed.

Such a certificate supplies compactness and positivity to the face-certificate
global solution API. This module does not claim that every endotactic network
has a suitable affine family or face certificate.
-/

namespace Endotactic

open Set

variable {d m : ℕ}

theorem AffineFamily.weighted_value_eq (A : AffineFamily d m) (w : Fin m → ℝ)
    (x : State d) :
    (∑ i, w i * A.value i x) = dot (fun j => ∑ i, w i * A.slope i j) x +
      ∑ i, w i * A.offset i := by
  have hdot : (∑ i, w i * dot (A.slope i) x) =
      dot (fun j => ∑ i, w i * A.slope i j) x := by
    unfold dot
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [AffineFamily.value, mul_add, Finset.sum_add_distrib]
  rw [hdot]

theorem AffineFamily.weighted_plateau_bound (A : AffineFamily d m) {M : ℝ}
    (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) {x : State d} (hx : x ∈ A.plateau M) :
    M * (∑ i, w i) ≤ ∑ i, w i * A.value i x := by
  calc
    M * (∑ i, w i) = ∑ i, w i * M := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => mul_comm M (w i))
    _ ≤ ∑ i, w i * A.value i x :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hw i)

theorem dot_coordinate_mask (j : Fin d) (a : ℝ) (x : State d) :
    dot (fun k => if k = j then a else 0) x = a * x j := by
  classical
  simp [dot]

/-- A finite, checkable dual witness for coordinate bounds at one plateau level. -/
structure AffineFamily.BoxCertificate (A : AffineFamily d m) (M : ℝ)
    (lo hi : State d) where
  lowerWeight : Fin d → Fin m → ℝ
  upperWeight : Fin d → Fin m → ℝ
  lower_nonneg : ∀ j i, 0 ≤ lowerWeight j i
  upper_nonneg : ∀ j i, 0 ≤ upperWeight j i
  lower_coordinate : ∀ j k, (∑ i, lowerWeight j i * A.slope i k) =
    if k = j then 1 else 0
  upper_coordinate : ∀ j k, (∑ i, upperWeight j i * A.slope i k) =
    if k = j then -1 else 0
  lower_bound : ∀ j, lo j ≤ M * (∑ i, lowerWeight j i) -
    ∑ i, lowerWeight j i * A.offset i
  upper_bound : ∀ j, (∑ i, upperWeight j i * A.offset i) -
    M * (∑ i, upperWeight j i) ≤ hi j

theorem AffineFamily.BoxCertificate.plateau_subset_box (A : AffineFamily d m)
    {M : ℝ} {lo hi : State d} (C : A.BoxCertificate M lo hi) :
    A.plateau M ⊆ Icc lo hi := by
  intro x hx
  constructor
  · intro j
    have hb := A.weighted_plateau_bound (C.lowerWeight j) (C.lower_nonneg j) hx
    rw [A.weighted_value_eq] at hb
    have heq : (fun k => ∑ i, C.lowerWeight j i * A.slope i k) =
        (fun k => if k = j then 1 else 0) := funext (C.lower_coordinate j)
    rw [heq, dot_coordinate_mask, one_mul] at hb
    linarith [C.lower_bound j]
  · intro j
    have hb := A.weighted_plateau_bound (C.upperWeight j) (C.upper_nonneg j) hx
    rw [A.weighted_value_eq] at hb
    have heq : (fun k => ∑ i, C.upperWeight j i * A.slope i k) =
        (fun k => if k = j then -1 else 0) := funext (C.upper_coordinate j)
    rw [heq, dot_coordinate_mask, neg_one_mul] at hb
    linarith [C.upper_bound j]

theorem AffineFamily.BoxCertificate.isCompact (A : AffineFamily d m)
    {M : ℝ} {lo hi : State d} (C : A.BoxCertificate M lo hi) :
    IsCompact (A.plateau M) :=
  A.plateau_isCompact_of_subset M isCompact_Icc (C.plateau_subset_box A)

theorem AffineFamily.BoxCertificate.positive (A : AffineFamily d m)
    {M : ℝ} {lo hi : State d} (C : A.BoxCertificate M lo hi) (hlo : Positive lo) :
    A.plateau M ⊆ {x | Positive x} :=
  fun _ hx j => (hlo j).trans_le ((C.plateau_subset_box A hx).1 j)

variable {E : Type*} [Fintype E] [Nonempty (Fin m)]

theorem Network.exists_global_positive_of_affine_certificates (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} {lo hi : State d}
    (C : A.BoxCertificate M lo hi) (hlo : Positive lo)
    (hfaces : N.AffineFaceCertificate A ℓ u M) {z : State d} (hz : z ∈ A.plateau M) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧ ∀ t, 0 ≤ t → x t ∈ A.plateau M :=
  N.exists_global_positive_of_compact_affine_face_certificate hk A (C.isCompact A)
    (C.positive A hlo) hfaces hz

theorem Network.positiveWellPosed_of_affine_certificates (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} {lo hi : State d}
    (C : A.BoxCertificate M lo hi) (hlo : Positive lo)
    (hfaces : N.AffineFaceCertificate A ℓ u M) {z : State d} (hz : z ∈ A.plateau M) :
    N.PositiveWellPosed k z :=
  N.positiveWellPosed_of_compact_affine_face_certificate hk A (C.isCompact A)
    (C.positive A hlo) hfaces hz

end Endotactic
