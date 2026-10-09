import Endotactic.IntegralTrajectory

/-!
# Normalize affine faces at a strictly feasible anchor

Positive rescaling preserves the original plateau, and makes every branch have
value one at the anchor. An exterior active face can then be repaired radially
to that same face without violating the other constraints. The repair distance
is at most the affine deficit times the distance to the anchor.

The existence of a strictly feasible anchor is an explicit hypothesis.
-/

namespace Endotactic

open Set

variable {d m : ℕ}

noncomputable def AffineFamily.normalizeAt (A : AffineFamily d m) (M : ℝ)
    (p : State d) : AffineFamily d m where
  slope := fun i => (A.value i p - M)⁻¹ • A.slope i
  offset := fun i => (A.value i p - M)⁻¹ * (A.offset i - M)

theorem AffineFamily.normalizeAt_dot (A : AffineFamily d m) (M : ℝ)
    (p v : State d) (i : Fin m) :
    dot ((A.normalizeAt M p).slope i) v = (A.value i p - M)⁻¹ * dot (A.slope i) v := by
  simp only [AffineFamily.normalizeAt, dot, Pi.smul_apply, smul_eq_mul, mul_assoc,
    Finset.mul_sum]

theorem AffineFamily.normalizeAt_value (A : AffineFamily d m) (M : ℝ)
    (p x : State d) (i : Fin m) :
    (A.normalizeAt M p).value i x = (A.value i p - M)⁻¹ * (A.value i x - M) := by
  change dot ((A.normalizeAt M p).slope i) x +
    (A.value i p - M)⁻¹ * (A.offset i - M) = _
  rw [A.normalizeAt_dot]
  unfold AffineFamily.value
  ring

theorem AffineFamily.normalizeAt_anchor (A : AffineFamily d m) {M : ℝ} {p : State d}
    (hp : ∀ i, M < A.value i p) (i : Fin m) :
    (A.normalizeAt M p).value i p = 1 := by
  rw [A.normalizeAt_value, inv_mul_cancel₀ (sub_pos.mpr (hp i)).ne']

theorem AffineFamily.normalizeAt_plateau (A : AffineFamily d m) {M : ℝ} {p : State d}
    (hp : ∀ i, M < A.value i p) :
    (A.normalizeAt M p).plateau 0 = A.plateau M := by
  ext x
  change (∀ i, 0 ≤ (A.normalizeAt M p).value i x) ↔ ∀ i, M ≤ A.value i x
  simp only [A.normalizeAt_value, mul_nonneg_iff_of_pos_left (inv_pos.mpr (sub_pos.mpr (hp _))),
    sub_nonneg]

variable [Nonempty (Fin m)]

noncomputable def AffineFamily.radialRepair (A : AffineFamily d m) (p y : State d) : State d :=
  (1 - A.minimum y)⁻¹ • y + (-A.minimum y * (1 - A.minimum y)⁻¹) • p

theorem AffineFamily.radialRepair_weights (A : AffineFamily d m) {y : State d}
    (hy : A.minimum y < 0) :
    0 ≤ (1 - A.minimum y)⁻¹ ∧
      0 ≤ -A.minimum y * (1 - A.minimum y)⁻¹ ∧
      (1 - A.minimum y)⁻¹ + (-A.minimum y * (1 - A.minimum y)⁻¹) = 1 := by
  have hden : 0 < 1 - A.minimum y := by linarith
  refine ⟨(inv_pos.mpr hden).le, mul_nonneg (by linarith) (inv_pos.mpr hden).le, ?_⟩
  field_simp
  ring

theorem AffineFamily.radialRepair_mem_convex (A : AffineFamily d m) {p y : State d}
    {B : Set (State d)} (hB : Convex ℝ B) (hp : p ∈ B) (hyB : y ∈ B)
    (hy : A.minimum y < 0) : A.radialRepair p y ∈ B := by
  obtain ⟨ha, hb, hab⟩ := A.radialRepair_weights hy
  exact hB hyB hp ha hb hab

theorem AffineFamily.radialRepair_value (A : AffineFamily d m) {p y : State d}
    (hp : ∀ i, A.value i p = 1) (hy : A.minimum y < 0) (i : Fin m) :
    A.value i (A.radialRepair p y) =
      (1 - A.minimum y)⁻¹ * (A.value i y - A.minimum y) := by
  rw [AffineFamily.radialRepair, A.value_convex_combination i y p
    (A.radialRepair_weights hy).2.2, hp i]
  ring

theorem AffineFamily.radialRepair_mem_plateau (A : AffineFamily d m) {p y : State d}
    (hp : ∀ i, A.value i p = 1) (hy : A.minimum y < 0) :
    A.radialRepair p y ∈ A.plateau 0 := by
  intro i
  rw [A.radialRepair_value hp hy]
  exact mul_nonneg (inv_nonneg.mpr (by linarith))
    (sub_nonneg.mpr (finiteMinimum_le (fun j => A.value j y) i))

theorem AffineFamily.radialRepair_active_face (A : AffineFamily d m) {p y : State d}
    (hp : ∀ i, A.value i p = 1) (hy : A.minimum y < 0) {i : Fin m}
    (hi : A.Active i y) : A.value i (A.radialRepair p y) = 0 := by
  rw [A.radialRepair_value hp hy, (A.active_iff_minimum_eq i y).mp hi]
  simp

theorem AffineFamily.radialRepair_dist_le (A : AffineFamily d m) (p : State d)
    {y : State d} (hy : A.minimum y < 0) :
    dist y (A.radialRepair p y) ≤ -A.minimum y * dist y p := by
  obtain ⟨_, hb, hab⟩ := A.radialRepair_weights hy
  have hden : 0 < 1 - A.minimum y := by linarith
  have hfactor : -A.minimum y * (1 - A.minimum y)⁻¹ ≤ -A.minimum y := by
    have hi : (1 - A.minimum y)⁻¹ ≤ (1 : ℝ) := by
      rw [inv_le_one₀ hden]
      linarith
    exact (mul_le_mul_of_nonneg_left hi (by linarith)).trans_eq (mul_one _)
  have heq : y - A.radialRepair p y =
      (-A.minimum y * (1 - A.minimum y)⁻¹) • (y - p) := by
    ext j
    simp only [AffineFamily.radialRepair, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun z : ℝ => z * y j) hab]
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb, ← dist_eq_norm]
  exact mul_le_mul_of_nonneg_right hfactor dist_nonneg

end Endotactic
