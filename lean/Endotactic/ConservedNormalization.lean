import Endotactic.WeakClassFaceTrap
import Endotactic.ClassDualBounds

/-!
# Conserved faces need no strictly feasible anchor

On a fixed stoichiometric class, a zero-projection branch is constant. If the
original carrier is nonempty, that constraint is feasible throughout the class.
Replace it by the constant one and normalize only the moving branches. The
class carrier is unchanged and the existing weak-face trap theorem applies.

A relative anchor is strict only on nonconserved branches. Its existence is
still a geometric obligation; per-face feasible witnesses can construct it by
repeated midpoints. This is not an all-endotactic geometry existence theorem.
-/

namespace Endotactic

open Set
open scoped Classical

variable {d m : ℕ} {E : Type*}

theorem Network.affine_value_eq_in_class (N : Network d E) (A : AffineFamily d m)
    {x c : State d} (hx : x ∈ N.stoichiometricClass c) {i : Fin m}
    (hi : ∀ e, N.projection (A.slope i) e = 0) : A.value i x = A.value i c := by
  unfold AffineFamily.value
  rw [N.dot_eq_in_stoichiometricClass _ hx hi]

theorem Network.conserved_faces_feasible (N : Network d E) (A : AffineFamily d m)
    {M : ℝ} {c : State d} (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty) :
    ∀ i, (∀ e, N.projection (A.slope i) e = 0) → M ≤ A.value i c := by
  obtain ⟨x, hx, hxC⟩ := hne
  intro i hi
  rw [← N.affine_value_eq_in_class A hxC hi]
  exact hx i

def Network.ClassRelativeAnchor (N : Network d E) (A : AffineFamily d m)
    (M : ℝ) (c p : State d) : Prop :=
  p ∈ N.stoichiometricClass c ∧
    ∀ i, (∀ e, N.projection (A.slope i) e = 0) ∨ M < A.value i p

noncomputable def Network.classNormalizeAt (N : Network d E) (A : AffineFamily d m)
    (M : ℝ) (p : State d) : AffineFamily d m := by
  classical
  exact {
    slope := fun i => if ∀ e, N.projection (A.slope i) e = 0 then 0
      else (A.normalizeAt M p).slope i
    offset := fun i => if ∀ e, N.projection (A.slope i) e = 0 then 1
      else (A.normalizeAt M p).offset i }

theorem Network.classNormalizeAt_value (N : Network d E) (A : AffineFamily d m)
    (M : ℝ) (p x : State d) (i : Fin m) :
    (N.classNormalizeAt A M p).value i x =
      if ∀ e, N.projection (A.slope i) e = 0 then 1 else (A.normalizeAt M p).value i x := by
  classical
  by_cases hi : ∀ e, N.projection (A.slope i) e = 0
  · simp [Network.classNormalizeAt, AffineFamily.value, hi, dot]
  · simp [Network.classNormalizeAt, AffineFamily.value, hi]

theorem Network.classNormalizeAt_dot (N : Network d E) (A : AffineFamily d m)
    (M : ℝ) (p v : State d) (i : Fin m) :
    dot ((N.classNormalizeAt A M p).slope i) v =
      if ∀ e, N.projection (A.slope i) e = 0 then 0
      else (A.value i p - M)⁻¹ * dot (A.slope i) v := by
  classical
  by_cases hi : ∀ e, N.projection (A.slope i) e = 0
  · simp [Network.classNormalizeAt, hi, dot]
  · simp only [Network.classNormalizeAt, hi, if_false]
    exact A.normalizeAt_dot M p v i

theorem Network.classNormalizeAt_anchor (N : Network d E) (A : AffineFamily d m)
    {M : ℝ} {c p : State d} (hp : N.ClassRelativeAnchor A M c p) (i : Fin m) :
    (N.classNormalizeAt A M p).value i p = 1 := by
  classical
  rw [N.classNormalizeAt_value]
  split_ifs with hi
  · rfl
  · have hs := (hp.2 i).resolve_left hi
    rw [A.normalizeAt_value, inv_mul_cancel₀ (sub_pos.mpr hs).ne']

theorem Network.classNormalizeAt_class_plateau (N : Network d E) (A : AffineFamily d m)
    {M : ℝ} {c p : State d} (hp : N.ClassRelativeAnchor A M c p)
    (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty) :
    (N.classNormalizeAt A M p).plateau 0 ∩ N.stoichiometricClass c =
      A.plateau M ∩ N.stoichiometricClass c := by
  classical
  have hfeas := N.conserved_faces_feasible A hne
  ext x
  constructor
  · rintro ⟨hx, hxC⟩
    refine ⟨?_, hxC⟩
    intro i
    by_cases hi : ∀ e, N.projection (A.slope i) e = 0
    · rw [N.affine_value_eq_in_class A hxC hi]
      exact hfeas i hi
    · have hh := hx i
      rw [N.classNormalizeAt_value, if_neg hi, A.normalizeAt_value] at hh
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left
        (inv_pos.mpr (sub_pos.mpr ((hp.2 i).resolve_left hi)))).mp hh)
  · rintro ⟨hx, hxC⟩
    refine ⟨?_, hxC⟩
    intro i
    rw [N.classNormalizeAt_value]
    split_ifs with hi
    · norm_num
    · rw [A.normalizeAt_value]
      exact mul_nonneg (inv_pos.mpr (sub_pos.mpr ((hp.2 i).resolve_left hi))).le
        (sub_nonneg.mpr (hx i))

theorem Network.classRelativeAnchor_mem (N : Network d E) (A : AffineFamily d m)
    {M : ℝ} {c p : State d} (hp : N.ClassRelativeAnchor A M c p)
    (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty) :
    p ∈ A.plateau M ∩ N.stoichiometricClass c := by
  refine ⟨?_, hp.1⟩
  intro i
  rcases hp.2 i with hi | hs
  · rw [N.affine_value_eq_in_class A hp.1 hi]
    exact N.conserved_faces_feasible A hne i hi
  · exact hs.le

theorem Network.exists_classRelativeAnchor_of_face_witnesses (N : Network d E)
    (A : AffineFamily d m) {M : ℝ} {c : State d}
    (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty)
    (hw : ∀ i, (∀ e, N.projection (A.slope i) e = 0) ∨
      ∃ x ∈ A.plateau M ∩ N.stoichiometricClass c, M < A.value i x) :
    ∃ p ∈ A.plateau M ∩ N.stoichiometricClass c, N.ClassRelativeAnchor A M c p := by
  classical
  have hc : Convex ℝ (A.plateau M ∩ N.stoichiometricClass c) :=
    (A.plateau_convex M).inter (N.stoichiometricClass_convex c)
  have hbuild : ∀ s : Finset (Fin m), ∃ p ∈ A.plateau M ∩ N.stoichiometricClass c,
      ∀ i ∈ s, (∀ e, N.projection (A.slope i) e = 0) ∨ M < A.value i p := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨p, hp⟩ := hne
      exact ⟨p, hp, by simp⟩
    | @insert i s _ ih =>
      obtain ⟨p, hp, hs⟩ := ih
      rcases hw i with hi | ⟨q, hq, hqi⟩
      · refine ⟨p, hp, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact Or.inl hi
        · exact hs j hj
      · let r : State d := (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q
        have hr : r ∈ A.plateau M ∩ N.stoichiometricClass c :=
          hc hp hq (by norm_num) (by norm_num) (by norm_num)
        refine ⟨r, hr, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · right
          rw [A.value_convex_combination j p q (by norm_num)]
          linarith [hp.1 j]
        · rcases hs j hj with hjzero | hjstrict
          · exact Or.inl hjzero
          · right
            rw [A.value_convex_combination j p q (by norm_num)]
            linarith [hq.1 j]
  obtain ⟨p, hp, hs⟩ := hbuild Finset.univ
  exact ⟨p, hp, hp.2, fun i => hs i (Finset.mem_univ i)⟩

variable [Fintype E]

theorem Network.classWeakAffineFaceCertificate_classNormalizeAt (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} {c p : State d}
    (hp : N.ClassRelativeAnchor A M c p)
    (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty)
    (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u M c) :
    N.ClassWeakAffineFaceCertificate (N.classNormalizeAt A M p) ℓ u 0 c := by
  classical
  intro i a ha y hy hf
  have hy' : y ∈ A.plateau M ∩ N.stoichiometricClass c := by
    rwa [N.classNormalizeAt_class_plateau A hp hne] at hy
  rw [N.classNormalizeAt_dot]
  split_ifs with hi
  · norm_num
  · have hs := (hp.2 i).resolve_left hi
    rw [N.classNormalizeAt_value, if_neg hi, A.normalizeAt_value] at hf
    have heq := (mul_eq_zero.mp hf).resolve_left (inv_ne_zero (sub_pos.mpr hs).ne')
    exact mul_nonneg (inv_pos.mpr (sub_pos.mpr hs)).le
      (hfaces i a ha y hy' (sub_eq_zero.mp heq))

variable [Nonempty (Fin m)]

theorem Network.exists_global_positive_of_relative_weak_class_faces (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} (c p : State d)
    (hp : N.ClassRelativeAnchor A M c p)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u M c)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ A.plateau M ∩ N.stoichiometricClass c := by
  have hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty := ⟨z, hz⟩
  have heq := N.classNormalizeAt_class_plateau A hp hne
  simpa only [heq] using N.exists_global_positive_of_normalized_weak_class_faces hk
    (N.classNormalizeAt A M p) c p (N.classNormalizeAt_anchor A hp) hp.1
    (by simpa only [heq] using hK) (by simpa only [heq] using hpos)
    (N.classWeakAffineFaceCertificate_classNormalizeAt A hp hne hfaces)
    (by simpa only [heq] using hz)

theorem Network.exists_global_positive_of_weak_face_witnesses (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} (c : State d)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u M c)
    (hw : ∀ i, (∀ e, N.projection (A.slope i) e = 0) ∨
      ∃ y ∈ A.plateau M ∩ N.stoichiometricClass c, M < A.value i y)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ A.plateau M ∩ N.stoichiometricClass c := by
  obtain ⟨p, _, hp⟩ := N.exists_classRelativeAnchor_of_face_witnesses A ⟨z, hz⟩ hw
  exact N.exists_global_positive_of_relative_weak_class_faces hk A c p hp hK hpos hfaces hz

end Endotactic
