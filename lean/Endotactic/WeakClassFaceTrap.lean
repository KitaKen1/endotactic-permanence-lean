import Endotactic.AffineNormalization
import Endotactic.LinearDeficitBarrier
import Endotactic.ClassFaceTrap
import Endotactic.UniformKinetics

/-!
# Nonstrict class faces with a strictly feasible anchor

Normalize the faces to value one at an interior anchor. Radial repair sends
an exterior active branch to its own boundary face within the class and box.
Uniform Lipschitz estimates bound negative flux by a constant times the affine
deficit. The AC linear-deficit barrier then preserves the original plateau.

Faces may have zero flux without being conserved. A strictly feasible anchor
is required; lower-dimensional traps without such an anchor are not covered.
No existence theorem for the general endotactic trapping geometry is asserted.
-/

namespace Endotactic

open Set
open scoped NNReal

variable {d m : ℕ} {E : Type*} [Fintype E]

def Network.ClassWeakAffineFaceCertificate (N : Network d E) (A : AffineFamily d m)
    (ℓ u M : ℝ) (c : State d) : Prop :=
  ∀ i, ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
    ∀ y ∈ A.plateau M ∩ N.stoichiometricClass c,
      A.value i y = M → 0 ≤ dot (A.slope i) (N.rhs a y)

theorem Network.classWeakAffineFaceCertificate_of_strict (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} {c : State d}
    (hfaces : N.ClassAffineFaceCertificate A ℓ u M c) :
    N.ClassWeakAffineFaceCertificate A ℓ u M c := by
  intro i a ha y hy hface
  rcases hfaces i with hz | hs
  · rw [hz]
  · exact (hs a ha y hy hface).le

theorem Network.classWeakAffineFaceCertificate_normalizeAt (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} {c p : State d}
    (hp : ∀ i, M < A.value i p)
    (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u M c) :
    N.ClassWeakAffineFaceCertificate (A.normalizeAt M p) ℓ u 0 c := by
  intro i a ha y hy hf
  have hy' : y ∈ A.plateau M ∩ N.stoichiometricClass c := by
    simpa only [A.normalizeAt_plateau hp] using hy
  have hf' : A.value i y = M := by
    rw [A.normalizeAt_value] at hf
    have hh := (mul_eq_zero.mp hf).resolve_left (inv_ne_zero (sub_pos.mpr (hp i)).ne')
    exact sub_eq_zero.mp hh
  rw [A.normalizeAt_dot]
  exact mul_nonneg (inv_pos.mpr (sub_pos.mpr (hp i))).le (hfaces i a ha y hy' hf')

variable [Nonempty (Fin m)]

theorem Network.exists_normalized_face_deficit_bound (N : Network d E)
    (A : AffineFamily d m) (ℓ u : ℝ) (c p lo hi : State d)
    (hp : ∀ i, A.value i p = 1) (hpC : p ∈ N.stoichiometricClass c)
    (hpB : p ∈ Icc lo hi)
    (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u 0 c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ Icc lo hi ∩ N.stoichiometricClass c,
        A.minimum y < 0 → ∀ i, A.Active i y →
          C * A.minimum y ≤ dot (A.slope i) (N.rhs a y) := by
  obtain ⟨L, hL⟩ := N.rhs_uniform_lipschitzOn_box (fun _ => ℓ) (fun _ => u) lo hi
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn (fun y : State d => dist y p) (Icc lo hi) from
      (continuous_id.dist continuous_const).continuousOn)
  have hR0 : 0 ≤ R := by simpa only [dist_self, norm_zero] using hR p hpB
  have hdist : ∀ y ∈ Icc lo hi, dist y p ≤ R := by
    intro y hy
    simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hR y hy
  let S : ℝ := ∑ j : Fin m, ‖dotCLM (A.slope j)‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let C : ℝ := S * (L : ℝ) * R
  refine ⟨C, mul_nonneg (mul_nonneg hS L.coe_nonneg) hR0, ?_⟩
  intro a ha y hy hn i hai
  let q := A.radialRepair p y
  have hqB : q ∈ Icc lo hi := A.radialRepair_mem_convex (convex_Icc _ _) hpB hy.1 hn
  have hqC : q ∈ N.stoichiometricClass c :=
    A.radialRepair_mem_convex (N.stoichiometricClass_convex c) hpC hy.2 hn
  have hqK : q ∈ A.plateau 0 := A.radialRepair_mem_plateau hp hn
  have hqface : A.value i q = 0 := A.radialRepair_active_face hp hn hai
  have hflux := hfaces i a ha q ⟨hqK, hqC⟩ hqface
  have hnorm : ‖dotCLM (A.slope i)‖ ≤ S :=
    Finset.single_le_sum (fun j _ => norm_nonneg (dotCLM (A.slope j))) (Finset.mem_univ i)
  have hrepair : dist y q ≤ -A.minimum y * R :=
    (A.radialRepair_dist_le p hn).trans
      (mul_le_mul_of_nonneg_left (hdist y hy.1) (by linarith))
  have hd : dist (dot (A.slope i) (N.rhs a y)) (dot (A.slope i) (N.rhs a q)) ≤
      -(C * A.minimum y) := by
    calc
      _ ≤ ‖dotCLM (A.slope i)‖ * dist (N.rhs a y) (N.rhs a q) :=
        (dotCLM (A.slope i)).dist_le_opNorm _ _
      _ ≤ ‖dotCLM (A.slope i)‖ * ((L : ℝ) * dist y q) :=
        mul_le_mul_of_nonneg_left ((hL a ha).dist_le_mul y hy.1 q hqB) (norm_nonneg _)
      _ ≤ S * ((L : ℝ) * dist y q) :=
        mul_le_mul_of_nonneg_right hnorm (mul_nonneg L.coe_nonneg dist_nonneg)
      _ ≤ S * ((L : ℝ) * (-A.minimum y * R)) := by
        gcongr
      _ = -(C * A.minimum y) := by dsimp [C]; ring
  rw [Real.dist_eq] at hd
  linarith [(abs_le.mp hd).1]

theorem Network.exists_global_positive_of_normalized_weak_class_faces (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) (c p : State d)
    (hp : ∀ i, A.value i p = 1) (hpC : p ∈ N.stoichiometricClass c)
    (hK : IsCompact (A.plateau 0 ∩ N.stoichiometricClass c))
    (hpos : A.plateau 0 ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u 0 c)
    {z : State d} (hz : z ∈ A.plateau 0 ∩ N.stoichiometricClass c) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ A.plateau 0 ∩ N.stoichiometricClass c := by
  obtain ⟨ε, lo, hi, hε, hbox, hlo, hsub⟩ :=
    A.exists_enlarged_positive_box_inter (N.stoichiometricClass_isClosed c)
      (N.stoichiometricClass_convex c) ⟨z, hz⟩ hK hpos
  have hpB : p ∈ Icc lo hi := hsub ⟨fun i => by rw [hp i]; linarith, hpC⟩
  obtain ⟨C, hC, hb⟩ := N.exists_normalized_face_deficit_bound A ℓ u c p lo hi hp hpC hpB hfaces
  obtain ⟨x, _, hx⟩ := N.exists_global_cutoff_integralSolution hk lo hi hbox z
  have hclass : ∀ t, 0 ≤ t → x t ∈ N.stoichiometricClass c :=
    fun t ht => hx.mem_stoichiometricClass N
      (fun s _ y => N.cutoffRhs_mem_stoichiometricSubspace k lo hi s y) hz.2 ht
  have hstay := hx.mem_affine_plateau_of_linear_deficit A hC hε hz.1 (by
    intro t ht hl hu i hai
    have hy : x t ∈ Icc lo hi := hsub
      ⟨(A.mem_plateau_iff_minimum_ge (x t) (0 - ε)).mpr hl.le, hclass t ht⟩
    rw [N.cutoffRhs_eq k lo hi ht hy, sub_zero]
    exact hb _ ⟨fun e => (hk.2 e t ht).1, fun e => (hk.2 e t ht).2⟩
      (x t) ⟨hy, hclass t ht⟩ hu i hai)
  have hxB : ∀ t, 0 ≤ t → x t ∈ Icc lo hi := by
    intro t ht
    exact hsub ⟨fun i => (by linarith : 0 - ε ≤ 0).trans (hstay t ht i), hclass t ht⟩
  have hactual : N.IsIntegralSolution k z x := hx.congr_field
    (fun t ht => N.cutoffRhs_eq k lo hi ht (hxB t ht))
  exact ⟨x, ⟨hactual, fun t ht i => (hlo i).trans_le ((hxB t ht).1 i)⟩,
    fun t ht => ⟨hstay t ht, hclass t ht⟩⟩

theorem Network.exists_global_positive_of_weak_class_faces (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} (c p : State d)
    (hp : ∀ i, M < A.value i p) (hpC : p ∈ N.stoichiometricClass c)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u M c)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ A.plateau M ∩ N.stoichiometricClass c := by
  have heq := A.normalizeAt_plateau hp
  simpa only [heq] using N.exists_global_positive_of_normalized_weak_class_faces hk
    (A.normalizeAt M p) c p (A.normalizeAt_anchor hp) hpC
    (by simpa only [heq] using hK) (by simpa only [heq] using hpos)
    (N.classWeakAffineFaceCertificate_normalizeAt A hp hfaces) (by simpa only [heq] using hz)

theorem Network.positiveWellPosed_of_weak_class_faces (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} (c p : State d)
    (hp : ∀ i, M < A.value i p) (hpC : p ∈ N.stoichiometricClass c)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u M c)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    N.PositiveWellPosed k z := by
  obtain ⟨x, hx, _⟩ := N.exists_global_positive_of_weak_class_faces hk A c p hp hpC hK hpos hfaces hz
  exact N.positiveWellPosed_of_exists hk ⟨x, hx⟩

end Endotactic
