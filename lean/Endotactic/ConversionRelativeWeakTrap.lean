import Endotactic.RelativeWeakFiniteClassTrap
import Endotactic.ConversionPermanence

/-!
# Conservative equality faces in an actual relative weak trap

Retain both inequalities for `x+y=s` in the family for `A ⇄ B`. They vanish
throughout the class, so no point in that class is strictly inside every face.
The moving lower faces have a strict relative anchor, and the new conserved
normalization yields actual global trapping and common permanence.
-/

namespace Endotactic.Conversion

open Set

noncomputable def augmentedFamily (α s : ℝ) : AffineFamily 2 4 where
  slope := ![![1, 0], ![0, 1], ![1, 1], ![-1, -1]]
  offset := ![-α, -α, -s, s]

theorem augmentedFamily_value (α s : ℝ) (i : Fin 4) (y : State 2) :
    (augmentedFamily α s).value i y =
      ![y 0 - α, y 1 - α, y 0 + y 1 - s, s - y 0 - y 1] i := by
  fin_cases i <;> simp [augmentedFamily, AffineFamily.value, dot, Fin.sum_univ_succ] <;> ring

theorem augmentedFamily_class_carrier (α : ℝ) (c : State 2) :
    (augmentedFamily α (c 0 + c 1)).plateau 0 ∩ conversion.stoichiometricClass c =
      (family α).plateau 0 ∩ conversion.stoichiometricClass c := by
  ext y
  constructor
  · rintro ⟨hy, hyC⟩
    refine ⟨?_, hyC⟩
    intro i
    fin_cases i
    · simpa [augmentedFamily_value, family_value] using hy 0
    · simpa [augmentedFamily_value, family_value] using hy 1
  · rintro ⟨hy, hyC⟩
    have hs := class_iff_total.mp hyC
    refine ⟨?_, hyC⟩
    intro i
    fin_cases i
    · simpa [augmentedFamily_value, family_value] using hy 0
    · simpa [augmentedFamily_value, family_value] using hy 1
    · simp [augmentedFamily_value, hs]
    · simp [augmentedFamily_value]; linarith

theorem augmentedFamily_conserved_faces {α : ℝ} {c y : State 2}
    (hy : y ∈ conversion.stoichiometricClass c) :
    (augmentedFamily α (c 0 + c 1)).value 2 y = 0 ∧
      (augmentedFamily α (c 0 + c 1)).value 3 y = 0 := by
  have hs := class_iff_total.mp hy
  constructor <;> simp [augmentedFamily_value] <;> linarith

theorem augmentedFamily_no_strict_class_anchor (α : ℝ) (c : State 2) :
    ¬ ∃ p ∈ conversion.stoichiometricClass c,
      ∀ i, 0 < (augmentedFamily α (c 0 + c 1)).value i p := by
  rintro ⟨p, hp, hs⟩
  have hh := hs 2
  rw [(augmentedFamily_conserved_faces hp).1] at hh
  exact lt_irrefl 0 hh

theorem negative_total_projection_zero (e : Fin 2) :
    conversion.projection ![-1, -1] e = 0 := by
  fin_cases e <;> norm_num [conversion, Network.projection, Network.vector,
    realComplex, dot, Fin.sum_univ_succ]

theorem augmentedFamily_relative_anchor {α : ℝ} (c : State 2)
    (hα : 0 < α) (hα4 : 4 * α ≤ c 0 + c 1) :
    conversion.ClassRelativeAnchor (augmentedFamily α (c 0 + c 1)) 0 c
      ![(c 0 + c 1) / 2, (c 0 + c 1) / 2] := by
  refine ⟨class_iff_total.mpr (by simp), ?_⟩
  intro i
  fin_cases i
  · right; simp [augmentedFamily_value]; linarith
  · right; simp [augmentedFamily_value]; linarith
  · left; exact total_projection_zero
  · left; exact negative_total_projection_zero

theorem augmentedFamily_weak_faces {α : ℝ} (c : State 2)
    (hα : 0 < α) (hα4 : 4 * α ≤ c 0 + c 1) :
    conversion.ClassWeakAffineFaceCertificate (augmentedFamily α (c 0 + c 1)) 1 2 0 c := by
  have hweak := conversion.classWeakAffineFaceCertificate_of_strict (family α)
    (family_face_certificate c hα hα4)
  intro i a ha y hy hf
  have hy' : y ∈ (family α).plateau 0 ∩ conversion.stoichiometricClass c := by
    rwa [augmentedFamily_class_carrier] at hy
  fin_cases i
  · have hf' : (family α).value 0 y = 0 := by simpa [family_value, augmentedFamily_value] using hf
    simpa [family, augmentedFamily] using hweak 0 a ha y hy' hf'
  · have hf' : (family α).value 1 y = 0 := by simpa [family_value, augmentedFamily_value] using hf
    simpa [family, augmentedFamily] using hweak 1 a ha y hy' hf'
  · change 0 ≤ dot (![1, 1] : State 2) (conversion.rhs a y)
    rw [conversion.dot_rhs_eq_zero_of_projections _ total_projection_zero]
  · change 0 ≤ dot (![-1, -1] : State 2) (conversion.rhs a y)
    rw [conversion.dot_rhs_eq_zero_of_projections _ negative_total_projection_zero]

noncomputable def augmentedInitialTrap {α : ℝ} (c : State 2)
    (hα : 0 < α) (hα4 : 4 * α ≤ c 0 + c 1) {z : State 2}
    (hz : z ∈ (family α).plateau 0 ∩ conversion.stoichiometricClass c) :
    conversion.RelativeWeakFiniteClassTrap 1 2 c z where
  branchCount := 4
  nonemptyBranches := inferInstance
  family := augmentedFamily α (c 0 + c 1)
  level := 0
  anchor := ![(c 0 + c 1) / 2, (c 0 + c 1) / 2]
  anchor_relative := augmentedFamily_relative_anchor c hα hα4
  initial_mem := by rw [augmentedFamily_class_carrier]; exact hz
  compact := by rw [augmentedFamily_class_carrier]; exact family_class_compact α c
  positive := by rw [augmentedFamily_class_carrier]; exact family_class_positive hα c
  faces := augmentedFamily_weak_faces c hα hα4

theorem augmentedInitialTrap_carrier {α : ℝ} (c : State 2)
    (hα : 0 < α) (hα4 : 4 * α ≤ c 0 + c 1) {z : State 2}
    (hz : z ∈ (family α).plateau 0 ∩ conversion.stoichiometricClass c) :
    (augmentedInitialTrap c hα hα4 hz).carrier =
      (family α).plateau 0 ∩ conversion.stoichiometricClass c :=
  augmentedFamily_class_carrier α c

theorem integralSolution_mem_augmented_trap {α : ℝ} (c : State 2)
    (hα : 0 < α) (hα4 : 4 * α ≤ c 0 + c 1) {z : State 2}
    (hz : z ∈ (family α).plateau 0 ∩ conversion.stoichiometricClass c)
    {k : Fin 2 → ℝ → ℝ} (hk : AdmissibleRates k 1 2)
    {x : ℝ → State 2} (hx : conversion.IsIntegralSolution k z x) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ (augmentedFamily α (c 0 + c 1)).plateau 0 ∩ conversion.stoichiometricClass c :=
  (augmentedInitialTrap c hα hα4 hz).integralSolution_mem hk hx ht

theorem uniformPermanent_via_relative_weak_traps (c : State 2) (hs : 0 < c 0 + c 1) :
    conversion.UniformPermanent 1 2 c (fun _ => True) := by
  let s : ℝ := c 0 + c 1
  have hs' : 0 < s := hs
  have hne : ((absorbingFamily s).plateau 0 ∩ conversion.stoichiometricClass c).Nonempty := by
    rw [absorbingFamily_plateau]
    refine ⟨![s / 2, s / 2], ?_, ?_⟩
    · intro i; fin_cases i <;> simp [family_value] <;> linarith
    · apply class_iff_total.mpr
      simp [s]
  apply conversion.uniformPermanent_of_relative_weak_finite_class_traps (absorbingFamily s)
    1 2 0 c (fun _ => True) hne
    (by rw [absorbingFamily_plateau]; exact family_class_compact _ _)
    (by rw [absorbingFamily_plateau]; exact family_class_positive (by linarith) c)
  intro z hz
  let α : ℝ := min (min (z 0) (z 1)) (s / 4)
  have hα : 0 < α := lt_min (lt_min (hz.1 0) (hz.1 1)) (by linarith)
  have hα0 : α ≤ z 0 := (min_le_left _ _).trans (min_le_left _ _)
  have hα1 : α ≤ z 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hα4 : 4 * α ≤ c 0 + c 1 := by
    have hh : α ≤ s / 4 := min_le_right _ _
    dsimp [s] at hh
    linarith
  have hzA : z ∈ (family α).plateau 0 ∩ conversion.stoichiometricClass c := by
    refine ⟨?_, hz.2⟩
    intro i; fin_cases i <;> simp [family_value] <;> linarith
  let T := augmentedInitialTrap c hα hα4 hzA
  refine ⟨T, ?_⟩
  intro a ha y hy hm i hai
  have htotal : y 0 + y 1 = s := class_iff_total.mp hy.2
  exact lt_of_lt_of_le (by linarith : 0 < s / 4)
    (absorbingFamily_flux_margin s a ha y (T.positive hy) htotal hm i hai)

end Endotactic.Conversion
