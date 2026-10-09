import Endotactic.ConversionRelativeWeakTrap

/-!
# Kernel-check the exact rational anchor discovery example

The external enumerator finds moving-face witnesses `(3/4,1/4)` and
`(1/4,3/4)` and the relative anchor `(3/8,5/8)` for total one. The two total
faces remain equalities. These declarations verify those actual numbers and
use the face-witness theorem to construct global solutions. JSON is not a proof.
-/

namespace Endotactic.Conversion.DiscoveredAnchor

open Set

theorem relative_anchor :
    conversion.ClassRelativeAnchor (augmentedFamily (1 / 4) 1) 0
      (![1 / 2, 1 / 2] : State 2) ![3 / 8, 5 / 8] := by
  refine ⟨class_iff_total.mpr (by norm_num), ?_⟩
  intro i
  fin_cases i
  · right; norm_num [augmentedFamily_value]
  · right; norm_num [augmentedFamily_value]
  · left; exact total_projection_zero
  · left; exact negative_total_projection_zero

theorem face_witnesses :
    ∀ i, (∀ e, conversion.projection ((augmentedFamily (1 / 4) 1).slope i) e = 0) ∨
      ∃ y ∈ (augmentedFamily (1 / 4) 1).plateau 0 ∩
        conversion.stoichiometricClass (![1 / 2, 1 / 2] : State 2),
        0 < (augmentedFamily (1 / 4) 1).value i y := by
  intro i
  fin_cases i
  · right
    refine ⟨![3 / 4, 1 / 4], ⟨?_, class_iff_total.mpr (by norm_num)⟩, ?_⟩
    · intro j; fin_cases j <;> norm_num [augmentedFamily_value]
    · norm_num [augmentedFamily_value]
  · right
    refine ⟨![1 / 4, 3 / 4], ⟨?_, class_iff_total.mpr (by norm_num)⟩, ?_⟩
    · intro j; fin_cases j <;> norm_num [augmentedFamily_value]
    · norm_num [augmentedFamily_value]
  · left; exact total_projection_zero
  · left; exact negative_total_projection_zero

theorem class_carrier :
    (augmentedFamily (1 / 4) 1).plateau 0 ∩
      conversion.stoichiometricClass (![1 / 2, 1 / 2] : State 2) =
    (family (1 / 4)).plateau 0 ∩
      conversion.stoichiometricClass (![1 / 2, 1 / 2] : State 2) := by
  have h := augmentedFamily_class_carrier (1 / 4) (![1 / 2, 1 / 2] : State 2)
  norm_num at h
  exact h

theorem exists_global_positive_from_face_witnesses {k : Fin 2 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 2}
    (hz : z ∈ (augmentedFamily (1 / 4) 1).plateau 0 ∩
      conversion.stoichiometricClass (![1 / 2, 1 / 2] : State 2)) :
    ∃ x, conversion.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ (augmentedFamily (1 / 4) 1).plateau 0 ∩
        conversion.stoichiometricClass (![1 / 2, 1 / 2] : State 2) := by
  apply conversion.exists_global_positive_of_weak_face_witnesses hk
    (augmentedFamily (1 / 4) 1) (![1 / 2, 1 / 2] : State 2)
  · rw [class_carrier]; exact family_class_compact _ _
  · rw [class_carrier]; exact family_class_positive (by norm_num) _
  · have h := augmentedFamily_weak_faces (![1 / 2, 1 / 2] : State 2)
      (α := 1 / 4) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  · exact face_witnesses
  · exact hz

end Endotactic.Conversion.DiscoveredAnchor
