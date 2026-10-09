import Endotactic.FiniteClassTrap
import Endotactic.ConversionPermanence

/-!
# The finite class-trap / compact-margin route on a conservative network

Supply the known lower-face family and conserved-direction dual witness for
each positive initial state of `A ⇄ B`. The new assembly derives existence,
uniqueness and common compact absorption without an explicitly supplied margin
or a cap hypothesis. The original exact-segment absorption theorem is retained
in `ConversionPermanence`.
-/

namespace Endotactic.Conversion

open Set

theorem uniformPermanent_via_finite_traps (c : State 2) (hs : 0 < c 0 + c 1) :
    conversion.UniformPermanent 1 2 c (fun _ => True) := by
  let s : ℝ := c 0 + c 1
  have hs' : 0 < s := hs
  have hne : ((absorbingFamily s).plateau 0 ∩ conversion.stoichiometricClass c).Nonempty := by
    rw [absorbingFamily_plateau]
    refine ⟨![s / 2, s / 2], ?_, ?_⟩
    · intro i; fin_cases i <;> simp [family_value] <;> linarith
    · apply class_iff_total.mpr
      simp [s]
  apply conversion.uniformPermanent_of_finite_class_traps (absorbingFamily s) 1 2 0 c
    (fun _ => True) hne
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
  let T : conversion.FiniteClassTrap 1 2 c z :=
    conversion.finiteClassTrap_of_dual_certificate (family α) (familyBoxCertificate α c)
      (by intro i; fin_cases i <;> exact hα) (family_face_certificate c hα hα4) hzA
  refine ⟨T, ?_⟩
  intro a ha y hy hm i hi
  have htotal : y 0 + y 1 = s := class_iff_total.mp hy.2
  have hb := absorbingFamily_flux_margin s a ha y (T.positive hy) htotal hm i hi
  exact lt_of_lt_of_le (by linarith : 0 < s / 4) hb

end Endotactic.Conversion
