import Endotactic.ClassDualBounds

/-!
# Complete measurable-rate permanence of the conservative conversion A ⇄ B

The full plateau `x ≥ α, y ≥ α` is unbounded. Its intersection with the
conserved class `x+y=s` is a positive compact segment. Nonnegative dual weights
plus the conserved normal `(1,1)` certify its upper bounds. Class-restricted
strict faces then give positive global existence for every positive initial
point. The known common target `x,y ≥ s/4` absorbs every positive trajectory
for all measurable rates in `[1,2]`, with active-branch margin `s/4`.

This exercises genuinely class-relative trapping; no full ambient compact
plateau and no explicit solution of the measurable linear equation are used.
-/

namespace Endotactic.Conversion

open Set

def conversion : Network 2 (Fin 2) where
  source := ![![1, 0], ![0, 1]]
  target := ![![0, 1], ![1, 0]]

theorem isEndotactic : conversion.IsEndotactic := by
  intro r e he
  fin_cases e
  · refine ⟨1, ?_, ?_⟩ <;>
      simp [conversion, Network.projection, Network.sourceLevel, Network.vector,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith
  · refine ⟨0, ?_, ?_⟩ <;>
      simp [conversion, Network.projection, Network.sourceLevel, Network.vector,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith

theorem total_projection_zero (e : Fin 2) : conversion.projection ![1, 1] e = 0 := by
  fin_cases e <;> norm_num [conversion, Network.projection, Network.vector,
    realComplex, dot, Fin.sum_univ_succ]

theorem class_iff_total {y c : State 2} :
    y ∈ conversion.stoichiometricClass c ↔ y 0 + y 1 = c 0 + c 1 := by
  constructor
  · intro hy
    have hh := conversion.dot_eq_in_stoichiometricClass ![1, 1] hy total_projection_zero
    simpa [dot, Fin.sum_univ_succ] using hh
  · intro hs
    change y - c ∈ conversion.stoichiometricSubspace
    have heq : y - c = (y 1 - c 1) • conversion.vector 0 := by
      ext i
      fin_cases i <;> simp [conversion, Network.vector, realComplex]
      linarith
    rw [heq]
    exact conversion.stoichiometricSubspace.smul_mem _ (Submodule.subset_span ⟨0, rfl⟩)

theorem rhs_at (a : Fin 2 → ℝ) (y : State 2) :
    conversion.rhs a y 0 = -a 0 * y 0 + a 1 * y 1 ∧
      conversion.rhs a y 1 = a 0 * y 0 - a 1 * y 1 := by
  constructor <;> simp [conversion, Network.rhs, monomial, Network.vector,
    realComplex, Fin.sum_univ_succ]
  ring

noncomputable def family (α : ℝ) : AffineFamily 2 2 where
  slope := ![![1, 0], ![0, 1]]
  offset := ![-α, -α]

theorem family_value (α : ℝ) (i : Fin 2) (y : State 2) :
    (family α).value i y = ![y 0 - α, y 1 - α] i := by
  fin_cases i <;> simp [family, AffineFamily.value, dot, Fin.sum_univ_succ] <;> ring

noncomputable def familyBoxCertificate (α : ℝ) (c : State 2) :
    conversion.ClassBoxCertificate (family α) 0 c
      (![α, α] : State 2) ![c 0 + c 1 - α, c 0 + c 1 - α] where
  lowerWeight := ![![1, 0], ![0, 1]]
  upperWeight := ![![0, 1], ![1, 0]]
  lowerConserved := fun _ => 0
  upperConserved := fun _ => ![1, 1]
  lower_nonneg := by intro j i; fin_cases j <;> fin_cases i <;> norm_num
  upper_nonneg := by intro j i; fin_cases j <;> fin_cases i <;> norm_num
  lower_zero := by intro j e; simp [Network.projection, dot]
  upper_zero := fun _ => total_projection_zero
  lower_coordinate := by
    intro j k
    fin_cases j <;> fin_cases k <;> norm_num [family, Fin.sum_univ_succ]
  upper_coordinate := by
    intro j k
    fin_cases j <;> fin_cases k <;> norm_num [family, Fin.sum_univ_succ]
  lower_bound := by
    intro j
    fin_cases j <;> simp [family, dot, Fin.sum_univ_succ]
  upper_bound := by
    intro j
    fin_cases j <;> simp [family, dot, Fin.sum_univ_succ, sub_eq_add_neg, add_comm]

theorem family_class_box (α : ℝ) (c : State 2) :
    (family α).plateau 0 ∩ conversion.stoichiometricClass c ⊆
      Icc (![α, α] : State 2) ![c 0 + c 1 - α, c 0 + c 1 - α] :=
  (familyBoxCertificate α c).class_plateau_subset_box conversion (family α)

theorem family_class_compact (α : ℝ) (c : State 2) :
    IsCompact ((family α).plateau 0 ∩ conversion.stoichiometricClass c) :=
  (familyBoxCertificate α c).isCompact conversion (family α)

theorem family_class_positive {α : ℝ} (hα : 0 < α) (c : State 2) :
    (family α).plateau 0 ∩ conversion.stoichiometricClass c ⊆ {y | Positive y} :=
  (familyBoxCertificate α c).positive conversion (family α) (by
    intro i; fin_cases i <;> exact hα)

theorem family_face_certificate {α : ℝ} (c : State 2)
    (hα : 0 < α) (hα4 : 4 * α ≤ c 0 + c 1) :
    conversion.ClassAffineFaceCertificate (family α) 1 2 0 c := by
  intro i
  right
  intro a ha y hy he
  have hs := class_iff_total.mp hy.2
  fin_cases i
  · have hx : y 0 = α := by
      have hh : y 0 - α = 0 := by simpa [family_value] using he
      linarith
    have hy0 : 0 ≤ y 1 := by linarith
    have hu := mul_le_mul_of_nonneg_right (ha.2 0) hα.le
    have hl := mul_le_mul_of_nonneg_right (ha.1 1) hy0
    change 0 < dot ((family α).slope 0) (conversion.rhs a y)
    simp [family, dot, Fin.sum_univ_succ]
    rw [(rhs_at a y).1, hx]
    nlinarith
  · have hy' : y 1 = α := by
      have hh : y 1 - α = 0 := by simpa [family_value] using he
      linarith
    have hx0 : 0 ≤ y 0 := by linarith
    have hu := mul_le_mul_of_nonneg_right (ha.2 1) hα.le
    have hl := mul_le_mul_of_nonneg_right (ha.1 0) hx0
    change 0 < dot ((family α).slope 1) (conversion.rhs a y)
    simp [family, dot, Fin.sum_univ_succ]
    rw [(rhs_at a y).2, hy']
    nlinarith

theorem exists_global_positive {k : Fin 2 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 2} (hz : Positive z) :
    ∃ x, conversion.IsGlobalPositiveSolution k z x := by
  let α : ℝ := min (min (z 0) (z 1)) ((z 0 + z 1) / 4)
  have hα : 0 < α := lt_min (lt_min (hz 0) (hz 1)) (by linarith [hz 0, hz 1])
  have hα0 : α ≤ z 0 := (min_le_left _ _).trans (min_le_left _ _)
  have hα1 : α ≤ z 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hα4 : 4 * α ≤ z 0 + z 1 := by linarith [min_le_right (min (z 0) (z 1)) ((z 0 + z 1) / 4)]
  have hzA : z ∈ (family α).plateau 0 ∩ conversion.stoichiometricClass z := by
    constructor
    · intro i; fin_cases i <;> simp [family_value] <;> linarith
    · exact class_iff_total.mpr rfl
  obtain ⟨x, hx, _⟩ := conversion.exists_global_positive_of_class_affine_certificates hk
    (family α) (familyBoxCertificate α z)
    (by intro i; fin_cases i <;> exact hα) (family_face_certificate z hα hα4) hzA
  exact ⟨x, hx⟩

theorem positiveWellPosed {k : Fin 2 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 2} (hz : Positive z) :
    conversion.PositiveWellPosed k z :=
  conversion.positiveWellPosed_of_exists hk (exists_global_positive hk hz)

noncomputable def absorbingFamily (s : ℝ) : AffineFamily 2 3 where
  slope := ![![1, 0], ![0, 1], ![0, 0]]
  offset := ![-s / 4, -s / 4, 0]

theorem absorbingFamily_value (s : ℝ) (i : Fin 3) (y : State 2) :
    (absorbingFamily s).value i y = ![y 0 - s / 4, y 1 - s / 4, 0] i := by
  fin_cases i <;> simp [absorbingFamily, AffineFamily.value, dot, Fin.sum_univ_succ] <;> ring

theorem absorbingFamily_plateau (s : ℝ) :
    (absorbingFamily s).plateau 0 = (family (s / 4)).plateau 0 := by
  ext y
  constructor
  · intro hy i
    fin_cases i
    · simpa [family_value, absorbingFamily_value] using hy 0
    · simpa [family_value, absorbingFamily_value] using hy 1
  · intro hy i
    fin_cases i
    · simpa [family_value, absorbingFamily_value] using hy 0
    · simpa [family_value, absorbingFamily_value] using hy 1
    · simp [absorbingFamily_value]

theorem absorbingFamily_cap (s : ℝ) (y : State 2) : (absorbingFamily s).minimum y ≤ 0 := by
  have hh := finiteMinimum_le (fun i => (absorbingFamily s).value i y) 2
  simpa [AffineFamily.minimum, absorbingFamily_value] using hh

theorem absorbingFamily_flux_margin (s : ℝ) (a : Fin 2 → ℝ)
    (ha : a ∈ Icc (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ))) (y : State 2)
    (hy : Positive y) (htotal : y 0 + y 1 = s)
    (hbelow : (absorbingFamily s).minimum y < 0) (i : Fin 3)
    (hai : (absorbingFamily s).Active i y) :
    s / 4 ≤ dot ((absorbingFamily s).slope i) (conversion.rhs a y) := by
  have heq := ((absorbingFamily s).active_iff_minimum_eq i y).mp hai
  fin_cases i
  · have hx : y 0 < s / 4 := by
      have hh : (absorbingFamily s).minimum y = y 0 - s / 4 := by
        simpa [absorbingFamily_value] using heq
      linarith
    have hu := mul_le_mul_of_nonneg_right (ha.2 0) (hy 0).le
    have hl := mul_le_mul_of_nonneg_right (ha.1 1) (hy 1).le
    simp [absorbingFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a y).1]
    nlinarith
  · have hy' : y 1 < s / 4 := by
      have hh : (absorbingFamily s).minimum y = y 1 - s / 4 := by
        simpa [absorbingFamily_value] using heq
      linarith
    have hu := mul_le_mul_of_nonneg_right (ha.2 1) (hy 1).le
    have hl := mul_le_mul_of_nonneg_right (ha.1 0) (hy 0).le
    simp [absorbingFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a y).2]
    nlinarith
  · have hh : (absorbingFamily s).minimum y = 0 := by
      simpa [absorbingFamily_value] using heq
    linarith

theorem uniformPermanent (c : State 2) (hs : 0 < c 0 + c 1) :
    conversion.UniformPermanent 1 2 c (fun _ => True) := by
  let s : ℝ := c 0 + c 1
  have hs' : 0 < s := hs
  have hpos : (absorbingFamily s).plateau 0 ∩ conversion.stoichiometricClass c ⊆
      {y | Positive y} := by
    rw [absorbingFamily_plateau]
    exact family_class_positive (by linarith) c
  have heq : (absorbingFamily s).plateau 0 ∩ conversion.positiveClass c =
      (absorbingFamily s).plateau 0 ∩ conversion.stoichiometricClass c := by
    ext y
    constructor
    · rintro ⟨hy, hp, hc⟩
      exact ⟨hy, hc⟩
    · intro hy
      exact ⟨hy.1, hpos hy, hy.2⟩
  have hne : ((absorbingFamily s).plateau 0 ∩ conversion.positiveClass c).Nonempty := by
    rw [heq, absorbingFamily_plateau]
    refine ⟨![s / 2, s / 2], ?_, ?_⟩
    · intro i; fin_cases i <;> simp [family_value] <;> linarith
    · apply class_iff_total.mpr
      simp [s]
  have hcompact : IsCompact ((absorbingFamily s).plateau 0 ∩ conversion.positiveClass c) := by
    rw [heq, absorbingFamily_plateau]
    exact family_class_compact _ _
  apply conversion.uniformPermanent_of_affine_plateau (absorbingFamily s) 1 2 0 c
    (fun _ => True) hne hcompact (fun y _ => absorbingFamily_cap s y)
  · intro k hk _ z hz
    exact positiveWellPosed hk hz.1
  · intro k hk _ z hz x hx
    refine ⟨s / 4, by linarith, ?_⟩
    intro t ht hb i hi
    have hclass := hx.mem_positiveClass hz ht
    have htotal : x t 0 + x t 1 = s := class_iff_total.mp hclass.2
    exact absorbingFamily_flux_margin s _
      ⟨fun e => (hk.2 e t ht).1, fun e => (hk.2 e t ht).2⟩ _ (hx.2 t ht) htotal hb i hi

end Endotactic.Conversion
