import Endotactic.StarGlobalExistence

/-!
# An initial-point-dependent positive trap for every star initial point

Use `x ≥ α`, `y ≥ α²/4`, `y ≤ Y`, `x+2y ≤ 2Y+8`, with `0<α≤1/8`
and `Y≥256`. All four faces are strictly inward for rates in `[1,2]`.
For an arbitrary positive initial point, choose `α=min(1/8,x₀,y₀)` and
`Y=max(256,x₀+2y₀)`. Fixed nonnegative dual weights reconstruct both
coordinate bounds. The enlarged positive box now follows automatically from
compact affine robustness. The strict-face theorem supplies positive global existence,
and the checked integral uniqueness supplies global well-posedness.
The trap depends on the initial point; common-set absorption is separate.
-/

namespace Endotactic.StarCertificate

open Set

noncomputable def initialFamily (α Y : ℝ) : AffineFamily 2 4 where
  slope := ![![1, 0], ![0, 1], ![0, -1], ![-1, -2]]
  offset := ![-α, -α ^ 2 / 4, Y, 2 * Y + 8]

theorem initialFamily_value (α Y : ℝ) (i : Fin 4) (z : State 2) :
    (initialFamily α Y).value i z =
      ![z 0 - α, z 1 - α ^ 2 / 4, Y - z 1, 2 * Y + 8 - z 0 - 2 * z 1] i := by
  fin_cases i <;> simp [initialFamily, AffineFamily.value, dot, Fin.sum_univ_succ] <;> ring

theorem initialFamily_face_certificate {α Y : ℝ}
    (hα : 0 < α) (hα8 : α ≤ 1 / 8) (hY : 256 ≤ Y) :
    star.AffineFaceCertificate (initialFamily α Y) 1 2 0 := by
  intro i
  right
  intro a ha z hz he
  have hk := rateBox_of_mem ha
  have hx : α ≤ z 0 := by
    have hh : 0 ≤ z 0 - α := by simpa [initialFamily_value] using hz 0
    linarith
  have hy : α ^ 2 / 4 ≤ z 1 := by
    have hh : 0 ≤ z 1 - α ^ 2 / 4 := by simpa [initialFamily_value] using hz 1
    linarith
  have hyY : z 1 ≤ Y := by
    have hh : 0 ≤ Y - z 1 := by simpa [initialFamily_value] using hz 2
    linarith
  have hm : z 0 + 2 * z 1 ≤ 2 * Y + 8 := by
    have hh : 0 ≤ 2 * Y + 8 - z 0 - 2 * z 1 := by simpa [initialFamily_value] using hz 3
    linarith
  have hy0 : 0 ≤ z 1 := (by positivity : 0 ≤ α ^ 2 / 4).trans hy
  have hsq : α ^ 2 ≤ 1 / 64 := by
    nlinarith [mul_nonneg hα.le (show 0 ≤ 1 / 8 - α by linarith)]
  fin_cases i
  · have heq : z 0 = α := by
      have hh : z 0 - α = 0 := by simpa [initialFamily_value] using he
      linarith
    change 0 < dot ((initialFamily α Y).slope 0) (star.rhs a z)
    simp [initialFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a z).1, heq]
    have hb := mul_le_mul_of_nonneg_right hk.2.2.2.1 hα.le
    have hc := mul_le_mul_of_nonneg_right hk.2.2.2.2.2.1 (sq_nonneg α)
    have hd : 0 ≤ a 3 * z 1 := mul_nonneg (by linarith [hk.2.2.2.2.2.2.1]) hy0
    unfold fx
    nlinarith [hk.1]
  · have heq : z 1 = α ^ 2 / 4 := by
      have hh : z 1 - α ^ 2 / 4 = 0 := by simpa [initialFamily_value] using he
      linarith
    change 0 < dot ((initialFamily α Y).slope 1) (star.rhs a z)
    simp [initialFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a z).2, heq]
    have hxx : α ^ 2 ≤ (z 0) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ z 0 - α by linarith)
        (show 0 ≤ z 0 + α by linarith)]
    have hc := mul_le_mul_of_nonneg_right hk.2.2.2.2.1 (sq_nonneg (z 0))
    have hd := mul_le_mul_of_nonneg_right hk.2.2.2.2.2.2.2
      (show 0 ≤ α ^ 2 / 4 by positivity)
    unfold fy
    nlinarith [pow_pos hα 2]
  · have heq : z 1 = Y := by
      have hh : Y - z 1 = 0 := by simpa [initialFamily_value] using he
      linarith
    have hx0 : 0 ≤ z 0 := hα.le.trans hx
    have hx8 : z 0 ≤ 8 := by linarith
    have hxx : (z 0) ^ 2 ≤ 64 := by
      nlinarith [mul_nonneg hx0 (show 0 ≤ 8 - z 0 by linarith)]
    change 0 < dot ((initialFamily α Y).slope 2) (star.rhs a z)
    simp [initialFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a z).2, heq]
    have hc := mul_le_mul_of_nonneg_right hk.2.2.2.2.2.1 (sq_nonneg (z 0))
    have hd := mul_le_mul_of_nonneg_right hk.2.2.2.2.2.2.1 (show 0 ≤ Y by linarith)
    unfold fy
    nlinarith
  · have heq : z 0 + 2 * z 1 = 2 * Y + 8 := by
      have hh : 2 * Y + 8 - z 0 - 2 * z 1 = 0 := by simpa [initialFamily_value] using he
      linarith
    have hx8 : 8 ≤ z 0 := by linarith
    change 0 < dot ((initialFamily α Y).slope 3) (star.rhs a z)
    simp [initialFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a z).1, (rhs_at a z).2]
    have hb := mul_le_mul_of_nonneg_right hk.2.2.1 (show 0 ≤ z 0 by linarith)
    have hh := mass_identity (a 0) (a 1) (a 2) (a 3) (z 0) (z 1)
    nlinarith [hk.2.1]

theorem initialFamily_enlarged_subset {α Y ε : ℝ}
    (heα : ε ≤ α / 2) (heβ : ε ≤ α ^ 2 / 8) (he1 : ε ≤ 1) :
    (initialFamily α Y).plateau (-ε) ⊆
      Icc (![α / 2, α ^ 2 / 8] : State 2) ![2 * Y + 9, Y + 1] := by
  intro z hz
  have h0 : -ε ≤ z 0 - α := by simpa [initialFamily_value] using hz 0
  have h1 : -ε ≤ z 1 - α ^ 2 / 4 := by simpa [initialFamily_value] using hz 1
  have h2 : -ε ≤ Y - z 1 := by simpa [initialFamily_value] using hz 2
  have h3 : -ε ≤ 2 * Y + 8 - z 0 - 2 * z 1 := by simpa [initialFamily_value] using hz 3
  constructor <;> intro i <;> fin_cases i <;> simp <;> nlinarith [sq_nonneg α]

noncomputable def initialFamilyBoxCertificate (α Y : ℝ) :
    (initialFamily α Y).BoxCertificate 0
      (![α, α ^ 2 / 4] : State 2) ![2 * Y + 8, Y] where
  lowerWeight := ![![1, 0, 0, 0], ![0, 1, 0, 0]]
  upperWeight := ![![0, 2, 0, 1], ![0, 0, 1, 0]]
  lower_nonneg := by intro j i; fin_cases j <;> fin_cases i <;> norm_num
  upper_nonneg := by intro j i; fin_cases j <;> fin_cases i <;> norm_num
  lower_coordinate := by
    intro j k
    fin_cases j <;> fin_cases k <;> norm_num [initialFamily, Fin.sum_univ_succ]
  upper_coordinate := by
    intro j k
    fin_cases j <;> fin_cases k <;> norm_num [initialFamily, Fin.sum_univ_succ]
  lower_bound := by
    intro j
    fin_cases j
    · simp [initialFamily, Fin.sum_univ_succ]
    · simp [initialFamily, Fin.sum_univ_succ]
      ring_nf
      exact le_rfl
  upper_bound := by
    intro j
    fin_cases j
    · simp [initialFamily, Fin.sum_univ_succ]
      nlinarith [sq_nonneg α]
    · simp [initialFamily, Fin.sum_univ_succ]

theorem initialFamily_dual_box (α Y : ℝ) :
    (initialFamily α Y).plateau 0 ⊆
      Icc (![α, α ^ 2 / 4] : State 2) ![2 * Y + 8, Y] :=
  (initialFamilyBoxCertificate α Y).plateau_subset_box (initialFamily α Y)

theorem exists_global_positive {k : Fin 4 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 2} (hz : Positive z) :
    ∃ x, star.IsGlobalPositiveSolution k z x := by
  let α : ℝ := min (1 / 8) (min (z 0) (z 1))
  let Y : ℝ := max 256 (z 0 + 2 * z 1)
  have hα : 0 < α := lt_min (by norm_num) (lt_min (hz 0) (hz 1))
  have hα8 : α ≤ 1 / 8 := min_le_left _ _
  have hαx : α ≤ z 0 := (min_le_right _ _).trans (min_le_left _ _)
  have hαy : α ≤ z 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hY : 256 ≤ Y := le_max_left _ _
  have hYm : z 0 + 2 * z 1 ≤ Y := le_max_right _ _
  have hsq : α ^ 2 ≤ α / 8 := by
    nlinarith [mul_nonneg hα.le (show 0 ≤ 1 / 8 - α by linarith)]
  have hzA : z ∈ (initialFamily α Y).plateau 0 := by
    intro i
    fin_cases i <;> simp [initialFamily_value] <;> nlinarith [hz 0, hz 1]
  obtain ⟨x, hx, _⟩ := star.exists_global_positive_of_affine_certificates hk
    (initialFamily α Y) (initialFamilyBoxCertificate α Y)
    (by
      intro i; fin_cases i <;> simp <;> positivity)
    (initialFamily_face_certificate hα hα8 hY) hzA
  exact ⟨x, hx⟩

theorem positiveWellPosed {k : Fin 4 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 2} (hz : Positive z) :
    star.PositiveWellPosed k z :=
  star.positiveWellPosed_of_exists hk (exists_global_positive hk hz)

end Endotactic.StarCertificate
