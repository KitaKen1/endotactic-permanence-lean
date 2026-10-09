import Endotactic.AffineDualBounds
import Endotactic.StarCertificate

/-!
# From the known rational star polygon to positive global well-posedness

The previously checked four inward face margins now form a certificate for
the strict-face trapping theorem. Nonnegative rational dual weights certify
the positive bounding box; compact affine robustness supplies an enlarged
positive box automatically. An explicit enlargement at level `-1/1024` is
also checked below. Hence every initial point in the
polygon has a unique positive global integral solution for all measurable
rates in `[1,2]`, and every integral solution with that initial point stays
in the polygon. Absorption from arbitrary positive initial points is separate.
-/

namespace Endotactic.StarCertificate

open Set

noncomputable def family : AffineFamily 2 4 where
  slope := ![![1, 0], ![0, 1], ![0, -1], ![-1, -2]]
  offset := ![-1 / 8, -1 / 256, 256, 520]

theorem family_value (i : Fin 4) (z : State 2) :
    family.value i z = ![z 0 - 1 / 8, z 1 - 1 / 256, 256 - z 1,
      520 - z 0 - 2 * z 1] i := by
  fin_cases i <;> simp [family, AffineFamily.value, dot, Fin.sum_univ_succ] <;> ring

theorem family_plateau : family.plateau 0 = polygon := by
  ext z
  constructor
  · intro hz
    have h0 : 0 ≤ z 0 - 1 / 8 := by simpa [family_value] using hz 0
    have h1 : 0 ≤ z 1 - 1 / 256 := by simpa [family_value] using hz 1
    have h2 : 0 ≤ 256 - z 1 := by simpa [family_value] using hz 2
    have h3 : 0 ≤ 520 - z 0 - 2 * z 1 := by simpa [family_value] using hz 3
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · intro hz i
    rcases hz with ⟨h0, h1, h2, h3⟩
    fin_cases i <;> simp [family_value] <;> linarith

theorem family_enlarged_subset :
    family.plateau (-(1 : ℝ) / 1024) ⊆
      Icc (![1 / 16, 1 / 512] : State 2) ![521, 257] := by
  intro z hz
  have h0 : -(1 : ℝ) / 1024 ≤ z 0 - 1 / 8 := by simpa [family_value] using hz 0
  have h1 : -(1 : ℝ) / 1024 ≤ z 1 - 1 / 256 := by simpa [family_value] using hz 1
  have h2 : -(1 : ℝ) / 1024 ≤ 256 - z 1 := by simpa [family_value] using hz 2
  have h3 : -(1 : ℝ) / 1024 ≤ 520 - z 0 - 2 * z 1 := by simpa [family_value] using hz 3
  constructor <;> intro i <;> fin_cases i <;> norm_num <;> linarith

/-- Known rational LP dual weights, checked without running or trusting a solver. -/
noncomputable def familyBoxCertificate :
    family.BoxCertificate 0 (![1 / 8, 1 / 256] : State 2) ![520, 256] where
  lowerWeight := ![![1, 0, 0, 0], ![0, 1, 0, 0]]
  upperWeight := ![![0, 2, 0, 1], ![0, 0, 1, 0]]
  lower_nonneg := by intro j i; fin_cases j <;> fin_cases i <;> norm_num
  upper_nonneg := by intro j i; fin_cases j <;> fin_cases i <;> norm_num
  lower_coordinate := by
    intro j k
    fin_cases j <;> fin_cases k <;> norm_num [family, Fin.sum_univ_succ]
  upper_coordinate := by
    intro j k
    fin_cases j <;> fin_cases k <;> norm_num [family, Fin.sum_univ_succ]
  lower_bound := by intro j; fin_cases j <;> norm_num [family, Fin.sum_univ_succ]
  upper_bound := by intro j; fin_cases j <;> norm_num [family, Fin.sum_univ_succ]

theorem family_dual_box :
    family.plateau 0 ⊆ Icc (![1 / 8, 1 / 256] : State 2) ![520, 256] :=
  familyBoxCertificate.plateau_subset_box family

theorem family_compact_from_dual : IsCompact (family.plateau 0) :=
  familyBoxCertificate.isCompact family

theorem rateBox_of_mem {a : Fin 4 → ℝ}
    (ha : a ∈ Icc (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ))) :
    RateBox (a 0) (a 1) (a 2) (a 3) :=
  ⟨ha.1 0, ha.2 0, ha.1 1, ha.2 1, ha.1 2, ha.2 2, ha.1 3, ha.2 3⟩

theorem rhs_at (a : Fin 4 → ℝ) (z : State 2) :
    star.rhs a z 0 = fx (a 0) (a 1) (a 2) (a 3) (z 0) (z 1) ∧
      star.rhs a z 1 = fy (a 2) (a 3) (z 0) (z 1) := by
  have ha : a = ![a 0, a 1, a 2, a 3] := by ext i; fin_cases i <;> rfl
  have hz : z = ![z 0, z 1] := by ext i; fin_cases i <;> rfl
  have hh := rhs_coordinates (a 0) (a 1) (a 2) (a 3) (z 0) (z 1)
  rw [← ha, ← hz] at hh
  constructor
  · exact congrFun hh 0
  · exact congrFun hh 1

theorem family_face_certificate : star.AffineFaceCertificate family 1 2 0 := by
  intro i
  right
  intro a ha z hz he
  rw [family_plateau] at hz
  have hk := rateBox_of_mem ha
  fin_cases i
  · have hx : z 0 = 1 / 8 := by
      have hh : z 0 - 1 / 8 = 0 := by simpa [family_value] using he
      linarith
    change 0 < dot (family.slope 0) (star.rhs a z)
    simp [family, dot, Fin.sum_univ_succ]
    rw [(rhs_at a z).1, hx]
    exact (by norm_num : (0 : ℝ) < 89 / 128).trans_le (lower_x_face hk hz.2.1)
  · have hy : z 1 = 1 / 256 := by
      have hh : z 1 - 1 / 256 = 0 := by simpa [family_value] using he
      linarith
    change 0 < dot (family.slope 1) (star.rhs a z)
    simp [family, dot, Fin.sum_univ_succ]
    rw [(rhs_at a z).2, hy]
    exact (by norm_num : (0 : ℝ) < 1 / 128).trans_le (lower_y_face hk hz.1)
  · have hy : z 1 = 256 := by
      have hh : 256 - z 1 = 0 := by simpa [family_value] using he
      linarith
    have hx0 : 0 ≤ z 0 := by linarith [hz.1]
    have hx8 : z 0 ≤ 8 := by linarith [hz.2.2.2]
    change 0 < dot (family.slope 2) (star.rhs a z)
    simp [family, dot, Fin.sum_univ_succ]
    rw [(rhs_at a z).2, hy]
    have hh := upper_y_face hk hx0 hx8
    linarith
  · have hm : z 0 + 2 * z 1 = 520 := by
      have hh : 520 - z 0 - 2 * z 1 = 0 := by simpa [family_value] using he
      linarith
    change 0 < dot (family.slope 3) (star.rhs a z)
    simp [family, dot, Fin.sum_univ_succ]
    rw [(rhs_at a z).1, (rhs_at a z).2]
    have hh := upper_mass_face hk hz.2.2.1 hm
    linarith

theorem exists_global_positive_in_polygon {k : Fin 4 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 2} (hz : z ∈ polygon) :
    ∃ x, star.IsGlobalPositiveSolution k z x ∧ ∀ t, 0 ≤ t → x t ∈ polygon := by
  rw [← family_plateau] at hz ⊢
  apply star.exists_global_positive_of_affine_certificates hk family familyBoxCertificate
  · intro i; fin_cases i <;> norm_num
  · exact family_face_certificate
  · exact hz

theorem positiveWellPosed_in_polygon {k : Fin 4 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 2} (hz : z ∈ polygon) :
    star.PositiveWellPosed k z := by
  obtain ⟨x, hx, _⟩ := exists_global_positive_in_polygon hk hz
  exact star.positiveWellPosed_of_exists hk ⟨x, hx⟩

theorem integralSolution_stays_in_polygon {k : Fin 4 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 2} (hz : z ∈ polygon)
    {y : ℝ → State 2} (hy : star.IsIntegralSolution k z y) :
    ∀ t, 0 ≤ t → y t ∈ polygon := by
  obtain ⟨x, hx, hstay⟩ := exists_global_positive_in_polygon hk hz
  intro t ht
  rw [Network.IsIntegralSolution.eqOn_nonnegative star hk hy hx.1 ht]
  exact hstay t ht

end Endotactic.StarCertificate
