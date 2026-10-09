import Endotactic.BoxInvariance
import Endotactic.Stoichiometry
import Endotactic.Examples

/-!
# A complete measurable-rate permanence example: `0 ⇄ A`

For every rate path in `[1,2]`, the common absorbing interval is `[1/4,4]`.
An initial-value-dependent invariant box first gives positive global existence.
The known interval is then checked by an affine minimum and uniform flux margin.
This closes existence, uniqueness and absorption, rather than just checking faces.
It is a one-species example, not the general endotactic theorem.
-/

namespace Endotactic.Examples

open Set

theorem birthDeath_rhs_coordinate (k : Fin 2 → ℝ) (x : State 1) :
    birthDeath.rhs k x 0 = k 0 - k 1 * x 0 := by
  simp [birthDeath, Network.rhs, Network.vector, realComplex, monomial,
    Fin.sum_univ_succ]
  ring

theorem birthDeath_stoichiometricSubspace : birthDeath.stoichiometricSubspace = ⊤ := by
  apply top_unique
  intro x _
  have hv : birthDeath.vector 0 ∈ birthDeath.stoichiometricSubspace :=
    Submodule.subset_span ⟨0, rfl⟩
  have heq : (x 0) • birthDeath.vector 0 = x := by
    ext i
    fin_cases i
    simp [birthDeath, Network.vector, realComplex]
  rw [← heq]
  exact birthDeath.stoichiometricSubspace.smul_mem (x 0) hv

theorem birthDeath_positiveClass (c : State 1) :
    birthDeath.positiveClass c = {x | 0 < x 0} := by
  ext x
  constructor
  · intro hx; exact hx.1 0
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i; fin_cases i; exact hx
    · rw [birthDeath_stoichiometricSubspace]; exact Submodule.mem_top

theorem birthDeath_positiveWellPosed {k : Fin 2 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 1} (hz : Positive z) :
    birthDeath.PositiveWellPosed k z := by
  let lo : State 1 := fun _ => min (z 0) (1 / 4)
  let hi : State 1 := fun _ => max (z 0) 4
  have hz0 := hz 0
  have hlo : Positive lo := fun _ => lt_min hz0 (by norm_num)
  have hbox : lo ≤ hi := fun _ => (min_le_left _ _).trans (le_max_left _ _)
  have hzbox : z ∈ Icc lo hi := by
    constructor <;> intro i <;> fin_cases i
    · exact min_le_left _ _
    · exact le_max_left _ _
  apply birthDeath.positiveWellPosed_of_exists hk
  obtain ⟨x, hx, _⟩ := birthDeath.exists_global_positive_in_box hk lo hi hbox hlo hzbox
    (by
      intro t ht y _ i he
      fin_cases i
      change y 0 = lo 0 at he
      change 0 ≤ birthDeath.rhs (fun e => k e t) y 0
      rw [birthDeath_rhs_coordinate, he]
      have hb := mul_le_mul_of_nonneg_right (hk.2 1 t ht).2 (hlo 0).le
      have ha := (hk.2 0 t ht).1
      have hl : lo 0 ≤ 1 / 4 := min_le_right _ _
      nlinarith)
    (by
      intro t ht y _ i he
      fin_cases i
      change y 0 = hi 0 at he
      change birthDeath.rhs (fun e => k e t) y 0 ≤ 0
      rw [birthDeath_rhs_coordinate, he]
      have hhi : 4 ≤ hi 0 := le_max_right _ _
      have hhi0 : 0 ≤ hi 0 := by linarith
      have hb := mul_le_mul_of_nonneg_right (hk.2 1 t ht).1 hhi0
      have ha := (hk.2 0 t ht).2
      nlinarith)
  exact ⟨x, hx⟩

noncomputable def birthDeathFamily : AffineFamily 1 3 where
  slope := ![![1], ![-1], ![0]]
  offset := ![-1 / 4, 4, 0]

theorem birthDeathFamily_values (x : State 1) :
    birthDeathFamily.value 0 x = x 0 - 1 / 4 ∧
      birthDeathFamily.value 1 x = 4 - x 0 ∧ birthDeathFamily.value 2 x = 0 := by
  simp [birthDeathFamily, AffineFamily.value, dot, sub_eq_add_neg, add_comm]
  norm_num

theorem birthDeathFamily_plateau :
    birthDeathFamily.plateau 0 = Icc (fun _ : Fin 1 => (1 : ℝ) / 4) (fun _ => (4 : ℝ)) := by
  ext x
  constructor
  · intro hx
    have hl := hx 0
    have hu := hx 1
    rw [(birthDeathFamily_values x).1] at hl
    rw [(birthDeathFamily_values x).2.1] at hu
    constructor
    · intro i; fin_cases i; change 1 / 4 ≤ x 0; linarith
    · intro i; fin_cases i; change x 0 ≤ 4; linarith
  · intro hx i
    have hl := hx.1 0
    have hu := hx.2 0
    fin_cases i
    · change 0 ≤ birthDeathFamily.value 0 x
      rw [(birthDeathFamily_values x).1]; linarith
    · change 0 ≤ birthDeathFamily.value 1 x
      rw [(birthDeathFamily_values x).2.1]; linarith
    · change 0 ≤ birthDeathFamily.value 2 x
      rw [(birthDeathFamily_values x).2.2]

theorem birthDeathFamily_flux_margin {k : Fin 2 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {t : ℝ} (ht : 0 ≤ t) {x : State 1} (hx : Positive x)
    (hmin : birthDeathFamily.minimum x < 0) (i : Fin 3)
    (hi : birthDeathFamily.Active i x) :
    (1 : ℝ) / 2 ≤ dot (birthDeathFamily.slope i) (birthDeath.rhs (fun e => k e t) x) := by
  have hvalue : birthDeathFamily.value i x < 0 :=
    ((birthDeathFamily.active_iff_minimum_eq i x).mp hi) ▸ hmin
  have hx0 := hx 0
  fin_cases i
  · change birthDeathFamily.value 0 x < 0 at hvalue
    rw [(birthDeathFamily_values x).1] at hvalue
    change 1 / 2 ≤ dot (birthDeathFamily.slope 0) (birthDeath.rhs (fun e => k e t) x)
    simp [birthDeathFamily, dot]
    rw [birthDeath_rhs_coordinate]
    have hb := mul_le_mul_of_nonneg_right (hk.2 1 t ht).2 hx0.le
    have ha := (hk.2 0 t ht).1
    nlinarith
  · change birthDeathFamily.value 1 x < 0 at hvalue
    rw [(birthDeathFamily_values x).2.1] at hvalue
    change 1 / 2 ≤ dot (birthDeathFamily.slope 1) (birthDeath.rhs (fun e => k e t) x)
    simp [birthDeathFamily, dot]
    rw [birthDeath_rhs_coordinate]
    have hb := mul_le_mul_of_nonneg_right (hk.2 1 t ht).1 hx0.le
    have ha := (hk.2 0 t ht).2
    nlinarith
  · change birthDeathFamily.value 2 x < 0 at hvalue
    rw [(birthDeathFamily_values x).2.2] at hvalue
    exact False.elim (lt_irrefl 0 hvalue)

/-- The common absorbing interval is independent of the initial point and rates. -/
theorem birthDeath_eventuallyIn_interval {k : Fin 2 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 1} {x : ℝ → State 1}
    (hx : birthDeath.IsGlobalPositiveSolution k z x) :
    EventuallyIn x (Icc (fun _ : Fin 1 => (1 : ℝ) / 4) (fun _ => (4 : ℝ))) := by
  have hcap : ∀ t, 0 ≤ t → birthDeathFamily.minimum (x t) ≤ 0 := by
    intro t _
    have hh := birthDeathFamily.minimum_le_constant_branch 2
      (by intro j; fin_cases j; rfl) (x t)
    simpa [birthDeathFamily] using hh
  have hh := birthDeathFamily.eventuallyIn_plateau hx.1
    (δ := 1 / 2) (by norm_num) hcap
    (fun t ht hm i hi => birthDeathFamily_flux_margin hk ht (hx.2 t ht) hm i hi)
  rwa [birthDeathFamily_plateau] at hh

theorem birthDeath_uniformPermanent (c : State 1) :
    birthDeath.UniformPermanent 1 2 c (fun _ => True) := by
  have hsubset : birthDeathFamily.plateau 0 ⊆ birthDeath.positiveClass c := by
    intro x hx
    rw [birthDeath_positiveClass]
    rw [birthDeathFamily_plateau] at hx
    have hh := hx.1 0
    change 0 < x 0
    linarith
  have hinter : birthDeathFamily.plateau 0 ∩ birthDeath.positiveClass c =
      birthDeathFamily.plateau 0 := inter_eq_left.mpr hsubset
  apply birthDeath.uniformPermanent_of_affine_plateau birthDeathFamily 1 2 0 c (fun _ => True)
  · rw [hinter, birthDeathFamily_plateau]
    exact ⟨![1], by constructor <;> intro i <;> fin_cases i <;> norm_num⟩
  · rw [hinter, birthDeathFamily_plateau]
    exact isCompact_Icc
  · intro z _
    have hh := birthDeathFamily.minimum_le_constant_branch 2 (by intro j; fin_cases j; rfl) z
    simpa [birthDeathFamily] using hh
  · intro k hk _ z hz
    exact birthDeath_positiveWellPosed hk hz.1
  · intro k hk _ z _ x hx
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro t ht hmin i hi
    exact birthDeathFamily_flux_margin hk ht (hx.2 t ht) hmin i hi

end Endotactic.Examples
