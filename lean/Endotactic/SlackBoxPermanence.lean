import Endotactic.CompactTrapPermanence

/-!
# A two-species example with vanishing flux on target faces

The independent reversible births `0 ⇄ A`, `0 ⇄ B` have arbitrary measurable
rates in `[1,2]`. The natural tight target is `[1/2,2]^2`. Its face flux can
vanish at coefficient endpoints, while flux is strictly inward everywhere
outside on every active face. Positive compact initial boxes are constructed
for all positive initial states.

The compact-strict-exterior theorem yields common permanence by relaxing the
target slightly. No strict target-face assumption or supplied numerical flux
margin is used in that assembly. This is a concrete multidimensional example,
not an instantiation for every endotactic network.
-/

namespace Endotactic.SlackBox

open Set

def network : Network 2 (Fin 4) where
  source := ![![0, 0], ![1, 0], ![0, 0], ![0, 1]]
  target := ![![1, 0], ![0, 0], ![0, 1], ![0, 0]]

theorem isEndotactic : network.IsEndotactic := by
  intro r e he
  fin_cases e
  · refine ⟨1, ?_, ?_⟩ <;>
      simp [network, Network.projection, Network.sourceLevel, Network.vector,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith
  · refine ⟨0, ?_, ?_⟩ <;>
      simp [network, Network.projection, Network.sourceLevel, Network.vector,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith
  · refine ⟨3, ?_, ?_⟩ <;>
      simp [network, Network.projection, Network.sourceLevel, Network.vector,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith
  · refine ⟨2, ?_, ?_⟩ <;>
      simp [network, Network.projection, Network.sourceLevel, Network.vector,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith

theorem rhs_at (a : Fin 4 → ℝ) (y : State 2) :
    network.rhs a y 0 = a 0 - a 1 * y 0 ∧
      network.rhs a y 1 = a 2 - a 3 * y 1 := by
  constructor <;> simp [network, Network.rhs, monomial, Network.vector,
    realComplex, Fin.sum_univ_succ] <;> ring

theorem stoichiometricSubspace : network.stoichiometricSubspace = ⊤ := by
  apply top_unique
  intro y _
  have h0 : network.vector 0 ∈ network.stoichiometricSubspace :=
    Submodule.subset_span ⟨0, rfl⟩
  have h2 : network.vector 2 ∈ network.stoichiometricSubspace :=
    Submodule.subset_span ⟨2, rfl⟩
  have heq : (y 0) • network.vector 0 + (y 1) • network.vector 2 = y := by
    ext i
    fin_cases i <;> simp [network, Network.vector, realComplex]
  rw [← heq]
  exact network.stoichiometricSubspace.add_mem
    (network.stoichiometricSubspace.smul_mem _ h0)
    (network.stoichiometricSubspace.smul_mem _ h2)

theorem stoichiometricClass (c : State 2) : network.stoichiometricClass c = univ := by
  ext y
  simp [Network.stoichiometricClass, stoichiometricSubspace]

noncomputable def targetFamily : AffineFamily 2 4 where
  slope := ![![1, 0], ![-1, 0], ![0, 1], ![0, -1]]
  offset := ![-1 / 2, 2, -1 / 2, 2]

theorem targetFamily_value (i : Fin 4) (y : State 2) :
    targetFamily.value i y = ![y 0 - 1 / 2, 2 - y 0, y 1 - 1 / 2, 2 - y 1] i := by
  fin_cases i <;> simp [targetFamily, AffineFamily.value, dot, Fin.sum_univ_succ] <;> ring

theorem targetFamily_plateau (Q : ℝ) :
    targetFamily.plateau Q =
      Icc (fun _ : Fin 2 => Q + 1 / 2) (fun _ => 2 - Q) := by
  ext y
  constructor
  · intro hy
    have h0 : Q ≤ y 0 - 1 / 2 := by simpa [targetFamily_value] using hy 0
    have h1 : Q ≤ 2 - y 0 := by simpa [targetFamily_value] using hy 1
    have h2 : Q ≤ y 1 - 1 / 2 := by simpa [targetFamily_value] using hy 2
    have h3 : Q ≤ 2 - y 1 := by simpa [targetFamily_value] using hy 3
    constructor <;> intro i <;> fin_cases i <;> dsimp <;> linarith
  · intro hy i
    have h0 := hy.1 0
    have h1 := hy.2 0
    have h2 := hy.1 1
    have h3 := hy.2 1
    fin_cases i <;> simp [targetFamily_value] <;> linarith

theorem targetFamily_strict_exterior (a : Fin 4 → ℝ)
    (ha : a ∈ Icc (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ)))
    {y : State 2} (hmin : targetFamily.minimum y < 0) (i : Fin 4)
    (hi : targetFamily.Active i y) : 0 < dot (targetFamily.slope i) (network.rhs a y) := by
  have hv : targetFamily.value i y < 0 :=
    (targetFamily.active_iff_minimum_eq i y).mp hi ▸ hmin
  fin_cases i
  · have hy : y 0 < 1 / 2 := by simpa [targetFamily_value] using hv
    simp [targetFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a y).1]
    have hb : a 1 * y 0 < 1 := by
      have hh := mul_lt_mul_of_pos_left hy (lt_of_lt_of_le (by norm_num) (ha.1 1))
      nlinarith [ha.2 1]
    linarith [ha.1 0]
  · have hy : 2 < y 0 := by
      have hh : 2 - y 0 < 0 := by simpa [targetFamily_value] using hv
      linarith
    simp [targetFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a y).1]
    have hb := mul_le_mul_of_nonneg_right (ha.1 1) (by linarith : 0 ≤ y 0)
    nlinarith [ha.2 0]
  · have hy : y 1 < 1 / 2 := by simpa [targetFamily_value] using hv
    simp [targetFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a y).2]
    have hb : a 3 * y 1 < 1 := by
      have hh := mul_lt_mul_of_pos_left hy (lt_of_lt_of_le (by norm_num) (ha.1 3))
      nlinarith [ha.2 3]
    linarith [ha.1 2]
  · have hy : 2 < y 1 := by
      have hh : 2 - y 1 < 0 := by simpa [targetFamily_value] using hv
      linarith
    simp [targetFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a y).2]
    have hb := mul_le_mul_of_nonneg_right (ha.1 3) (by linarith : 0 ≤ y 1)
    nlinarith [ha.2 2]

/-- A tight target face really has zero flux at an admissible coefficient endpoint. -/
theorem target_face_zero_flux :
    let a : Fin 4 → ℝ := ![1, 2, 1, 1]
    let y : State 2 := ![1 / 2, 1]
    a ∈ Icc (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ)) ∧
      y ∈ targetFamily.plateau 0 ∧ targetFamily.value 0 y = 0 ∧
      dot (targetFamily.slope 0) (network.rhs a y) = 0 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor <;> intro e <;> fin_cases e <;> norm_num
  · intro i; fin_cases i <;> norm_num [targetFamily_value]
  · norm_num [targetFamily_value]
  · simp [targetFamily, dot, Fin.sum_univ_succ, (rhs_at _ _).1]

theorem not_strict_target_face_certificate :
    ¬ network.AffineFaceCertificate targetFamily 1 2 0 := by
  intro h
  rcases h 0 with hzero | hstrict
  · have hb := hzero (fun _ => 1) (fun _ => 0)
    norm_num [targetFamily, dot, Fin.sum_univ_succ, (rhs_at _ _).1] at hb
  · rcases target_face_zero_flux with ⟨ha, hy, he, hf⟩
    have hb := hstrict _ ha _ hy he
    rw [hf] at hb
    exact lt_irrefl 0 hb

noncomputable def initialLower (z : State 2) : State 2 := fun i => min (z i) (1 / 4)

def initialUpper (z : State 2) : State 2 := fun i => max (z i) 4

theorem initialLower_positive {z : State 2} (hz : Positive z) :
    Positive (initialLower z) := fun i => lt_min (hz i) (by norm_num)

theorem initial_mem_box (z : State 2) : z ∈ Icc (initialLower z) (initialUpper z) :=
  ⟨fun _ => min_le_left _ _, fun _ => le_max_left _ _⟩

theorem exists_global_positive_in_initial_box {k : Fin 4 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 2} (hz : Positive z) :
    ∃ x, network.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ Icc (initialLower z) (initialUpper z) := by
  apply network.exists_global_positive_in_box hk (initialLower z) (initialUpper z)
    (fun i => (min_le_left _ _).trans (le_max_left _ _))
    (initialLower_positive hz) (initial_mem_box z)
  · intro t ht y _ i he
    fin_cases i
    · change 0 ≤ network.rhs (fun e => k e t) y 0
      change y 0 = initialLower z 0 at he
      rw [(rhs_at _ _).1, he]
      have hb := mul_le_mul_of_nonneg_right (hk.2 1 t ht).2 (initialLower_positive hz 0).le
      have hl : initialLower z 0 ≤ 1 / 4 := min_le_right _ _
      nlinarith [(hk.2 0 t ht).1]
    · change 0 ≤ network.rhs (fun e => k e t) y 1
      change y 1 = initialLower z 1 at he
      rw [(rhs_at _ _).2, he]
      have hb := mul_le_mul_of_nonneg_right (hk.2 3 t ht).2 (initialLower_positive hz 1).le
      have hl : initialLower z 1 ≤ 1 / 4 := min_le_right _ _
      nlinarith [(hk.2 2 t ht).1]
  · intro t ht y _ i he
    fin_cases i
    · change network.rhs (fun e => k e t) y 0 ≤ 0
      change y 0 = initialUpper z 0 at he
      rw [(rhs_at _ _).1, he]
      have hh : 4 ≤ initialUpper z 0 := le_max_right _ _
      have hb := mul_le_mul_of_nonneg_right (hk.2 1 t ht).1 (by linarith : 0 ≤ initialUpper z 0)
      nlinarith [(hk.2 0 t ht).2]
    · change network.rhs (fun e => k e t) y 1 ≤ 0
      change y 1 = initialUpper z 1 at he
      rw [(rhs_at _ _).2, he]
      have hh : 4 ≤ initialUpper z 1 := le_max_right _ _
      have hb := mul_le_mul_of_nonneg_right (hk.2 3 t ht).1 (by linarith : 0 ≤ initialUpper z 1)
      nlinarith [(hk.2 2 t ht).2]

theorem positiveWellPosed {k : Fin 4 → ℝ → ℝ} (hk : AdmissibleRates k 1 2)
    {z : State 2} (hz : Positive z) : network.PositiveWellPosed k z := by
  obtain ⟨x, hx, _⟩ := exists_global_positive_in_initial_box hk hz
  exact network.positiveWellPosed_of_exists hk ⟨x, hx⟩

theorem integralSolution_mem_initial_box {k : Fin 4 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 2} (hz : Positive z)
    {x : ℝ → State 2} (hx : network.IsIntegralSolution k z x) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ Icc (initialLower z) (initialUpper z) := by
  obtain ⟨y, hy, hstay⟩ := exists_global_positive_in_initial_box hk hz
  exact network.integralSolution_mem_of_trapped_solution hk hx ⟨y, hy.1, hstay⟩ ht

theorem eventuallyIn_relaxed_box {k : Fin 4 → ℝ → ℝ} (hk : AdmissibleRates k 1 2)
    {z : State 2} (hz : Positive z) {x : ℝ → State 2}
    (hx : network.IsIntegralSolution k z x) {ε : ℝ} (hε : 0 < ε) :
    EventuallyIn x (Icc (fun _ : Fin 2 => 1 / 2 - ε) (fun _ => 2 + ε)) := by
  have hh := targetFamily.eventuallyIn_plateau_of_compact_strict_exterior
    (M := 0) (Q := -ε) hk hx (B := Icc (initialLower z) (initialUpper z)) isCompact_Icc
    (fun t ht => integralSolution_mem_initial_box hk hz hx ht) (by linarith)
    (fun a ha y _ hm i hi => targetFamily_strict_exterior a ha hm i hi)
  simpa only [targetFamily_plateau, neg_add_eq_sub, sub_neg_eq_add] using hh

theorem uniformPermanent (c : State 2) : network.UniformPermanent 1 2 c (fun _ => True) := by
  apply network.uniformPermanent_of_compact_strict_exterior targetFamily 1 2 0 c
    (fun _ => True)
  · rw [stoichiometricClass, inter_univ, targetFamily_plateau]
    exact ⟨![1, 1], by constructor <;> intro i <;> fin_cases i <;> norm_num⟩
  · rw [stoichiometricClass, inter_univ, targetFamily_plateau]
    exact isCompact_Icc
  · rw [stoichiometricClass, inter_univ, targetFamily_plateau]
    intro y hy i
    have hh := hy.1 i
    norm_num at hh
    linarith
  · intro k hk _ z hz
    exact positiveWellPosed hk hz.1
  · intro z hz
    refine ⟨Icc (initialLower z) (initialUpper z), isCompact_Icc, ?_, ?_⟩
    · intro k hk _ x hx t ht
      exact integralSolution_mem_initial_box hk hz.1 hx.1 ht
    · intro a ha y _ hm i hi
      exact targetFamily_strict_exterior a ha hm i hi

end Endotactic.SlackBox
