import Endotactic.WeakFiniteClassTrap
import Endotactic.SlackBoxPermanence

/-!
# Tight, nonstrict initial traps for the independent birth-death example

The sharper initial box uses `min(z_i,1/2)` and `max(z_i,2)`, rather than the
previous strict-face bounds `1/4` and `4`. Its boundary flux may vanish. The
midpoint is a strictly feasible anchor, so the weak polyhedral theorem provides
actual global solutions and traps every original integral solution.

The tight target is invariant for initial states inside it; finite entry from
outside still requires the separate positive relaxation proved earlier.
-/

namespace Endotactic.SlackBox

open Set

noncomputable def rectFamily (lo hi : State 2) : AffineFamily 2 4 where
  slope := targetFamily.slope
  offset := ![-lo 0, hi 0, -lo 1, hi 1]

theorem rectFamily_value (lo hi y : State 2) (i : Fin 4) :
    (rectFamily lo hi).value i y = ![y 0 - lo 0, hi 0 - y 0, y 1 - lo 1, hi 1 - y 1] i := by
  fin_cases i <;> simp [rectFamily, targetFamily, AffineFamily.value, dot,
    Fin.sum_univ_succ] <;> ring

theorem rectFamily_plateau (lo hi : State 2) : (rectFamily lo hi).plateau 0 = Icc lo hi := by
  ext y
  constructor
  · intro hy
    have h0 : 0 ≤ y 0 - lo 0 := by simpa [rectFamily_value] using hy 0
    have h1 : 0 ≤ hi 0 - y 0 := by simpa [rectFamily_value] using hy 1
    have h2 : 0 ≤ y 1 - lo 1 := by simpa [rectFamily_value] using hy 2
    have h3 : 0 ≤ hi 1 - y 1 := by simpa [rectFamily_value] using hy 3
    constructor <;> intro i <;> fin_cases i <;> dsimp <;> linarith
  · intro hy i
    have h0 := hy.1 0
    have h1 := hy.2 0
    have h2 := hy.1 1
    have h3 := hy.2 1
    fin_cases i <;> simp [rectFamily_value] <;> linarith

theorem rectFamily_weak_faces (lo hi c : State 2) (hlo : Positive lo)
    (hl : ∀ i, lo i ≤ 1 / 2) (hh : ∀ i, 2 ≤ hi i) :
    network.ClassWeakAffineFaceCertificate (rectFamily lo hi) 1 2 0 c := by
  intro i a ha y _ hf
  fin_cases i
  · have he : y 0 = lo 0 := by
      have he' : y 0 - lo 0 = 0 := by simpa [rectFamily_value] using hf
      linarith
    simp [rectFamily, targetFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at _ _).1, he]
    have hb := mul_le_mul_of_nonneg_right (ha.2 1) (hlo 0).le
    nlinarith [ha.1 0, hl 0]
  · have he : y 0 = hi 0 := by
      have he' : hi 0 - y 0 = 0 := by simpa [rectFamily_value] using hf
      linarith
    simp [rectFamily, targetFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at _ _).1, he]
    have hb := mul_le_mul_of_nonneg_right (ha.1 1) (by linarith [hh 0] : 0 ≤ hi 0)
    nlinarith [ha.2 0, hh 0]
  · have he : y 1 = lo 1 := by
      have he' : y 1 - lo 1 = 0 := by simpa [rectFamily_value] using hf
      linarith
    simp [rectFamily, targetFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at _ _).2, he]
    have hb := mul_le_mul_of_nonneg_right (ha.2 3) (hlo 1).le
    nlinarith [ha.1 2, hl 1]
  · have he : y 1 = hi 1 := by
      have he' : hi 1 - y 1 = 0 := by simpa [rectFamily_value] using hf
      linarith
    simp [rectFamily, targetFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at _ _).2, he]
    have hb := mul_le_mul_of_nonneg_right (ha.1 3) (by linarith [hh 1] : 0 ≤ hi 1)
    nlinarith [ha.2 2, hh 1]

theorem rectFamily_midpoint_strict (lo hi : State 2) (hlt : ∀ i, lo i < hi i) :
    ∀ i, 0 < (rectFamily lo hi).value i ((1 / 2 : ℝ) • lo + (1 / 2 : ℝ) • hi) := by
  intro i
  have h0 := hlt 0
  have h1 := hlt 1
  fin_cases i <;> simp [rectFamily_value, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> linarith

noncomputable def tightInitialLower (z : State 2) : State 2 := fun i => min (z i) (1 / 2)

def tightInitialUpper (z : State 2) : State 2 := fun i => max (z i) 2

theorem tightInitialLower_positive {z : State 2} (hz : Positive z) :
    Positive (tightInitialLower z) := fun i => lt_min (hz i) (by norm_num)

theorem tight_initial_mem (z : State 2) : z ∈ Icc (tightInitialLower z) (tightInitialUpper z) :=
  ⟨fun _ => min_le_left _ _, fun _ => le_max_left _ _⟩

noncomputable def tightInitialTrap (c : State 2) {z : State 2} (hz : Positive z) :
    network.WeakFiniteClassTrap 1 2 c z where
  branchCount := 4
  nonemptyBranches := inferInstance
  family := rectFamily (tightInitialLower z) (tightInitialUpper z)
  level := 0
  anchor := (1 / 2 : ℝ) • tightInitialLower z + (1 / 2 : ℝ) • tightInitialUpper z
  anchor_class := by rw [stoichiometricClass]; trivial
  anchor_strict := rectFamily_midpoint_strict _ _ (fun i =>
    lt_of_le_of_lt (min_le_right _ _) (lt_of_lt_of_le (by norm_num) (le_max_right _ _)))
  initial_mem := by rw [rectFamily_plateau, stoichiometricClass, inter_univ]; exact tight_initial_mem z
  compact := by rw [rectFamily_plateau, stoichiometricClass, inter_univ]; exact isCompact_Icc
  positive := by
    rw [rectFamily_plateau, stoichiometricClass, inter_univ]
    exact fun y hy i => (tightInitialLower_positive hz i).trans_le (hy.1 i)
  faces := rectFamily_weak_faces _ _ c (tightInitialLower_positive hz)
    (fun _ => min_le_right _ _) (fun _ => le_max_right _ _)

theorem tightInitialTrap_carrier (c : State 2) {z : State 2} (hz : Positive z) :
    (tightInitialTrap c hz).carrier = Icc (tightInitialLower z) (tightInitialUpper z) := by
  change (rectFamily _ _).plateau 0 ∩ network.stoichiometricClass c = _
  rw [rectFamily_plateau, stoichiometricClass, inter_univ]

theorem integralSolution_mem_tight_initial_box {k : Fin 4 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 2} (hz : Positive z)
    {x : ℝ → State 2} (hx : network.IsIntegralSolution k z x) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ Icc (tightInitialLower z) (tightInitialUpper z) := by
  simpa only [tightInitialTrap_carrier] using (tightInitialTrap z hz).integralSolution_mem hk hx ht

theorem integralSolution_mem_tight_target {k : Fin 4 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 2} (hz : z ∈ targetFamily.plateau 0)
    {x : ℝ → State 2} (hx : network.IsIntegralSolution k z x) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ targetFamily.plateau 0 := by
  have hzB : z ∈ Icc (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ => 2) := by
    simpa only [targetFamily_plateau, zero_add, sub_zero] using hz
  have hzP : Positive z := fun i => lt_of_lt_of_le (by norm_num) (hzB.1 i)
  have hl : tightInitialLower z = fun _ => (1 / 2 : ℝ) := by
    funext i; exact min_eq_right (hzB.1 i)
  have hh : tightInitialUpper z = fun _ => (2 : ℝ) := by
    funext i; exact max_eq_right (hzB.2 i)
  simpa only [targetFamily_plateau, zero_add, sub_zero, hl, hh] using
    integralSolution_mem_tight_initial_box hk hzP hx ht

theorem uniformPermanent_via_weak_traps (c : State 2) :
    network.UniformPermanent 1 2 c (fun _ => True) := by
  apply network.uniformPermanent_of_weak_finite_class_traps targetFamily 1 2 0 c (fun _ => True)
  · rw [stoichiometricClass, inter_univ, targetFamily_plateau]
    exact ⟨![1, 1], by constructor <;> intro i <;> fin_cases i <;> norm_num⟩
  · rw [stoichiometricClass, inter_univ, targetFamily_plateau]
    exact isCompact_Icc
  · rw [stoichiometricClass, inter_univ, targetFamily_plateau]
    intro y hy i
    have hh := hy.1 i
    norm_num at hh
    linarith
  · intro z hz
    exact ⟨tightInitialTrap c hz.1, fun a ha y _ hm i hai => targetFamily_strict_exterior a ha hm i hai⟩

end Endotactic.SlackBox
