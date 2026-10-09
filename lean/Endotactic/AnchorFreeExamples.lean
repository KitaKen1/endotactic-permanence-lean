import Endotactic.RateBoxRestriction
import Endotactic.ConversionRelativeWeakTrap
import Endotactic.BirthDeathPermanence

/-!
# Actual conservative application and necessity of distinct rate endpoints

The four-face conservative example now omits both anchors and moving-face
witnesses. A positive singleton for fixed birth/death rates has weak faces but
no relative anchor. The same singleton fails the weak-face certificate when
one rate is varied, illustrating why a wider certificate must be proved.
-/

namespace Endotactic.Conversion

open Set

noncomputable def augmentedAnchorFreeTrap {α : ℝ} (c : State 2)
    (hα : 0 < α) (hα4 : 4 * α ≤ c 0 + c 1) {z : State 2}
    (hz : z ∈ (family α).plateau 0 ∩ conversion.stoichiometricClass c) :
    conversion.AnchorFreeWeakFiniteClassTrap 1 2 c z where
  branchCount := 4
  nonemptyBranches := inferInstance
  family := augmentedFamily α (c 0 + c 1)
  level := 0
  initial_mem := by rw [augmentedFamily_class_carrier]; exact hz
  compact := by rw [augmentedFamily_class_carrier]; exact family_class_compact α c
  positive := by rw [augmentedFamily_class_carrier]; exact family_class_positive hα c
  faces := augmentedFamily_weak_faces c hα hα4

theorem augmentedAnchorFreeTrap_carrier {α : ℝ} (c : State 2)
    (hα : 0 < α) (hα4 : 4 * α ≤ c 0 + c 1) {z : State 2}
    (hz : z ∈ (family α).plateau 0 ∩ conversion.stoichiometricClass c) :
    (augmentedAnchorFreeTrap c hα hα4 hz).carrier =
      (family α).plateau 0 ∩ conversion.stoichiometricClass c :=
  augmentedFamily_class_carrier α c

theorem integralSolution_mem_anchor_free_trap {α : ℝ} (c : State 2)
    (hα : 0 < α) (hα4 : 4 * α ≤ c 0 + c 1) {z : State 2}
    (hz : z ∈ (family α).plateau 0 ∩ conversion.stoichiometricClass c)
    {k : Fin 2 → ℝ → ℝ} (hk : AdmissibleRates k 1 2)
    {x : ℝ → State 2} (hx : conversion.IsIntegralSolution k z x) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ (augmentedFamily α (c 0 + c 1)).plateau 0 ∩ conversion.stoichiometricClass c :=
  (augmentedAnchorFreeTrap c hα hα4 hz).integralSolution_mem (by norm_num) hk hx ht

theorem uniformPermanent_via_anchor_free_weak_traps (c : State 2) (hs : 0 < c 0 + c 1) :
    conversion.UniformPermanent 1 2 c (fun _ => True) := by
  let s : ℝ := c 0 + c 1
  have hne : ((absorbingFamily s).plateau 0 ∩ conversion.stoichiometricClass c).Nonempty := by
    rw [absorbingFamily_plateau]
    refine ⟨![s / 2, s / 2], ?_, ?_⟩
    · intro i; fin_cases i <;> simp [family_value] <;> linarith
    · apply class_iff_total.mpr
      simp [s]
  apply conversion.uniformPermanent_of_anchor_free_weak_finite_class_traps (absorbingFamily s)
    1 2 0 c (fun _ => True) (by norm_num) hne
    (by rw [absorbingFamily_plateau]; exact family_class_compact _ _)
    (by rw [absorbingFamily_plateau]; exact family_class_positive (by dsimp [s]; linarith) c)
  intro z hz
  let α : ℝ := min (min (z 0) (z 1)) (s / 4)
  have hα : 0 < α := lt_min (lt_min (hz.1 0) (hz.1 1)) (by dsimp [s]; linarith)
  have hα0 : α ≤ z 0 := (min_le_left _ _).trans (min_le_left _ _)
  have hα1 : α ≤ z 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hα4 : 4 * α ≤ c 0 + c 1 := by
    have hh : α ≤ s / 4 := min_le_right _ _
    dsimp [s] at hh
    linarith
  have hzA : z ∈ (family α).plateau 0 ∩ conversion.stoichiometricClass c := by
    refine ⟨?_, hz.2⟩
    intro i; fin_cases i <;> simp [family_value] <;> linarith
  let T := augmentedAnchorFreeTrap c hα hα4 hzA
  refine ⟨T, ?_⟩
  intro a ha y hy hm i hai
  have htotal : y 0 + y 1 = s := class_iff_total.mp hy.2
  exact lt_of_lt_of_le (by dsimp [s]; linarith : 0 < s / 4)
    (absorbingFamily_flux_margin s a ha y (T.positive hy) htotal hm i hai)

end Endotactic.Conversion

namespace Endotactic.Examples.AnchorFree

open Set

noncomputable def singletonFamily : AffineFamily 1 2 where
  slope := ![![1], ![-1]]
  offset := ![-1, 1]

theorem singletonFamily_value (i : Fin 2) (y : State 1) :
    singletonFamily.value i y = if i = 0 then y 0 - 1 else 1 - y 0 := by
  fin_cases i <;> simp [singletonFamily, AffineFamily.value, dot] <;> ring

theorem singletonFamily_mem_iff (y : State 1) :
    y ∈ singletonFamily.plateau 0 ↔ y 0 = 1 := by
  constructor
  · intro hy
    have hl := hy 0
    have hu := hy 1
    rw [singletonFamily_value] at hl hu
    norm_num at hl hu
    linarith
  · intro hy i
    rw [singletonFamily_value, hy]
    split_ifs <;> norm_num

theorem singletonFamily_positive : singletonFamily.plateau 0 ⊆ {y | Positive y} := by
  intro y hy i
  fin_cases i
  change 0 < y 0
  rw [(singletonFamily_mem_iff y).mp hy]
  norm_num

theorem singletonFamily_weak_fixed_rates (c : State 1) :
    birthDeath.ClassWeakAffineFaceCertificate singletonFamily 1 1 0 c := by
  intro i a ha y hy _
  have ha0 : a 0 = 1 := le_antisymm (ha.2 0) (ha.1 0)
  have ha1 : a 1 = 1 := le_antisymm (ha.2 1) (ha.1 1)
  have hy0 : y 0 = 1 := (singletonFamily_mem_iff y).mp hy.1
  have hz : birthDeath.rhs a y = 0 := by
    ext j
    fin_cases j
    simp [birthDeath_rhs_coordinate, ha0, ha1, hy0]
  rw [hz]
  simp [dot]

theorem singletonFamily_no_relative_anchor (c : State 1) :
    ¬ ∃ p, birthDeath.ClassRelativeAnchor singletonFamily 0 c p := by
  rintro ⟨p, hp⟩
  have hn0 : ¬ ∀ e, birthDeath.projection (singletonFamily.slope 0) e = 0 := by
    intro h
    have hh := h 0
    norm_num [singletonFamily, birthDeath, Network.projection, Network.vector,
      realComplex, dot] at hh
  have hn1 : ¬ ∀ e, birthDeath.projection (singletonFamily.slope 1) e = 0 := by
    intro h
    have hh := h 0
    norm_num [singletonFamily, birthDeath, Network.projection, Network.vector,
      realComplex, dot] at hh
  have h0 := (hp.2 0).resolve_left hn0
  have h1 := (hp.2 1).resolve_left hn1
  rw [singletonFamily_value] at h0 h1
  norm_num at h0 h1
  linarith

theorem singletonFamily_not_weak_variable_rates :
    ¬ birthDeath.ClassWeakAffineFaceCertificate singletonFamily 1 2 0 (![1] : State 1) := by
  intro h
  have hy : (![1] : State 1) ∈ singletonFamily.plateau 0 ∩
      birthDeath.stoichiometricClass (![1] : State 1) := by
    refine ⟨(singletonFamily_mem_iff _).mpr (by simp), ?_⟩
    change (![1] : State 1) - ![1] ∈ birthDeath.stoichiometricSubspace
    simp
  have ha : (![2, 1] : Fin 2 → ℝ) ∈ Icc (fun _ => 1) (fun _ => 2) := by
    constructor <;> intro e <;> fin_cases e <;> norm_num
  have hh := h 1 ![2, 1] ha ![1] hy (by norm_num [singletonFamily_value])
  norm_num [singletonFamily, dot, birthDeath_rhs_coordinate] at hh

end Endotactic.Examples.AnchorFree
