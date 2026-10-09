import Endotactic.OneSpeciesDominance
import Endotactic.BoxInvariance
import Endotactic.IntegralUniqueness
import Endotactic.Stoichiometry

/-!
# From scalar exterior signs to measurable-rate permanence

First trap each positive initial value in its own positive interval. Uniqueness
places every original integral solution in that interval. Compactness of the
coefficient box times that interval then supplies a strictly positive margin
on both exterior regions. The capped affine minimum gives finite entry into
the common interval, chosen before rates and initial values.

The margin may depend on the initial interval; a common entry time is neither
assumed nor claimed. In particular, no positive flux bound near zero over the
entire positive half-line is assumed.
-/

namespace Endotactic

open Set

variable {E : Type*} [Fintype E] {N : Network 1 E} {ℓ u : ℝ}

namespace Network.ScalarTrap

variable (T : N.ScalarTrap ℓ u)

include T

def initialLower (z : State 1) : State 1 := fun _ => min (z 0) T.lower

def initialUpper (z : State 1) : State 1 := fun _ => max (z 0) T.upper

theorem initialLower_positive {z : State 1} (hz : Positive z) :
    Positive (T.initialLower z) := fun _ => lt_min (hz 0) T.lower_pos

theorem initial_box_order (z : State 1) : T.initialLower z ≤ T.initialUpper z :=
  fun _ => (min_le_left _ _).trans (le_max_left _ _)

theorem initial_mem_box (z : State 1) : z ∈ Icc (T.initialLower z) (T.initialUpper z) := by
  constructor <;> intro i <;> fin_cases i
  · exact min_le_left _ _
  · exact le_max_left _ _

theorem exists_global_positive_in_initial_box {k : E → ℝ → ℝ}
    (hk : AdmissibleRates k ℓ u) {z : State 1} (hz : Positive z) :
    ∃ x : ℝ → State 1, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ Icc (T.initialLower z) (T.initialUpper z) := by
  apply N.exists_global_positive_in_box hk (T.initialLower z) (T.initialUpper z)
    (T.initial_box_order z) (T.initialLower_positive hz) (T.initial_mem_box z)
  · intro t ht y _ i he
    fin_cases i
    have hy : 0 < y 0 := he ▸ T.initialLower_positive hz 0
    have hya : y 0 ≤ T.lower := he ▸ min_le_right _ _
    exact (T.lower_flux _ (fun e => hk.2 e t ht) y hy hya).le
  · intro t ht y _ i he
    fin_cases i
    have hyb : T.upper ≤ y 0 := he ▸ le_max_right _ _
    exact (T.upper_flux _ (fun e => hk.2 e t ht) y hyb).le

theorem positiveWellPosed {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u)
    {z : State 1} (hz : Positive z) : N.PositiveWellPosed k z := by
  obtain ⟨x, hx, _⟩ := T.exists_global_positive_in_initial_box hk hz
  exact N.positiveWellPosed_of_exists hk ⟨x, hx⟩

theorem integralSolution_mem_initial_box {k : E → ℝ → ℝ}
    (hk : AdmissibleRates k ℓ u) {z : State 1} (hz : Positive z)
    {x : ℝ → State 1} (hx : N.IsIntegralSolution k z x) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ Icc (T.initialLower z) (T.initialUpper z) := by
  obtain ⟨y, hy, hstay⟩ := T.exists_global_positive_in_initial_box hk hz
  rw [hx.eqOn_nonnegative N hk hy.1 ht]
  exact hstay t ht

noncomputable def family : AffineFamily 1 3 where
  slope := ![![1], ![-1], ![0]]
  offset := ![-T.lower, T.upper, 0]

theorem family_values (x : State 1) :
    T.family.value 0 x = x 0 - T.lower ∧
      T.family.value 1 x = T.upper - x 0 ∧ T.family.value 2 x = 0 := by
  simp [family, AffineFamily.value, dot, sub_eq_add_neg, add_comm]

theorem family_plateau :
    T.family.plateau 0 = Icc (fun _ : Fin 1 => T.lower) (fun _ => T.upper) := by
  ext x
  constructor
  · intro hx
    have hl := hx 0
    have hu := hx 1
    rw [(T.family_values x).1] at hl
    rw [(T.family_values x).2.1] at hu
    constructor
    · intro i; fin_cases i; change T.lower ≤ x 0; linarith
    · intro i; fin_cases i; change x 0 ≤ T.upper; linarith
  · intro hx i
    have hl := hx.1 0
    have hu := hx.2 0
    fin_cases i
    · change 0 ≤ T.family.value 0 x
      rw [(T.family_values x).1]; linarith
    · change 0 ≤ T.family.value 1 x
      rw [(T.family_values x).2.1]; linarith
    · change 0 ≤ T.family.value 2 x
      rw [(T.family_values x).2.2]

theorem family_minimum_le_zero (x : State 1) : T.family.minimum x ≤ 0 := by
  have hh := T.family.minimum_le_constant_branch 2
    (by intro j; fin_cases j; rfl) x
  simpa [family] using hh

theorem exists_outside_margin_in_box (lo hi : State 1) (hlo : Positive lo) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
      ∀ x ∈ Icc lo hi,
        (x 0 ≤ T.lower → δ ≤ N.rhs k x 0) ∧
        (T.upper ≤ x 0 → δ ≤ -N.rhs k x 0) := by
  let lowerSide : Set ((E → ℝ) × State 1) :=
    (Icc (fun _ : E => ℓ) (fun _ => u) ×ˢ Icc lo hi) ∩ {p | p.2 0 ≤ T.lower}
  let upperSide : Set ((E → ℝ) × State 1) :=
    (Icc (fun _ : E => ℓ) (fun _ => u) ×ˢ Icc lo hi) ∩ {p | T.upper ≤ p.2 0}
  have hc : Continuous (fun p : (E → ℝ) × State 1 => N.rhs p.1 p.2 0) :=
    (continuous_apply 0).comp N.rhs_joint_contDiff.continuous
  have hlc : IsCompact lowerSide := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le ((continuous_apply 0).comp continuous_snd) continuous_const)
  have huc : IsCompact upperSide := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const ((continuous_apply 0).comp continuous_snd))
  obtain ⟨δl, hδl, hbl⟩ := hlc.exists_forall_le' hc.continuousOn (a := 0) (by
    intro p hp
    exact T.lower_flux p.1 (fun e => ⟨hp.1.1.1 e, hp.1.1.2 e⟩) p.2
      ((hlo 0).trans_le (hp.1.2.1 0)) hp.2)
  obtain ⟨δu, hδu, hbu⟩ := huc.exists_forall_le' hc.neg.continuousOn (a := 0) (by
    intro p hp
    exact neg_pos.mpr (T.upper_flux p.1 (fun e => ⟨hp.1.1.1 e, hp.1.1.2 e⟩) p.2 hp.2))
  refine ⟨min δl δu, lt_min hδl hδu, ?_⟩
  intro k hk x hx
  have hkbox : k ∈ Icc (fun _ : E => ℓ) (fun _ => u) :=
    ⟨fun e => (hk e).1, fun e => (hk e).2⟩
  exact ⟨fun hxl => (min_le_left _ _).trans (hbl (k, x) ⟨⟨hkbox, hx⟩, hxl⟩),
    fun hxu => (min_le_right _ _).trans (hbu (k, x) ⟨⟨hkbox, hx⟩, hxu⟩)⟩

theorem exists_active_margin_in_box (lo hi : State 1) (hlo : Positive lo) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
      ∀ x ∈ Icc lo hi, T.family.minimum x < 0 → ∀ i,
        T.family.Active i x → δ ≤ dot (T.family.slope i) (N.rhs k x) := by
  obtain ⟨δ, hδ, hb⟩ := T.exists_outside_margin_in_box lo hi hlo
  refine ⟨δ, hδ, ?_⟩
  intro k hk x hx hmin i hi
  have hvalue : T.family.value i x < 0 :=
    ((T.family.active_iff_minimum_eq i x).mp hi) ▸ hmin
  fin_cases i
  · change T.family.value 0 x < 0 at hvalue
    rw [(T.family_values x).1] at hvalue
    simpa [family, dot] using (hb k hk x hx).1 (by linarith)
  · change T.family.value 1 x < 0 at hvalue
    rw [(T.family_values x).2.1] at hvalue
    simpa [family, dot] using (hb k hk x hx).2 (by linarith)
  · change T.family.value 2 x < 0 at hvalue
    rw [(T.family_values x).2.2] at hvalue
    exact False.elim (lt_irrefl 0 hvalue)

theorem eventuallyIn_interval {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u)
    {z : State 1} (hz : Positive z) {x : ℝ → State 1} (hx : N.IsIntegralSolution k z x) :
    EventuallyIn x (Icc (fun _ : Fin 1 => T.lower) (fun _ => T.upper)) := by
  obtain ⟨δ, hδ, hb⟩ := T.exists_active_margin_in_box (T.initialLower z) (T.initialUpper z)
    (T.initialLower_positive hz)
  have hh := T.family.eventuallyIn_plateau hx hδ
    (fun t _ => T.family_minimum_le_zero (x t))
    (fun t ht hm i hi => hb _ (fun e => hk.2 e t ht) (x t)
      (T.integralSolution_mem_initial_box hk hz hx ht) hm i hi)
  rwa [T.family_plateau] at hh

theorem uniformPermanent (hnonzero : ∃ e, N.vector e 0 ≠ 0) (c : State 1)
    (regular : (E → ℝ → ℝ) → Prop) : N.UniformPermanent ℓ u c regular := by
  refine ⟨Icc (fun _ : Fin 1 => T.lower) (fun _ => T.upper), ?_, isCompact_Icc, ?_, ?_⟩
  · exact ⟨fun _ => T.lower, le_rfl, fun _ => T.lower_lt_upper.le⟩
  · intro x hx
    rw [N.oneSpecies_positiveClass_of_nonzero hnonzero]
    exact T.lower_pos.trans_le (hx.1 0)
  · intro k hk _
    refine ⟨fun z hz => T.positiveWellPosed hk hz.1, ?_⟩
    intro z hz x hx
    exact T.eventuallyIn_interval hk hz.1 hx.1

end Network.ScalarTrap

end Endotactic
