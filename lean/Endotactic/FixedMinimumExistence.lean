import Endotactic.AffineSupportInduction

/-!
# Fixed-minimum families exist under the lower-dimensional induction hypothesis

Dimension one and the cube's top use the actual seed. The other cases now
construct every block and level, rather than accepting FixedMinimumData as an
input. This module retains minimum combination as an explicit input;
`MinimumBandSelection` supplies its proof downstream and closes full A.
-/

namespace Endotactic

open Filter Topology Asymptotics

structure FixedMinimumApproximation (d : ℕ) [NeZero d] (a b t : ℝ) (E : State d → ℝ) where
  size : ℕ
  size_pos : 0 < size
  family : ScaledAffineFamily d size
  seed : Fin size
  seed_slope : family.slope seed = fun _ => t
  seed_offset : ∀ h, family.offset seed h = 0
  cube : ∀ i, family.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)
  minimum : ∀ i, exponentMinimum (family.slope i) = t
  power_bound : ∀ i, ∃ β : ℝ, t < β ∧
    IsBigO (𝓝[>] (0 : ℝ)) (family.offset i) (fun h => h ^ β)
  approximation : family.HasSequentialActivityBound
    (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = t})
    (fun i => E (family.slope i))

theorem exists_seed_fixedMinimumApproximation {d : ℕ} [NeZero d]
    {a b t : ℝ} (E : State d → ℝ) (ht : t ∈ Set.Icc a b)
    (hE : ∀ r ∈ Set.Icc (fun _ => a) (fun _ => b), 0 < E r)
    (hcase : d = 1 ∨ t = b) : Nonempty (FixedMinimumApproximation d a b t E) := by
  have htol : 0 < E (fun _ => t) := hE _ ⟨fun _ => ht.1, fun _ => ht.2⟩
  refine ⟨{ size := 1
            size_pos := by norm_num
            family := minimumSeedFamily d t
            seed := 0
            seed_slope := rfl
            seed_offset := fun _ => rfl
            cube := fun _ => ⟨fun _ => ht.1, fun _ => ht.2⟩
            minimum := ?_
            power_bound := ?_
            approximation := ?_ }⟩
  · intro i
    obtain ⟨j, hj⟩ := exponentMinimum_attained (fun _ : Fin d => t)
    exact hj
  · intro i
    refine ⟨t + 1, by linarith, ?_⟩
    exact isBigO_zero _ _
  · rcases hcase with hd | htop
    · subst d
      exact minimumSeedFamily_oneDim_fixedMinimum a b t htol
    · subst t
      exact minimumSeedFamily_top_fixedMinimum a b htol

theorem exists_fixedMinimumApproximation_of_lower_dimensions {d : ℕ} [NeZero d]
    {a b : ℝ} (E : State d → ℝ)
    (hE : ∀ r ∈ Set.Icc (fun _ => a) (fun _ => b), 0 < E r)
    (hIH : ∀ n : ℕ, 0 < n → n < d → AffineApproximationInDimension n)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    Nonempty (FixedMinimumApproximation d a b t E) := by
  by_cases hcase : d = 1 ∨ t = b
  · exact exists_seed_fixedMinimumApproximation E ht hE hcase
  · have hd0 : d ≠ 0 := NeZero.ne d
    have hd : 1 < d := by omega
    have htb : t < b := lt_of_le_of_ne ht.2 (fun heq => hcase (Or.inr heq))
    have hEt : ∀ r ∈ Set.Icc (fun _ : Fin d => t) (fun _ => b), 0 < E r := by
      intro r hr
      exact hE r ⟨fun j => ht.1.trans (hr.1 j), hr.2⟩
    obtain ⟨D⟩ := exists_fixedMinimumData_of_lower_dimensions E hd htb hEt hIH
    exact ⟨{ size := _
             size_pos := seededAffine_card_pos D.size
             family := D.family
             seed := seededAffineSeed D.size
             seed_slope := ScaledAffineFamily.seededUnion_seed_slope t D.size D.lift
             seed_offset := ScaledAffineFamily.seededUnion_seed_offset t D.size D.lift
             cube := fun i => ⟨fun j => ht.1.trans ((D.slopes_mem_cube htb.le i).1 j),
               (D.slopes_mem_cube htb.le i).2⟩
             minimum := D.slopes_minimum
             power_bound := D.offset_power_bounds
             approximation := D.sequentialActivityBound_on_cube a hd htb.le hEt }⟩

theorem FixedMinimumApproximation.offsets_isLittleO {d : ℕ} [NeZero d]
    {a b t : ℝ} {E : State d → ℝ} (D : FixedMinimumApproximation d a b t E) :
    ∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (D.family.offset i) (fun h => h ^ t) := by
  intro i
  obtain ⟨β, htβ, hc⟩ := D.power_bound i
  exact offset_isLittleO_of_powerBound hc htβ

theorem FixedMinimumApproximation.near_minimum_with_decay {d : ℕ} [NeZero d]
    {a b t : ℝ} {E : State d → ℝ} (D : FixedMinimumApproximation d a b t E) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (D.family.offset i) (fun h => h ^ (t + ρ))) ∧
      D.family.HasSequentialActivityBound
        (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | |exponentMinimum q - t| ≤ ρ})
        (fun i => E (D.family.slope i)) := by
  choose β hβ hc using D.power_bound
  exact D.family.sequentialActivityBound_near_minimum_with_decay a b _ t
    D.approximation β hβ hc

theorem FixedMinimumApproximation.uniform_near_minimum {d : ℕ} [NeZero d]
    {a b t : ℝ} {E : State d → ℝ} (D : FixedMinimumApproximation d a b t E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => a) (fun _ => b), |exponentMinimum q - t| ≤ ρ →
          ∀ i, (D.family.atScale h).Active i (exponentialPoint h q) →
            ‖q - D.family.slope i‖ < E (D.family.slope i) :=
  D.family.uniformActivityBound_near_minimum a b _ t D.approximation

def FixedMinimumApproximationInDimension (d : ℕ) [NeZero d] : Prop :=
  ∀ a b : ℝ, a < b → ∀ E : State d → ℝ,
    (∀ p ∈ Set.Icc (fun _ => a) (fun _ => b), 0 < E p) →
      ∀ t ∈ Set.Icc a b, Nonempty (FixedMinimumApproximation d a b t E)

theorem fixedMinimumApproximation_of_lower_dimensions {d : ℕ} [NeZero d]
    (hIH : ∀ n : ℕ, 0 < n → n < d → AffineApproximationInDimension n) :
    FixedMinimumApproximationInDimension d := by
  intro a b _ E hE t ht
  exact exists_fixedMinimumApproximation_of_lower_dimensions E hE hIH t ht

/-- The global combination type retains all active labels at interval cuts.
It is proved downstream by `affineMinimumCombination`; it is not an axiom. -/
def AffineMinimumCombinationStatement : Prop :=
  ∀ d : ℕ, ∀ (_ : NeZero d), FixedMinimumApproximationInDimension d →
    AffineApproximationInDimension d

/-- Strong induction is closed once the minimum-combination theorem is
provided. The generic combination hypothesis is explicit in this type, and
`MinimumBandSelection` supplies it downstream without additional assumptions. -/
theorem finiteAffineApproximation_of_minimumCombination
    (hcombine : AffineMinimumCombinationStatement) : FiniteAffineApproximationStatement := by
  apply finiteAffineApproximation_iff_dimensions.mpr
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    let : NeZero d := ⟨by omega⟩
    exact hcombine d inferInstance (fixedMinimumApproximation_of_lower_dimensions
      (fun n hn hnd => ih n hnd hn))

end Endotactic
