import Endotactic.FiniteLiftTolerance
import Endotactic.AffinePowerExamples

/-!
# Actual 1D-to-2D lifts, ties and the final minimum type

The omitted exponent and common offset are arbitrary in the binary tests.
The singleton last-type example has a nonempty minimum stratum and verifies
approximation, cube slopes and negative-power decay with real lifted labels.
-/

namespace Endotactic.LiftExamples

open Filter Topology Asymptotics

def firstCoordinate : Fin 1 ↪ Fin 2 where
  toFun _ := 0
  inj' _ _ _ := Subsingleton.elim _ _

theorem firstCoordinate_only_omitted (j : Fin 2) (hj : j ∉ Set.range firstCoordinate) :
    j = 1 := by
  fin_cases j
  · exact (hj ⟨0, rfl⟩).elim
  · rfl

theorem binary_lift_raised_active_iff (β t : ℝ) (γ : ℝ → ℝ)
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1) (p : State 2) :
    (((PowerExamples.binaryPowerFamily β).coordinateLift firstCoordinate t γ).atScale h).Active
        1 (exponentialPoint h p) ↔ β ≤ p 0 := by
  rw [ScaledAffineFamily.coordinateLift_exponential_active_iff,
    PowerExamples.binaryPowerFamily_raised_active_iff hh hh1]
  rfl

theorem binary_lift_boundary_all_active (β t η h : ℝ) (γ : ℝ → ℝ) (i : Fin 2) :
    (((PowerExamples.binaryPowerFamily β).coordinateLift firstCoordinate t γ).atScale h).Active
      i (exponentialPoint h ![β, η]) := by
  rw [ScaledAffineFamily.coordinateLift_exponential_active_iff]
  have heq : restrictCoordinates firstCoordinate ![β, η] = fun _ => β := by
    funext j
    rfl
  rw [heq]
  exact PowerExamples.binaryPowerFamily_boundary_all_active β h i

theorem binary_lift_raised_limit_ge (β t : ℝ) (γ : ℝ → ℝ)
    {h : ℕ → ℝ} {p : ℕ → State 2} {q : State 2}
    (hh : Tendsto h atTop (𝓝 0)) (hpos : ∀ n, 0 < h n)
    (hp : Tendsto p atTop (𝓝 q))
    (hactive : ∀ n,
      (((PowerExamples.binaryPowerFamily β).coordinateLift firstCoordinate t γ).atScale
        (h n)).Active 1 (exponentialPoint (h n) (p n))) : β ≤ q 0 := by
  apply PowerExamples.binaryPowerFamily_raised_limit_ge β hh hpos
    (tendsto_restrictCoordinates firstCoordinate hp)
  intro n
  exact (ScaledAffineFamily.coordinateLift_exponential_active_iff _ _ _ _ _ _ _).mp
    (hactive n)

theorem last_minimum_seed_sequential (t β : ℝ) (htβ : t < β) (γ : ℝ → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ((minimumSeedFamily 1 β).coordinateLift firstCoordinate t γ).HasSequentialActivityBound
        {q | q ≤ (fun _ => β) ∧ exponentMinimum q = t ∧ β ≤ q 0} (fun _ => ε) := by
  have hB : (minimumSeedFamily 1 β).HasSequentialActivityBound
      (Set.Icc (fun _ => β) (fun _ => β)) (fun _ => ε) := by
    intro i h p q _ _ _ hq _
    have heq : q = fun _ => β := funext fun j => le_antisymm (hq.2 j) (hq.1 j)
    change ‖q - (fun _ => β)‖ < ε
    rw [heq, sub_self, norm_zero]
    exact hε
  have hseq := (minimumSeedFamily 1 β).coordinateLift_last_minimum_stratum
    firstCoordinate 1 firstCoordinate_only_omitted t β β htβ γ (fun _ => ε)
    (fun _ => hε) hB
  apply ScaledAffineFamily.sequentialActivityBound_mono _ hseq
  intro q hq
  exact ⟨hq.1, hq.2.1, fun _ => hq.2.2⟩

theorem last_minimum_seed_stratum_nonempty (t β : ℝ) (htβ : t < β) :
    ({q : State 2 | q ≤ (fun _ => β) ∧ exponentMinimum q = t ∧ β ≤ q 0} :
      Set (State 2)).Nonempty := by
  let q := extendCoordinates firstCoordinate t (fun _ : Fin 1 => β)
  have ho : (1 : Fin 2) ∉ Set.range firstCoordinate := by
    rintro ⟨j, hj⟩
    change (0 : Fin 2) = 1 at hj
    norm_num at hj
  refine ⟨q, ?_, ?_, ?_⟩
  · exact (extendCoordinates_mem_cube firstCoordinate ⟨le_rfl, htβ.le⟩
      ⟨fun _ => htβ.le, fun _ => le_rfl⟩).2
  · exact extendCoordinates_minimum firstCoordinate t _ (fun _ => htβ.le) 1 ho
  · change β ≤ extendCoordinates firstCoordinate t (fun _ => β) (firstCoordinate 0)
    rw [extendCoordinates_apply]

theorem last_minimum_seed_slopes_and_decay (t β : ℝ) (htβ : t < β) :
    (∀ i, ((minimumSeedFamily 1 β).coordinateLift firstCoordinate t
      (fun h => -(h ^ β))).slope i ∈ Set.Icc (fun _ => t) (fun _ => β)) ∧
    (∀ i, IsLittleO (𝓝[>] (0 : ℝ))
      (((minimumSeedFamily 1 β).coordinateLift firstCoordinate t
        (fun h => -(h ^ β))).offset i) (fun h => h ^ t)) := by
  constructor
  · exact (minimumSeedFamily 1 β).coordinateLift_slopes_mem_cube firstCoordinate _
      ⟨le_rfl, htβ.le⟩ (fun _ => ⟨fun _ => htβ.le, fun _ => le_rfl⟩)
  · exact (minimumSeedFamily 1 β).coordinateLift_offset_isLittleO firstCoordinate t t _
      (rpow_isLittleO_nhdsGT_zero htβ).neg_left
      (fun i => minimumSeedFamily_offset_littleO 1 β t i)

end Endotactic.LiftExamples
