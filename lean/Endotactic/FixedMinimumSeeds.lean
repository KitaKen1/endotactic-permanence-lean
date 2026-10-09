import Endotactic.ExponentMinimum
import Endotactic.ScaledActivityExamples

/-!
# Genuine fixed-minimum seed families and discontinuous-offset limit sets

The singleton family gives the fixed-minimum starting cases in dimension one
and at the top of any cube. Neighborhood extension is actually instantiated.
These are local stratum families, not the globally combined affine family A.
-/

namespace Endotactic

open Filter Topology

def minimumSeedFamily (d : ℕ) (t : ℝ) : ScaledAffineFamily d 1 where
  slope _ := fun _ => t
  offset _ _ := 0

theorem minimumSeedFamily_activityLimit (d : ℕ) (t : ℝ) (i : Fin 1) :
    (minimumSeedFamily d t).activityLimit i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  refine mem_scaleLimit_of_sequences (fun n : ℕ => 1 / ((n : ℝ) + 1))
    (fun _ => q) (fun _ => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat tendsto_const_nhds ?_
  intro n j
  have hji : j = i := Subsingleton.elim _ _
  rw [hji]

theorem minimumSeedFamily_offset_littleO (d : ℕ) (t a : ℝ) (i : Fin 1) :
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) ((minimumSeedFamily d t).offset i)
      (fun h => h ^ a) := Asymptotics.isLittleO_zero _ _

/-- Any positive tolerance works on each one-dimensional minimum stratum.
The sequences approaching that stratum may lie outside the cube. -/
theorem minimumSeedFamily_oneDim_fixedMinimum (a b t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (minimumSeedFamily 1 t).HasSequentialActivityBound
      (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = t})
      (fun _ => ε) := by
  intro i h p q _ _ _ hq _
  have hqt : q = fun _ => t := by
    obtain ⟨j, hj⟩ := exponentMinimum_attained q
    funext k
    have hkj : k = j := Subsingleton.elim _ _
    rw [hkj, ← hj]
    exact hq.2
  change ‖q - (fun _ => t)‖ < ε
  rw [hqt, sub_self, norm_zero]
  exact hε

/-- In any positive dimension, the cube's top minimum stratum is a singleton.
This is an actual seed construction; only positivity of the chosen tolerance
at that one slope is required. -/
theorem minimumSeedFamily_top_fixedMinimum {d : ℕ} [NeZero d]
    (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (minimumSeedFamily d b).HasSequentialActivityBound
      (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = b})
      (fun _ => ε) := by
  intro i h p q _ _ _ hq _
  have hqt := (exponentMinimum_eq_top_iff hq.1.2).mp hq.2
  change ‖q - (fun _ => b)‖ < ε
  rw [hqt, sub_self, norm_zero]
  exact hε

theorem minimumSeedFamily_oneDim_nearby_uniform (a b t : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => a) (fun _ => b), |exponentMinimum q - t| ≤ ρ →
          ∀ i : Fin 1,
            ((minimumSeedFamily 1 t).atScale h).Active i (exponentialPoint h q) →
              ‖q - (minimumSeedFamily 1 t).slope i‖ < ε :=
  (minimumSeedFamily 1 t).uniformActivityBound_near_minimum a b (fun _ => ε) t
    (minimumSeedFamily_oneDim_fixedMinimum a b t hε)

theorem minimumSeedFamily_top_nearby_uniform {d : ℕ} [NeZero d]
    (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => a) (fun _ => b), |exponentMinimum q - b| ≤ ρ →
          ∀ i : Fin 1,
            ((minimumSeedFamily d b).atScale h).Active i (exponentialPoint h q) →
              ‖q - (minimumSeedFamily d b).slope i‖ < ε :=
  (minimumSeedFamily d b).uniformActivityBound_near_minimum a b (fun _ => ε) b
    (minimumSeedFamily_top_fixedMinimum a b hε)

/-- Both tied labels of the already checked discontinuous-offset family have
the whole ambient exponent space as their closed activity-limit set. This
instantiates the limit-set API without a hidden continuity assumption. -/
theorem ActivityExamples.parallelFamily_activityLimit {d : ℕ} (r : State d)
    (i : Fin 2) : (ActivityExamples.parallelFamily r).activityLimit i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  refine mem_scaleLimit_of_sequences (fun n : ℕ => 1 / ((n : ℝ) + 1))
    (fun _ => q) (fun _ => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat tendsto_const_nhds ?_
  intro n
  exact ActivityExamples.parallelFamily_all_active r (by positivity) i _

end Endotactic
