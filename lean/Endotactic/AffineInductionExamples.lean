import Endotactic.FixedMinimumExistence

/-!
# Actual oracle construction and a discontinuous-tolerance application

For tolerances at least the ambient cube width, singleton lower blocks prove
the oracle, while the ambient seed alone still fails at a cube boundary. The
new staged construction then produces the complete fixed-minimum family.
Arbitrarily small tolerances still require the general lower-dimensional A.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem supportFamilyOracle_of_wide_tolerance {d : ℕ} {t b : ℝ}
    (E : State d → ℝ) (htb : t < b)
    (hwide : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), b - t ≤ E r) :
    SupportFamilyOracle d t b E := by
  intro U β htβ hβb
  let C : SupportAffineEntry U := ⟨1, minimumSeedFamily U.val.card β⟩
  have hcube : extendCoordinates U.embedding t (fun _ => β) ∈
      Set.Icc (fun _ => t) (fun _ => b) :=
    extendCoordinates_mem_cube U.embedding ⟨le_rfl, htb.le⟩
      ⟨fun _ => htβ.le, fun _ => hβb.le⟩
  have htol := hwide _ hcube
  refine ⟨C, by norm_num [C], ?_, ?_, ?_⟩
  · intro i
    exact ⟨fun _ => le_rfl, fun _ => hβb.le⟩
  · intro i
    exact isLittleO_zero _ _
  · intro i h p q _ _ _ hq _
    change ‖q - (fun _ => β)‖ < E (extendCoordinates U.embedding t (fun _ => β))
    rw [pi_norm_lt_iff ((sub_pos.mpr htb).trans_le htol)]
    intro j
    change |q j - β| < E (extendCoordinates U.embedding t (fun _ => β))
    rw [abs_of_nonneg (sub_nonneg.mpr (hq.1 j))]
    have hu := hq.2 j
    linarith

theorem exists_fixedMinimumData_of_wide_tolerance {d : ℕ} {t b : ℝ}
    (E : State d → ℝ) (hd : 1 < d) (htb : t < b)
    (hwide : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), b - t ≤ E r) :
    Nonempty (FixedMinimumData d t b E) :=
  exists_fixedMinimumData_of_oracle E hd htb
    (fun r hr => (sub_pos.mpr htb).trans_le (hwide r hr))
    (supportFamilyOracle_of_wide_tolerance E htb hwide)

theorem exists_fixedMinimumApproximation_of_wide_tolerance {d : ℕ} [NeZero d]
    {t b : ℝ} (E : State d → ℝ) (hd : 1 < d) (htb : t < b)
    (hwide : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), b - t ≤ E r) :
    Nonempty (FixedMinimumApproximation d t b t E) := by
  obtain ⟨D⟩ := exists_fixedMinimumData_of_wide_tolerance E hd htb hwide
  exact ⟨{ size := _
           size_pos := seededAffine_card_pos D.size
           family := D.family
           seed := seededAffineSeed D.size
           seed_slope := ScaledAffineFamily.seededUnion_seed_slope t D.size D.lift
           seed_offset := ScaledAffineFamily.seededUnion_seed_offset t D.size D.lift
           cube := D.slopes_mem_cube htb.le
           minimum := D.slopes_minimum
           power_bound := D.offset_power_bounds
           approximation := D.sequentialActivityBound hd htb.le
             (fun r hr => (sub_pos.mpr htb).trans_le (hwide r hr)) }⟩

/-- This actual active sequence prevents replacing the all-support output by
its ambient seed, even with tolerance equal to the whole cube width. -/
theorem seed_alone_fails_cube_width {d : ℕ} [NeZero d] (hd : 1 < d)
    {t b : ℝ} (htb : t < b) :
    ¬ (minimumSeedFamily d t).HasSequentialActivityBound
      (Set.Icc (fun _ => t) (fun _ => b) ∩ {q | exponentMinimum q = t})
      (fun _ => b - t) := by
  intro hseed
  let q : State d := fun j => if j = 0 then t else b
  have hq : q ∈ Set.Icc (fun _ => t) (fun _ => b) ∩ {q | exponentMinimum q = t} := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro j
      dsimp [q]
      split_ifs <;> first | exact le_rfl | exact htb.le
    · intro j
      dsimp [q]
      split_ifs <;> first | exact le_rfl | exact htb.le
    · apply le_antisymm
      · simpa [q] using exponentMinimum_le_coordinate q 0
      · obtain ⟨j, hj⟩ := exponentMinimum_attained q
        rw [hj]
        dsimp [q]
        split_ifs <;> first | exact le_rfl | exact htb.le
  have hn := hseed 0 (fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun _ => q) q
    (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
    tendsto_const_nhds hq (fun _ j => by have hj : j = 0 := Subsingleton.elim _ _; rw [hj])
  let j : Fin d := ⟨1, hd⟩
  have hj : j ≠ 0 := by simp [j, Fin.ext_iff]
  have heq : ‖(q - (minimumSeedFamily d t).slope 0) j‖ = b - t := by
    simp only [Pi.sub_apply, minimumSeedFamily, q, if_neg hj, Real.norm_eq_abs]
    exact abs_of_nonneg (sub_nonneg.mpr htb.le)
  have hl := norm_le_pi_norm (q - (minimumSeedFamily d t).slope 0) j
  rw [heq] at hl
  exact (not_lt_of_ge hl) hn

namespace InductionExamples

noncomputable def discontinuousTolerance (r : State 3) : ℝ := if r 0 = 0 then 1 else 2

theorem discontinuousTolerance_lower_bound (r : State 3) : 1 ≤ discontinuousTolerance r := by
  unfold discontinuousTolerance
  split_ifs <;> norm_num

theorem discontinuousTolerance_not_continuous : ¬ Continuous discontinuousTolerance := by
  intro hc
  let p : ℕ → State 3 := fun n j => if j = 0 then 1 / ((n : ℝ) + 1) else 0
  have hp : Tendsto p atTop (𝓝 (fun _ => 0)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hj : j = 0
    · simpa only [p, hj, if_pos rfl] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))
    · simp only [p, if_neg hj]
      exact tendsto_const_nhds
  have heq : (fun n => discontinuousTolerance (p n)) = fun _ : ℕ => 2 := by
    funext n
    have hn : (1 : ℝ) / ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
    change (if (1 : ℝ) / ((n : ℝ) + 1) = 0 then 1 else 2) = 2
    rw [if_neg hn]
  have hlim := (hc.tendsto (fun _ => 0)).comp hp
  change Tendsto (fun n => discontinuousTolerance (p n)) atTop
    (𝓝 (discontinuousTolerance (fun _ => 0))) at hlim
  rw [heq] at hlim
  have hbad : (2 : ℝ) = 1 := by
    simpa [discontinuousTolerance] using tendsto_nhds_unique tendsto_const_nhds hlim
  norm_num at hbad

theorem discontinuous_all_support_data_exists :
    Nonempty (FixedMinimumData 3 0 1 discontinuousTolerance) :=
  exists_fixedMinimumData_of_wide_tolerance discontinuousTolerance (by norm_num) (by norm_num)
    (fun r _ => by simpa using discontinuousTolerance_lower_bound r)

theorem discontinuous_fixed_minimum_exists :
    Nonempty (FixedMinimumApproximation 3 0 1 0 discontinuousTolerance) :=
  exists_fixedMinimumApproximation_of_wide_tolerance discontinuousTolerance
    (by norm_num) (by norm_num)
    (fun r _ => by simpa using discontinuousTolerance_lower_bound r)

theorem discontinuous_neighborhood_exists :
    ∃ D : FixedMinimumApproximation 3 0 1 0 discontinuousTolerance, ∃ ρ : ℝ, 0 < ρ ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (D.family.offset i) (fun h => h ^ ρ)) ∧
      D.family.HasSequentialActivityBound
        (Set.Icc (fun _ => 0) (fun _ => 1) ∩ {q | |exponentMinimum q| ≤ ρ})
        (fun i => discontinuousTolerance (D.family.slope i)) := by
  obtain ⟨D⟩ := discontinuous_fixed_minimum_exists
  obtain ⟨ρ, hρ, hdecay, hseq⟩ := D.near_minimum_with_decay
  exact ⟨D, ρ, hρ, by simpa using hdecay, by simpa using hseq⟩

end InductionExamples
end Endotactic
