import Endotactic.FixedMinimumAssembly

/-! A concrete all-support 3D family instantiates the assembly theorem.
Its seven labels cover types 0, 1 and 2. This is a local fixed-minimum
construction with constant tolerance 1, not the arbitrary-tolerance theorem. -/

namespace Endotactic.AssemblyExamples

open Filter Topology Asymptotics

noncomputable def exampleLevel (k : ℕ) : ℝ := if k = 1 then 1 / 2 else 1 / 3

theorem exampleLevel_pos (k : ℕ) : 0 < exampleLevel k := by
  unfold exampleLevel
  split_ifs <;> norm_num

theorem exampleLevel_lt_one (k : ℕ) : exampleLevel k < 1 := by
  unfold exampleLevel
  split_ifs <;> norm_num

noncomputable def allSupportData : FixedMinimumData 3 0 1 (fun _ => 1) where
  size _ := 1
  size_pos _ := by norm_num
  level := exampleLevel
  level_gt U := exampleLevel_pos U.val.card
  level_desc U hnext := by
    have hc : U.val.card = 1 := by have := U.property.1; omega
    norm_num [hc, exampleLevel]
  block U := minimumSeedFamily U.val.card (exampleLevel U.val.card)
  cube U _ := ⟨fun _ => le_rfl, fun _ => (exampleLevel_lt_one U.val.card).le⟩
  decay _ _ := isLittleO_zero _ _
  approximation U := by
    intro i h p q _ _ _ hq _
    change ‖q - (fun _ => exampleLevel U.val.card)‖ < 1
    rw [pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
    intro k
    change |q k - exampleLevel U.val.card| < 1
    rw [abs_of_nonneg (sub_nonneg.mpr (hq.1 k))]
    have hp := exampleLevel_pos U.val.card
    have hu := hq.2 k
    linarith
  seed_width := by norm_num [exampleLevel]
  next_width U _ _ := by simpa using exampleLevel_lt_one (U.val.card + 1)

theorem all_support_count : Fintype.card (RaisedSupport 3) = 6 := by decide

theorem all_label_count :
    Fintype.card (Σ U : Option (RaisedSupport 3), Fin (seededAffineSizes allSupportData.size U))
      = 7 := by decide

theorem all_support_fixed_minimum : allSupportData.family.HasSequentialActivityBound
    (Set.Icc (fun _ => 0) (fun _ => 1) ∩ {q | exponentMinimum q = 0}) (fun _ => 1) :=
  allSupportData.sequentialActivityBound (by norm_num) (by norm_num) (by intros; norm_num)

theorem all_support_slopes_and_decay :
    (∀ i, allSupportData.family.slope i ∈ Set.Icc (fun _ => 0) (fun _ => 1)) ∧
    (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (allSupportData.family.offset i) (fun h => h ^ (0 : ℝ))) :=
  ⟨allSupportData.slopes_mem_cube (by norm_num), allSupportData.offsets_isLittleO⟩

theorem all_support_stratum_nonempty :
    (Set.Icc (fun _ : Fin 3 => (0 : ℝ)) (fun _ => 1) ∩
      {q | exponentMinimum q = 0}).Nonempty := by
  refine ⟨fun _ => 0, ⟨⟨fun _ => le_rfl, fun _ => by norm_num⟩, ?_⟩⟩
  obtain ⟨j, hj⟩ := exponentMinimum_attained (fun _ : Fin 3 => (0 : ℝ))
  exact hj

/-- The seed alone fails the strict tolerance at this cube boundary, so the
other six labels serve a purpose even in this constant-tolerance example. -/
theorem seed_alone_fails :
    ¬ (minimumSeedFamily 3 0).HasSequentialActivityBound
      (Set.Icc (fun _ => 0) (fun _ => 1) ∩ {q | exponentMinimum q = 0}) (fun _ => 1) := by
  intro hseed
  let q : State 3 := ![0, 1, 1]
  have hq : q ∈ Set.Icc (fun _ => 0) (fun _ => 1) ∩ {q | exponentMinimum q = 0} := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro j
      fin_cases j <;> norm_num [q]
    · intro j
      fin_cases j <;> norm_num [q]
    · apply le_antisymm
      · simpa [q] using exponentMinimum_le_coordinate q 0
      · obtain ⟨j, hj⟩ := exponentMinimum_attained q
        rw [hj]
        fin_cases j <;> norm_num [q]
  have hn := hseed 0 (fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun _ => q) q
    (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
    tendsto_const_nhds hq (fun _ j => by have hj : j = 0 := Subsingleton.elim _ _; rw [hj])
  have hl := norm_le_pi_norm (q - (minimumSeedFamily 3 0).slope 0) (1 : Fin 3)
  have heq : ‖(q - (minimumSeedFamily 3 0).slope 0) (1 : Fin 3)‖ = 1 := by
    norm_num [q, minimumSeedFamily]
  rw [heq] at hl
  linarith

theorem all_support_nearby_uniform :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => 0) (fun _ => 1), |exponentMinimum q| ≤ ρ →
          ∀ i, (allSupportData.family.atScale h).Active i (exponentialPoint h q) →
            ‖q - allSupportData.family.slope i‖ < 1 := by
  simpa using allSupportData.uniformActivityBound_near_minimum
    (by norm_num) (by norm_num) (by intros; norm_num)

end Endotactic.AssemblyExamples
