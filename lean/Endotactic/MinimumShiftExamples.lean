import Endotactic.MinimumShiftChain

/-!
# An actual two-block assembly with both labels active at the cut

The values are 0 and x-h^(1/2). The local bands meet at their closed
endpoints, and the same exponent point 1/2 makes both labels active at every
positive scale. The certificate is supplied explicitly, with no existence
oracle or unproved affine theorem.
-/

namespace Endotactic.ShiftExamples

open Filter Topology Asymptotics

noncomputable def seedApproximation (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    FixedMinimumApproximation 1 0 1 t (fun _ => 1) where
  size := 1
  size_pos := by norm_num
  family := minimumSeedFamily 1 t
  seed := 0
  seed_slope := rfl
  seed_offset := fun _ => rfl
  cube := fun _ => ⟨fun _ => ht.1, fun _ => ht.2⟩
  minimum := fun _ => (exponentMinimum_attained (fun _ : Fin 1 => t)).choose_spec
  power_bound := fun _ => ⟨t + 1, by linarith, isBigO_zero _ _⟩
  approximation := minimumSeedFamily_oneDim_fixedMinimum 0 1 t (by norm_num)

noncomputable def twoBlockChain : MinimumShiftChain 1 1 0 1 (fun _ => 1) where
  center j := (j.val : ℝ)
  center_mem j := by fin_cases j <;> norm_num
  block j := seedApproximation (j.val : ℝ) (by fin_cases j <;> norm_num)
  radius _ := 1 / 2
  radius_pos _ := by norm_num
  cut _ := 1 / 2
  cut_between k hk := by
    have hk0 : k = 0 := by omega
    subst k
    norm_num
  band_left j := by fin_cases j <;> norm_num
  band_right j := by fin_cases j <;> norm_num
  decay j i := minimumSeedFamily_offset_littleO 1 (j.val : ℝ) _ i
  approximation j := by
    intro i h p q _ _ _ hq _
    change ‖q - (fun _ => (j.val : ℝ))‖ < 1
    rw [pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
    intro k
    change |q k - (j.val : ℝ)| < 1
    obtain ⟨l, hl⟩ := exponentMinimum_attained q
    have hkl : k = l := Subsingleton.elim _ _
    rw [hkl, ← hl]
    exact hq.2.trans_lt (by norm_num)

theorem twoBlockChain_card : Fintype.card (Σ j : Fin 2, Fin (twoBlockChain.size j)) = 2 := by
  change Fintype.card (Σ _ : Fin 2, Fin 1) = 2
  rw [Fintype.card_sigma]
  norm_num

theorem twoBlockChain_all_active_at_cut (h : ℝ)
    (i : Fin (Fintype.card (Σ j : Fin 2, Fin (twoBlockChain.size j)))) :
    (twoBlockChain.family.atScale h).Active i (exponentialPoint h (fun _ => 1 / 2)) := by
  have hv : ∀ l, (twoBlockChain.family.atScale h).value l
      (exponentialPoint h (fun _ => 1 / 2)) = 0 := by
    intro l
    obtain ⟨j, k, rfl⟩ := affineBlockLabel_surjective twoBlockChain.size l
    change ((ScaledAffineFamily.blockUnion twoBlockChain.size
      twoBlockChain.shiftedBlock).atScale h).value (affineBlockLabel twoBlockChain.size j k)
        (exponentialPoint h (fun _ => 1 / 2)) = 0
    rw [ScaledAffineFamily.blockUnion_value]
    change (((twoBlockChain.block j).family.offsetShift
      (powerPrefixShift twoBlockChain.cut j.val)).atScale h).value k
        (exponentialPoint h (fun _ => 1 / 2)) = 0
    rw [ScaledAffineFamily.offsetShift_value]
    change dot (fun _ : Fin 1 => (j.val : ℝ))
      (exponentialPoint h (fun _ => 1 / 2)) + 0 +
        powerPrefixShift (fun _ => 1 / 2) j.val h = 0
    fin_cases j <;> simp [dot, exponentialPoint, powerPrefixShift]
  intro j
  rw [hv i, hv j]

theorem twoBlockChain_active_minimum_bounds
    (j : Fin 2) (i : Fin (twoBlockChain.size j))
    {h : ℕ → ℝ} {p : ℕ → State 1} {q : State 1}
    (hpos : ∀ k, 0 < h k) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q))
    (hq : q ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1))
    (hactive : ∀ k, (twoBlockChain.family.atScale (h k)).Active (twoBlockChain.label j i)
      (exponentialPoint (h k) (p k))) :
    |exponentMinimum q - (j.val : ℝ)| ≤ 1 / 2 :=
  twoBlockChain.active_limit_in_band j i hpos hh hp hq hactive

theorem twoBlockChain_sequentialActivityBound :
    twoBlockChain.family.HasSequentialActivityBound
      (Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1)) (fun _ => 1) :=
  twoBlockChain.sequentialActivityBound

theorem twoBlockChain_cut_is_actual_activity_limit
    (i : Fin (Fintype.card (Σ j : Fin 2, Fin (twoBlockChain.size j)))) :
    (fun _ : Fin 1 => (1 / 2 : ℝ)) ∈ twoBlockChain.family.activityLimit i := by
  exact mem_scaleLimit_of_sequences (fun k : ℕ => 1 / ((k : ℝ) + 1))
    (fun _ => (fun _ => (1 / 2 : ℝ))) (fun _ => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat tendsto_const_nhds
    (fun k => twoBlockChain_all_active_at_cut _ i)

end Endotactic.ShiftExamples
