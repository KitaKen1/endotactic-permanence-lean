import Endotactic.SeededAffineUnion

/-!
# Three actual labels with competing power offsets

The values are 0, x₀-h^β and x₀+x₁-h^η, where η<β. This is a
genuine seeded union, not an abstract comparison assumption. It verifies
the omitted-coordinate upper bound, every boundary tie, and an actual active
exponent sequence, so the comparison is not only used on an empty domain.
-/

namespace Endotactic.UnionExamples

open Filter Topology Asymptotics

abbrev exampleSizes : Fin 2 → ℕ := fun _ => 1

noncomputable def competitorBlock (β η : ℝ) (b : Fin 2) : ScaledAffineFamily 3 1 where
  slope _ j := if j = 0 then 1 else if b = 1 ∧ j = 1 then 1 else 0
  offset _ h := if b = 0 then -(h ^ β) else -(h ^ η)

noncomputable def competitorFamily (β η : ℝ) :=
  ScaledAffineFamily.seededUnion 0 exampleSizes (competitorBlock β η)

noncomputable def oldLabel := seededAffineLabel exampleSizes 0 0
noncomputable def strongerLabel := seededAffineLabel exampleSizes 1 0

theorem competitorFamily_old_slope (β η : ℝ) :
    (competitorFamily β η).slope oldLabel = ![1, 0, 0] := by
  dsimp only [competitorFamily, oldLabel]
  rw [ScaledAffineFamily.seededUnion_block_slope]
  funext j
  fin_cases j <;> simp [competitorBlock]

theorem competitorFamily_stronger_slope (β η : ℝ) :
    (competitorFamily β η).slope strongerLabel = ![1, 1, 0] := by
  dsimp only [competitorFamily, strongerLabel]
  rw [ScaledAffineFamily.seededUnion_block_slope]
  funext j
  fin_cases j <;> simp [competitorBlock]

theorem competitorFamily_old_offset (β η h : ℝ) :
    (competitorFamily β η).offset oldLabel h = -(h ^ β) := by
  dsimp only [competitorFamily, oldLabel]
  rw [ScaledAffineFamily.seededUnion_block_offset]
  simp [competitorBlock]

theorem competitorFamily_stronger_offset (β η h : ℝ) :
    (competitorFamily β η).offset strongerLabel h = -(h ^ η) := by
  dsimp only [competitorFamily, strongerLabel]
  rw [ScaledAffineFamily.seededUnion_block_offset]
  simp [competitorBlock]

theorem competitorFamily_old_value (β η h : ℝ) (x : State 3) :
    ((competitorFamily β η).atScale h).value oldLabel x = x 0 - h ^ β := by
  rw [ScaledAffineFamily.atScale_value, competitorFamily_old_slope,
    competitorFamily_old_offset]
  simp [dot, Fin.sum_univ_succ, sub_eq_add_neg]

theorem competitorFamily_stronger_value (β η h : ℝ) (x : State 3) :
    ((competitorFamily β η).atScale h).value strongerLabel x = x 0 + x 1 - h ^ η := by
  rw [ScaledAffineFamily.atScale_value, competitorFamily_stronger_slope,
    competitorFamily_stronger_offset]
  simp [dot, Fin.sum_univ_succ, sub_eq_add_neg]

theorem competitorFamily_all_active_at_tie (β η h z : ℝ)
    (i : Fin (Fintype.card (Σ b : Option (Fin 2), Fin (seededAffineSizes exampleSizes b)))) :
    ((competitorFamily β η).atScale h).Active i ![h ^ β, h ^ η - h ^ β, z] := by
  have hv : ∀ j, ((competitorFamily β η).atScale h).value j
      ![h ^ β, h ^ η - h ^ β, z] = 0 := by
    intro j
    obtain ⟨b, l, rfl⟩ := affineBlockLabel_surjective (seededAffineSizes exampleSizes) j
    change ((ScaledAffineFamily.blockUnion (seededAffineSizes exampleSizes)
      (seededAffineBlocks 0 exampleSizes (competitorBlock β η))).atScale h).value
      (affineBlockLabel (seededAffineSizes exampleSizes) b l) _ = _
    rw [ScaledAffineFamily.blockUnion_value]
    cases b with
    | none => simp [seededAffineBlocks, ScaledAffineFamily.atScale_value,
        minimumSeedFamily, dot]
    | some b =>
      fin_cases b <;> simp [seededAffineBlocks, ScaledAffineFamily.atScale_value,
        competitorBlock, dot, Fin.sum_univ_succ]
  intro j
  rw [hv i, hv j]

theorem competitorFamily_tie_point_positive {β η h z : ℝ} (hgap : η < β)
    (hh : 0 < h) (hh1 : h < 1) (hz : 0 < z) :
    ∀ j : Fin 3, 0 < (![h ^ β, h ^ η - h ^ β, z] : State 3) j := by
  have hp := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hgap
  intro j
  fin_cases j
  · exact Real.rpow_pos_of_pos hh β
  · exact sub_pos.mpr hp
  · exact hz

/-- The actual larger-support label bounds the omitted exponent. Both
offset remainders are zero, but h and approaching exponent points are arbitrary. -/
theorem competitorFamily_old_active_omitted_le {β η : ℝ} (hgap : η < β)
    {h : ℕ → ℝ} {p : ℕ → State 3} {q : State 3}
    (hh : Tendsto h atTop (𝓝 0)) (hpos : ∀ n, 0 < h n)
    (hp : Tendsto p atTop (𝓝 q))
    (hactive : ∀ n, ((competitorFamily β η).atScale (h n)).Active oldLabel
      (exponentialPoint (h n) (p n))) : q 1 ≤ η := by
  apply (competitorFamily β η).active_omitted_coordinate_le_of_raised_type
    oldLabel (seededAffineSeed exampleSizes) strongerLabel {0} 1 0 β η
    (fun _ => 0) (fun _ => 0) hgap
    (ScaledAffineFamily.seededUnion_seed_slope 0 exampleSizes (competitorBlock β η))
    (ScaledAffineFamily.seededUnion_seed_offset 0 exampleSizes (competitorBlock β η))
    _ _ _ _ _ (isLittleO_zero _ _) (isLittleO_zero _ _)
    hh (Eventually.of_forall hpos) hp (Eventually.of_forall hactive)
  · intro k hk
    rw [competitorFamily_old_slope]
    fin_cases k <;> simp_all
  · intro k hk
    rw [competitorFamily_old_slope]
    rcases Finset.mem_singleton.mp hk with rfl
    norm_num
  · intro a
    rw [competitorFamily_old_offset, add_zero]
  · intro k hk
    rw [competitorFamily_stronger_slope]
    fin_cases k <;> simp_all
  · intro a
    rw [competitorFamily_stronger_offset, add_zero]

theorem competitorFamily_seed_active_first_le (β η : ℝ)
    {h : ℕ → ℝ} {p : ℕ → State 3} {q : State 3}
    (hh : Tendsto h atTop (𝓝 0)) (hpos : ∀ n, 0 < h n)
    (hp : Tendsto p atTop (𝓝 q))
    (hactive : ∀ n, ((competitorFamily β η).atScale (h n)).Active
      (seededAffineSeed exampleSizes) (exponentialPoint (h n) (p n))) : q 0 ≤ β := by
  apply (competitorFamily β η).seed_active_omitted_coordinate_le
    (seededAffineSeed exampleSizes) oldLabel 0 0 β (fun _ => 0)
    (ScaledAffineFamily.seededUnion_seed_slope 0 exampleSizes (competitorBlock β η))
    (ScaledAffineFamily.seededUnion_seed_offset 0 exampleSizes (competitorBlock β η))
    _ _ (isLittleO_zero _ _) hh (Eventually.of_forall hpos) hp (Eventually.of_forall hactive)
  · intro k hk
    rw [competitorFamily_old_slope]
    fin_cases k <;> simp_all
  · intro a
    rw [competitorFamily_old_offset, add_zero]

/-- An explicit exponent point has the old label active at every scale in
(0,1]. This validates that the limiting comparison is instantiated nonvacuously. -/
theorem competitorFamily_old_active_witness (β : ℝ) {η h : ℝ}
    (hη : 0 < η) (hh : 0 < h) (hh1 : h ≤ 1) :
    ((competitorFamily β η).atScale h).Active oldLabel
      (exponentialPoint h ![β, η / 2, 0]) := by
  have hr : h ^ η ≤ h ^ (η / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)
  have hold : ((competitorFamily β η).atScale h).value oldLabel
      (exponentialPoint h ![β, η / 2, 0]) = 0 := by
    rw [competitorFamily_old_value]
    simp [exponentialPoint]
  intro j
  rw [hold]
  obtain ⟨b, i, rfl⟩ := affineBlockLabel_surjective (seededAffineSizes exampleSizes) j
  change 0 ≤ ((ScaledAffineFamily.blockUnion (seededAffineSizes exampleSizes)
    (seededAffineBlocks 0 exampleSizes (competitorBlock β η))).atScale h).value
    (affineBlockLabel (seededAffineSizes exampleSizes) b i) _
  rw [ScaledAffineFamily.blockUnion_value]
  cases b with
  | none => simp [seededAffineBlocks, ScaledAffineFamily.atScale_value,
      minimumSeedFamily, dot]
  | some b =>
    fin_cases b
    · simp [seededAffineBlocks, ScaledAffineFamily.atScale_value,
        competitorBlock, dot, exponentialPoint]
    · simp only [seededAffineBlocks, ScaledAffineFamily.atScale_value]
      have hz : 0 < h ^ β := Real.rpow_pos_of_pos hh β
      simp [competitorBlock, dot, Fin.sum_univ_succ, exponentialPoint]
      linarith

theorem competitorFamily_old_activityLimit_nonempty (β : ℝ) {η : ℝ} (hη : 0 < η) :
    ![β, η / 2, 0] ∈ (competitorFamily β η).activityLimit oldLabel := by
  apply mem_scaleLimit_of_sequences (fun n : ℕ => 1 / ((n : ℝ) + 1))
    (fun _ => ![β, η / 2, 0]) (fun _ => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat tendsto_const_nhds
  intro n
  apply competitorFamily_old_active_witness β hη (by positivity)
  rw [div_le_one₀ (by positivity : 0 < (n : ℝ) + 1)]
  linarith [Nat.cast_nonneg (α := ℝ) n]

end Endotactic.UnionExamples
