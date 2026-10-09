import Endotactic.AffineApproximationExistence

/-!
# A positive discontinuous tolerance with no uniform positive lower bound

This two-dimensional tolerance is much smaller than the cube width near its
jump. The full affine theorem applies without the old wide-tolerance oracle.
The resulting family is an existence witness, not an enumerated numerical output.
-/

namespace Endotactic.ExistenceExamples

open Filter Topology Asymptotics

noncomputable def singularTolerance (r : State 2) : ℝ :=
  if r 0 = 0 then 1 else |r 0| / 100

theorem singularTolerance_pos (r : State 2) : 0 < singularTolerance r := by
  unfold singularTolerance
  split_ifs with h
  · norm_num
  · exact div_pos (abs_pos.mpr h) (by norm_num)

theorem singularTolerance_no_uniform_positive_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ r ∈ Set.Icc (fun _ : Fin 2 => (0 : ℝ)) (fun _ => 1), singularTolerance r < ε := by
  let x := min (1 / 2 : ℝ) (50 * ε)
  have hx : 0 < x := lt_min (by norm_num) (by positivity)
  have hx1 : x ≤ 1 := (min_le_left _ _).trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hxε : x ≤ 50 * ε := min_le_right _ _
  let r : State 2 := fun j => if j = 0 then x else 0
  refine ⟨r, ⟨?_, ?_⟩, ?_⟩
  · intro j
    dsimp [r]
    split_ifs <;> first | exact hx.le | exact le_rfl
  · intro j
    dsimp [r]
    split_ifs <;> first | exact hx1 | norm_num
  · change (if x = 0 then 1 else |x| / 100) < ε
    rw [if_neg hx.ne', abs_of_pos hx]
    linarith

theorem singularTolerance_not_continuous : ¬ Continuous singularTolerance := by
  intro hc
  let p : ℕ → State 2 := fun n j => if j = 0 then 1 / ((n : ℝ) + 1) else 0
  have hp : Tendsto p atTop (𝓝 (fun _ => 0)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hj : j = 0
    · simpa only [p, hj, if_pos rfl] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))
    · simp only [p, if_neg hj]
      exact tendsto_const_nhds
  have heq : (fun n => singularTolerance (p n)) =
      fun n : ℕ => (1 / ((n : ℝ) + 1)) / 100 := by
    funext n
    have hn : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    change (if (1 : ℝ) / ((n : ℝ) + 1) = 0 then 1 else
      |(1 : ℝ) / ((n : ℝ) + 1)| / 100) = _
    rw [if_neg hn.ne', abs_of_pos hn]
  have hzero : Tendsto (fun n => singularTolerance (p n)) atTop (𝓝 0) := by
    rw [heq]
    simpa only [zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0)).div_const 100
  have hlim := (hc.tendsto (fun _ => 0)).comp hp
  have hbad : (0 : ℝ) = 1 := by
    simpa [singularTolerance] using tendsto_nhds_unique hzero hlim
  norm_num at hbad

theorem singularTolerance_affine_exists :
    ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily 2 m,
      (∀ i, A.slope i ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1)) ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ (0 : ℝ))) ∧
      A.HasSequentialActivityBound (Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1))
        (fun i => singularTolerance (A.slope i)) :=
  finiteAffineApproximation 2 (by norm_num) 0 1 (by norm_num) singularTolerance
    (fun r _ => singularTolerance_pos r)

theorem singularTolerance_uniform_affine_exists :
    ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily 2 m,
      (∀ i, A.slope i ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1)) ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ (0 : ℝ))) ∧
      A.HasSequentialActivityBound (Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1))
        (fun i => singularTolerance (A.slope i)) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ p ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1), ∀ i,
          (A.atScale h).Active i (exponentialPoint h p) →
            ‖p - A.slope i‖ < singularTolerance (A.slope i) :=
  exists_uniform_affine_approximation (by norm_num) (by norm_num) singularTolerance
    (fun r _ => singularTolerance_pos r)

end Endotactic.ExistenceExamples
