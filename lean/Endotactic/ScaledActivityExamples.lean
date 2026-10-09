import Endotactic.ActivityFluxBridge

/-!
# Actual tied labels, discontinuous offsets, and a failed approximation

The successful family has two parallel labels tied at every positive scale;
one offset is discontinuous at zero. Its sequential guarantee is proved on a
nonempty exponent neighborhood, and the flux bridge is actually instantiated.
The failed singleton family shows that finiteness and compactness alone do not
imply the sequential activity approximation assumed by the bridge.
-/

namespace Endotactic.ActivityExamples

open Filter Topology

noncomputable def parallelFamily {d : ℕ} (r : State d) : ScaledAffineFamily d 2 := by
  classical
  exact {
    slope := fun _ => r
    offset := fun i h => if i = 0 then 0 else if h = 0 then 1 else 0 }

theorem parallelFamily_value {d : ℕ} (r : State d) {h : ℝ} (hh : h ≠ 0)
    (i : Fin 2) (x : State d) :
    ((parallelFamily r).atScale h).value i x = dot r x := by
  classical
  simp [ScaledAffineFamily.atScale_value, parallelFamily, hh]

theorem parallelFamily_all_active {d : ℕ} (r : State d) {h : ℝ} (hh : h ≠ 0)
    (i : Fin 2) (x : State d) : ((parallelFamily r).atScale h).Active i x := by
  intro j
  rw [parallelFamily_value r hh, parallelFamily_value r hh]

theorem parallelFamily_has_sequential_bound {d : ℕ} (r : State d)
    {ε : ℝ} (hε : 0 < ε) :
    (parallelFamily r).HasSequentialActivityBound (Metric.closedBall r (ε / 2))
      (fun _ => ε) := by
  intro i h p q _ _ _ hq _
  have hnorm : ‖q - r‖ ≤ ε / 2 := by
    simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hq
  change ‖q - r‖ < ε
  exact hnorm.trans_lt (by linarith)

theorem parallelFamily_offset_not_continuous {d : ℕ} (r : State d) :
    ¬ ContinuousAt ((parallelFamily r).offset 1) 0 := by
  classical
  intro hc
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hvalue : ∀ n : ℕ,
      (parallelFamily r).offset 1 (1 / ((n : ℝ) + 1)) = 0 := by
    intro n
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    change (if (1 : Fin 2) = 0 then (0 : ℝ)
      else if 1 / ((n : ℝ) + 1) = 0 then 1 else 0) = 0
    rw [if_neg (by decide), if_neg hn.ne']
  have hzero : Tendsto (fun n : ℕ => (parallelFamily r).offset 1 (1 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa only [hvalue] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hone := hc.tendsto.comp hlim
  have heq := tendsto_nhds_unique hone hzero
  norm_num [parallelFamily] at heq

/-- A genuine nonempty exponent neighborhood and all tied labels satisfy the
new uniform-flux bridge. This is a local family example, not general affine A. -/
theorem exists_parallelFamily_uniform_flux {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (r : State d) (hnonzero : ∃ e, N.projection r e ≠ 0)
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ ε : ℝ, 0 < ε ∧ (Metric.closedBall r (ε / 2)).Nonempty ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ p ∈ Metric.closedBall r (ε / 2), ∀ i : Fin 2,
          ((parallelFamily r).atScale h).Active i (exponentialPoint h p) ∧
          ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
            0 < dot ((parallelFamily r).slope i) (N.rhs k (exponentialPoint h p)) := by
  obtain ⟨ε, hε⟩ := N.exists_slopeTolerance hN
  have hseq : (parallelFamily r).HasSequentialActivityBound
      (Metric.closedBall r (ε r / 2)) (fun i => ε ((parallelFamily r).slope i)) :=
    parallelFamily_has_sequential_bound r (hε r).1
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ := N.uniform_active_flux_of_sequentialActivityBound
    (parallelFamily r) _ (isCompact_closedBall r _) ε hε hseq hℓ hu
  refine ⟨ε r, (hε r).1, ⟨r, Metric.mem_closedBall_self
    (div_nonneg (hε r).1.le (by norm_num))⟩,
    h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall p hp i
  have hi := parallelFamily_all_active r hh.ne' i (exponentialPoint h p)
  exact ⟨hi, hflux h hh hsmall p hp i hi hnonzero⟩

def badFamily : ScaledAffineFamily 1 1 where
  slope _ := 1
  offset _ _ := 0

theorem badFamily_slope_mem_cube (i : Fin 1) :
    badFamily.slope i ∈ Set.Icc (0 : State 1) 1 := by
  simp [badFamily, Set.mem_Icc]

theorem badFamily_offset_littleO (a : ℝ) (i : Fin 1) :
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) (badFamily.offset i) (fun h => h ^ a) :=
  Asymptotics.isLittleO_zero _ _

theorem badFamily_not_sequential :
    ¬ badFamily.HasSequentialActivityBound (Set.Icc (0 : State 1) 1)
      (fun _ => 1 / 2) := by
  intro hseq
  have hpositive : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hclose := hseq 0 (fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun _ => 0) 0
    hpositive tendsto_one_div_add_atTop_nhds_zero_nat tendsto_const_nhds
    (by simp) (fun _ j => by fin_cases j; exact le_rfl)
  norm_num [badFamily] at hclose

theorem badFamily_no_uniform_activity :
    ¬ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ p ∈ Set.Icc (0 : State 1) 1, ∀ i : Fin 1,
        (badFamily.atScale h).Active i (exponentialPoint h p) →
          ‖p - badFamily.slope i‖ < 1 / 2 := by
  rintro ⟨h₀, hh₀, hbound⟩
  have hclose := hbound (h₀ / 2) (by positivity) (by linarith) 0 (by simp) 0
    (fun j => by fin_cases j; exact le_rfl)
  norm_num [badFamily] at hclose

end Endotactic.ActivityExamples
