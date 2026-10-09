import Endotactic.AffinePowerComparison
import Endotactic.FixedMinimumSeeds

/-!
# Actual power-offset labels, boundary ties, and decay improvement

The two-label family has values 0 and x-h^β. It tests the actual activity
comparison, including the equality case where both labels remain active.
Zero-offset seeds instantiate the joint neighborhood/decay theorem.
-/

namespace Endotactic.PowerExamples

open Filter Topology Asymptotics

noncomputable def binaryPowerFamily (β : ℝ) : ScaledAffineFamily 1 2 where
  slope i := fun _ => if i = 0 then 0 else 1
  offset i h := if i = 0 then 0 else -(h ^ β)

theorem binaryPowerFamily_boundary_all_active (β h : ℝ) (i : Fin 2) :
    ((binaryPowerFamily β).atScale h).Active i (exponentialPoint h (fun _ => β)) := by
  have hv : ∀ j : Fin 2, ((binaryPowerFamily β).atScale h).value j
      (exponentialPoint h (fun _ => β)) = 0 := by
    intro j
    fin_cases j <;> simp [ScaledAffineFamily.atScale_value, binaryPowerFamily,
      dot, exponentialPoint]
  intro j
  rw [hv i, hv j]

theorem binaryPowerFamily_raised_active_iff {β h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (p : State 1) :
    ((binaryPowerFamily β).atScale h).Active 1 (exponentialPoint h p) ↔ β ≤ p 0 := by
  have hv0 : ((binaryPowerFamily β).atScale h).value 0 (exponentialPoint h p) = 0 := by
    simp [ScaledAffineFamily.atScale_value, binaryPowerFamily, dot, exponentialPoint]
  have hv1 : ((binaryPowerFamily β).atScale h).value 1 (exponentialPoint h p) =
      h ^ p 0 - h ^ β := by
    simp [ScaledAffineFamily.atScale_value, binaryPowerFamily, dot,
      exponentialPoint, sub_eq_add_neg]
  constructor
  · intro hi
    have hle := hi 0
    rw [hv1, hv0] at hle
    by_contra hbad
    have hlt := Real.rpow_lt_rpow_of_exponent_gt hh hh1 (lt_of_not_ge hbad)
    linarith
  · intro hge j
    fin_cases j
    · change ((binaryPowerFamily β).atScale h).value 1 (exponentialPoint h p) ≤
        ((binaryPowerFamily β).atScale h).value 0 (exponentialPoint h p)
      rw [hv1, hv0]
      have hle := Real.rpow_le_rpow_of_exponent_ge hh hh1.le hge
      linarith
    · exact le_rfl

/-- The new semantic activity-to-exponent theorem is actually instantiated.
No small-scale bound h<1 or exponent monotonicity is an input here. -/
theorem binaryPowerFamily_raised_limit_ge (β : ℝ)
    {h : ℕ → ℝ} {p : ℕ → State 1} {q : State 1}
    (hh : Tendsto h atTop (𝓝 0)) (hpos : ∀ n, 0 < h n)
    (hp : Tendsto p atTop (𝓝 q))
    (hactive : ∀ n, ((binaryPowerFamily β).atScale (h n)).Active 1
      (exponentialPoint (h n) (p n))) : β ≤ q 0 := by
  have hlim := (binaryPowerFamily β).raised_coordinate_limits_ge 1 0 Finset.univ
    0 β (fun _ => 0) (by simp [binaryPowerFamily]) (by simp [binaryPowerFamily])
    (by simp) (by intro j _; simp [binaryPowerFamily])
    (by simp [binaryPowerFamily]) (isLittleO_zero _ _)
    hh (Eventually.of_forall hpos) hp (Eventually.of_forall hactive)
  exact hlim 0 (Finset.mem_univ _)

/-- An actual seed has offsets o(h^(b+ρ)) and approximation on the very same
minimum band, with positive radius supplied by the checked joint theorem. -/
theorem top_seed_neighborhood_with_decay {d : ℕ} [NeZero d]
    (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ i : Fin 1, IsLittleO (𝓝[>] (0 : ℝ)) ((minimumSeedFamily d b).offset i)
        (fun h => h ^ (b + ρ))) ∧
      (minimumSeedFamily d b).HasSequentialActivityBound
        (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | |exponentMinimum q - b| ≤ ρ})
        (fun _ => ε) :=
  (minimumSeedFamily d b).sequentialActivityBound_near_minimum_with_decay a b
    (fun _ => ε) b (minimumSeedFamily_top_fixedMinimum a b hε)
    (fun _ => b + 1) (fun _ => by linarith) (fun _ => isBigO_zero _ _)

/-- Dropping the strict exponent gap would falsely assert that a nonzero
power is little-o of itself. This statement uses positive scales explicitly. -/
theorem rpow_not_littleO_same_exponent (β : ℝ) :
    ¬ IsLittleO (𝓝[>] (0 : ℝ)) (fun h : ℝ => h ^ β) (fun h => h ^ β) := by
  intro hbad
  have hz := hbad.tendsto_div_nhds_zero
  have hone : Tendsto (fun h : ℝ => h ^ β / h ^ β) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (div_self (Real.rpow_pos_of_pos hh _).ne').symm
  have hcontra := tendsto_nhds_unique hz hone
  norm_num at hcontra

end Endotactic.PowerExamples
