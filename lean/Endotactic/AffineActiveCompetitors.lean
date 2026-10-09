import Endotactic.AffinePowerComparison

/-!
# Actual active-label comparisons bound omitted limiting exponents

The competitors are labels of the same supplied affine family. Their negative
power offsets beat the old branch when every exponent on the competitor's
support is too large. Activity gives the contradictory reverse inequality.
Existence and coverage of all required competing supports remain separate.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem ScaledAffineFamily.eventually_competitor_value_lt
    {d m : ℕ} {I : Type*} {l : Filter I}
    (A : ScaledAffineFamily d m) (i competitor : Fin m) (V : Finset (Fin d))
    (t β η : ℝ) (c drem : ℝ → ℝ) (hgap : η < β)
    (holdSlope : ∀ j, t ≤ A.slope i j)
    (holdOffset : ∀ h, A.offset i h = -(h ^ β) + c h)
    (hcompOutside : ∀ j ∉ V, A.slope competitor j = t)
    (hcompOffset : ∀ h, A.offset competitor h = -(h ^ η) + drem h)
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β))
    (hd : IsLittleO (𝓝[>] (0 : ℝ)) drem (fun h => h ^ η))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q)) (hq : ∀ j ∈ V, η < q j) :
    ∀ᶠ x in l, (A.atScale (h x)).value competitor (exponentialPoint (h x) (p x)) <
      (A.atScale (h x)).value i (exponentialPoint (h x) (p x)) := by
  let old := fun x => (A.atScale (h x)).value i (exponentialPoint (h x) (p x)) -
    dot (fun _ => t) (exponentialPoint (h x) (p x))
  have hlower : ∀ᶠ x in l, -(h x ^ β) + c (h x) ≤ old x := by
    filter_upwards [hpos] with x hx
    have hn : 0 ≤ dot (A.slope i) (exponentialPoint (h x) (p x)) -
        dot (fun _ => t) (exponentialPoint (h x) (p x)) := by
      rw [dot_exponential_increment_on_coordinates _ _ _ _ Finset.univ (by simp)]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (sub_nonneg.mpr (holdSlope j))
        (Real.rpow_pos_of_pos hx _).le
    dsimp [old]
    rw [ScaledAffineFamily.atScale_value, holdOffset]
    linarith
  have hbeat := raised_competitor_eventually_beats_lower_bound V
    (fun j => A.slope competitor j - t) hh hpos hgap
    (fun j _ => (continuous_apply j).tendsto q |>.comp hp) hq
    (offset_isLittleO_along_scales hd hh hpos)
    (offset_isLittleO_along_scales hc hh hpos) hlower
  filter_upwards [hbeat] with x hx
  have heq := dot_exponential_increment_on_coordinates (A.slope competitor)
    t (h x) (p x) V hcompOutside
  simp only [Function.comp_apply] at hx
  dsimp [old] at hx
  rw [ScaledAffineFamily.atScale_value, hcompOffset]
  linarith

theorem ScaledAffineFamily.active_omitted_coordinate_le
    {d m : ℕ} {I : Type*} {l : Filter I} [l.NeBot]
    (A : ScaledAffineFamily d m) (i competitor : Fin m) (V : Finset (Fin d))
    (j : Fin d) (_hj : j ∈ V) (t β η : ℝ) (c drem : ℝ → ℝ) (hgap : η < β)
    (holdSlope : ∀ k, t ≤ A.slope i k)
    (holdOffset : ∀ h, A.offset i h = -(h ^ β) + c h)
    (hcompOutside : ∀ k ∉ V, A.slope competitor k = t)
    (hcompOffset : ∀ h, A.offset competitor h = -(h ^ η) + drem h)
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β))
    (hd : IsLittleO (𝓝[>] (0 : ℝ)) drem (fun h => h ^ η))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q)) (hq : ∀ k ∈ V, k ≠ j → η < q k)
    (hactive : ∀ᶠ x in l, (A.atScale (h x)).Active i (exponentialPoint (h x) (p x))) :
    q j ≤ η := by
  by_contra hbad
  have hlarge : η < q j := lt_of_not_ge hbad
  have hall : ∀ k ∈ V, η < q k := by
    intro k hk
    by_cases hkj : k = j
    · simpa only [hkj] using hlarge
    · exact hq k hk hkj
  have hbeat := A.eventually_competitor_value_lt i competitor V t β η c drem hgap
    holdSlope holdOffset hcompOutside hcompOffset hc hd hh hpos hp hall
  obtain ⟨x, hbx, hax⟩ := (hbeat.and hactive).exists
  exact (not_lt_of_ge (hax competitor)) hbx

theorem ScaledAffineFamily.eventually_competitor_value_lt_seed
    {d m : ℕ} {I : Type*} {l : Filter I}
    (A : ScaledAffineFamily d m) (seed competitor : Fin m) (V : Finset (Fin d))
    (t η : ℝ) (drem : ℝ → ℝ)
    (hseed : A.slope seed = fun _ => t) (hseedOffset : ∀ h, A.offset seed h = 0)
    (hcompOutside : ∀ k ∉ V, A.slope competitor k = t)
    (hcompOffset : ∀ h, A.offset competitor h = -(h ^ η) + drem h)
    (hd : IsLittleO (𝓝[>] (0 : ℝ)) drem (fun h => h ^ η))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q)) (hq : ∀ k ∈ V, η < q k) :
    ∀ᶠ x in l, (A.atScale (h x)).value competitor (exponentialPoint (h x) (p x)) <
      (A.atScale (h x)).value seed (exponentialPoint (h x) (p x)) := by
  have hbeat := raised_competitor_eventually_beats_zero V
    (fun k => A.slope competitor k - t) hh hpos
    (fun k _ => (continuous_apply k).tendsto q |>.comp hp) hq
    (offset_isLittleO_along_scales hd hh hpos)
  filter_upwards [hbeat] with x hx
  have heq := dot_exponential_increment_on_coordinates (A.slope competitor)
    t (h x) (p x) V hcompOutside
  simp only [Function.comp_apply] at hx
  simp only [ScaledAffineFamily.atScale_value, hseed, hseedOffset, add_zero, hcompOffset]
  linarith

theorem ScaledAffineFamily.seed_active_omitted_coordinate_le
    {d m : ℕ} {I : Type*} {l : Filter I} [l.NeBot]
    (A : ScaledAffineFamily d m) (seed competitor : Fin m) (j : Fin d)
    (t η : ℝ) (drem : ℝ → ℝ)
    (hseed : A.slope seed = fun _ => t) (hseedOffset : ∀ h, A.offset seed h = 0)
    (hcompOutside : ∀ k ∉ ({j} : Finset (Fin d)), A.slope competitor k = t)
    (hcompOffset : ∀ h, A.offset competitor h = -(h ^ η) + drem h)
    (hd : IsLittleO (𝓝[>] (0 : ℝ)) drem (fun h => h ^ η))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q))
    (hactive : ∀ᶠ x in l, (A.atScale (h x)).Active seed
      (exponentialPoint (h x) (p x))) : q j ≤ η := by
  by_contra hbad
  have hall : ∀ k ∈ ({j} : Finset (Fin d)), η < q k := by
    intro k hk
    simpa only [Finset.mem_singleton.mp hk] using lt_of_not_ge hbad
  have hbeat := A.eventually_competitor_value_lt_seed seed competitor {j} t η drem
    hseed hseedOffset hcompOutside hcompOffset hd hh hpos hp hall
  obtain ⟨x, hbx, hax⟩ := (hbeat.and hactive).exists
  exact (not_lt_of_ge (hax competitor)) hbx

/-- This theorem derives both exponent bounds from the actual active label:
the seed supplies q>=β on U, and the larger-support competitor supplies q_j<=η.
No omitted-coordinate upper bound is an input. -/
theorem ScaledAffineFamily.active_omitted_coordinate_le_of_raised_type
    {d m : ℕ} {I : Type*} {l : Filter I} [l.NeBot]
    (A : ScaledAffineFamily d m) (i seed competitor : Fin m) (U : Finset (Fin d))
    (j : Fin d) (t β η : ℝ) (c drem : ℝ → ℝ) (hgap : η < β)
    (hseed : A.slope seed = fun _ => t) (hseedOffset : ∀ h, A.offset seed h = 0)
    (houtside : ∀ k ∉ U, A.slope i k = t) (hraised : ∀ k ∈ U, t < A.slope i k)
    (holdOffset : ∀ h, A.offset i h = -(h ^ β) + c h)
    (hcompOutside : ∀ k ∉ insert j U, A.slope competitor k = t)
    (hcompOffset : ∀ h, A.offset competitor h = -(h ^ η) + drem h)
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β))
    (hd : IsLittleO (𝓝[>] (0 : ℝ)) drem (fun h => h ^ η))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q))
    (hactive : ∀ᶠ x in l, (A.atScale (h x)).Active i (exponentialPoint (h x) (p x))) :
    q j ≤ η := by
  classical
  have hU := A.raised_coordinate_limits_ge i seed U t β c hseed hseedOffset
    houtside hraised holdOffset hc hh hpos hp hactive
  apply A.active_omitted_coordinate_le i competitor (insert j U) j
    (Finset.mem_insert_self j U) t β η c drem hgap _ holdOffset
    hcompOutside hcompOffset hc hd hh hpos hp _ hactive
  · intro k
    by_cases hk : k ∈ U
    · exact (hraised k hk).le
    · rw [houtside k hk]
  · intro k hk hkj
    exact hgap.trans_le (hU k ((Finset.mem_insert.mp hk).resolve_left hkj))

end Endotactic
