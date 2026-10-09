import Endotactic.OffsetDecayNeighborhood

/-!
# Power comparisons needed by raised-coordinate affine labels

The first comparison forces a raised coordinate's limiting exponent to lie
above the offset exponent. The second makes a competitor with a stronger
negative offset strictly smaller. These prove the comparison steps without
assuming that a whole inductive label family has already been constructed.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem exponent_ge_of_power_upper_bound {I : Type*} {l : Filter I} [l.NeBot]
    {h p c : I → ℝ} {p₀ β w : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 p₀)) (hw : 0 < w)
    (hc : IsLittleO l c (fun x => h x ^ β))
    (hupper : ∀ᶠ x in l, w * h x ^ p x ≤ h x ^ β - c x) : β ≤ p₀ := by
  by_contra hbad
  have hgap : p₀ < β := lt_of_not_ge hbad
  have hlarge := (moving_rpow_ratio_tendsto_atTop hh hpos hp
    tendsto_const_nhds hgap).eventually_gt_atTop (2 / w)
  have hsmall : ∀ᶠ x in l, -1 < c x / h x ^ β :=
    hc.tendsto_div_nhds_zero.eventually (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0))
  obtain ⟨x, hx, hux, hlx, hsx⟩ := (hpos.and (hupper.and (hlarge.and hsmall))).exists
  have hb : 0 < h x ^ β := Real.rpow_pos_of_pos hx _
  have hdiv : w * (h x ^ p x / h x ^ β) ≤ 1 - c x / h x ^ β := by
    simpa only [sub_div, div_self hb.ne', mul_div_assoc] using
      div_le_div_of_nonneg_right hux hb.le
  have htwo : 2 < w * (h x ^ p x / h x ^ β) := by
    have hm := mul_lt_mul_of_pos_left hlx hw
    simpa only [mul_div_cancel₀ _ hw.ne'] using hm
  linarith

theorem raised_coordinate_limits_ge_of_sum_bound {I J : Type*} {l : Filter I} [l.NeBot]
    (s : Finset J) (w : J → ℝ) {h c : I → ℝ} {p : J → I → ℝ}
    {p₀ : J → ℝ} {β : ℝ} (hh : Tendsto h l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < h x) (hw : ∀ j ∈ s, 0 < w j)
    (hp : ∀ j ∈ s, Tendsto (p j) l (𝓝 (p₀ j)))
    (hc : IsLittleO l c (fun x => h x ^ β))
    (hupper : ∀ᶠ x in l, (∑ j ∈ s, w j * h x ^ p j x) ≤ h x ^ β - c x) :
    ∀ j ∈ s, β ≤ p₀ j := by
  intro j hj
  apply exponent_ge_of_power_upper_bound hh hpos (hp j hj) (hw j hj) hc
  filter_upwards [hpos, hupper] with x hx hux
  exact (Finset.single_le_sum (fun k hk =>
    mul_nonneg (hw k hk).le (Real.rpow_pos_of_pos hx (p k x)).le) hj).trans hux

theorem negative_power_offset_ratio_tendsto {I : Type*} {l : Filter I}
    {h c : I → ℝ} {β : ℝ} (hpos : ∀ᶠ x in l, 0 < h x)
    (hc : IsLittleO l c (fun x => h x ^ β)) :
    Tendsto (fun x => (-(h x ^ β) + c x) / h x ^ β) l (𝓝 (-1)) := by
  have hlim := tendsto_const_nhds.add hc.tendsto_div_nhds_zero
    (f := fun _ : I => (-1 : ℝ))
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [hpos] with x hx
  have hb : h x ^ β ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  simp only [add_div, neg_div, div_self hb]

theorem eventually_lt_of_normalized_limits {I : Type*} {l : Filter I}
    {f g s : I → ℝ} {a b : ℝ} (hs : ∀ᶠ x in l, 0 < s x)
    (hf : Tendsto (fun x => f x / s x) l (𝓝 a))
    (hg : Tendsto (fun x => g x / s x) l (𝓝 b)) (hab : a < b) :
    ∀ᶠ x in l, f x < g x := by
  filter_upwards [hs, hf.eventually_lt hg hab] with x hx hlt
  exact (div_lt_div_iff_of_pos_right hx).mp hlt

/-- A negative offset with a strictly smaller exponent beats the lower bound
of the old label. All remainders are controlled along the actual scale filter. -/
theorem stronger_negative_power_eventually_lt {I : Type*} {l : Filter I}
    {h c d : I → ℝ} {γ β : ℝ} (hh : Tendsto h l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < h x) (hgap : γ < β)
    (hc : IsLittleO l c (fun x => h x ^ γ))
    (hd : IsLittleO l d (fun x => h x ^ β)) :
    ∀ᶠ x in l, -(h x ^ γ) + c x < -(h x ^ β) + d x := by
  have hp : IsLittleO l (fun x => h x ^ β) (fun x => h x ^ γ) :=
    moving_rpow_isLittleO hh hpos tendsto_const_nhds tendsto_const_nhds hgap
  have hold : IsLittleO l (fun x => -(h x ^ β) + d x) (fun x => h x ^ γ) :=
    hp.neg_left.add (hd.trans hp)
  exact eventually_lt_of_normalized_limits
    (hpos.mono fun x hx => Real.rpow_pos_of_pos hx _)
    (negative_power_offset_ratio_tendsto hpos hc) hold.tendsto_div_nhds_zero
    (by norm_num)

theorem zero_label_beaten_by_negative_power {I : Type*} {l : Filter I}
    {h c : I → ℝ} {β : ℝ} (hpos : ∀ᶠ x in l, 0 < h x)
    (hc : IsLittleO l c (fun x => h x ^ β)) :
    ∀ᶠ x in l, -(h x ^ β) + c x < 0 :=
  eventually_lt_of_normalized_limits
    (hpos.mono fun x hx => Real.rpow_pos_of_pos hx _)
    (negative_power_offset_ratio_tendsto hpos hc)
    (by simpa only [zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : I => (0 : ℝ)) l (𝓝 0)))
    (by norm_num)

/-- All raised terms are little-o of the competitor's negative offset when
their limiting exponents are strictly above its exponent. The old branch only
needs a lower bound; its raised terms need not be asymptotically negligible. -/
theorem raised_competitor_eventually_beats_lower_bound
    {I J : Type*} {l : Filter I} (s : Finset J) (w : J → ℝ)
    {h c d old : I → ℝ} {p : J → I → ℝ} {p₀ : J → ℝ} {γ β : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x) (hgap : γ < β)
    (hp : ∀ j ∈ s, Tendsto (p j) l (𝓝 (p₀ j))) (hraised : ∀ j ∈ s, γ < p₀ j)
    (hc : IsLittleO l c (fun x => h x ^ γ))
    (hd : IsLittleO l d (fun x => h x ^ β))
    (hold : ∀ᶠ x in l, -(h x ^ β) + d x ≤ old x) :
    ∀ᶠ x in l, (∑ j ∈ s, w j * h x ^ p j x) - h x ^ γ + c x < old x := by
  have hrem := (moving_weighted_power_sum_isLittleO s w hh hpos hp hraised).add hc
  have hbeat := stronger_negative_power_eventually_lt hh hpos hgap hrem hd
  filter_upwards [hbeat, hold] with x hbx hox
  linarith

theorem raised_competitor_eventually_beats_zero
    {I J : Type*} {l : Filter I} (s : Finset J) (w : J → ℝ)
    {h c : I → ℝ} {p : J → I → ℝ} {p₀ : J → ℝ} {γ : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : ∀ j ∈ s, Tendsto (p j) l (𝓝 (p₀ j))) (hraised : ∀ j ∈ s, γ < p₀ j)
    (hc : IsLittleO l c (fun x => h x ^ γ)) :
    ∀ᶠ x in l, (∑ j ∈ s, w j * h x ^ p j x) - h x ^ γ + c x < 0 := by
  have hrem := (moving_weighted_power_sum_isLittleO s w hh hpos hp hraised).add hc
  have hbeat := zero_label_beaten_by_negative_power hpos hrem
  filter_upwards [hbeat] with x hbx
  linarith

theorem dot_exponential_increment_on_coordinates {d : ℕ} (r : State d)
    (t h : ℝ) (p : State d) (U : Finset (Fin d))
    (houtside : ∀ j ∉ U, r j = t) :
    dot r (exponentialPoint h p) - dot (fun _ => t) (exponentialPoint h p) =
      ∑ j ∈ U, (r j - t) * h ^ p j := by
  classical
  simp only [dot, exponentialPoint, ← Finset.sum_sub_distrib, ← sub_mul]
  exact (Finset.sum_subset (Finset.subset_univ U)
    (fun j _ hj => by rw [houtside j hj, sub_self, zero_mul])).symm

/-- Actual activity comparison with the type-zero seed supplies the sum
bound. The raised-coordinate conclusion does not assume it as separate data. -/
theorem ScaledAffineFamily.raised_coordinate_limits_ge {d m : ℕ}
    {I : Type*} {l : Filter I} [l.NeBot]
    (A : ScaledAffineFamily d m) (i seed : Fin m) (U : Finset (Fin d))
    (t β : ℝ) (c : ℝ → ℝ)
    (hseed : A.slope seed = fun _ => t) (hseedoffset : ∀ h, A.offset seed h = 0)
    (houtside : ∀ j ∉ U, A.slope i j = t)
    (hraised : ∀ j ∈ U, t < A.slope i j)
    (hoffset : ∀ h, A.offset i h = -(h ^ β) + c h)
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q))
    (hactive : ∀ᶠ x in l, (A.atScale (h x)).Active i (exponentialPoint (h x) (p x))) :
    ∀ j ∈ U, β ≤ q j := by
  apply raised_coordinate_limits_ge_of_sum_bound U (fun j => A.slope i j - t)
    hh hpos (fun j hj => sub_pos.mpr (hraised j hj))
    (fun j _ => (continuous_apply j).tendsto q |>.comp hp)
    (offset_isLittleO_along_scales hc hh hpos)
  filter_upwards [hactive] with x hx
  have hs := hx seed
  simp only [ScaledAffineFamily.atScale_value,
    hseed, hseedoffset, add_zero, hoffset] at hs
  simp only [Function.comp_apply]
  rw [← dot_exponential_increment_on_coordinates (A.slope i) t (h x) (p x) U houtside]
  linarith

end Endotactic
