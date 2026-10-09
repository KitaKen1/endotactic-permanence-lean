import Endotactic.AffineOffsetShift
import Endotactic.AffinePowerComparison

/-!
# Adjacent shifted seeds confine the limiting minimum

These comparisons are with labels in the actual global family. The lower
bound uses positive slope differences; the upper bound uses moving powers.
Both conclusions are non-strict, so cut ties remain valid labels.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem ScaledAffineFamily.active_minimum_le_of_next_seed
    {d m : ℕ} [NeZero d] {I : Type*} {l : Filter I} [l.NeBot]
    (A : ScaledAffineFamily d m) (i seed : Fin m) (s β : ℝ) (γ c : ℝ → ℝ)
    (hseed : A.slope seed = fun _ => s)
    (hoffset : ∀ h, A.offset i h = γ h + c h)
    (hseedoffset : ∀ h, A.offset seed h = γ h - h ^ β)
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q))
    (hactive : ∀ᶠ x in l, (A.atScale (h x)).Active i (exponentialPoint (h x) (p x))) :
    exponentMinimum q ≤ β := by
  classical
  by_contra hbad
  have hgap : β < exponentMinimum q := lt_of_not_ge hbad
  have hsum := moving_weighted_power_sum_isLittleO Finset.univ
    (fun j => A.slope i j - s) hh hpos
    (fun j _ => (continuous_apply j).tendsto q |>.comp hp)
    (fun j _ => hgap.trans_le (exponentMinimum_le_coordinate q j))
  have hrem := hsum.add (offset_isLittleO_along_scales hc hh hpos)
  have hbeat := zero_label_beaten_by_negative_power hpos hrem.neg_left
  obtain ⟨x, hx, hbx⟩ := (hactive.and hbeat).exists
  have hs := hx seed
  simp only [ScaledAffineFamily.atScale_value, hseed, hoffset, hseedoffset] at hs
  have heq := dot_exponential_increment_on_coordinates (A.slope i) s (h x) (p x)
    Finset.univ (by simp)
  simp only [Function.comp_apply] at hbx
  linarith

theorem ScaledAffineFamily.active_minimum_ge_of_previous_seed
    {d m : ℕ} [NeZero d] {I : Type*} {l : Filter I} [l.NeBot]
    (A : ScaledAffineFamily d m) (i seed : Fin m) (s β : ℝ) (γ c : ℝ → ℝ)
    (hseed : A.slope seed = fun _ => s) (hraised : ∀ j, s < A.slope i j)
    (hoffset : ∀ h, A.offset i h = γ h - h ^ β + c h)
    (hseedoffset : ∀ h, A.offset seed h = γ h)
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q))
    (hactive : ∀ᶠ x in l, (A.atScale (h x)).Active i (exponentialPoint (h x) (p x))) :
    β ≤ exponentMinimum q := by
  classical
  have hcoords : ∀ j ∈ (Finset.univ : Finset (Fin d)), β ≤ q j := by
    apply raised_coordinate_limits_ge_of_sum_bound Finset.univ (fun j => A.slope i j - s)
      hh hpos (fun j _ => sub_pos.mpr (hraised j))
      (fun j _ => (continuous_apply j).tendsto q |>.comp hp)
      (offset_isLittleO_along_scales hc hh hpos)
    filter_upwards [hactive] with x hx
    have hs := hx seed
    simp only [ScaledAffineFamily.atScale_value, hseed, hoffset, hseedoffset] at hs
    have heq := dot_exponential_increment_on_coordinates (A.slope i) s (h x) (p x)
      Finset.univ (by simp)
    simp only [Function.comp_apply]
    linarith
  obtain ⟨j, hj⟩ := exponentMinimum_attained q
  rw [hj]
  exact hcoords j (Finset.mem_univ j)

end Endotactic
