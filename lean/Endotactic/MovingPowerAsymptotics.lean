import Endotactic.MonomialOrder
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Moving exponent comparisons at vanishing positive scales

Strict gaps are imposed only on limiting exponents. Joint continuity of real
power at a zero base and a positive exponent avoids a separate logarithmic or
quantitative gap argument. Neither the scale nor the exponent is monotone.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem moving_rpow_ratio_tendsto_zero {I : Type*} {l : Filter I}
    {h p q : I → ℝ} {p₀ q₀ : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 p₀)) (hq : Tendsto q l (𝓝 q₀)) (hgap : q₀ < p₀) :
    Tendsto (fun x => h x ^ p x / h x ^ q x) l (𝓝 0) := by
  have hd : Tendsto (fun x => h x ^ (p x - q x)) l (𝓝 0) := by
    simpa only [Real.zero_rpow (sub_pos.mpr hgap).ne'] using
      hh.rpow (hp.sub hq) (Or.inr (sub_pos.mpr hgap))
  apply hd.congr'
  filter_upwards [hpos] with x hx
  exact Real.rpow_sub hx _ _

theorem moving_rpow_isLittleO {I : Type*} {l : Filter I}
    {h p q : I → ℝ} {p₀ q₀ : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 p₀)) (hq : Tendsto q l (𝓝 q₀)) (hgap : q₀ < p₀) :
    IsLittleO l (fun x => h x ^ p x) (fun x => h x ^ q x) := by
  apply isLittleO_of_tendsto' _ (moving_rpow_ratio_tendsto_zero hh hpos hp hq hgap)
  filter_upwards [hpos] with x hx
  exact fun hzero => ((Real.rpow_pos_of_pos hx _).ne' hzero).elim

theorem moving_rpow_ratio_tendsto_atTop {I : Type*} {l : Filter I}
    {h p q : I → ℝ} {p₀ q₀ : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 p₀)) (hq : Tendsto q l (𝓝 q₀)) (hgap : p₀ < q₀) :
    Tendsto (fun x => h x ^ p x / h x ^ q x) l atTop := by
  have hz := moving_rpow_ratio_tendsto_zero hh hpos hq hp hgap
  have hgt : Tendsto (fun x => h x ^ q x / h x ^ p x) l (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hz, ?_⟩
    filter_upwards [hpos] with x hx
    exact div_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hx _)
  convert hgt.inv_tendsto_nhdsGT_zero using 1
  ext x
  simp

theorem rpow_isLittleO_nhdsGT_zero {a b : ℝ} (hab : a < b) :
    IsLittleO (𝓝[>] (0 : ℝ)) (fun h : ℝ => h ^ b) (fun h : ℝ => h ^ a) :=
  moving_rpow_isLittleO nhdsWithin_le_nhds
    (self_mem_nhdsWithin : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Set.Ioi 0)
    tendsto_const_nhds tendsto_const_nhds hab

theorem offset_isLittleO_along_scales {I : Type*} {l : Filter I}
    {h : I → ℝ} {c : ℝ → ℝ} {a : ℝ}
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ a))
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x) :
    IsLittleO l (fun x => c (h x)) (fun x => h x ^ a) :=
  hc.comp_tendsto (tendsto_nhdsWithin_iff.mpr ⟨hh, hpos⟩)

theorem moving_weighted_power_sum_isLittleO {I J : Type*} {l : Filter I}
    (s : Finset J) (w : J → ℝ) {h : I → ℝ} {p : J → I → ℝ}
    {p₀ : J → ℝ} {q : ℝ} (hh : Tendsto h l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : ∀ j ∈ s, Tendsto (p j) l (𝓝 (p₀ j))) (hgap : ∀ j ∈ s, q < p₀ j) :
    IsLittleO l (fun x => ∑ j ∈ s, w j * h x ^ p j x) (fun x => h x ^ q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using isLittleO_zero (fun x => h x ^ q) l
  | @insert j s hjs ih =>
    have hj := (moving_rpow_isLittleO hh hpos (hp j (by simp))
      tendsto_const_nhds (hgap j (by simp))).const_mul_left (w j)
    have hs := ih (fun k hk => hp k (Finset.mem_insert_of_mem hk))
      (fun k hk => hgap k (Finset.mem_insert_of_mem hk))
    simpa only [Finset.sum_insert hjs] using hj.add hs

end Endotactic
