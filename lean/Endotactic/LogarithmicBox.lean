import Endotactic.MonomialOrder
import Mathlib.Analysis.Convex.PathConnected

/-!
# Positive boxes and inverse exponential coordinates

For a fixed positive state, its exponent coordinates tend to zero as the
scale tends to zero. Connectedness turns absence of box-boundary points into
containment in the open box when one interior point is known.
-/

namespace Endotactic

open Filter Topology

noncomputable def logarithmicExponent {d : ℕ} (h : ℝ) (x : State d) : State d :=
  fun j => Real.log (x j) / Real.log h

theorem exponentialPoint_logarithmicExponent {d : ℕ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1) {x : State d} (hx : Positive x) :
    exponentialPoint h (logarithmicExponent h x) = x := by
  have hl : Real.log h ≠ 0 := ne_of_lt (Real.log_neg hh hh1)
  ext j
  change h ^ (Real.log (x j) / Real.log h) = x j
  rw [Real.rpow_def_of_pos hh]
  have heq : Real.log h * (Real.log (x j) / Real.log h) = Real.log (x j) := by
    field_simp
  rw [heq, Real.exp_log (hx j)]

theorem tendsto_logarithmicExponent {d : ℕ} (x : State d) :
    Tendsto (fun h => logarithmicExponent h x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro j
  exact Real.tendsto_log_nhdsGT_zero.const_div_atBot (Real.log (x j))

theorem logarithmicExponent_mem_cube {d : ℕ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1) {x : State d}
    (hx : x ∈ Set.Icc (fun _ => h) (fun _ => h⁻¹)) :
    logarithmicExponent h x ∈ Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
  have hl : Real.log h < 0 := Real.log_neg hh hh1
  have hxpos : Positive x := fun j => hh.trans_le (hx.1 j)
  constructor
  · intro j
    apply (le_div_iff_of_neg hl).mpr
    have hb := Real.log_le_log (hxpos j) (hx.2 j)
    rw [Real.log_inv] at hb
    simpa only [neg_one_mul] using hb
  · intro j
    apply (div_le_iff_of_neg hl).mpr
    simpa only [one_mul] using Real.log_le_log hh (hx.1 j)

theorem logarithmicExponent_boundary_norm {d : ℕ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1) {x : State d}
    (hx : x ∈ Set.Icc (fun _ => h) (fun _ => h⁻¹))
    (hboundary : ¬ ∀ j, h < x j ∧ x j < h⁻¹) :
    1 ≤ ‖logarithmicExponent h x‖ := by
  classical
  have hl : Real.log h ≠ 0 := ne_of_lt (Real.log_neg hh hh1)
  push Not at hboundary
  obtain ⟨j, hj⟩ := hboundary
  have heq : x j = h ∨ x j = h⁻¹ := by
    by_cases hlow : h < x j
    · exact Or.inr (le_antisymm (hx.2 j) (hj hlow))
    · exact Or.inl (le_antisymm (not_lt.mp hlow) (hx.1 j))
  have hn : |logarithmicExponent h x j| ≤ ‖logarithmicExponent h x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (logarithmicExponent h x) j
  rcases heq with heq | heq
  · simpa only [logarithmicExponent, heq, div_self hl, abs_one] using hn
  · simpa only [logarithmicExponent, heq, Real.log_inv, neg_div, div_self hl,
      abs_neg, abs_one] using hn

def openCoordinateBox {d : ℕ} (lo hi : State d) : Set (State d) :=
  {x | ∀ j, lo j < x j ∧ x j < hi j}

theorem isOpen_openCoordinateBox {d : ℕ} (lo hi : State d) :
    IsOpen (openCoordinateBox lo hi) := by
  have h := isOpen_iInter_of_finite (fun j : Fin d =>
    (isOpen_Ioo : IsOpen (Set.Ioo (lo j) (hi j))).preimage
      (continuous_apply j : Continuous (fun x : State d => x j)))
  convert h using 1
  ext x
  simp only [openCoordinateBox, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage,
    Set.mem_Ioo]

/-- No coercivity or support-function computation is needed. -/
theorem convex_subset_open_box_of_no_boundary {d : ℕ} {K : Set (State d)}
    (hK : Convex ℝ K) {lo hi : State d} {z : State d}
    (hz : z ∈ K) (hzbox : z ∈ openCoordinateBox lo hi)
    (hboundary : ∀ x ∈ K, x ∈ Set.Icc lo hi → x ∈ openCoordinateBox lo hi) :
    K ⊆ openCoordinateBox lo hi := by
  classical
  have hsub : openCoordinateBox lo hi ⊆ Set.Icc lo hi :=
    fun x hx => ⟨fun j => (hx j).1.le, fun j => (hx j).2.le⟩
  have hunion : K ⊆ openCoordinateBox lo hi ∪ (Set.Icc lo hi)ᶜ := by
    intro x hx
    by_cases hb : x ∈ Set.Icc lo hi
    · exact Or.inl (hboundary x hx hb)
    · exact Or.inr hb
  have hdis : Disjoint (openCoordinateBox lo hi) (Set.Icc lo hi)ᶜ := by
    exact Set.disjoint_left.mpr (fun x hx hn => hn (hsub hx))
  rcases IsPreconnected.subset_or_subset (isOpen_openCoordinateBox lo hi)
      isClosed_Icc.isOpen_compl hdis hunion hK.isPreconnected with h | h
  · exact h
  · exact ((h hz) (hsub hzbox)).elim

end Endotactic
