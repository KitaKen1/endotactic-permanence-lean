import Endotactic.CompactSequentialExclusion
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Closed limits of arbitrary relations at vanishing positive scales

No continuity or closedness of the relation is assumed. Local witnesses at
arbitrarily small scales characterize the limit set and prove its closedness.
This is the diagonal-selection step used for affine activity-limit sets.
-/

namespace Endotactic

open Filter Topology

def scaleLimit {X : Type*} [TopologicalSpace X] (R : ℝ → X → Prop) : Set X :=
  {q | ∃ (h : ℕ → ℝ) (x : ℕ → X), (∀ n, 0 < h n) ∧
    Tendsto h atTop (𝓝 0) ∧ Tendsto x atTop (𝓝 q) ∧ ∀ n, R (h n) (x n)}

theorem mem_scaleLimit_of_sequences {X : Type*} [TopologicalSpace X]
    {R : ℝ → X → Prop} {q : X} (h : ℕ → ℝ) (x : ℕ → X)
    (hh : ∀ n, 0 < h n) (hhlim : Tendsto h atTop (𝓝 0))
    (hxlim : Tendsto x atTop (𝓝 q)) (hR : ∀ n, R (h n) (x n)) :
    q ∈ scaleLimit R := ⟨h, x, hh, hhlim, hxlim, hR⟩

theorem scaleLimit_mono {X : Type*} [TopologicalSpace X]
    {R S : ℝ → X → Prop} (hRS : ∀ h x, R h x → S h x) :
    scaleLimit R ⊆ scaleLimit S := by
  rintro q ⟨h, x, hh, hhlim, hxlim, hR⟩
  exact ⟨h, x, hh, hhlim, hxlim, fun n => hRS _ _ (hR n)⟩

theorem mem_scaleLimit_iff_small_witness {X : Type*} [PseudoMetricSpace X]
    {R : ℝ → X → Prop} {q : X} :
    q ∈ scaleLimit R ↔ ∀ δ : ℝ, 0 < δ →
      ∃ h : ℝ, 0 < h ∧ h < δ ∧ ∃ x : X, dist x q < δ ∧ R h x := by
  classical
  constructor
  · rintro ⟨h, x, hh, hhlim, hxlim, hR⟩ δ hδ
    have hhsmall : ∀ᶠ n in atTop, h n < δ := hhlim.eventually (gt_mem_nhds hδ)
    have hxsmall : ∀ᶠ n in atTop, dist (x n) q < δ :=
      (tendsto_iff_dist_tendsto_zero.mp hxlim).eventually (gt_mem_nhds hδ)
    obtain ⟨n, hhn, hxn⟩ := (hhsmall.and hxsmall).exists
    exact ⟨h n, hh n, hhn, x n, hxn, hR n⟩
  · intro hw
    have hw' : ∀ n : ℕ, ∃ h : ℝ, 0 < h ∧ h < 1 / ((n : ℝ) + 1) ∧
        ∃ x : X, dist x q < 1 / ((n : ℝ) + 1) ∧ R h x :=
      fun n => hw _ (by positivity)
    choose h hh hsmall x hx hR using hw'
    have hhlim : Tendsto h atTop (𝓝 0) :=
      squeeze_zero (fun n => (hh n).le) (fun n => (hsmall n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hxlim : Tendsto x atTop (𝓝 q) :=
      tendsto_iff_dist_tendsto_zero.mpr <|
        squeeze_zero (fun n => dist_nonneg) (fun n => (hx n).le)
          tendsto_one_div_add_atTop_nhds_zero_nat
    exact ⟨h, x, hh, hhlim, hxlim, hR⟩

theorem isClosed_scaleLimit {X : Type*} [PseudoMetricSpace X]
    (R : ℝ → X → Prop) : IsClosed (scaleLimit R) := by
  apply isClosed_of_closure_subset
  intro q hq
  apply mem_scaleLimit_iff_small_witness.mpr
  intro δ hδ
  obtain ⟨z, hz, hqz⟩ := Metric.mem_closure_iff.mp hq (δ / 2) (by positivity)
  obtain ⟨h, hh, hsmall, x, hxz, hR⟩ :=
    mem_scaleLimit_iff_small_witness.mp hz (δ / 2) (by positivity)
  refine ⟨h, hh, hsmall.trans (by linarith), x, ?_, hR⟩
  have hdist := dist_triangle x z q
  rw [dist_comm z q] at hdist
  linarith

theorem isCompact_scaleLimit_inter {X : Type*} [PseudoMetricSpace X]
    (R : ℝ → X → Prop) {K : Set X} (hK : IsCompact K) :
    IsCompact (K ∩ scaleLimit R) :=
  hK.inter_right (isClosed_scaleLimit R)

/-- A compact bad set missing one continuous level misses an entire band.
The empty bad set is included. No positive lower bound is assumed in advance. -/
theorem compact_avoids_level_band {X : Type*} [TopologicalSpace X]
    {B : Set X} (hB : IsCompact B) (f : X → ℝ) (hf : Continuous f) (t : ℝ)
    (hlevel : ∀ q ∈ B, f q ≠ t) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ B, ρ ≤ |f q - t| := by
  apply hB.exists_forall_le' ((hf.sub continuous_const).abs.continuousOn)
  intro q hq
  exact abs_pos.mpr (sub_ne_zero.mpr (hlevel q hq))

end Endotactic
