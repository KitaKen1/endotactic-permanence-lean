import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max

/-!
# Uniform exclusion from sequential compactness

The bad relation need not be continuous or closed. The explicit sequential
hypothesis rules out every bad sequence at scales tending to zero. Compactness
alone does not supply that hypothesis.
-/

namespace Endotactic

open Filter Topology

theorem compact_sequential_exclusion {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] (K : Set X) (hK : IsCompact K) (R : ℝ → X → Prop)
    (hseq : ∀ (h : ℕ → ℝ) (x : ℕ → X) (p : X),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      (∀ n, x n ∈ K) → Tendsto x atTop (𝓝 p) → p ∈ K →
      (∀ n, R (h n) (x n)) → False) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ x ∈ K, ¬ R h x := by
  classical
  by_contra hbad
  push Not at hbad
  have hw : ∀ n : ℕ, ∃ h : ℝ, 0 < h ∧ h < 1 / ((n : ℝ) + 1) ∧
      ∃ x ∈ K, R h x := by
    intro n
    exact hbad (1 / ((n : ℝ) + 1)) (by positivity)
  choose h hh hsmall x hx hR using hw
  have hlim : Tendsto h atTop (𝓝 0) :=
    squeeze_zero (fun n => (hh n).le) (fun n => (hsmall n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨p, hp, φ, hφ, hxp⟩ := hK.tendsto_subseq hx
  exact hseq (h ∘ φ) (x ∘ φ) p (fun n => hh (φ n))
    (hlim.comp hφ.tendsto_atTop) (fun n => hx (φ n)) hxp hp
    (fun n => hR (φ n))

/-- The finite label set is fixed before a common scale threshold is chosen.
Empty label sets are handled without inventing a witness. -/
theorem finite_compact_sequential_exclusion {X I : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [Fintype I]
    (K : Set X) (hK : IsCompact K) (R : I → ℝ → X → Prop)
    (hseq : ∀ i : I, ∀ (h : ℕ → ℝ) (x : ℕ → X) (p : X),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      (∀ n, x n ∈ K) → Tendsto x atTop (𝓝 p) → p ∈ K →
      (∀ n, R i (h n) (x n)) → False) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ x ∈ K, ∀ i : I, ¬ R i h x := by
  classical
  by_cases hI : Nonempty I
  · let : Nonempty I := hI
    choose δ hδ hgood using fun i => compact_sequential_exclusion K hK (R i) (hseq i)
    let s := Finset.univ.image δ
    have hs : s.Nonempty := Finset.univ_nonempty.image δ
    have hmin : 0 < s.min' hs := by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (s.min'_mem hs)
      rw [← hi]
      exact hδ i
    refine ⟨min (s.min' hs) 1, lt_min hmin (by norm_num), min_le_right _ _, ?_⟩
    intro h hh hsmall x hx i
    apply hgood i h hh
      (hsmall.trans_le ((min_le_left _ _).trans
        (s.min'_le _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))) x hx
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    intro h hh hsmall x hx i
    exact (hI ⟨i⟩).elim

end Endotactic
