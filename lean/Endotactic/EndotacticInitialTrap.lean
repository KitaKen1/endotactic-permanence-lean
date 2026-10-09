import Endotactic.AffineApproximationExistence
import Endotactic.ScaledZeroCap
import Endotactic.AffineRobustness

/-!
# General endotactic initial traps and positive global well-posedness

The affine theorem, a zero-forcing tolerance and the logarithmic box construct
a genuine compact positive plateau around every positive initial state.
Its faces are conserved or strictly inward for the whole coefficient box.
No carrier, affine-existence oracle or numerical face certificate is supplied.

The compact trap is chosen before the rate path but after the initial state.
It does not yet establish the common absorbing set required by permanence.
-/

namespace Endotactic

open Filter Topology

theorem Network.exists_compact_positive_initial_face_trap {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (hd : 0 < d) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    {z : State d} (hz : Positive z) :
    ∃ m : ℕ, 0 < m ∧ ∃ A : AffineFamily d m, ∃ M : ℝ,
      z ∈ A.plateau M ∧ IsCompact (A.plateau M) ∧
      A.plateau M ⊆ {x | Positive x} ∧ N.AffineFaceCertificate A ℓ u M := by
  classical
  obtain ⟨ε, hε⟩ := N.exists_slopeTolerance hN
  obtain ⟨m, hm, A, _, _, hseq⟩ := finiteAffineApproximation d hd (-1) 1 (by norm_num)
    (zeroForcingTolerance ε) (fun r _ => zeroForcingTolerance_pos (fun r => (hε r).1) r)
  let : NeZero m := ⟨by omega⟩
  have hseq' := A.sequentialActivityBound_tolerance_mono hseq
    (fun i => zeroForcingTolerance_le ε (A.slope i))
  obtain ⟨H₁, hH₁, _, hflux⟩ := N.uniform_active_flux_of_sequentialActivityBound
    A _ isCompact_Icc ε hε hseq' hℓ hu
  obtain ⟨H₂, hH₂, hH₂1, hcap⟩ := A.exists_small_scale_zero_cap ε hseq hz
  let h : ℝ := min H₁ H₂ / 2
  have hh : 0 < h := div_pos (lt_min hH₁ hH₂) (by norm_num)
  have hlt : h < min H₁ H₂ := by dsimp [h]; linarith [lt_min hH₁ hH₂]
  have hlt₁ : h < H₁ := hlt.trans_le (min_le_left _ _)
  have hlt₂ : h < H₂ := hlt.trans_le (min_le_right _ _)
  have hh1 : h < 1 := hlt₂.trans_le hH₂1
  obtain ⟨i₀, _, hzK, hcompact, hpos, hbox⟩ := hcap h hh hlt₂
  refine ⟨m, hm, A.atScale h, A.offset i₀ h, hzK, hcompact, hpos, ?_⟩
  apply N.affineFaceCertificate_of_projections
  intro i
  by_cases hi : ∀ e, N.projection (A.slope i) e = 0
  · exact Or.inl hi
  · have hnonzero : ∃ e, N.projection (A.slope i) e ≠ 0 := by
      push Not at hi
      exact hi
    refine Or.inr ?_
    intro a ha y hy hvalue
    have hypos := hpos hy
    have hpow := exponentialPoint_logarithmicExponent hh hh1 hypos
    have hp := logarithmicExponent_mem_cube hh hh1 (hbox hy)
    have hactive : (A.atScale h).Active i y := by
      intro j
      rw [hvalue]
      exact hy j
    have hb := hflux h hh hlt₁ (logarithmicExponent h y) hp i
      (hpow.symm ▸ hactive) hnonzero a (fun e => ⟨ha.1 e, ha.2 e⟩)
    simpa only [hpow, ScaledAffineFamily.atScale_slope] using hb

theorem Network.positiveWellPosed_of_endotactic {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (hd : 0 < d) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u)
    {z : State d} (hz : Positive z) : N.PositiveWellPosed k z := by
  obtain ⟨m, hm, A, M, hzK, hK, hpos, hfaces⟩ :=
    N.exists_compact_positive_initial_face_trap hN hd hℓ hu hz
  let : NeZero m := ⟨by omega⟩
  exact N.positiveWellPosed_of_compact_affine_face_certificate hk A hK hpos hfaces hzK

/-- One compact positive trap works for every admissible rate path from this
fixed initial state. All positive integral solutions stay there from time 0. -/
theorem Network.exists_uniform_compact_initial_trap {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (hd : 0 < d) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    {z : State d} (hz : Positive z) :
    ∃ K : Set (State d), z ∈ K ∧ IsCompact K ∧ K ⊆ {x | Positive x} ∧
      ∀ k : E → ℝ → ℝ, AdmissibleRates k ℓ u →
        N.PositiveWellPosed k z ∧ ∀ x : ℝ → State d,
          N.IsGlobalPositiveSolution k z x → ∀ t : ℝ, 0 ≤ t → x t ∈ K := by
  obtain ⟨m, hm, A, M, hzK, hK, hpos, hfaces⟩ :=
    N.exists_compact_positive_initial_face_trap hN hd hℓ hu hz
  let : NeZero m := ⟨by omega⟩
  refine ⟨A.plateau M, hzK, hK, hpos, ?_⟩
  intro k hk
  obtain ⟨x, hx, htrap⟩ := N.exists_global_positive_of_compact_affine_face_certificate
    hk A hK hpos hfaces hzK
  refine ⟨N.positiveWellPosed_of_exists hk ⟨x, hx⟩, ?_⟩
  intro y hy t ht
  rw [Network.IsIntegralSolution.eqOn_nonnegative N hk hy.1 hx.1 ht]
  exact htrap t ht

/-- Explicit coordinate bounds, common to the rate paths from one initial
state. These bounds are not claimed common to all positive initial states. -/
theorem Network.exists_uniform_positive_trajectory_box {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (hd : 0 < d) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    {z : State d} (hz : Positive z) :
    ∃ lo hi : State d, lo ≤ hi ∧ Positive lo ∧
      ∀ k : E → ℝ → ℝ, AdmissibleRates k ℓ u →
        N.PositiveWellPosed k z ∧ ∀ x : ℝ → State d,
          N.IsGlobalPositiveSolution k z x → ∀ t : ℝ, 0 ≤ t → x t ∈ Set.Icc lo hi := by
  obtain ⟨m, hm, A, M, hzK, hK, hpos, hfaces⟩ :=
    N.exists_compact_positive_initial_face_trap hN hd hℓ hu hz
  let : NeZero m := ⟨by omega⟩
  obtain ⟨ε, lo, hi, hε, hbox, hlo, hrelax⟩ :=
    A.exists_enlarged_positive_box ⟨z, hzK⟩ hK hpos
  have hsub : A.plateau M ⊆ Set.Icc lo hi := by
    intro y hy
    apply hrelax
    intro i
    exact (sub_le_self M hε.le).trans (hy i)
  refine ⟨lo, hi, hbox, hlo, ?_⟩
  intro k hk
  obtain ⟨x, hx, htrap⟩ := N.exists_global_positive_of_compact_affine_face_certificate
    hk A hK hpos hfaces hzK
  refine ⟨N.positiveWellPosed_of_exists hk ⟨x, hx⟩, ?_⟩
  intro y hy t ht
  rw [Network.IsIntegralSolution.eqOn_nonnegative N hk hy.1 hx.1 ht]
  exact hsub (htrap t ht)

end Endotactic
