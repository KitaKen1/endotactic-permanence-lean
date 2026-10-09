import Endotactic.Stoichiometry
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.Field.Pi

/-! # Coordinate bounds and compact absorption -/

namespace Endotactic

open Set

variable {d : ℕ} {E : Type*} [Fintype E]

/-- Eventual positive coordinate bounds for one rate path. -/
def Network.BoundedPermanentForRates (N : Network d E) (k : E → ℝ → ℝ)
    (c : State d) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    (∀ x₀ ∈ N.positiveClass c, N.PositiveWellPosed k x₀) ∧
    ∀ x₀ ∈ N.positiveClass c, ∀ x : ℝ → State d,
      N.IsGlobalPositiveSolution k x₀ x →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
          ∀ i, ε ≤ x t i ∧ x t i ≤ ε⁻¹

/-- Common eventual coordinate bounds for all admissible rate paths. -/
def Network.UniformBoundedPermanent (N : Network d E) (ℓ u : ℝ) (c : State d) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    ∀ k : E → ℝ → ℝ, AdmissibleRates k ℓ u →
      (∀ x₀ ∈ N.positiveClass c, N.PositiveWellPosed k x₀) ∧
      ∀ x₀ ∈ N.positiveClass c, ∀ x : ℝ → State d,
        N.IsGlobalPositiveSolution k x₀ x →
          ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
            ∀ i, ε ≤ x t i ∧ x t i ≤ ε⁻¹

/-- A compact positive set has common positive coordinate bounds. -/
theorem compact_positive_coordinate_bounds (hd : 0 < d) {K : Set (State d)}
    (hne : K.Nonempty) (hK : IsCompact K) (hpos : ∀ x ∈ K, Positive x) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x ∈ K, ∀ i, ε ≤ x i ∧ x i ≤ ε⁻¹ := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  choose a ha hamin using fun i : Fin d =>
    hK.exists_isMinOn hne (continuous_apply i).continuousOn
  choose b hb hbmax using fun i : Fin d =>
    hK.exists_isMaxOn hne (continuous_apply i).continuousOn
  let δ : Fin d → ℝ := fun i => min (a i i) (min 1 (max (b i i) 1)⁻¹)
  have hδ : ∀ i, 0 < δ i := by
    intro i
    exact lt_min (hpos (a i) (ha i) i)
      (lt_min zero_lt_one (inv_pos.mpr (zero_lt_one.trans_le (le_max_right _ _))))
  let q : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
  have hq : 0 < q := (Finset.lt_inf'_iff _).mpr (fun i _ => hδ i)
  have hqi : ∀ i, q ≤ δ i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  let ε : ℝ := q / 2
  have hε : 0 < ε := half_pos hq
  have hεi : ∀ i, ε ≤ δ i := fun i => (half_le_self hq.le).trans (hqi i)
  have hε₁ : ε < 1 := by
    have := (hqi (⟨0, hd⟩ : Fin d)).trans
      ((min_le_right _ _).trans (min_le_left _ _))
    dsimp [ε]
    linarith
  refine ⟨ε, hε, hε₁, ?_⟩
  intro x hx i
  refine ⟨((hεi i).trans (min_le_left _ _)).trans (hamin i hx), ?_⟩
  have he : ε ≤ (max (b i i) 1)⁻¹ :=
    (hεi i).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hu : max (b i i) 1 ≤ ε⁻¹ := by
    simpa only [inv_inv] using inv_anti₀ hε he
  exact (hbmax i hx).trans ((le_max_left _ _).trans hu)

omit [Fintype E] in
/-- Coordinate bounds yield a nonempty compact set in a positive class. -/
theorem Network.coordinate_bounds_compact_class (N : Network d E) (hd : 0 < d)
    {c : State d} (hc : Positive c) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set (State d), K.Nonempty ∧ IsCompact K ∧ K ⊆ N.positiveClass c ∧
      ∀ x ∈ N.positiveClass c, (∀ i, ε ≤ x i ∧ x i ≤ ε⁻¹) → x ∈ K := by
  obtain ⟨η, hη, _, hcb⟩ := compact_positive_coordinate_bounds hd
    (singleton_nonempty c) isCompact_singleton (by simpa using hc)
  let δ : ℝ := min ε η
  have hδ : 0 < δ := lt_min hε hη
  let C : Set (State d) := {x | x - c ∈ N.stoichiometricSubspace}
  have hC : IsClosed C :=
    N.stoichiometricSubspace.closed_of_finiteDimensional.preimage
      (continuous_id.sub continuous_const)
  let K : Set (State d) := Icc (fun _ => δ) (fun _ => δ⁻¹) ∩ C
  have he : δ ≤ ε := min_le_left _ _
  have hη' : δ ≤ η := min_le_right _ _
  have huε : ε⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ he
  have huη : η⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hη'
  refine ⟨K, ⟨c, ?_⟩, isCompact_Icc.inter_right hC, ?_, ?_⟩
  · refine ⟨⟨fun i => hη'.trans ((hcb c (mem_singleton c) i).1),
      fun i => ((hcb c (mem_singleton c) i).2).trans huη⟩, ?_⟩
    simp [C]
  · intro x hx
    exact ⟨fun i => hδ.trans_le (hx.1.1 i), hx.2⟩
  · intro x hx hb
    exact ⟨⟨fun i => he.trans (hb i).1, fun i => (hb i).2.trans huε⟩, hx.2⟩

/-- Coordinate-bound and compact-set permanence are equivalent. -/
theorem Network.boundedPermanentForRates_iff (N : Network d E) (hd : 0 < d)
    {k : E → ℝ → ℝ} {c : State d} (hc : Positive c) :
    N.BoundedPermanentForRates k c ↔ N.PermanentForRates k c := by
  constructor
  · rintro ⟨ε, hε, _, hwell, hb⟩
    obtain ⟨K, hne, hK, hclass, hbox⟩ := N.coordinate_bounds_compact_class hd hc hε
    refine ⟨K, hne, hK, hclass, hwell, ?_⟩
    intro x₀ h₀ x hx
    obtain ⟨T, hT, hstay⟩ := hb x₀ h₀ x hx
    exact ⟨T, hT, fun t ht =>
      hbox (x t) (hx.mem_positiveClass h₀ (hT.trans ht)) (hstay t ht)⟩
  · rintro ⟨K, hne, hK, hclass, hwell, hstay⟩
    obtain ⟨ε, hε, hε₁, hbox⟩ := compact_positive_coordinate_bounds hd hne hK
      (fun x hx => (hclass hx).1)
    refine ⟨ε, hε, hε₁, hwell, ?_⟩
    intro x₀ h₀ x hx
    obtain ⟨T, hT, ht⟩ := hstay x₀ h₀ x hx
    exact ⟨T, hT, fun t h => hbox (x t) (ht t h)⟩

/-- Common coordinate bounds and a common compact absorbing set are equivalent. -/
theorem Network.uniformBoundedPermanent_iff (N : Network d E) (hd : 0 < d)
    {ℓ u : ℝ} {c : State d} (hc : Positive c) :
    N.UniformBoundedPermanent ℓ u c ↔ N.UniformPermanent ℓ u c (fun _ => True) := by
  constructor
  · rintro ⟨ε, hε, _, hb⟩
    obtain ⟨K, hne, hK, hclass, hbox⟩ := N.coordinate_bounds_compact_class hd hc hε
    refine ⟨K, hne, hK, hclass, ?_⟩
    intro k hk _
    refine ⟨(hb k hk).1, ?_⟩
    intro x₀ h₀ x hx
    obtain ⟨T, hT, hstay⟩ := (hb k hk).2 x₀ h₀ x hx
    exact ⟨T, hT, fun t ht =>
      hbox (x t) (hx.mem_positiveClass h₀ (hT.trans ht)) (hstay t ht)⟩
  · rintro ⟨K, hne, hK, hclass, hstay⟩
    obtain ⟨ε, hε, hε₁, hbox⟩ := compact_positive_coordinate_bounds hd hne hK
      (fun x hx => (hclass hx).1)
    refine ⟨ε, hε, hε₁, ?_⟩
    intro k hk
    refine ⟨(hstay k hk True.intro).1, ?_⟩
    intro x₀ h₀ x hx
    obtain ⟨T, hT, ht⟩ := (hstay k hk True.intro).2 x₀ h₀ x hx
    exact ⟨T, hT, fun t h => hbox (x t) (ht t h)⟩

end Endotactic
