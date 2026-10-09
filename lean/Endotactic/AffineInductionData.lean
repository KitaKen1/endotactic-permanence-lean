import Endotactic.FixedMinimumAssembly

/-!
# Dimension-wise induction and finite staged support data

Unselected entries are harmless seed placeholders. Every entry has an ambient
cube slope, but only selected ranks have the lower-dimensional approximation.
Choosing a level after the finite entries prevents a circular tolerance choice.
-/

namespace Endotactic

open Filter Topology Asymptotics

def AffineApproximationInDimension (d : ℕ) : Prop :=
  ∀ a b : ℝ, a < b → ∀ E : State d → ℝ,
    (∀ p ∈ Set.Icc (fun _ => a) (fun _ => b), 0 < E p) →
      ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily d m,
        (∀ i, A.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) ∧
        (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) ∧
        A.HasSequentialActivityBound (Set.Icc (fun _ => a) (fun _ => b))
          (fun i => E (A.slope i))

theorem finiteAffineApproximation_iff_dimensions : FiniteAffineApproximationStatement ↔
    ∀ d : ℕ, 0 < d → AffineApproximationInDimension d := Iff.rfl

abbrev SupportAffineEntry {d : ℕ} (U : RaisedSupport d) :=
  Σ m : ℕ, ScaledAffineFamily U.val.card m

def SupportAffineEntry.Valid {d : ℕ} (t b : ℝ) (E : State d → ℝ)
    (U : RaisedSupport d) (β : ℝ) (C : SupportAffineEntry U) : Prop :=
  (∀ i, C.2.slope i ∈ Set.Icc (fun _ => β) (fun _ => b)) ∧
  (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (C.2.offset i) (fun h => h ^ β)) ∧
  C.2.HasSequentialActivityBound (Set.Icc (fun _ => β) (fun _ => b))
    (fun i => E (extendCoordinates U.embedding t (C.2.slope i)))

theorem exists_support_entry_of_lower_dimensions {d : ℕ} {t β b : ℝ}
    (E : State d → ℝ) (htβ : t < β) (hβb : β < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hIH : ∀ k : ℕ, 0 < k → k < d → AffineApproximationInDimension k)
    (U : RaisedSupport d) :
    ∃ C : SupportAffineEntry U, 0 < C.1 ∧ C.Valid t b E U β := by
  have htol : ∀ r ∈ Set.Icc (fun _ : Fin U.val.card => β) (fun _ => b),
      0 < E (extendCoordinates U.embedding t r) := by
    intro r hr
    exact hE _ (extendCoordinates_mem_cube U.embedding ⟨le_rfl, htβ.le.trans hβb.le⟩
      ⟨fun j => htβ.le.trans (hr.1 j), hr.2⟩)
  obtain ⟨m, hm, B, hc, ho, ha⟩ := hIH U.val.card U.property.1 U.property.2
    β b hβb (fun r => E (extendCoordinates U.embedding t r)) htol
  exact ⟨⟨m, B⟩, hm, hc, ho, ha⟩

/-- A reaction-specific or known-answer route may supply just these support
families for the actual pullback of E, instead of the universal lower theorem. -/
def SupportFamilyOracle (d : ℕ) (t b : ℝ) (E : State d → ℝ) : Prop :=
  ∀ U : RaisedSupport d, ∀ β : ℝ, t < β → β < b →
    ∃ C : SupportAffineEntry U, 0 < C.1 ∧ C.Valid t b E U β

theorem supportFamilyOracle_of_lower_dimensions {d : ℕ} {t b : ℝ}
    (E : State d → ℝ)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hIH : ∀ k : ℕ, 0 < k → k < d → AffineApproximationInDimension k) :
    SupportFamilyOracle d t b E := by
  intro U β htβ hβb
  exact exists_support_entry_of_lower_dimensions E htβ hβb hE hIH U

structure AffineSupportPrefix (d : ℕ) (t b : ℝ) (E : State d → ℝ) (k : ℕ) where
  entry : ∀ U : RaisedSupport d, SupportAffineEntry U
  size_pos : ∀ U, 0 < (entry U).1
  ambient_cube : ∀ U i, extendCoordinates U.embedding t ((entry U).2.slope i) ∈
    Set.Icc (fun _ => t) (fun _ => b)
  level : ℕ → ℝ
  level_bounds : ∀ n, 1 ≤ n → n ≤ k → t < level n ∧ level n < b
  descending : ∀ n, 1 ≤ n → n + 1 ≤ k → level (n + 1) < level n
  selected : ∀ U : RaisedSupport d, U.val.card ≤ k →
    (entry U).Valid t b E U (level U.val.card)
  seed_width : 1 ≤ k → level 1 - t < E (fun _ => t)
  next_width : ∀ U : RaisedSupport d, U.val.card + 1 ≤ k → ∀ i,
    level (U.val.card + 1) - t <
      E (extendCoordinates U.embedding t ((entry U).2.slope i))

noncomputable def AffineSupportPrefix.initial {d : ℕ} {t b : ℝ}
    (E : State d → ℝ) (htb : t ≤ b) : AffineSupportPrefix d t b E 0 where
  entry U := ⟨1, minimumSeedFamily U.val.card t⟩
  size_pos _ := by norm_num
  ambient_cube U _ := extendCoordinates_mem_cube U.embedding ⟨le_rfl, htb⟩
    ⟨fun _ => le_rfl, fun _ => htb⟩
  level _ := b
  level_bounds _ hpos hzero := by omega
  descending _ hpos hzero := by omega
  selected U hzero := by have := U.property.1; omega
  seed_width hzero := by omega
  next_width _ hzero := by omega

/-- One level works for the seed and all finite stored slopes. It is chosen
before the next rank's lower-dimensional families, with no regularity of E. -/
theorem AffineSupportPrefix.exists_next_level {d k : ℕ} {t b : ℝ} {E : State d → ℝ}
    (P : AffineSupportPrefix d t b E k) (htb : t < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r) :
    ∃ β : ℝ, t < β ∧ β < b ∧ (0 < k → β < P.level k) ∧
      β - t < E (fun _ => t) ∧ ∀ U i,
        β - t < E (extendCoordinates U.embedding t ((P.entry U).2.slope i)) := by
  classical
  let I := Σ U : RaisedSupport d, Fin (P.entry U).1
  let ε : Option I → ℝ
    | none => E (fun _ => t)
    | some l => E (extendCoordinates l.1.embedding t ((P.entry l.1).2.slope l.2))
  have hε : ∀ i, 0 < ε i := by
    intro i
    cases i with
    | none => exact hE _ ⟨fun _ => le_rfl, fun _ => htb.le⟩
    | some l => exact hE _ (P.ambient_cube l.1 l.2)
  let R := if k = 0 then b else P.level k
  have htR : t < R := by
    by_cases hk : k = 0
    · simpa [R, hk] using htb
    · simpa [R, hk] using (P.level_bounds k (by omega) le_rfl).1
  obtain ⟨δ, hδ, hδR, hδε⟩ := exists_common_positive_width ε hε (sub_pos.mpr htR)
  refine ⟨t + δ, by linarith, ?_, ?_, ?_, ?_⟩
  · by_cases hk : k = 0
    · simp only [R, if_pos hk] at hδR
      linarith
    · have hb := (P.level_bounds k (by omega) le_rfl).2
      simp only [R, if_neg hk] at hδR
      linarith
  · intro hk
    have hk0 : k ≠ 0 := by omega
    simp only [R, if_neg hk0] at hδR
    linarith
  · simpa [ε] using hδε none
  · intro U i
    simpa [ε] using hδε (some ⟨U, i⟩)

end Endotactic
