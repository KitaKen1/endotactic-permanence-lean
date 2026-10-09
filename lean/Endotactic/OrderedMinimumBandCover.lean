import Endotactic.FiniteMinimumBandCover

/-!
# Sort a pruned open band cover and certify adjacent overlap

Minimal-cardinality pruning makes both endpoint orders agree with the center
order. Coverage then excludes a gap between adjacent bands and places the
two interval endpoints inside the first and last band.
-/

namespace Endotactic

structure OrderedOpenMinimumBandCover (n : ℕ) (a b : ℝ) (ρ : ℝ → ℝ) where
  center : Fin (n + 1) → ℝ
  center_mem : ∀ j, center j ∈ Set.Icc a b
  center_strict : StrictMono center
  left_strict : StrictMono (fun j => center j - ρ (center j))
  right_strict : StrictMono (fun j => center j + ρ (center j))
  cover : ∀ x ∈ Set.Icc a b, ∃ j,
    center j - ρ (center j) < x ∧ x < center j + ρ (center j)

theorem exists_ordered_open_minimum_band_cover {a b : ℝ} (hab : a ≤ b) (ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) :
    ∃ n : ℕ, Nonempty (OrderedOpenMinimumBandCover n a b ρ) := by
  classical
  obtain ⟨s, hs, hprune⟩ := exists_pruned_minimum_band_cover ρ hρ
  have hcard0 : 0 < s.card := Finset.card_pos.mpr (hs.nonempty hab)
  let n := s.card - 1
  have hcard : s.card = n + 1 := by dsimp [n]; omega
  let f : Fin (n + 1) ↪o ℝ := s.orderEmbOfFin hcard
  have hmem : ∀ j, f j ∈ s := fun j => Finset.orderEmbOfFin_mem s hcard j
  have hends : ∀ i j, i < j → f i - ρ (f i) < f j - ρ (f j) ∧
      f i + ρ (f i) < f j + ρ (f j) := by
    intro i j hij
    have hf := f.strictMono hij
    exact minimum_band_endpoints_strict_of_noncontainment ρ hf
      (hprune (f i) (hmem i) (f j) (hmem j) (ne_of_lt hf))
      (hprune (f j) (hmem j) (f i) (hmem i) (ne_of_gt hf))
  refine ⟨n, ⟨{
    center := f
    center_mem := fun j => hs.1 (f j) (hmem j)
    center_strict := f.strictMono
    left_strict := fun _ _ hij => (hends _ _ hij).1
    right_strict := fun _ _ hij => (hends _ _ hij).2
    cover := ?_ }⟩⟩
  intro x hx
  obtain ⟨t, ht, hleft, hright⟩ := hs.2 x hx
  have htrange : t ∈ Set.range f := by
    change t ∈ Set.range (s.orderEmbOfFin hcard)
    rw [Finset.range_orderEmbOfFin]
    exact ht
  obtain ⟨j, rfl⟩ := htrange
  exact ⟨j, hleft, hright⟩

theorem OrderedOpenMinimumBandCover.first_contains_left {n : ℕ} {a b : ℝ} {ρ : ℝ → ℝ}
    (D : OrderedOpenMinimumBandCover n a b ρ) (hab : a ≤ b) :
    D.center 0 - ρ (D.center 0) < a := by
  obtain ⟨j, hj, _⟩ := D.cover a ⟨le_rfl, hab⟩
  exact (D.left_strict.monotone (Fin.zero_le j)).trans_lt hj

theorem OrderedOpenMinimumBandCover.last_contains_right {n : ℕ} {a b : ℝ} {ρ : ℝ → ℝ}
    (D : OrderedOpenMinimumBandCover n a b ρ) (hab : a ≤ b) :
    b < D.center (Fin.last n) + ρ (D.center (Fin.last n)) := by
  obtain ⟨j, _, hj⟩ := D.cover b ⟨hab, le_rfl⟩
  exact hj.trans_le (D.right_strict.monotone (Fin.le_last j))

theorem OrderedOpenMinimumBandCover.adjacent_overlap {n : ℕ} {a b : ℝ} {ρ : ℝ → ℝ}
    (D : OrderedOpenMinimumBandCover n a b ρ)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) (k : ℕ) (hk : k < n) :
    D.center ⟨k + 1, by omega⟩ - ρ (D.center ⟨k + 1, by omega⟩) <
      D.center ⟨k, by omega⟩ + ρ (D.center ⟨k, by omega⟩) := by
  let i : Fin (n + 1) := ⟨k, by omega⟩
  let next : Fin (n + 1) := ⟨k + 1, by omega⟩
  by_contra hbad
  have hgap : D.center i + ρ (D.center i) ≤ D.center next - ρ (D.center next) :=
    le_of_not_gt hbad
  have hposi := hρ (D.center i) (D.center_mem i)
  have hposnext := hρ (D.center next) (D.center_mem next)
  have hx : D.center i + ρ (D.center i) ∈ Set.Icc a b := by
    have hi := (D.center_mem i).1
    have hn := (D.center_mem next).2
    constructor <;> linarith
  obtain ⟨j, hleft, hright⟩ := D.cover _ hx
  by_cases hji : j.val ≤ k
  · have hjle : j ≤ i := hji
    have hr := D.right_strict.monotone hjle
    linarith
  · have hnj : next ≤ j := by change k + 1 ≤ j.val; omega
    have hl := D.left_strict.monotone hnj
    linarith

theorem OrderedOpenMinimumBandCover.exists_adjacent_cut {n : ℕ} {a b : ℝ} {ρ : ℝ → ℝ}
    (D : OrderedOpenMinimumBandCover n a b ρ)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) (k : ℕ) (hk : k < n) :
    ∃ q : ℝ,
      D.center ⟨k, by omega⟩ < q ∧ q < D.center ⟨k + 1, by omega⟩ ∧
      D.center ⟨k + 1, by omega⟩ - ρ (D.center ⟨k + 1, by omega⟩) < q ∧
      q < D.center ⟨k, by omega⟩ + ρ (D.center ⟨k, by omega⟩) := by
  let i : Fin (n + 1) := ⟨k, by omega⟩
  let next : Fin (n + 1) := ⟨k + 1, by omega⟩
  have hc : D.center i < D.center next := D.center_strict (by change k < k + 1; omega)
  have hpi := hρ (D.center i) (D.center_mem i)
  have hpn := hρ (D.center next) (D.center_mem next)
  have ho := D.adjacent_overlap hρ k hk
  have hgap : max (D.center i) (D.center next - ρ (D.center next)) <
      min (D.center next) (D.center i + ρ (D.center i)) := by
    apply lt_min
    · exact max_lt_iff.mpr ⟨hc, by linarith⟩
    · exact max_lt_iff.mpr ⟨by linarith, ho⟩
  obtain ⟨q, hlow, hupp⟩ := exists_between hgap
  exact ⟨q, (le_max_left _ _).trans_lt hlow,
    hupp.trans_le (min_le_left _ _), (le_max_right _ _).trans_lt hlow,
    hupp.trans_le (min_le_right _ _)⟩

end Endotactic
