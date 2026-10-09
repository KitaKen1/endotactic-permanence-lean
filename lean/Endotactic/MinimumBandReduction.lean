import Endotactic.MinimumShiftChain

/-!
# Reduce the remaining affine existence gap to a pure interval lemma

The radius function is only pointwise positive on [a,b]. This target assumes
no continuity or global lower bound of the radius. If its finite ordered
certificate exists, the checked local induction and offset shifts prove the
exact full affine statement. `MinimumBandSelection` proves the interval target
downstream; this module supplies the independent type and generic reduction.
-/

namespace Endotactic

open Filter Topology Asymptotics

structure OrderedMinimumBandChain (n : ℕ) (a b : ℝ) (ρ : ℝ → ℝ) where
  center : Fin (n + 1) → ℝ
  center_mem : ∀ j, center j ∈ Set.Icc a b
  cut : ℕ → ℝ
  cut_between : ∀ k (hk : k < n),
    center ⟨k, by omega⟩ < cut k ∧ cut k < center ⟨k + 1, by omega⟩
  band_left : ∀ j, center j - ρ (center j) ≤ if j.val = 0 then a else cut (j.val - 1)
  band_right : ∀ j, (if j.val = n then b else cut j.val) ≤ center j + ρ (center j)

/-- This interval target has only real intervals and an arbitrary positive
radius function. It has no affine family, tolerance, ODE or network input.
It is proved downstream by `minimumBandSelection`. -/
def MinimumBandSelectionStatement : Prop :=
  ∀ a b : ℝ, a < b → ∀ ρ : ℝ → ℝ,
    (∀ t ∈ Set.Icc a b, 0 < ρ t) →
      ∃ n : ℕ, Nonempty (OrderedMinimumBandChain n a b ρ)

theorem affineMinimumCombination_of_bandSelection
    (hselect : MinimumBandSelectionStatement) : AffineMinimumCombinationStatement := by
  classical
  intro d hd hlocal a b hab E hE
  let : NeZero d := hd
  let block : ∀ t : Set.Icc a b, FixedMinimumApproximation d a b t.val E :=
    fun t => Classical.choice (hlocal a b hab E hE t.val t.property)
  have hnear := fun t : Set.Icc a b => (block t).near_minimum_with_decay
  choose radius hpos hdecay happrox using hnear
  let ρ : ℝ → ℝ := fun t => if ht : t ∈ Set.Icc a b then radius ⟨t, ht⟩ else 1
  have hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t := by
    intro t ht
    simpa only [ρ, dif_pos ht] using hpos ⟨t, ht⟩
  obtain ⟨n, ⟨S⟩⟩ := hselect a b hab ρ hρ
  let D : MinimumShiftChain d n a b E := {
    center := S.center
    center_mem := S.center_mem
    block := fun j => block ⟨S.center j, S.center_mem j⟩
    radius := fun j => ρ (S.center j)
    radius_pos := fun j => hρ (S.center j) (S.center_mem j)
    cut := S.cut
    cut_between := S.cut_between
    band_left := S.band_left
    band_right := S.band_right
    decay := fun j => by
      simpa only [ρ, dif_pos (S.center_mem j)] using hdecay ⟨S.center j, S.center_mem j⟩
    approximation := fun j => by
      simpa only [ρ, dif_pos (S.center_mem j)] using happrox ⟨S.center j, S.center_mem j⟩ }
  exact D.affine_approximation

theorem finiteAffineApproximation_of_minimumBandSelection
    (hselect : MinimumBandSelectionStatement) : FiniteAffineApproximationStatement :=
  finiteAffineApproximation_of_minimumCombination
    (affineMinimumCombination_of_bandSelection hselect)

end Endotactic
