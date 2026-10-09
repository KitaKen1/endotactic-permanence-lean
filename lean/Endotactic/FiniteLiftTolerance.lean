import Endotactic.AffineCoordinateLift

/-!
# Finite tolerance selection and omitted-coordinate errors

Only the tolerance at the already fixed finite slopes is used. No continuity
of the original tolerance function, or positive lower bound over a cube, is
assumed. The omitted-coordinate upper bound still needs the competing types.
-/

namespace Endotactic

open Filter Topology

theorem exists_common_positive_width {I : Type*} [Fintype I]
    (ε : I → ℝ) (hε : ∀ i, 0 < ε i) {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧ ∀ i, δ < ε i := by
  classical
  by_cases hI : Nonempty I
  · let : Nonempty I := hI
    let s := Finset.univ.image ε
    have hs : s.Nonempty := Finset.univ_nonempty.image _
    have hm : 0 < s.min' hs := by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (s.min'_mem hs)
      rw [← hi]
      exact hε i
    refine ⟨min R (s.min' hs) / 2, by positivity, ?_, ?_⟩
    · have hc := min_le_left R (s.min' hs)
      have hp : 0 < min R (s.min' hs) := lt_min hR hm
      linarith
    · intro i
      have hi := s.min'_le (ε i) (Finset.mem_image_of_mem ε (Finset.mem_univ i))
      have hc := min_le_right R (s.min' hs)
      have hp : 0 < min R (s.min' hs) := lt_min hR hm
      linarith
  · exact ⟨R / 2, by positivity, by linarith, fun i => (hI ⟨i⟩).elim⟩

theorem ScaledAffineFamily.exists_next_lift_level {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d)
    (E : State d → ℝ) {t β : ℝ} (htβ : t < β)
    (hE : ∀ i, 0 < E (extendCoordinates e t (B.slope i))) :
    ∃ η : ℝ, t < η ∧ η < β ∧
      ∀ i, η - t < E (extendCoordinates e t (B.slope i)) := by
  obtain ⟨δ, hδ, hδβ, hδε⟩ := exists_common_positive_width
    (fun i => E (extendCoordinates e t (B.slope i))) hE (sub_pos.mpr htβ)
  refine ⟨t + δ, by linarith, by linarith, ?_⟩
  intro i
  simpa using hδε i

theorem coordinate_error_lt_of_minimum_upper {d : ℕ} [NeZero d]
    {q : State d} {t η ε : ℝ} (hminimum : exponentMinimum q = t)
    (hgap : η - t < ε) (j : Fin d) (hupper : q j ≤ η) : |q j - t| < ε := by
  have hlower : t ≤ q j := hminimum ▸ exponentMinimum_le_coordinate q j
  rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

/-- Once the competing types have bounded omitted exponents by η, both
coordinate blocks combine into the strict ambient sup-norm tolerance. -/
theorem ScaledAffineFamily.coordinateLift_active_limit_of_minimum_upper
    {k d m : ℕ} [NeZero d] (B : ScaledAffineFamily k m)
    (e : Fin k ↪ Fin d) (t : ℝ) (γ : ℝ → ℝ)
    (L : Set (State k)) (ε : Fin m → ℝ) (hB : B.HasSequentialActivityBound L ε)
    (i : Fin m) {h : ℕ → ℝ} {p : ℕ → State d} {q : State d} {η : ℝ}
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q)) (hq : restrictCoordinates e q ∈ L)
    (hactive : ∀ n, ((B.coordinateLift e t γ).atScale (h n)).Active i
      (exponentialPoint (h n) (p n))) (hminimum : exponentMinimum q = t)
    (hgap : η - t < ε i) (hupper : ∀ j ∉ Set.range e, q j ≤ η) :
    ‖q - (B.coordinateLift e t γ).slope i‖ < ε i := by
  apply B.coordinateLift_active_limit_norm_lt e t γ L ε hB i hpos hh hp hq hactive
  intro j hj
  exact coordinate_error_lt_of_minimum_upper hminimum hgap j (hupper j hj)

end Endotactic
