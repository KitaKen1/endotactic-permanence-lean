import Endotactic.ExponentMinimum

/-!
# Restrict and extend exponent coordinates

An injective coordinate map records the raised-coordinate type. Extension
sets every other slope coordinate to the common minimum t. The norm is the
ambient sup norm; projected and omitted-coordinate errors suffice separately.
-/

namespace Endotactic

open Filter Topology

def restrictCoordinates {k d : ℕ} (e : Fin k ↪ Fin d) (p : State d) : State k :=
  fun j => p (e j)

noncomputable def extendCoordinates {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (r : State k) : State d := Function.extend e r (fun _ => t)

theorem extendCoordinates_apply {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (r : State k) (j : Fin k) : extendCoordinates e t r (e j) = r j :=
  e.injective.extend_apply r (fun _ => t) j

theorem extendCoordinates_apply_outside {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (r : State k) {j : Fin d} (hj : j ∉ Set.range e) :
    extendCoordinates e t r j = t := Function.extend_apply' _ _ _ hj

theorem restrict_extendCoordinates {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (r : State k) : restrictCoordinates e (extendCoordinates e t r) = r := by
  funext j
  exact extendCoordinates_apply e t r j

theorem restrictCoordinates_exponentialPoint {k d : ℕ} (e : Fin k ↪ Fin d)
    (h : ℝ) (p : State d) :
    restrictCoordinates e (exponentialPoint h p) =
      exponentialPoint h (restrictCoordinates e p) := rfl

theorem continuous_restrictCoordinates {k d : ℕ} (e : Fin k ↪ Fin d) :
    Continuous (restrictCoordinates e) := continuous_pi fun j => continuous_apply (e j)

theorem tendsto_restrictCoordinates {k d : ℕ} (e : Fin k ↪ Fin d)
    {p : ℕ → State d} {q : State d} (hp : Tendsto p atTop (𝓝 q)) :
    Tendsto (fun n => restrictCoordinates e (p n)) atTop (𝓝 (restrictCoordinates e q)) :=
  ((continuous_restrictCoordinates e).tendsto q).comp hp

theorem restrictCoordinates_mem_cube {k d : ℕ} (e : Fin k ↪ Fin d)
    {a b : ℝ} {p : State d} (hp : p ∈ Set.Icc (fun _ => a) (fun _ => b)) :
    restrictCoordinates e p ∈ Set.Icc (fun _ => a) (fun _ => b) :=
  ⟨fun j => hp.1 (e j), fun j => hp.2 (e j)⟩

theorem extendCoordinates_mem_cube {k d : ℕ} (e : Fin k ↪ Fin d)
    {a b t : ℝ} {r : State k} (ht : t ∈ Set.Icc a b)
    (hr : r ∈ Set.Icc (fun _ => a) (fun _ => b)) :
    extendCoordinates e t r ∈ Set.Icc (fun _ => a) (fun _ => b) := by
  have hc : ∀ j, a ≤ extendCoordinates e t r j ∧ extendCoordinates e t r j ≤ b := by
    intro j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      rw [extendCoordinates_apply]
      exact ⟨hr.1 i, hr.2 i⟩
    · rw [extendCoordinates_apply_outside e t r hj]
      exact ht
  exact ⟨fun j => (hc j).1, fun j => (hc j).2⟩

theorem norm_sub_extendCoordinates_lt {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (r : State k) (q : State d) {ε : ℝ} (hε : 0 < ε)
    (hin : ‖restrictCoordinates e q - r‖ < ε)
    (hout : ∀ j ∉ Set.range e, |q j - t| < ε) :
    ‖q - extendCoordinates e t r‖ < ε := by
  apply (pi_norm_lt_iff hε).mpr
  intro j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    have hi := (norm_le_pi_norm (restrictCoordinates e q - r) i).trans_lt hin
    simpa only [Pi.sub_apply, restrictCoordinates, extendCoordinates_apply] using hi
  · simpa only [Pi.sub_apply, Real.norm_eq_abs,
      extendCoordinates_apply_outside e t r hj] using hout j hj

/-- Both lifted slopes have the same omitted coordinates, so these terms
cancel without any approximation or assumption on the state. -/
theorem dot_extendCoordinates_sub {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (r s : State k) (x : State d) :
    dot (extendCoordinates e t r) x - dot (extendCoordinates e t s) x =
      dot r (restrictCoordinates e x) - dot s (restrictCoordinates e x) := by
  classical
  simp only [dot, ← Finset.sum_sub_distrib]
  have hsum : (∑ j ∈ Finset.univ.map e,
      (extendCoordinates e t r j * x j - extendCoordinates e t s j * x j)) =
      ∑ j : Fin d, (extendCoordinates e t r j * x j -
        extendCoordinates e t s j * x j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have ho : j ∉ Set.range e := by
      rintro ⟨i, rfl⟩
      exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    rw [extendCoordinates_apply_outside e t r ho,
      extendCoordinates_apply_outside e t s ho, sub_self]
  rw [← hsum, Finset.sum_map]
  simp only [extendCoordinates_apply, restrictCoordinates]

/-- At the last raised-coordinate type the only omitted coordinate must
attain the minimum. This conclusion uses the strict lower bound on every
raised coordinate, rather than assuming the omitted value equals t. -/
theorem omitted_coordinate_eq_minimum {k d : ℕ} [NeZero d]
    (e : Fin k ↪ Fin d) (j : Fin d) {q : State d} {t : ℝ}
    (hminimum : exponentMinimum q = t) (hraised : ∀ i, t < q (e i))
    (hunique : ∀ l ∉ Set.range e, l = j) : q j = t := by
  obtain ⟨l, hl⟩ := exponentMinimum_attained q
  have hout : l ∉ Set.range e := by
    rintro ⟨i, rfl⟩
    exact (ne_of_gt (hraised i)) (hl.symm.trans hminimum)
  rw [← hunique l hout]
  exact hl.symm.trans hminimum

theorem extendCoordinates_minimum {k d : ℕ} [NeZero d]
    (e : Fin k ↪ Fin d) (t : ℝ) (r : State k)
    (hr : ∀ i, t ≤ r i) (j : Fin d) (hj : j ∉ Set.range e) :
    exponentMinimum (extendCoordinates e t r) = t := by
  apply le_antisymm
  · simpa only [extendCoordinates_apply_outside e t r hj] using
      exponentMinimum_le_coordinate (extendCoordinates e t r) j
  · obtain ⟨l, hl⟩ := exponentMinimum_attained (extendCoordinates e t r)
    rw [hl]
    by_cases ho : l ∈ Set.range e
    · obtain ⟨i, rfl⟩ := ho
      simpa only [extendCoordinates_apply] using hr i
    · rw [extendCoordinates_apply_outside e t r ho]

end Endotactic
