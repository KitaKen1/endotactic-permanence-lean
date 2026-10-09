import Endotactic.CoordinateEmbedding
import Endotactic.AffinePowerComparison

/-!
# Lift lower-dimensional affine families without losing any active label

The common offset γ and common omitted-coordinate contribution cancel in all
pairwise comparisons. Thus a lifted active label is exactly a projected active
label, including ties. The lower-dimensional bound and omitted-coordinate
bound are explicit inputs; this module does not construct all inductive types.
-/

namespace Endotactic

open Filter Topology Asymptotics

noncomputable def ScaledAffineFamily.coordinateLift {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (t : ℝ) (γ : ℝ → ℝ) :
    ScaledAffineFamily d m where
  slope i := extendCoordinates e t (B.slope i)
  offset i h := γ h + B.offset i h

theorem ScaledAffineFamily.coordinateLift_value_sub {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (t : ℝ) (γ : ℝ → ℝ)
    (h : ℝ) (i j : Fin m) (x : State d) :
    ((B.coordinateLift e t γ).atScale h).value i x -
        ((B.coordinateLift e t γ).atScale h).value j x =
      (B.atScale h).value i (restrictCoordinates e x) -
        (B.atScale h).value j (restrictCoordinates e x) := by
  simp only [ScaledAffineFamily.atScale_value, ScaledAffineFamily.coordinateLift]
  have heq := dot_extendCoordinates_sub e t (B.slope i) (B.slope j) x
  linarith

theorem ScaledAffineFamily.coordinateLift_active_iff {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (t : ℝ) (γ : ℝ → ℝ)
    (h : ℝ) (i : Fin m) (x : State d) :
    ((B.coordinateLift e t γ).atScale h).Active i x ↔
      (B.atScale h).Active i (restrictCoordinates e x) := by
  change (∀ j, _ ≤ _) ↔ ∀ j, _ ≤ _
  have heq := B.coordinateLift_value_sub e t γ h i
  constructor <;> intro hi j
  · have hj := hi j
    have hd := heq j x
    linarith
  · have hj := hi j
    have hd := heq j x
    linarith

theorem ScaledAffineFamily.coordinateLift_exponential_active_iff {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (t : ℝ) (γ : ℝ → ℝ)
    (h : ℝ) (i : Fin m) (p : State d) :
    ((B.coordinateLift e t γ).atScale h).Active i (exponentialPoint h p) ↔
      (B.atScale h).Active i (exponentialPoint h (restrictCoordinates e p)) := by
  rw [B.coordinateLift_active_iff, restrictCoordinates_exponentialPoint]

theorem ScaledAffineFamily.coordinateLift_slopes_mem_cube {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (γ : ℝ → ℝ)
    {a b t : ℝ} (ht : t ∈ Set.Icc a b)
    (hB : ∀ i, B.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) :
    ∀ i, (B.coordinateLift e t γ).slope i ∈ Set.Icc (fun _ => a) (fun _ => b) :=
  fun i => extendCoordinates_mem_cube e ht (hB i)

theorem ScaledAffineFamily.coordinateLift_offset_isLittleO {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (t a : ℝ) (γ : ℝ → ℝ)
    (hγ : IsLittleO (𝓝[>] (0 : ℝ)) γ (fun h => h ^ a))
    (hB : ∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (B.offset i) (fun h => h ^ a)) :
    ∀ i, IsLittleO (𝓝[>] (0 : ℝ)) ((B.coordinateLift e t γ).offset i)
      (fun h => h ^ a) := fun i => hγ.add (hB i)

/-- The sup-norm estimate at an actual active limit. Approaching points may
be outside either cube; only the projected limit must be in the lower set. -/
theorem ScaledAffineFamily.coordinateLift_active_limit_norm_lt {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (t : ℝ) (γ : ℝ → ℝ)
    (L : Set (State k)) (ε : Fin m → ℝ) (hB : B.HasSequentialActivityBound L ε)
    (i : Fin m) {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q)) (hq : restrictCoordinates e q ∈ L)
    (hactive : ∀ n, ((B.coordinateLift e t γ).atScale (h n)).Active i
      (exponentialPoint (h n) (p n)))
    (hout : ∀ j ∉ Set.range e, |q j - t| < ε i) :
    ‖q - (B.coordinateLift e t γ).slope i‖ < ε i := by
  have hin := hB i h (fun n => restrictCoordinates e (p n)) (restrictCoordinates e q)
    hpos hh (tendsto_restrictCoordinates e hp) hq
    (fun n => (B.coordinateLift_exponential_active_iff e t γ (h n) i (p n)).mp
      (hactive n))
  exact norm_sub_extendCoordinates_lt e t (B.slope i) q
    (lt_of_le_of_lt (norm_nonneg _) hin) hin hout

theorem ScaledAffineFamily.coordinateLift_sequentialActivityBound {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (t : ℝ) (γ : ℝ → ℝ)
    (K : Set (State d)) (L : Set (State k)) (ε : Fin m → ℝ)
    (hB : B.HasSequentialActivityBound L ε)
    (hprojection : ∀ q ∈ K, restrictCoordinates e q ∈ L)
    (hout : ∀ q ∈ K, ∀ i : Fin m, ∀ j ∉ Set.range e, |q j - t| < ε i) :
    (B.coordinateLift e t γ).HasSequentialActivityBound K ε := by
  intro i h p q hpos hh hp hq hactive
  exact B.coordinateLift_active_limit_norm_lt e t γ L ε hB i hpos hh hp
    (hprojection q hq) hactive (hout q hq i)

/-- The last type has no omitted-coordinate error. Its value t follows from
the minimum condition and strict raised gap t<β. Neither B's existence nor
the existence of every type is asserted here. -/
theorem ScaledAffineFamily.coordinateLift_last_minimum_stratum {k d m : ℕ}
    [NeZero d] (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d)
    (j : Fin d) (hunique : ∀ l ∉ Set.range e, l = j)
    (t β b : ℝ) (htβ : t < β) (γ : ℝ → ℝ) (ε : Fin m → ℝ)
    (hε : ∀ i, 0 < ε i)
    (hB : B.HasSequentialActivityBound (Set.Icc (fun _ => β) (fun _ => b)) ε) :
    (B.coordinateLift e t γ).HasSequentialActivityBound
      {q | q ≤ (fun _ => b) ∧ exponentMinimum q = t ∧ ∀ i, β ≤ q (e i)} ε := by
  apply B.coordinateLift_sequentialActivityBound e t γ _ _ ε hB
  · intro q hq
    exact ⟨hq.2.2, fun i => hq.1 (e i)⟩
  · intro q hq i l hl
    have hj := omitted_coordinate_eq_minimum e j hq.2.1
      (fun i => htβ.trans_le (hq.2.2 i)) hunique
    rw [hunique l hl, hj, sub_self, abs_zero]
    exact hε i

end Endotactic
