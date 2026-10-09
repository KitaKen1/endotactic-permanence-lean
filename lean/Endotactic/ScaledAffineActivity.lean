import Endotactic.AffinePlateau
import Endotactic.MonomialOrder
import Endotactic.CompactSequentialExclusion
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Scale-dependent offsets, fixed slopes, and uniform activity approximation

Offsets need not be continuous. The sequential approximation is an explicit
hypothesis of the uniformization theorem here. The exact approximation
statement below is proved downstream by `finiteAffineApproximation` in
`MinimumBandSelection`; it is neither an axiom nor an assumed proof input there.
-/

namespace Endotactic

open Filter Topology

structure ScaledAffineFamily (d m : ℕ) where
  slope : Fin m → State d
  offset : Fin m → ℝ → ℝ

def ScaledAffineFamily.atScale {d m : ℕ} (A : ScaledAffineFamily d m) (h : ℝ) :
    AffineFamily d m where
  slope := A.slope
  offset i := A.offset i h

/-- Approaching exponent points may lie outside `K`; only the limiting point
belongs to `K`. Every fixed label remaining active must meet its tolerance. -/
def ScaledAffineFamily.HasSequentialActivityBound {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (ε : Fin m → ℝ) : Prop :=
  ∀ i : Fin m, ∀ (h : ℕ → ℝ) (p : ℕ → State d) (q : State d),
    (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) → Tendsto p atTop (𝓝 q) → q ∈ K →
    (∀ n, (A.atScale (h n)).Active i (exponentialPoint (h n) (p n))) →
      ‖q - A.slope i‖ < ε i

theorem ScaledAffineFamily.atScale_slope {d m : ℕ}
    (A : ScaledAffineFamily d m) (h : ℝ) (i : Fin m) :
    (A.atScale h).slope i = A.slope i := rfl

theorem ScaledAffineFamily.atScale_value {d m : ℕ}
    (A : ScaledAffineFamily d m) (h : ℝ) (i : Fin m) (x : State d) :
    (A.atScale h).value i x = dot (A.slope i) x + A.offset i h := rfl

/-- The uniform activity corollary follows from sequential approximation,
compactness, and a fixed finite label set. Neither tolerance nor offsets need
continuity. All minimizing labels, including ties, are quantified. -/
theorem ScaledAffineFamily.uniformActivityBound_of_sequential {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (hK : IsCompact K)
    (ε : Fin m → ℝ) (hseq : A.HasSequentialActivityBound K ε) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ p ∈ K, ∀ i : Fin m,
        (A.atScale h).Active i (exponentialPoint h p) → ‖p - A.slope i‖ < ε i := by
  let R := fun i h p =>
    (A.atScale h).Active i (exponentialPoint h p) ∧ ε i ≤ ‖p - A.slope i‖
  have hbad : ∀ i : Fin m, ∀ (h : ℕ → ℝ) (p : ℕ → State d) (q : State d),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      (∀ n, p n ∈ K) → Tendsto p atTop (𝓝 q) → q ∈ K →
      (∀ n, R i (h n) (p n)) → False := by
    intro i h p q hh hlim _ hplim hq hR
    have hstrict := hseq i h p q hh hlim hplim hq (fun n => (hR n).1)
    have hnorm : Tendsto (fun n => ‖p n - A.slope i‖) atTop (𝓝 ‖q - A.slope i‖) :=
      (hplim.sub tendsto_const_nhds).norm
    have hle := ge_of_tendsto hnorm (Eventually.of_forall fun n => (hR n).2)
    exact (not_lt_of_ge hle) hstrict
  obtain ⟨h₀, hh₀, hh₀1, hgood⟩ := finite_compact_sequential_exclusion K hK R hbad
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall p hp i hi
  exact lt_of_not_ge (fun hle => hgood h hh hsmall p hp i ⟨hi, hle⟩)

theorem ScaledAffineFamily.norm_close_coordinate {d m : ℕ}
    (A : ScaledAffineFamily d m) {p : State d} {i : Fin m} {ε : ℝ}
    (hclose : ‖p - A.slope i‖ < ε) : ∀ j, |p j - A.slope i j| ≤ ε := by
  intro j
  have hj : |p j - A.slope i j| ≤ ‖p - A.slope i‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (p - A.slope i) j
  exact (hj.trans_lt hclose).le

/-- Formal type of the affine lemma, proved downstream by
`finiteAffineApproximation`. The tolerance is chosen before the finite family and may be
discontinuous. Offsets must decay relative to `h^a` from the positive side. -/
def FiniteAffineApproximationStatement : Prop :=
  ∀ d : ℕ, 0 < d → ∀ a b : ℝ, a < b →
    ∀ E : State d → ℝ, (∀ p ∈ Set.Icc (fun _ => a) (fun _ => b), 0 < E p) →
      ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily d m,
        (∀ i, A.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) ∧
        (∀ i, Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) ∧
        A.HasSequentialActivityBound (Set.Icc (fun _ => a) (fun _ => b))
          (fun i => E (A.slope i))

end Endotactic
