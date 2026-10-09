import Endotactic.ScaledAffineActivity
import Endotactic.FiniteSlopeDominance
import Endotactic.LinearGeometry
import Endotactic.ClassInvariance

/-!
# From the affine approximation target to all-active flux

The slope tolerance is chosen pointwise before the finite affine family.
Conserved slopes are allowed and excluded automatically on exterior class
branches. The final theorem assumes the affine approximation statement
explicitly. `AffineApproximationExistence` supplies the proved statement
downstream, so its flux-family APIs no longer require an affine oracle.
-/

namespace Endotactic

open Filter Topology

def Network.IsSlopeTolerance {d : ℕ} {E : Type*} [Fintype E]
    (N : Network d E) (ε : State d → ℝ) : Prop :=
  ∀ r : State d, 0 < ε r ∧
    ((∃ e : E, N.projection r e ≠ 0) → ∃ H B : ℝ, 0 < H ∧
      ∀ p : State d, (∀ j, |p j - r j| ≤ ε r) →
        Nonempty (N.DirectionalCertificate r p H B))

/-- A possibly discontinuous tolerance function is selected before the affine
family. Conserved directions receive an arbitrary positive tolerance. -/
theorem Network.exists_slopeTolerance {d : ℕ} {E : Type*} [Fintype E]
    (N : Network d E) (hN : N.IsEndotactic) :
    ∃ ε : State d → ℝ, N.IsSlopeTolerance ε := by
  classical
  have hex : ∀ r : State d, ∃ ε : ℝ, 0 < ε ∧
      ((∃ e : E, N.projection r e ≠ 0) → ∃ H B : ℝ, 0 < H ∧
        ∀ p : State d, (∀ j, |p j - r j| ≤ ε) →
          Nonempty (N.DirectionalCertificate r p H B)) := by
    intro r
    by_cases hr : ∃ e : E, N.projection r e ≠ 0
    · obtain ⟨ε, H, B, hε, hH, _, hC⟩ := exists_fixed_slope_tolerantCertificate N hN r hr
      exact ⟨ε, hε, fun _ => ⟨H, B, hH, hC⟩⟩
    · exact ⟨1, by norm_num, fun h => (hr h).elim⟩
  choose ε hε hC using hex
  exact ⟨ε, fun r => ⟨hε r, hC r⟩⟩

theorem Network.finite_slopes_flux_of_tolerance {d : ℕ} {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I] [Nonempty I]
    (N : Network d E) (r : I → State d) (ε : State d → ℝ)
    (hε : N.IsSlopeTolerance ε) (hnonzero : ∀ i, ∃ e, N.projection (r i) e ≠ 0)
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ i : I, ∀ p : State d, (∀ j, |p j - r i j| ≤ ε (r i)) →
        ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
          0 < dot (r i) (N.rhs k (exponentialPoint h p)) := by
  classical
  choose H B hH hC using fun i => (hε (r i)).2 (hnonzero i)
  let Q : Set (State d × State d) :=
    {q | ∃ i : I, q.1 = r i ∧ ∀ j, |q.2 j - r i j| ≤ ε (r i)}
  have hcover : ∀ q ∈ Q, ∃ i, Nonempty (N.DirectionalCertificate q.1 q.2 (H i) (B i)) := by
    rintro q ⟨i, hi, hp⟩
    exact ⟨i, hi.symm ▸ hC i q.2 hp⟩
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ :=
    finite_directional_cover_eventual_flux N Q H B hH hℓ hu hcover
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall i p hp k hk
  exact hflux h hh hsmall (r i, p) ⟨i, rfl, hp⟩ k hk

/-- Conserved labels need no flux certificate. All nonconserved active labels,
including ties, share the threshold after the family has been fixed. -/
theorem Network.uniform_active_flux_of_sequentialActivityBound {d m : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (A : ScaledAffineFamily d m)
    (K : Set (State d)) (hK : IsCompact K) (ε : State d → ℝ)
    (hε : N.IsSlopeTolerance ε)
    (hseq : A.HasSequentialActivityBound K (fun i => ε (A.slope i)))
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ p ∈ K, ∀ i : Fin m,
        (A.atScale h).Active i (exponentialPoint h p) →
        (∃ e, N.projection (A.slope i) e ≠ 0) →
        ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
          0 < dot (A.slope i) (N.rhs k (exponentialPoint h p)) := by
  classical
  let I := {i : Fin m // ∃ e, N.projection (A.slope i) e ≠ 0}
  by_cases hI : Nonempty I
  · let : Nonempty I := hI
    obtain ⟨h₁, hh₁, hh₁1, hclose⟩ :=
      A.uniformActivityBound_of_sequential K hK (fun i => ε (A.slope i)) hseq
    obtain ⟨h₂, hh₂, _, hflux⟩ := N.finite_slopes_flux_of_tolerance
      (fun i : I => A.slope i.val) ε hε (fun i => i.property) hℓ hu
    refine ⟨min h₁ h₂, lt_min hh₁ hh₂, (min_le_left _ _).trans hh₁1, ?_⟩
    intro h hh hsmall p hp i hi hnonzero k hk
    apply hflux h hh (hsmall.trans_le (min_le_right _ _)) ⟨i, hnonzero⟩ p
      (A.norm_close_coordinate
        (hclose h hh (hsmall.trans_le (min_le_left _ _)) p hp i hi)) k hk
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    intro h hh hsmall p hp i hi hnonzero
    exact (hI ⟨⟨i, hnonzero⟩⟩).elim

/-- The class representative need not lie in the plateau: a single feasible
point of the original class carrier rules out conserved exterior branches. -/
theorem active_direction_has_nonzero_projection_of_carrier_nonempty
    {d m : ℕ} {E : Type*} (N : Network d E) (A : AffineFamily d m)
    {c x : State d} {M : ℝ} {i : Fin m}
    (hx : x ∈ N.positiveClass c) (hi : A.Active i x) (hout : x ∉ A.plateau M)
    (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty) :
    ∃ e, N.projection (A.slope i) e ≠ 0 := by
  by_contra h
  have hzero : ∀ e, N.projection (A.slope i) e = 0 := by
    simpa only [not_exists, not_not] using h
  obtain ⟨y, hy, hyC⟩ := hne
  have hxq := dot_eq_of_zero_projections N (A.slope i) hx.2 hzero
  have hyq := dot_eq_of_zero_projections N (A.slope i) hyC hzero
  have hlt := A.active_value_lt_of_notin_plateau hi hout
  have hge := hy i
  simp only [AffineFamily.value] at hlt hge
  rw [hxq] at hlt
  rw [hyq] at hge
  linarith

/-- Outside a nonempty original plateau carrier in a stoichiometric class,
conservation rules out every zero-projection active label automatically. -/
theorem Network.uniform_exterior_active_flux_of_sequentialActivityBound
    {d m : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (N : Network d E) (A : ScaledAffineFamily d m)
    (K : Set (State d)) (hK : IsCompact K) (ε : State d → ℝ)
    (hε : N.IsSlopeTolerance ε)
    (hseq : A.HasSequentialActivityBound K (fun i => ε (A.slope i)))
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ p ∈ K, ∀ c : State d, ∀ M : ℝ,
        exponentialPoint h p ∈ N.positiveClass c →
        exponentialPoint h p ∉ (A.atScale h).plateau M →
        ((A.atScale h).plateau M ∩ N.stoichiometricClass c).Nonempty →
        ∀ i : Fin m, (A.atScale h).Active i (exponentialPoint h p) →
          ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
            0 < dot (A.slope i) (N.rhs k (exponentialPoint h p)) := by
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ :=
    N.uniform_active_flux_of_sequentialActivityBound A K hK ε hε hseq hℓ hu
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall p hp c M hx hout hne i hi k hk
  exact hflux h hh hsmall p hp i hi
    (active_direction_has_nonzero_projection_of_carrier_nonempty N (A.atScale h)
      hx hi hout hne) k hk

/-- A checked conditional reduction from the precise affine research target to
uniform all-active inward flux on an exponent cube. The affine target remains
an explicit hypothesis, and compact class carriers/absorption are not derived. -/
theorem Network.uniform_active_flux_of_affineApproximation {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (hA : FiniteAffineApproximationStatement) (hd : 0 < d) {a b ℓ u : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily d m,
      (∀ i, A.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) ∧
      (∀ i, Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ p ∈ Set.Icc (fun _ => a) (fun _ => b), ∀ i : Fin m,
          (A.atScale h).Active i (exponentialPoint h p) →
          (∃ e, N.projection (A.slope i) e ≠ 0) →
          ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
            0 < dot (A.slope i) (N.rhs k (exponentialPoint h p)) := by
  obtain ⟨ε, hε⟩ := N.exists_slopeTolerance hN
  obtain ⟨m, hm, A, hslope, hoffset, hseq⟩ := hA d hd a b hab ε
    (fun p _ => (hε p).1)
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ :=
    N.uniform_active_flux_of_sequentialActivityBound A _ isCompact_Icc ε hε hseq hℓ hu
  exact ⟨m, hm, A, hslope, hoffset, h₀, hh₀, hh₀1, hflux⟩

end Endotactic
