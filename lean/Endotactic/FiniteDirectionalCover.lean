import Endotactic.UniformDirectionalCertificate
import Endotactic.GeometryMargins

/-!
# A finite certificate cover, rather than finite sampling

The cover hypothesis quantifies over every pair of directions and exponent
points in the region. Its existence is not inferred from pointwise dominance or
compactness alone. Positive scaling of directions does not change its bounds.
-/

namespace Endotactic

def Network.DirectionalCertificate.transfer_exponent {d : ℕ} {E : Type*}
    [Fintype E] {N : Network d E} {r p : State d} {H B ε : ℝ}
    (C : N.DirectionalCertificate r r H B)
    (hclose : ∀ i, |p i - r i| ≤ ε)
    (herror : ∀ e, N.projection r e < 0 →
      ε * l1 (realComplex (N.source e) - realComplex (N.source C.pivot)) ≤ H / 2) :
    N.DirectionalCertificate r p (H / 2) B where
  pivot := C.pivot
  positive := C.positive
  relative_mass := C.relative_mass
  gap e he := source_gap_transfer N p r C.pivot e hclose
    ((herror e he).trans (by linarith only [C.gap e he]))
    (by linarith only [C.gap e he])

/-- Arbitrarily many direction/exponent pairs are covered by finitely many
verified parameter bounds. Every pair must have a certificate in some chart. -/
theorem finite_directional_cover_eventual_flux {d : ℕ} {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I] [Nonempty I]
    (N : Network d E) (Q : Set (State d × State d)) (H B : I → ℝ)
    (hH : ∀ i, 0 < H i) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    (hcover : ∀ q ∈ Q, ∃ i, Nonempty (N.DirectionalCertificate q.1 q.2 (H i) (B i))) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ q ∈ Q, ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
        0 < dot q.1 (N.rhs k (exponentialPoint h q.2)) := by
  classical
  let hs := Finset.univ.image H
  let bs := Finset.univ.image B
  have hhs : hs.Nonempty := Finset.univ_nonempty.image H
  have hbs : bs.Nonempty := Finset.univ_nonempty.image B
  let H₀ := hs.min' hhs
  let B₀ := bs.max' hbs
  have hH₀ : 0 < H₀ := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hs.min'_mem hhs)
    change 0 < hs.min' hhs
    rw [← hi]
    exact hH i
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ :=
    exists_uniform_directional_flux_threshold N (B := B₀) hℓ hu hH₀
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall q hq k hk
  obtain ⟨i, ⟨C⟩⟩ := hcover q hq
  apply hflux h hh hsmall q.1 q.2
    (C.weaken (hs.min'_le _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      (bs.le_max' _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))) k hk

/-- Certificates may cover rays of arbitrary positive magnitude without a new
threshold or a positive lower bound on the norm of each direction. -/
theorem finite_directional_cover_scaled_eventual_flux {d : ℕ} {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I] [Nonempty I]
    (N : Network d E) (Q : Set (State d × State d)) (H B : I → ℝ)
    (hH : ∀ i, 0 < H i) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    (hcover : ∀ q ∈ Q, ∃ i, Nonempty (N.DirectionalCertificate q.1 q.2 (H i) (B i))) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ q ∈ Q, ∀ s : ℝ, 0 < s →
        ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
          0 < dot (s • q.1) (N.rhs k (exponentialPoint h q.2)) := by
  let R : Set (State d × State d) :=
    {v | ∃ q ∈ Q, ∃ s : ℝ, 0 < s ∧ v = (s • q.1, q.2)}
  have hR : ∀ v ∈ R, ∃ i, Nonempty (N.DirectionalCertificate v.1 v.2 (H i) (B i)) := by
    rintro v ⟨q, hq, s, hs, rfl⟩
    obtain ⟨i, ⟨C⟩⟩ := hcover q hq
    exact ⟨i, ⟨C.smul_direction hs⟩⟩
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ :=
    finite_directional_cover_eventual_flux N R H B hH hℓ hu hR
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall q hq s hs k hk
  exact hflux h hh hsmall (s • q.1, q.2) ⟨q, hq, s, hs, rfl⟩ k hk

end Endotactic
