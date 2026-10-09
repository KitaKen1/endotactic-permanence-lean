import Endotactic.DirectionalDominance

/-!
# Uniform flux from moving-direction certificates

A certificate records the gap in exponent space and bounds negative projected
mass relative to one positive pivot. No lower bound on the magnitude of the
direction is needed. The existence of uniformly bounded certificates over all
active directions is a separate geometric obligation.
-/

namespace Endotactic

open Filter Topology

theorem negativeMass_nonneg {E : Type*} [Fintype E] (p : E → ℝ) :
    0 ≤ negativeMass p :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem projection_smul_direction {d : ℕ} {E : Type*} (N : Network d E)
    (s : ℝ) (r : State d) (e : E) :
    N.projection (s • r) e = s * N.projection r e := by
  simp only [Network.projection, dot, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [Finset.mul_sum]

theorem negativeMass_smul {E : Type*} [Fintype E] (p : E → ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    negativeMass (fun e => s * p e) = s * negativeMass p := by
  unfold negativeMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hp : 0 ≤ p e
  · simp [max_eq_right (neg_nonpos.mpr hp),
      max_eq_right (neg_nonpos.mpr (mul_nonneg hs hp))]
  · have hp' : p e ≤ 0 := (lt_of_not_ge hp).le
    rw [max_eq_left (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hs hp')),
      max_eq_left (neg_nonneg.mpr hp')]
    ring

/-- Finite data sufficient for an inward flux; it need not certify an essential
minimum, nor assume endotacticity when the data have already been verified. -/
structure Network.DirectionalCertificate {d : ℕ} {E : Type*} [Fintype E]
    (N : Network d E) (r p : State d) (H B : ℝ) where
  pivot : E
  positive : 0 < N.projection r pivot
  relative_mass : negativeMass (N.projection r) ≤ B * N.projection r pivot
  gap : ∀ e, N.projection r e < 0 →
    H ≤ N.sourceLevel p e - N.sourceLevel p pivot

def Network.DirectionalCertificate.weaken {d : ℕ} {E : Type*} [Fintype E]
    {N : Network d E} {r p : State d} {H B H' B' : ℝ}
    (C : N.DirectionalCertificate r p H B) (hH : H' ≤ H) (hB : B ≤ B') :
    N.DirectionalCertificate r p H' B' where
  pivot := C.pivot
  positive := C.positive
  relative_mass := C.relative_mass.trans
    (mul_le_mul_of_nonneg_right hB C.positive.le)
  gap e he := hH.trans (C.gap e he)

def Network.DirectionalCertificate.smul_direction {d : ℕ} {E : Type*}
    [Fintype E] {N : Network d E} {r p : State d} {H B s : ℝ}
    (C : N.DirectionalCertificate r p H B) (hs : 0 < s) :
    N.DirectionalCertificate (s • r) p H B := by
  refine ⟨C.pivot, ?_, ?_, ?_⟩
  · rw [projection_smul_direction]
    exact mul_pos hs C.positive
  · have heq : N.projection (s • r) = fun e => s * N.projection r e :=
      funext (projection_smul_direction N s r)
    rw [heq, negativeMass_smul _ hs.le]
    have h := mul_le_mul_of_nonneg_left C.relative_mass hs.le
    nlinarith only [h]
  · intro e he
    rw [projection_smul_direction] at he
    exact C.gap e (by nlinarith only [he, hs])

theorem exponentialPoint_flux_pos_of_directionalCertificate {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (r p : State d)
    (k : E → ℝ) {ℓ u h H B : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    (hh : 0 < h) (hh1 : h ≤ 1) (hk : ∀ e, ℓ ≤ k e ∧ k e ≤ u)
    (C : N.DirectionalCertificate r p H B) (hsmall : u * h ^ H * B < ℓ) :
    0 < dot r (N.rhs k (exponentialPoint h p)) := by
  rw [dot_rhs]
  apply weighted_sum_pos (N.projection r)
    (fun e => monomial (exponentialPoint h p) (N.source e)) k C.pivot ℓ u (h ^ H)
    hu (fun e => (monomial_pos (exponentialPoint_positive hh p) _).le) hk
    (fun e => hℓ.le.trans (hk e).1) C.positive.le
    (monomial_pos (exponentialPoint_positive hh p) _)
  · intro e he
    exact monomial_domination_of_exponent_gap hh hh1 p _ _ (C.gap e he)
  · calc
      u * h ^ H * negativeMass (N.projection r) ≤
          u * h ^ H * (B * N.projection r C.pivot) :=
        mul_le_mul_of_nonneg_left C.relative_mass
          (mul_nonneg hu (Real.rpow_nonneg hh.le _))
      _ = (u * h ^ H * B) * N.projection r C.pivot := by ring
      _ < ℓ * N.projection r C.pivot :=
        mul_lt_mul_of_pos_right hsmall C.positive

/-- One threshold for every direction, exponent point, and coefficient vector
with the specified common geometric bounds. -/
theorem exists_uniform_directional_flux_threshold {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) {ℓ u H B : ℝ}
    (hℓ : 0 < ℓ) (hu : 0 ≤ u) (hH : 0 < H) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ r p : State d, N.DirectionalCertificate r p H B →
        ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
          0 < dot r (N.rhs k (exponentialPoint h p)) := by
  have hlimit : Tendsto (fun h : ℝ => u * h ^ H * B) (𝓝 0) (𝓝 0) := by
    have hr : Tendsto (fun h : ℝ => h ^ H) (𝓝 0) (𝓝 0) := by
      simpa only [Real.zero_rpow hH.ne'] using
        (Real.continuousAt_rpow_const 0 H (.inr hH.le)).tendsto
    simpa only [mul_zero, zero_mul] using (hr.const_mul u).mul_const B
  obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp
    (hlimit.eventually (eventually_lt_nhds hℓ))
  refine ⟨min ε 1, lt_min hε (by norm_num), min_le_right _ _, ?_⟩
  intro h hh hh₀ r p C k hk
  have hhε : h < ε := hh₀.trans_le (min_le_left _ _)
  exact exponentialPoint_flux_pos_of_directionalCertificate N r p k hℓ hu hh
    (hh₀.le.trans (min_le_right _ _)) hk C
    (hsmall (by simpa [Real.dist_eq, abs_of_pos hh] using hhε))

/-- Endotacticity supplies a certificate in each fixed direction, but its
parameters are not asserted to be uniform as the direction changes. -/
theorem exists_fixed_directionalCertificate {d : ℕ} {E : Type*}
    [Fintype E] (N : Network d E) (hN : N.IsEndotactic) (r : State d)
    (hnonzero : ∃ e : E, N.projection r e ≠ 0) :
    ∃ H B : ℝ, 0 < H ∧ 0 ≤ B ∧ Nonempty (N.DirectionalCertificate r r H B) := by
  obtain ⟨a, ha⟩ := exists_essentialMinimum N hnonzero
  obtain ⟨H, hH, hgap⟩ := exists_positive_negative_source_gap N hN ha
  have hpos := essentialMinimum_projection_pos N hN ha
  refine ⟨H, negativeMass (N.projection r) / N.projection r a, hH,
    div_nonneg (negativeMass_nonneg _) hpos.le, ⟨⟨a, hpos, ?_, hgap⟩⟩⟩
  rw [div_mul_cancel₀ _ hpos.ne']

end Endotactic
