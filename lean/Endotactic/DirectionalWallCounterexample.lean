import Endotactic.FiniteDirectionalCover
import Endotactic.FiniteSlopeDominance
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compact nonconserved directions need not have a common ray threshold

The reversible network `A ⇄ 2A, 0 ⇄ B` has positive flux eventually on every
fixed nonconserved exponent ray. Nevertheless, for coefficients `(1,1,1,3)`,
directions `(1,1/n)` and scales `h=2^(-n)` have negative flux for every `n ≥ 3`.
All these directions lie in the compact segment `(1,t), 0 ≤ t ≤ 1`.
This refutes automatic uniformization of the fixed-direction lemma, not
permanence, nor the candidate affine approximation argument.
-/

namespace Endotactic.DirectionalWall

open Filter Topology

def network : Network 2 (Fin 4) where
  source := ![![1, 0], ![2, 0], ![0, 0], ![0, 1]]
  target := ![![2, 0], ![1, 0], ![0, 1], ![0, 0]]

theorem network_endotactic : network.IsEndotactic := by
  intro r e he
  fin_cases e
  · refine ⟨1, ?_, ?_⟩ <;>
      simp [network, Network.projection, Network.vector, Network.sourceLevel,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith
  · refine ⟨0, ?_, ?_⟩ <;>
      simp [network, Network.projection, Network.vector, Network.sourceLevel,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith
  · refine ⟨3, ?_, ?_⟩ <;>
      simp [network, Network.projection, Network.vector, Network.sourceLevel,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith
  · refine ⟨2, ?_, ?_⟩ <;>
      simp [network, Network.projection, Network.vector, Network.sourceLevel,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith

def directions : Set (State 2) :=
  (fun t : ℝ => ![1, t]) '' Set.Icc 0 1

theorem directions_compact : IsCompact directions := by
  apply isCompact_Icc.image
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun _ : ℝ => (1 : ℝ))
    exact continuous_const
  · change Continuous (fun t : ℝ => t)
    exact continuous_id

theorem directions_nonconserved (r : State 2) (hr : r ∈ directions) :
    ∃ e : Fin 4, network.projection r e ≠ 0 := by
  obtain ⟨t, _, rfl⟩ := hr
  refine ⟨0, ?_⟩
  norm_num [network, Network.projection, Network.vector, realComplex, dot,
    Fin.sum_univ_succ]

noncomputable def direction (n : ℕ) : State 2 := ![1, (n : ℝ)⁻¹]

theorem direction_mem {n : ℕ} (hn : 1 ≤ n) : direction n ∈ directions := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨(n : ℝ)⁻¹, ⟨inv_nonneg.mpr (by positivity), ?_⟩, rfl⟩
  exact inv_le_one_of_one_le₀ hnR

def rates : Fin 4 → ℝ := ![1, 1, 1, 3]

theorem rates_mem_box : ∀ e : Fin 4, 1 ≤ rates e ∧ rates e ≤ 3 := by
  intro e
  fin_cases e <;> norm_num [rates]

theorem rhs_formula (x : State 2) :
    network.rhs rates x = ![x 0 - (x 0) ^ 2, 1 - 3 * x 1] := by
  ext i
  fin_cases i <;>
    simp [network, Network.rhs, Network.vector, realComplex, monomial, rates,
      Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring

theorem exponentialPoint_at_direction {n : ℕ} (hn : 0 < n) :
    exponentialPoint ((1 / 2 : ℝ) ^ n) (direction n) =
      ![(1 / 2 : ℝ) ^ n, 1 / 2] := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  ext i
  fin_cases i
  · simp [exponentialPoint, direction]
  · change (((1 / 2 : ℝ) ^ n) ^ (n : ℝ)⁻¹) = 1 / 2
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      mul_inv_cancel₀ hnR, Real.rpow_one]

theorem twice_nat_lt_two_pow {n : ℕ} (hn : 3 ≤ n) : 2 * n < 2 ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show 3 + (m + 1) = (3 + m) + 1 by omega, pow_succ]
    nlinarith only [ih]

theorem negative_flux_at_direction {n : ℕ} (hn : 3 ≤ n) :
    dot (direction n)
      (network.rhs rates (exponentialPoint ((1 / 2 : ℝ) ^ n) (direction n))) < 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (2 : ℝ) * n < 2 ^ n := by exact_mod_cast twice_nat_lt_two_pow hn
  have hh : (0 : ℝ) < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hh2 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hsmall : (1 / 2 : ℝ) ^ n < (n : ℝ)⁻¹ / 2 := by
    have hmul := mul_lt_mul_of_pos_left hp hh
    rw [hh2] at hmul
    have hinv : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnR.ne'
    nlinarith only [hmul, hinv, hnR]
  rw [exponentialPoint_at_direction (by omega)]
  rw [rhs_formula]
  norm_num [dot, direction, Fin.sum_univ_succ]
  nlinarith only [hsmall, sq_nonneg ((1 / 2 : ℝ) ^ n)]

theorem scale_tendsto_zero :
    Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Pointwise fixed-ray dominance cannot be compactified without additional
geometric control near projection-zero walls. -/
theorem no_uniform_ray_threshold :
    ¬ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ r ∈ directions, ∀ k : Fin 4 → ℝ,
        (∀ e, 1 ≤ k e ∧ k e ≤ 3) →
          0 < dot r (network.rhs k (exponentialPoint h r)) := by
  rintro ⟨h₀, hh₀, hflux⟩
  have hevent := scale_tendsto_zero.eventually (eventually_lt_nhds hh₀)
  obtain ⟨n, hn, hsmall⟩ := (hevent.and (eventually_ge_atTop 3)).exists
  have hpos := hflux ((1 / 2 : ℝ) ^ n) (pow_pos (by norm_num) _)
    hn (direction n) (direction_mem (by omega)) rates rates_mem_box
  exact (not_lt_of_ge (negative_flux_at_direction hsmall).le) hpos

theorem no_uniform_directional_certificates :
    ¬ ∃ H B : ℝ, 0 < H ∧ ∀ r ∈ directions,
      Nonempty (network.DirectionalCertificate r r H B) := by
  rintro ⟨H, B, hH, hC⟩
  obtain ⟨h₀, hh₀, _, hflux⟩ := exists_uniform_directional_flux_threshold
    network (ℓ := 1) (u := 3) (B := B) (by norm_num) (by norm_num) hH
  apply no_uniform_ray_threshold
  refine ⟨h₀, hh₀, ?_⟩
  intro h hh hsmall r hr k hk
  obtain ⟨C⟩ := hC r hr
  exact hflux h hh hsmall r r C k hk

/-- Every finite sample passes eventual positivity, even though the whole
compact direction segment has no uniform threshold. -/
theorem finite_samples_eventually_positive (s : Finset (State 2))
    (hs : ∀ r ∈ s, r ∈ directions) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ r ∈ s, ∀ k : Fin 4 → ℝ, (∀ e, 1 ≤ k e ∧ k e ≤ 3) →
        0 < dot r (network.rhs k (exponentialPoint h r)) := by
  classical
  by_cases hne : s.Nonempty
  · let : Nonempty s := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    obtain ⟨ε, hε, h₀, hh₀, hh₀1, hflux⟩ := finite_slopes_tolerant_eventual_flux
      network network_endotactic (fun i : s => (i : State 2))
      (fun i => directions_nonconserved i (hs i i.property))
      (ℓ := 1) (u := 3) (by norm_num) (by norm_num)
    refine ⟨h₀, hh₀, hh₀1, ?_⟩
    intro h hh hsmall r hr k hk
    exact hflux h hh hsmall ⟨r, hr⟩ r
      (fun _ => by simpa using (hε ⟨r, hr⟩).le) k hk
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    intro h hh hsmall r hr
    exact (hne ⟨r, hr⟩).elim

end Endotactic.DirectionalWall
