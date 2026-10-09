import Endotactic.DirectionalDominance

/-!
# Uniform inward signs for every nontrivial one-species endotactic network

The two exponent directions `+1` and `-1` cover respectively all sufficiently
small and all sufficiently large positive states. This avoids the unresolved
uniform-direction geometry in higher dimensions. Thresholds are uniform over
the entire coefficient box and may depend on the network and that box.
-/

namespace Endotactic

variable {E : Type*} [Fintype E]

/-- Strict inward signs on the whole positive exterior of one common interval. -/
structure Network.ScalarTrap (N : Network 1 E) (ℓ u : ℝ) where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_lt_upper : lower < upper
  lower_flux : ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
    ∀ x : State 1, 0 < x 0 → x 0 ≤ lower → 0 < N.rhs k x 0
  upper_flux : ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
    ∀ x : State 1, upper ≤ x 0 → N.rhs k x 0 < 0

omit [Fintype E] in
theorem Network.oneSpecies_stoichiometricSubspace_eq_top (N : Network 1 E)
    (hnonzero : ∃ e, N.vector e 0 ≠ 0) : N.stoichiometricSubspace = ⊤ := by
  obtain ⟨e, he⟩ := hnonzero
  apply top_unique
  intro x _
  have hv : N.vector e ∈ N.stoichiometricSubspace := Submodule.subset_span ⟨e, rfl⟩
  have heq : (x 0 / N.vector e 0) • N.vector e = x := by
    ext i
    fin_cases i
    simp [Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ he]
  rw [← heq]
  exact N.stoichiometricSubspace.smul_mem _ hv

omit [Fintype E] in
theorem Network.oneSpecies_positiveClass_of_nonzero (N : Network 1 E)
    (hnonzero : ∃ e, N.vector e 0 ≠ 0) (c : State 1) :
    N.positiveClass c = {x | 0 < x 0} := by
  ext x
  constructor
  · exact fun hx => hx.1 0
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i; fin_cases i; exact hx
    · rw [N.oneSpecies_stoichiometricSubspace_eq_top hnonzero]
      exact Submodule.mem_top

theorem Network.exists_scalarTrap_of_oneSpecies_endotactic (N : Network 1 E)
    (hN : N.IsEndotactic) (hnonzero : ∃ e, N.vector e 0 ≠ 0)
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hlu : ℓ ≤ u) : Nonempty (N.ScalarTrap ℓ u) := by
  classical
  have hplus : ∃ e, N.projection (fun _ => 1) e ≠ 0 := by
    simpa [Network.projection, dot] using hnonzero
  have hminus : ∃ e, N.projection (fun _ => -1) e ≠ 0 := by
    simpa [Network.projection, dot] using hnonzero
  obtain ⟨a₀, ha₀, hsmall⟩ := fixed_direction_eventual_positive_flux N hN
    (fun _ => 1) hplus hℓ hlu
  obtain ⟨b₀, hb₀, hlarge⟩ := fixed_direction_eventual_positive_flux N hN
    (fun _ => -1) hminus hℓ hlu
  let a : ℝ := min a₀ 1 / 2
  let b : ℝ := max (2 / b₀) 2
  have ha : 0 < a := div_pos (lt_min ha₀ zero_lt_one) (by norm_num)
  have haa : a < a₀ := by
    have hh := min_le_left a₀ 1
    dsimp [a]
    linarith
  have ha1 : a ≤ 1 / 2 := div_le_div_of_nonneg_right (min_le_right a₀ 1) (by norm_num)
  have hb2 : 2 ≤ b := le_max_right _ _
  refine ⟨⟨a, b, ha, by linarith, ?_, ?_⟩⟩
  · intro k hk x hx hxsmall
    have heq : exponentialPoint (x 0) (fun _ : Fin 1 => 1) = x := by
      ext i; fin_cases i
      simp [exponentialPoint]
    have hh := hsmall (x 0) hx (hxsmall.trans_lt haa) k hk
    rw [heq] at hh
    simpa [dot] using hh
  · intro k hk x hxlarge
    have hx0 : 0 < x 0 := lt_of_lt_of_le (by linarith : 0 < b) hxlarge
    have hinv : (x 0)⁻¹ < b₀ := by
      have h2 : 2 / b₀ ≤ x 0 := (le_max_left _ _).trans hxlarge
      have hmul : 2 ≤ x 0 * b₀ := (div_le_iff₀ hb₀).mp h2
      have h1 : 1 < b₀ * x 0 := by nlinarith
      have hh := (div_lt_iff₀ hx0).mpr h1
      simpa only [one_div] using hh
    have heq : exponentialPoint (x 0)⁻¹ (fun _ : Fin 1 => -1) = x := by
      ext i; fin_cases i
      simp [exponentialPoint, Real.rpow_neg_one]
    have hh := hlarge (x 0)⁻¹ (inv_pos.mpr hx0) hinv k hk
    rw [heq] at hh
    have hh' : 0 < -N.rhs k x 0 := by simpa [dot] using hh
    linarith

end Endotactic
