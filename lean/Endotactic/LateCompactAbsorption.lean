import Endotactic.CompactAbsorption

/-!
# Absorption after an arbitrary entry time

The original integral solution is retained. An arbitrary starting time in the
AC cap barrier avoids translating the rates or the integral equation.
-/

namespace Endotactic

open Set MeasureTheory

variable {d m : ℕ} [Nonempty (Fin m)] {E : Type*} [Fintype E]

theorem AffineFamily.minimum_ae_deriv_lower_bound_below_after
    (A : AffineFamily d m) {N : Network d E} {k : E → ℝ → ℝ}
    {z : State d} {x : ℝ → State d} (hx : N.IsIntegralSolution k z x)
    {s T M δ : ℝ} (hs : 0 ≤ s) (hT : s ≤ T)
    (hbound : ∀ t ∈ Icc s T, A.minimum (x t) < M → ∀ i,
      A.Active i (x t) → δ ≤ dot (A.slope i) (N.rhs (fun e => k e t) (x t))) :
    ∀ᵐ t ∂volume, t ∈ Icc s T → A.minimum (x t) < M →
      δ ≤ deriv (fun r => A.minimum (x r)) t := by
  have hT0 := hs.trans hT
  have hsub : uIcc s T ⊆ uIcc 0 T := by
    simp only [uIcc_of_le hT, uIcc_of_le hT0]
    exact fun _ ht => ⟨hs.trans ht.1, ht.2⟩
  have hderivs : ∀ᵐ t ∂volume, ∀ i, t ∈ Icc 0 T →
      HasDerivAt (fun r => A.value i (x r))
        (dot (A.slope i) (N.rhs (fun e => k e t) (x t))) t :=
    ae_all_iff.mpr fun i => A.branch_ae_hasDerivAt hx i hT0
  have hb : ∀ᵐ t ∂volume, t ∈ uIcc s T → A.minimum (x t) < M → ∀ i,
      finiteMinimum (fun j => A.value j (x t)) = A.value i (x t) →
        δ ≤ deriv (fun r => A.value i (x r)) t := by
    filter_upwards [hderivs] with t ht hmem hlt i hi
    have hmem' : t ∈ Icc s T := by simpa only [uIcc_of_le hT] using hmem
    rw [(ht i ⟨hs.trans hmem'.1, hmem'.2⟩).deriv]
    exact hbound t hmem' hlt i ((A.active_iff_minimum_eq i (x t)).mpr hi)
  simpa only [AffineFamily.minimum, uIcc_of_le hT] using
    finiteMinimum_ae_deriv_lower_bound_on (fun i t => A.value i (x t))
      (fun t => A.minimum (x t) < M)
      (fun i => (A.branch_ac hx i hT0).mono hsub) hb

theorem AffineFamily.eventuallyIn_plateau_after
    (A : AffineFamily d m) {N : Network d E} {k : E → ℝ → ℝ}
    {z : State d} {x : ℝ → State d} (hx : N.IsIntegralSolution k z x)
    {s M δ : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ)
    (hcap : ∀ t, s ≤ t → A.minimum (x t) ≤ M)
    (hbound : ∀ t, s ≤ t → A.minimum (x t) < M → ∀ i,
      A.Active i (x t) → δ ≤ dot (A.slope i) (N.rhs (fun e => k e t) (x t))) :
    EventuallyIn x (A.plateau M) := by
  obtain ⟨T, hT, hstay⟩ := eventual_plateau_of_ac (fun t => A.minimum (x t)) hs hδ
    (fun T hT => (A.minimum_ac hx (hs.trans hT)).mono (by
      simp only [uIcc_of_le hT, uIcc_of_le (hs.trans hT)]
      exact fun _ ht => ⟨hs.trans ht.1, ht.2⟩)) hcap
    (fun T hT => A.minimum_ae_deriv_lower_bound_below_after hx hs hT
      (fun t ht => hbound t ht.1))
  exact ⟨T, hT, fun t ht => (A.mem_plateau_iff_minimum_ge (x t) M).mpr (hstay t ht).ge⟩

theorem AffineFamily.eventuallyIn_plateau_of_eventual_compact_strict_exterior
    (A : AffineFamily d m) {N : Network d E} {k : E → ℝ → ℝ} {ℓ u M Q : ℝ}
    (hk : AdmissibleRates k ℓ u) {z : State d} {x : ℝ → State d}
    (hx : N.IsIntegralSolution k z x) {B : Set (State d)} (hB : IsCompact B)
    (hstay : EventuallyIn x B) (hQ : Q < M)
    (hstrict : ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ B, A.minimum y < M → ∀ i, A.Active i y →
        0 < dot (A.slope i) (N.rhs a y)) : EventuallyIn x (A.plateau Q) := by
  obtain ⟨s, hs, hstay⟩ := hstay
  obtain ⟨δ, hδ, hb⟩ := N.exists_affine_active_margin_on_compact_sublevel A hB hQ hstrict
  have hbound : ∀ t, s ≤ t → (A.withCap Q).minimum (x t) < Q → ∀ i,
      (A.withCap Q).Active i (x t) →
        δ ≤ dot ((A.withCap Q).slope i) (N.rhs (fun e => k e t) (x t)) := by
    intro t ht hmin i hi
    have hvalue : (A.withCap Q).value i (x t) < Q :=
      ((A.withCap Q).active_iff_minimum_eq i (x t)).mp hi ▸ hmin
    revert hi hvalue
    refine Fin.cases ?_ (fun j => ?_) i
    · intro _ hv
      rw [A.withCap_value_zero] at hv
      exact False.elim (lt_irrefl Q hv)
    · intro hj _
      have hactive := A.active_of_withCap_active Q hj
      have hsub := (A.minimum_lt_of_withCap_active Q hj hmin).le
      simpa only [AffineFamily.withCap, Fin.cons_succ] using
        hb _ ⟨fun e => (hk.2 e t (hs.trans ht)).1, fun e => (hk.2 e t (hs.trans ht)).2⟩
          (x t) (hstay t ht) hsub j hactive
  have hh := (A.withCap Q).eventuallyIn_plateau_after hx hs hδ
    (fun t _ => A.withCap_minimum_le Q (x t)) hbound
  rwa [A.withCap_plateau] at hh

end Endotactic
