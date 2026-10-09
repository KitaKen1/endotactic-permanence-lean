import Endotactic.Permanence
import Endotactic.LinearGeometry
import Endotactic.FiniteMinimum
import Endotactic.AbsoluteBarrier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Affine observables and finite minima of integral trajectories

No differentiability of the rate path is assumed. Interval integrability in the
solution predicate suffices to obtain scalar absolute continuity and the ODE
for each affine observable almost everywhere.
-/

namespace Endotactic

open MeasureTheory Set Filter
open scoped Topology

noncomputable def dotCLM {d : ℕ} (r : State d) : State d →L[ℝ] ℝ :=
  (dotLinear r).toContinuousLinearMap

theorem clm_intervalIntegrable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W)
    {f : ℝ → V} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => L (f t)) volume a b :=
  ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩

variable {d : ℕ} {E : Type*} [Fintype E]
variable {N : Network d E} {k : E → ℝ → ℝ} {x₀ : State d} {x : ℝ → State d}

theorem Network.IsIntegralSolution.dot_integral_eq
    (hx : N.IsIntegralSolution k x₀ x) (r : State d) {t : ℝ} (ht : 0 ≤ t) :
    dot r (x t) = dot r x₀ +
      ∫ s in (0 : ℝ)..t, dot r (N.rhs (fun e => k e s) (x s)) := by
  have h := congrArg (dotCLM r) (hx.2.2.2 t ht)
  rw [map_add, ← (dotCLM r).intervalIntegral_comp_comm (hx.2.2.1 t ht)] at h
  exact h

theorem Network.IsIntegralSolution.dot_intervalIntegrable
    (hx : N.IsIntegralSolution k x₀ x) (r : State d) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun s => dot r (N.rhs (fun e => k e s) (x s))) volume 0 T :=
  clm_intervalIntegrable (dotCLM r) (hx.2.2.1 T hT)

theorem Network.IsIntegralSolution.dot_ac
    (hx : N.IsIntegralSolution k x₀ x) (r : State d) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => dot r (x t)) 0 T := by
  have hp := (hx.dot_intervalIntegrable r hT).absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) (by simp)
  apply ac_congrOn ((ac_const (dot r x₀) 0 T).add hp)
  intro t ht
  have ht' : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
  exact (hx.dot_integral_eq r ht'.1).symm

theorem Network.IsIntegralSolution.dot_ae_hasDerivAt
    (hx : N.IsIntegralSolution k x₀ x) (r : State d) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt (fun s => dot r (x s)) (dot r (N.rhs (fun e => k e t) (x t))) t := by
  have hzero : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have htop : ∀ᵐ t : ℝ ∂volume, t ≠ T := by simp [ae_iff, measure_singleton]
  filter_upwards [(hx.dot_intervalIntegrable r hT).ae_hasDerivAt_integral, hzero, htop]
    with t hp hz ht hmem
  have hlt0 : 0 < t := lt_of_le_of_ne hmem.1 hz.symm
  have hltT : t < T := lt_of_le_of_ne hmem.2 ht
  have hp' := (hp (by simpa only [uIcc_of_le hT] using hmem) 0 (by simp)).const_add (dot r x₀)
  apply hp'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hlt0 hltT] with s hs
  exact hx.dot_integral_eq r hs.1.le

theorem AffineFamily.branch_ac {m : ℕ} (A : AffineFamily d m)
    (hx : N.IsIntegralSolution k x₀ x) (i : Fin m) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => A.value i (x t)) 0 T := by
  exact (hx.dot_ac (A.slope i) hT).add (ac_const (A.offset i) 0 T)

theorem AffineFamily.branch_ae_hasDerivAt {m : ℕ} (A : AffineFamily d m)
    (hx : N.IsIntegralSolution k x₀ x) (i : Fin m) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt (fun s => A.value i (x s))
      (dot (A.slope i) (N.rhs (fun e => k e t) (x t))) t := by
  filter_upwards [hx.dot_ae_hasDerivAt (A.slope i) hT] with t ht hmem
  exact (ht hmem).add_const (A.offset i)

noncomputable def AffineFamily.minimum {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (z : State d) : ℝ := finiteMinimum (fun i => A.value i z)

theorem AffineFamily.active_iff_minimum_eq {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (i : Fin m) (z : State d) :
    A.Active i z ↔ A.minimum z = A.value i z := by
  constructor
  · intro hi
    apply le_antisymm (finiteMinimum_le _ i)
    exact Finset.le_inf' Finset.univ_nonempty _ (fun j _ => hi j)
  · intro hi j
    rw [← hi]
    exact finiteMinimum_le _ j

theorem AffineFamily.minimum_ac {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (hx : N.IsIntegralSolution k x₀ x)
    {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => A.minimum (x t)) 0 T :=
  finiteMinimum_ac (fun i t => A.value i (x t)) (fun i => A.branch_ac hx i hT)

theorem AffineFamily.minimum_growth {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (hx : N.IsIntegralSolution k x₀ x) {a b δ : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hbound : ∀ t ∈ Icc a b, ∀ i, A.Active i (x t) →
      δ ≤ dot (A.slope i) (N.rhs (fun e => k e t) (x t))) :
    δ * (b - a) ≤ A.minimum (x b) - A.minimum (x a) := by
  have hb : 0 ≤ b := ha.trans hab
  apply finiteMinimum_growth (fun i t => A.value i (x t)) hab
  · intro i
    apply (A.branch_ac hx i hb).mono
    simpa only [uIcc_of_le hab, uIcc_of_le hb] using
      (show Icc a b ⊆ Icc 0 b from fun _ ht => ⟨ha.trans ht.1, ht.2⟩)
  · have hderivs : ∀ᵐ t ∂volume, ∀ i, t ∈ Icc 0 b →
        HasDerivAt (fun s => A.value i (x s))
          (dot (A.slope i) (N.rhs (fun e => k e t) (x t))) t :=
      ae_all_iff.mpr fun i => A.branch_ae_hasDerivAt hx i hb
    filter_upwards [hderivs] with t ht hmem i hactive
    rw [(ht i ⟨ha.trans hmem.1, hmem.2⟩).deriv]
    exact hbound t hmem i ((A.active_iff_minimum_eq i (x t)).mpr hactive)

theorem AffineFamily.mem_plateau_iff_minimum_ge {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (z : State d) (M : ℝ) :
    z ∈ A.plateau M ↔ M ≤ A.minimum z := by
  constructor
  · intro hz
    exact Finset.le_inf' Finset.univ_nonempty _ (fun i _ => hz i)
  · intro hz i
    exact hz.trans (finiteMinimum_le _ i)

theorem AffineFamily.minimum_le_constant_branch {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (i : Fin m) (hslope : ∀ j, A.slope i j = 0)
    (z : State d) : A.minimum z ≤ A.offset i := by
  simpa only [AffineFamily.minimum, A.constant_value i hslope z] using
    (finiteMinimum_le (fun j => A.value j z) i)

theorem AffineFamily.minimum_ae_deriv_lower_bound_below {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (hx : N.IsIntegralSolution k x₀ x) {T M δ : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ t ∈ Icc 0 T, A.minimum (x t) < M → ∀ i,
      A.Active i (x t) → δ ≤ dot (A.slope i) (N.rhs (fun e => k e t) (x t))) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T → A.minimum (x t) < M →
      δ ≤ deriv (fun s => A.minimum (x s)) t := by
  have hderivs : ∀ᵐ t ∂volume, ∀ i, t ∈ Icc 0 T →
      HasDerivAt (fun s => A.value i (x s))
        (dot (A.slope i) (N.rhs (fun e => k e t) (x t))) t :=
    ae_all_iff.mpr fun i => A.branch_ae_hasDerivAt hx i hT
  have hb : ∀ᵐ t ∂volume, t ∈ uIcc 0 T → A.minimum (x t) < M → ∀ i,
      finiteMinimum (fun j => A.value j (x t)) = A.value i (x t) →
        δ ≤ deriv (fun s => A.value i (x s)) t := by
    filter_upwards [hderivs] with t ht hmem hlt i hactive
    have hmem' : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using hmem
    rw [(ht i hmem').deriv]
    exact hbound t hmem' hlt i ((A.active_iff_minimum_eq i (x t)).mpr hactive)
  simpa only [AffineFamily.minimum, uIcc_of_le hT] using finiteMinimum_ae_deriv_lower_bound_on
    (fun i t => A.value i (x t)) (fun t => A.minimum (x t) < M)
    (fun i => A.branch_ac hx i hT) hb

/-- The analytic absorption step, conditional on the uniform geometric flux bound.
This neither constructs the family nor establishes existence of the trajectory. -/
theorem AffineFamily.eventuallyIn_plateau {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (hx : N.IsIntegralSolution k x₀ x) {M δ : ℝ} (hδ : 0 < δ)
    (hcap : ∀ t, 0 ≤ t → A.minimum (x t) ≤ M)
    (hbound : ∀ t, 0 ≤ t → A.minimum (x t) < M → ∀ i,
      A.Active i (x t) → δ ≤ dot (A.slope i) (N.rhs (fun e => k e t) (x t))) :
    EventuallyIn x (A.plateau M) := by
  obtain ⟨T, hT, hstay⟩ := eventual_plateau_of_ac (fun t => A.minimum (x t))
    (s := 0) le_rfl hδ (fun T hT => A.minimum_ac hx hT) hcap (by
      intro T hT
      exact A.minimum_ae_deriv_lower_bound_below hx hT
        (fun t ht => hbound t ht.1))
  refine ⟨T, hT, fun t ht => (A.mem_plateau_iff_minimum_ge (x t) M).mpr ?_⟩
  exact (hstay t ht).ge

end Endotactic
