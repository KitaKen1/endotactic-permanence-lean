import Endotactic.UniformKinetics
import Endotactic.Permanence
import Endotactic.NonlinearVolterra

/-!
# Bounded mass-action fields by coordinate clamping

Clamping the state to a finite closed box preserves the field inside the box.
It makes polynomial mass action bounded and globally Lipschitz in state, with
one constant for all admissible rate vectors. Negative times use the rate at
zero, since admissibility only bounds nonnegative times.
-/

namespace Endotactic

open Set MeasureTheory
open scoped NNReal

variable {d : ℕ} {E : Type*} [Fintype E]

def boxClamp (lo hi : State d) (x : State d) : State d :=
  fun i => max (lo i) (min (hi i) (x i))

theorem boxClamp_mem (lo hi : State d) (hbox : lo ≤ hi) (x : State d) :
    boxClamp lo hi x ∈ Icc lo hi := by
  exact ⟨fun i => le_max_left _ _, fun i => max_le (hbox i) (min_le_left _ _)⟩

theorem boxClamp_eq_of_mem (lo hi : State d) {x : State d} (hx : x ∈ Icc lo hi) :
    boxClamp lo hi x = x := by
  funext i
  simp [boxClamp, max_eq_right (hx.1 i), min_eq_right (hx.2 i)]

theorem boxClamp_lipschitz (lo hi : State d) : LipschitzWith 1 (boxClamp lo hi) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  simpa only [boxClamp, NNReal.coe_one, one_mul] using
    (((LipschitzWith.eval i).const_min (hi i)).const_max (lo i)).dist_le_mul x y

def Network.cutoffRhs (N : Network d E) (k : E → ℝ → ℝ) (lo hi : State d)
    (t : ℝ) (x : State d) : State d :=
  N.rhs (fun e => k e (max 0 t)) (boxClamp lo hi x)

theorem Network.cutoffRhs_eq (N : Network d E) (k : E → ℝ → ℝ)
    (lo hi : State d) {t : ℝ} (ht : 0 ≤ t) {x : State d} (hx : x ∈ Icc lo hi) :
    N.cutoffRhs k lo hi t x = N.rhs (fun e => k e t) x := by
  simp [Network.cutoffRhs, max_eq_right ht, boxClamp_eq_of_mem lo hi hx]

theorem Network.cutoffRhs_measurable (N : Network d E) {k : E → ℝ → ℝ}
    {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u) (lo hi : State d) :
    Measurable (fun p : ℝ × State d => N.cutoffRhs k lo hi p.1 p.2) := by
  have hm : Measurable (fun p : ℝ × State d => fun e => k e (max 0 p.1)) :=
    measurable_pi_iff.mpr fun e => (hk.1 e).comp
      ((continuous_const.max continuous_fst).measurable)
  have hc : Measurable (fun p : ℝ × State d => boxClamp lo hi p.2) :=
    (boxClamp_lipschitz lo hi).continuous.measurable.comp measurable_snd
  exact N.rhs_joint_contDiff.continuous.measurable.comp (hm.prodMk hc)

theorem Network.rhs_bounded_on_box (N : Network d E) (ℓ u : ℝ) (lo hi : State d) :
    ∃ R : ℝ, ∀ k ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ x ∈ Icc lo hi, ‖N.rhs k x‖ ≤ R := by
  have hcompact : IsCompact
      (Icc (fun _ : E => ℓ) (fun _ : E => u) ×ˢ Icc lo hi) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨R, hR⟩ := hcompact.exists_bound_of_continuousOn
    (N.rhs_joint_contDiff.continuous.continuousOn :
      ContinuousOn (fun p : (E → ℝ) × State d => N.rhs p.1 p.2)
        (Icc (fun _ => ℓ) (fun _ => u) ×ˢ Icc lo hi))
  exact ⟨R, fun k hk x hx => hR (k, x) ⟨hk, hx⟩⟩

theorem Network.cutoffRhs_uniform_lipschitz (N : Network d E) {k : E → ℝ → ℝ}
    {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u) (lo hi : State d) (hbox : lo ≤ hi) :
    ∃ L : ℝ≥0, ∀ t, LipschitzWith L (N.cutoffRhs k lo hi t) := by
  obtain ⟨L, hL⟩ := N.rhs_uniform_lipschitzOn_box (fun _ => ℓ) (fun _ => u) lo hi
  have hrate : ∀ t : ℝ, (fun e => k e (max 0 t)) ∈ Icc (fun _ => ℓ) (fun _ => u) :=
    fun t => ⟨fun e => (hk.2 e (max 0 t) (le_max_left _ _)).1,
      fun e => (hk.2 e (max 0 t) (le_max_left _ _)).2⟩
  refine ⟨L, fun t => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (N.rhs (fun e => k e (max 0 t)) (boxClamp lo hi x))
    (N.rhs (fun e => k e (max 0 t)) (boxClamp lo hi y)) ≤ (L : ℝ) * dist x y
  have hh := (hL _ (hrate t)).dist_le_mul (boxClamp lo hi x) (boxClamp_mem lo hi hbox x)
    (boxClamp lo hi y) (boxClamp_mem lo hi hbox y)
  have hd : dist (boxClamp lo hi x) (boxClamp lo hi y) ≤ dist x y := by
    simpa only [NNReal.coe_one, one_mul] using (boxClamp_lipschitz lo hi).dist_le_mul x y
  exact hh.trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)

theorem Network.cutoffRhs_bounded_lipschitz (N : Network d E) {k : E → ℝ → ℝ}
    {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u) (lo hi : State d) (hbox : lo ≤ hi) :
    ∃ R : ℝ, ∃ L : ℝ≥0, (∀ t x, ‖N.cutoffRhs k lo hi t x‖ ≤ R) ∧
      ∀ t, LipschitzWith L (N.cutoffRhs k lo hi t) := by
  obtain ⟨R, hR⟩ := N.rhs_bounded_on_box ℓ u lo hi
  obtain ⟨L, hL⟩ := N.cutoffRhs_uniform_lipschitz hk lo hi hbox
  refine ⟨R, L, ?_, hL⟩
  intro t x
  change ‖N.rhs (fun e => k e (max 0 t)) (boxClamp lo hi x)‖ ≤ R
  exact hR _ ⟨fun e => (hk.2 e (max 0 t) (le_max_left _ _)).1,
    fun e => (hk.2 e (max 0 t) (le_max_left _ _)).2⟩ _ (boxClamp_mem lo hi hbox x)

theorem Network.exists_cutoffODE (N : Network d E) {k : E → ℝ → ℝ}
    {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u) (lo hi : State d) (hbox : lo ≤ hi)
    (z : State d) :
    ∃ D : BoundedMeasurableODE d, D.field = N.cutoffRhs k lo hi ∧ D.initial = z := by
  obtain ⟨R, L, hR, hL⟩ := N.cutoffRhs_bounded_lipschitz hk lo hi hbox
  exact ⟨⟨N.cutoffRhs k lo hi, z, R, L, N.cutoffRhs_measurable hk lo hi, hR, hL⟩,
    rfl, rfl⟩

end Endotactic
