import Endotactic.AffineCap
import Endotactic.UniformKinetics
import Mathlib.Topology.Order.Compact

/-!
# Compact initial traps turn strict exterior signs into finite-time absorption

Only pointwise strict flux below `M` is assumed. On a compact state trap and
the compact coefficient box, the closed active sublevel at any `Q < M` has
a positive uniform flux margin. This avoids demanding strict flux on the
original `M`-boundary, or a numerical margin on the entire positive class.

Append a constant cap at `Q` to obtain finite entry into `A.plateau Q`.
The trap and margin may depend on the trajectory or initial point. The target
level may be selected independently of both.
-/

namespace Endotactic

open Set

variable {d m : ℕ} [Nonempty (Fin m)] {E : Type*} [Fintype E]

omit [Nonempty (Fin m)] in
theorem AffineFamily.isClosed_active (A : AffineFamily d m) (i : Fin m) :
    IsClosed {x | A.Active i x} := by
  have heq : {x | A.Active i x} = ⋂ j, {x | A.value i x ≤ A.value j x} := by
    ext x
    simp [AffineFamily.Active]
  rw [heq]
  exact isClosed_iInter fun j => isClosed_le (A.continuous_value i) (A.continuous_value j)

theorem Network.exists_affine_active_margin_on_compact_sublevel (N : Network d E)
    (A : AffineFamily d m) {ℓ u M Q : ℝ} {B : Set (State d)} (hB : IsCompact B)
    (hQ : Q < M)
    (hstrict : ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ B, A.minimum y < M → ∀ i, A.Active i y →
        0 < dot (A.slope i) (N.rhs a y)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ B, A.minimum y ≤ Q → ∀ i, A.Active i y →
        δ ≤ dot (A.slope i) (N.rhs a y) := by
  have hbranch : ∀ i : Fin m, ∃ δ : ℝ, 0 < δ ∧
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
        ∀ y ∈ B, A.Active i y → A.value i y ≤ Q →
          δ ≤ dot (A.slope i) (N.rhs a y) := by
    intro i
    let C : Set ((E → ℝ) × State d) :=
      (Icc (fun _ : E => ℓ) (fun _ => u) ×ˢ B) ∩
        {p | A.Active i p.2 ∧ A.value i p.2 ≤ Q}
    have hC : IsCompact C := (isCompact_Icc.prod hB).inter_right
      (((A.isClosed_active i).preimage continuous_snd).inter
        (isClosed_le ((A.continuous_value i).comp continuous_snd) continuous_const))
    have hc : Continuous (fun p : (E → ℝ) × State d =>
        dot (A.slope i) (N.rhs p.1 p.2)) :=
      (dotCLM (A.slope i)).continuous.comp N.rhs_joint_contDiff.continuous
    obtain ⟨δ, hδ, hb⟩ := hC.exists_forall_le' hc.continuousOn (a := 0) (by
      intro p hp
      have heq := (A.active_iff_minimum_eq i p.2).mp hp.2.1
      exact hstrict p.1 hp.1.1 p.2 hp.1.2 (heq ▸ hp.2.2.trans_lt hQ) i hp.2.1)
    exact ⟨δ, hδ, fun a ha y hy hi hval => hb (a, y) ⟨⟨ha, hy⟩, hi, hval⟩⟩
  choose δ hδ hb using hbranch
  let Δ : ℝ := finiteMinimum δ
  have hΔ : 0 < Δ := by
    obtain ⟨i, hi⟩ := finiteMinimum_attained δ
    change 0 < finiteMinimum δ
    rw [hi]
    exact hδ i
  refine ⟨Δ, hΔ, ?_⟩
  intro a ha y hy hmin i hi
  have hval : A.value i y ≤ Q := (A.active_iff_minimum_eq i y).mp hi ▸ hmin
  exact (finiteMinimum_le δ i).trans (hb i a ha y hy hi hval)

theorem AffineFamily.eventuallyIn_plateau_of_compact_strict_exterior
    (A : AffineFamily d m) {N : Network d E} {k : E → ℝ → ℝ} {ℓ u M Q : ℝ}
    (hk : AdmissibleRates k ℓ u) {z : State d} {x : ℝ → State d}
    (hx : N.IsIntegralSolution k z x) {B : Set (State d)} (hB : IsCompact B)
    (hstay : ∀ t, 0 ≤ t → x t ∈ B) (hQ : Q < M)
    (hstrict : ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ B, A.minimum y < M → ∀ i, A.Active i y →
        0 < dot (A.slope i) (N.rhs a y)) : EventuallyIn x (A.plateau Q) := by
  obtain ⟨δ, hδ, hb⟩ := N.exists_affine_active_margin_on_compact_sublevel A hB hQ hstrict
  have hbound : ∀ t, 0 ≤ t → (A.withCap Q).minimum (x t) < Q → ∀ i,
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
        hb _ ⟨fun e => (hk.2 e t ht).1, fun e => (hk.2 e t ht).2⟩
          (x t) (hstay t ht) hsub j hactive
  have hh := (A.withCap Q).eventuallyIn_plateau hx hδ
    (fun t _ => A.withCap_minimum_le Q (x t)) hbound
  rwa [A.withCap_plateau] at hh

end Endotactic
