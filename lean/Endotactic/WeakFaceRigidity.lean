import Endotactic.RelativeWeakFiniteClassTrap
import Endotactic.FluxBound

/-!
# Weak faces in a nondegenerate rate box force relative anchors

A finite convex carrier has a point strict on every branch not identically
equal to its level. At that point an inward vector admits a short feasible
straight step. A branch equal throughout the carrier therefore annihilates
every admissible velocity. Varying one rate between two different endpoints,
at a positive state, forces every individual reaction projection to vanish.

Thus, when `ell < u`, nonempty positive carriers with weak faces automatically
supply the relative anchor needed by the existing analytic trap theorem.
Compactness is not needed for this geometric argument. No endotactic carrier
existence theorem is asserted.
-/

namespace Endotactic

open Set Filter Topology
open scoped Classical

variable {d m : ℕ}

theorem AffineFamily.value_forward_step (A : AffineFamily d m) (i : Fin m)
    (p v : State d) (t : ℝ) :
    A.value i (p + t • v) = A.value i p + t * dot (A.slope i) v := by
  simp only [AffineFamily.value, dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.sum_add_distrib]
  have hsum : (∑ j, A.slope i j * (t * v j)) = t * ∑ j, A.slope i j * v j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

theorem AffineFamily.exists_strict_or_equality_anchor (A : AffineFamily d m)
    {M : ℝ} {C : Set (State d)} (hconv : Convex ℝ C)
    (hne : (A.plateau M ∩ C).Nonempty) :
    ∃ p ∈ A.plateau M ∩ C, ∀ i,
      (∀ y ∈ A.plateau M ∩ C, A.value i y = M) ∨ M < A.value i p := by
  classical
  let K := A.plateau M ∩ C
  have hc : Convex ℝ K := (A.plateau_convex M).inter hconv
  have hw : ∀ i, (∀ y ∈ K, A.value i y = M) ∨ ∃ y ∈ K, M < A.value i y := by
    intro i
    by_cases hi : ∀ y ∈ K, A.value i y = M
    · exact Or.inl hi
    · right
      push Not at hi
      obtain ⟨y, hy, hne'⟩ := hi
      exact ⟨y, hy, lt_of_le_of_ne (hy.1 i) (Ne.symm hne')⟩
  have hbuild : ∀ s : Finset (Fin m), ∃ p ∈ K, ∀ i ∈ s,
      (∀ y ∈ K, A.value i y = M) ∨ M < A.value i p := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨p, hp⟩ := hne
      exact ⟨p, hp, by simp⟩
    | @insert i s _ ih =>
      obtain ⟨p, hp, hs⟩ := ih
      rcases hw i with hi | ⟨q, hq, hqi⟩
      · refine ⟨p, hp, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact Or.inl hi
        · exact hs j hj
      · refine ⟨(1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q,
          hc hp hq (by norm_num) (by norm_num) (by norm_num), ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · right
          rw [A.value_convex_combination j p q (by norm_num)]
          linarith [hp.1 j]
        · rcases hs j hj with heq | hstrict
          · exact Or.inl heq
          · right
            rw [A.value_convex_combination j p q (by norm_num)]
            linarith [hq.1 j]
  obtain ⟨p, hp, hs⟩ := hbuild Finset.univ
  exact ⟨p, hp, fun i => hs i (Finset.mem_univ i)⟩

theorem AffineFamily.exists_feasible_forward_step (A : AffineFamily d m)
    {M : ℝ} {p v : State d} (hp : p ∈ A.plateau M)
    (hv : ∀ i, A.value i p = M → 0 ≤ dot (A.slope i) v) :
    ∃ t : ℝ, 0 < t ∧ p + t • v ∈ A.plateau M := by
  have hi : ∀ i, ∀ᶠ t : ℝ in 𝓝[>] 0, M ≤ A.value i (p + t • v) := by
    intro i
    by_cases heq : A.value i p = M
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [A.value_forward_step, heq]
      exact le_add_of_nonneg_right (mul_nonneg ht.le (hv i heq))
    · have hstrict : M < A.value i p := lt_of_le_of_ne (hp i) (Ne.symm heq)
      have hc : Continuous (fun t : ℝ => A.value i (p + t • v)) :=
        (A.continuous_value i).comp (continuous_const.add (continuous_id.smul continuous_const))
      have hevent : ∀ᶠ t : ℝ in 𝓝 0, M < A.value i (p + t • v) := by
        apply (hc.tendsto 0).eventually
        simpa using (eventually_gt_nhds hstrict)
      exact (hevent.filter_mono nhdsWithin_le_nhds).mono fun t ht => ht.le
  have hpositive : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hall : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ i, M ≤ A.value i (p + t • v) :=
    Filter.eventually_all.mpr hi
  obtain ⟨t, ht, hstep⟩ := (hpositive.and hall).exists
  exact ⟨t, ht, hstep⟩

variable {E : Type*} [Fintype E]

omit [Fintype E] in
theorem Network.class_mem_forward_step (N : Network d E) {c p v : State d}
    (hp : p ∈ N.stoichiometricClass c) (hv : v ∈ N.stoichiometricSubspace)
    (t : ℝ) : p + t • v ∈ N.stoichiometricClass c := by
  change (p + t • v) - c ∈ N.stoichiometricSubspace
  rw [add_sub_right_comm]
  exact N.stoichiometricSubspace.add_mem hp (N.stoichiometricSubspace.smul_mem t hv)

theorem Network.rhs_projection_update (N : Network d E) (r p : State d)
    (a : E → ℝ) (e : E) (b : ℝ) :
    dot r (N.rhs (Function.update a e b) p) - dot r (N.rhs a p) =
      (b - a e) * monomial p (N.source e) * N.projection r e := by
  classical
  rw [dot_rhs, dot_rhs, ← Finset.sum_sub_distrib]
  have heq : ∀ f, Function.update a e b f * monomial p (N.source f) * N.projection r f -
      a f * monomial p (N.source f) * N.projection r f =
      if f = e then (b - a e) * monomial p (N.source e) * N.projection r e else 0 := by
    intro f
    by_cases hf : f = e
    · subst f; simp only [Function.update_self, if_true]; ring
    · simp [hf]
  simp_rw [heq]
  simp

theorem Network.projections_zero_of_flux_zero_on_box (N : Network d E)
    {r p : State d} {ℓ u : ℝ} (hgap : ℓ < u) (hp : Positive p)
    (hzero : ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u), dot r (N.rhs a p) = 0) :
    ∀ e, N.projection r e = 0 := by
  classical
  intro e
  let a : E → ℝ := fun _ => ℓ
  have ha : a ∈ Icc (fun _ => ℓ) (fun _ => u) := ⟨le_rfl, fun _ => hgap.le⟩
  have hb : Function.update a e u ∈ Icc (fun _ => ℓ) (fun _ => u) := by
    constructor <;> intro f <;> by_cases hf : f = e
    · subst f; simp [hgap.le]
    · simp [Function.update_of_ne hf, a]
    · subst f; simp
    · simp [Function.update_of_ne hf, a, hgap.le]
  have h := N.rhs_projection_update r p a e u
  rw [hzero _ hb, hzero _ ha, sub_self] at h
  have hm : 0 < (u - a e) * monomial p (N.source e) :=
    mul_pos (sub_pos.mpr hgap) (monomial_pos hp _)
  exact (mul_eq_zero.mp h.symm).resolve_left hm.ne'

theorem Network.equality_face_conserved_of_weak_faces (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} {c p : State d}
    (hgap : ℓ < u) (hp : p ∈ A.plateau M ∩ N.stoichiometricClass c)
    (hpos : Positive p)
    (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u M c) {i : Fin m}
    (hi : ∀ y ∈ A.plateau M ∩ N.stoichiometricClass c, A.value i y = M) :
    ∀ e, N.projection (A.slope i) e = 0 := by
  apply N.projections_zero_of_flux_zero_on_box hgap hpos
  intro a ha
  obtain ⟨t, ht, hstep⟩ := A.exists_feasible_forward_step hp.1 (by
    intro j hj
    exact hfaces j a ha p hp hj)
  have hclass := N.class_mem_forward_step hp.2 (rhs_mem_stoichiometricSubspace N a p) t
  have h := hi (p + t • N.rhs a p) ⟨hstep, hclass⟩
  rw [A.value_forward_step, hi p hp] at h
  have hprod : t * dot (A.slope i) (N.rhs a p) = 0 := by linarith
  exact (mul_eq_zero.mp hprod).resolve_left ht.ne'

theorem Network.exists_classRelativeAnchor_of_weak_faces (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} {c : State d}
    (hgap : ℓ < u) (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty)
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (hfaces : N.ClassWeakAffineFaceCertificate A ℓ u M c) :
    ∃ p ∈ A.plateau M ∩ N.stoichiometricClass c, N.ClassRelativeAnchor A M c p := by
  obtain ⟨p, hp, hanchor⟩ := A.exists_strict_or_equality_anchor
    (N.stoichiometricClass_convex c) hne
  refine ⟨p, hp, hp.2, ?_⟩
  intro i
  rcases hanchor i with hi | hs
  · exact Or.inl (N.equality_face_conserved_of_weak_faces A hgap hp (hpos hp) hfaces hi)
  · exact Or.inr hs

end Endotactic
