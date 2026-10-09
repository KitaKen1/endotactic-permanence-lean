import Endotactic.AffineRobustness

/-!
# Robust relaxation within a closed convex set

Only the intersection of the original plateau with the closed convex set needs
to be compact. Radial clipping preserves both the relaxed affine inequalities
and membership of that convex set. For stoichiometric affine classes this
avoids bounding the entire ambient plateau.
-/

namespace Endotactic

open Set

variable {d m : ℕ} [Nonempty (Fin m)]

theorem AffineFamily.exists_relaxed_plateau_inter_subset_open (A : AffineFamily d m)
    {M : ℝ} {C : Set (State d)} (hC : IsClosed C) (hconv : Convex ℝ C)
    (hne : (A.plateau M ∩ C).Nonempty) (hK : IsCompact (A.plateau M ∩ C))
    {U : Set (State d)} (hU : IsOpen U) (hsub : A.plateau M ∩ C ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ A.plateau (M - ε) ∩ C ⊆ U := by
  obtain ⟨c, hc, hcC⟩ := hne
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (continuous_id.dist continuous_const).continuousOn
  let R : ℝ := max B 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hball : A.plateau M ∩ C ⊆ Metric.ball c R := by
    intro y hy
    rw [Metric.mem_ball]
    have hb := hB y hy
    rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] at hb
    exact hb.trans_lt (by dsimp [R]; linarith [le_max_left B 0])
  let bad : Set (State d) :=
    ((Metric.closedBall c R ∩ Uᶜ) ∪ Metric.sphere c R) ∩ C
  have hbad : IsCompact bad :=
    (((isCompact_closedBall c R).inter_right hU.isClosed_compl).union
      (isCompact_sphere c R)).inter_right hC
  have hdis : Disjoint bad (A.plateau M) := by
    apply Set.disjoint_left.mpr
    intro y hy hp
    rcases hy with ⟨hy | hy, hyC⟩
    · exact hy.2 (hsub ⟨hp, hyC⟩)
    · have heq := Metric.mem_sphere.mp hy
      have hlt := Metric.mem_ball.mp (hball ⟨hp, hyC⟩)
      linarith
  obtain ⟨ε, hε, hgap⟩ := A.compact_disjoint_plateau_gap hbad hdis
  refine ⟨ε, hε, ?_⟩
  rintro x ⟨hx, hxC⟩
  by_contra hn
  by_cases hnear : dist x c < R
  · exact Set.disjoint_left.mp hgap
      ⟨Or.inl ⟨Metric.mem_closedBall.mpr hnear.le, hn⟩, hxC⟩ hx
  · have hd : 0 < dist x c := hR.trans_le (le_of_not_gt hnear)
    let s : ℝ := R / dist x c
    have hs : 0 ≤ s := le_of_lt (div_pos hR hd)
    have hs₁ : s ≤ 1 := (div_le_one hd).mpr (le_of_not_gt hnear)
    let y : State d := (1 - s) • c + s • x
    have hc' : c ∈ A.plateau (M - ε) :=
      fun i => (sub_le_self M hε.le).trans (hc i)
    have hy : y ∈ A.plateau (M - ε) :=
      A.plateau_convex (M - ε) hc' hx (sub_nonneg.mpr hs₁) hs (by ring)
    have hyC : y ∈ C := hconv hcC hxC (sub_nonneg.mpr hs₁) hs (by ring)
    have heq : y - c = s • (x - c) := by
      ext i
      simp only [y, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hdist : dist y c = R := by
      rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs,
        ← dist_eq_norm]
      exact div_mul_cancel₀ R (ne_of_gt hd)
    exact Set.disjoint_left.mp hgap
      ⟨Or.inr (Metric.mem_sphere.mpr hdist), hyC⟩ hy

theorem AffineFamily.exists_enlarged_positive_box_inter (A : AffineFamily d m)
    {M : ℝ} {C : Set (State d)} (hC : IsClosed C) (hconv : Convex ℝ C)
    (hne : (A.plateau M ∩ C).Nonempty) (hK : IsCompact (A.plateau M ∩ C))
    (hpos : A.plateau M ∩ C ⊆ {x | Positive x}) :
    ∃ (ε : ℝ) (lo hi : State d), 0 < ε ∧ lo ≤ hi ∧ Positive lo ∧
      A.plateau (M - ε) ∩ C ⊆ Icc lo hi := by
  have hmin := fun i : Fin d => hK.exists_isMinOn hne
    (continuous_apply i).continuousOn
  have hmax := fun i : Fin d => hK.exists_isMaxOn hne
    (continuous_apply i).continuousOn
  choose a ha hamin using hmin
  choose b hb hbmax using hmax
  let lo : State d := fun i => a i i / 2
  let hi : State d := fun i => b i i + 1
  have hlo : Positive lo := fun i => half_pos (hpos (ha i) i)
  let U : Set (State d) := {x | ∀ i, lo i < x i ∧ x i < hi i}
  have hU : IsOpen U := by
    have heq : U = ⋂ i, {x | lo i < x i ∧ x i < hi i} := by
      ext x; simp [U]
    rw [heq]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (continuous_apply i)).inter
        (isOpen_lt (continuous_apply i) continuous_const)
  have hsub : A.plateau M ∩ C ⊆ U := by
    intro x hx i
    constructor
    · have hsmall : lo i < a i i := by dsimp [lo]; linarith [hpos (ha i) i]
      exact hsmall.trans_le (hamin i hx)
    · have hlarge : b i i < hi i := by dsimp [hi]; linarith
      exact (hbmax i hx).trans_lt hlarge
  obtain ⟨ε, hε, hrelax⟩ :=
    A.exists_relaxed_plateau_inter_subset_open hC hconv hne hK hU hsub
  obtain ⟨c, hc⟩ := hne
  refine ⟨ε, lo, hi, hε, (fun i => ((hsub hc i).1.trans (hsub hc i).2).le), hlo, ?_⟩
  exact fun x hx => ⟨fun i => (hrelax hx i).1.le, fun i => (hrelax hx i).2.le⟩

end Endotactic
