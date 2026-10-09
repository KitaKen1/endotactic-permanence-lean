import Endotactic.StrictFaceTrap
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Compact affine plateaux have robust positive bounding boxes

A nonempty compact plateau stays inside any open neighborhood after a small
common relaxation of its finitely many inequalities. To control points far
away, scale the segment from a point in the original plateau to a relaxed
point until it reaches a fixed sphere. Convexity preserves the relaxed
inequalities, and compact separation excludes that sphere.

Consequently a compact positive plateau automatically has a slightly enlarged
plateau inside a positive coordinate box. The face-certificate global solution
API no longer requires a separate enlarged-box witness. The existence of the
compact positive plateau and its inward face certificates remains a hypothesis.
-/

namespace Endotactic

open Set

variable {d m : ℕ} [Nonempty (Fin m)]

theorem AffineFamily.continuous_minimum (A : AffineFamily d m) :
    Continuous A.minimum := by
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun i _ => A.continuous_value i)

theorem AffineFamily.compact_disjoint_plateau_gap (A : AffineFamily d m) {M : ℝ}
    {S : Set (State d)} (hS : IsCompact S) (hdis : Disjoint S (A.plateau M)) :
    ∃ ε : ℝ, 0 < ε ∧ Disjoint S (A.plateau (M - ε)) := by
  by_cases hne : S.Nonempty
  · obtain ⟨x, hx, hmax⟩ := hS.exists_isMaxOn hne A.continuous_minimum.continuousOn
    have hlt : A.minimum x < M := by
      by_contra hn
      exact Set.disjoint_left.mp hdis hx
        ((A.mem_plateau_iff_minimum_ge x M).mpr (le_of_not_gt hn))
    refine ⟨(M - A.minimum x) / 2, by linarith, Set.disjoint_left.mpr ?_⟩
    intro y hy hp
    have hle : A.minimum y ≤ A.minimum x := hmax hy
    have hge := (A.mem_plateau_iff_minimum_ge y _).mp hp
    linarith
  · exact ⟨1, zero_lt_one, by simp [Set.not_nonempty_iff_eq_empty.mp hne]⟩

theorem AffineFamily.exists_relaxed_plateau_subset_open (A : AffineFamily d m) {M : ℝ}
    (hne : (A.plateau M).Nonempty) (hK : IsCompact (A.plateau M))
    {U : Set (State d)} (hU : IsOpen U) (hsub : A.plateau M ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ A.plateau (M - ε) ⊆ U := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (continuous_id.dist continuous_const).continuousOn
  let R : ℝ := max B 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hball : A.plateau M ⊆ Metric.ball c R := by
    intro y hy
    rw [Metric.mem_ball]
    have hb := hB y hy
    rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] at hb
    exact hb.trans_lt (by dsimp [R]; linarith [le_max_left B 0])
  let bad : Set (State d) := (Metric.closedBall c R ∩ Uᶜ) ∪ Metric.sphere c R
  have hbad : IsCompact bad :=
    ((isCompact_closedBall c R).inter_right hU.isClosed_compl).union
      (isCompact_sphere c R)
  have hdis : Disjoint bad (A.plateau M) := by
    apply Set.disjoint_left.mpr
    intro y hy hp
    rcases hy with hy | hy
    · exact hy.2 (hsub hp)
    · have heq := Metric.mem_sphere.mp hy
      have hlt := Metric.mem_ball.mp (hball hp)
      linarith
  obtain ⟨ε, hε, hgap⟩ := A.compact_disjoint_plateau_gap hbad hdis
  refine ⟨ε, hε, ?_⟩
  intro x hx
  by_contra hn
  by_cases hnear : dist x c < R
  · exact Set.disjoint_left.mp hgap
      (Or.inl ⟨Metric.mem_closedBall.mpr hnear.le, hn⟩) hx
  · have hd : 0 < dist x c := hR.trans_le (le_of_not_gt hnear)
    let s : ℝ := R / dist x c
    have hs : 0 ≤ s := le_of_lt (div_pos hR hd)
    have hs₁ : s ≤ 1 := (div_le_one hd).mpr (le_of_not_gt hnear)
    let y : State d := (1 - s) • c + s • x
    have hc' : c ∈ A.plateau (M - ε) :=
      fun i => (sub_le_self M hε.le).trans (hc i)
    have hy : y ∈ A.plateau (M - ε) :=
      A.plateau_convex (M - ε) hc' hx (sub_nonneg.mpr hs₁) hs (by ring)
    have heq : y - c = s • (x - c) := by
      ext i
      simp only [y, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hdist : dist y c = R := by
      rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs,
        ← dist_eq_norm]
      exact div_mul_cancel₀ R (ne_of_gt hd)
    exact Set.disjoint_left.mp hgap
      (Or.inr (Metric.mem_sphere.mpr hdist)) hy

theorem AffineFamily.exists_enlarged_positive_box (A : AffineFamily d m) {M : ℝ}
    (hne : (A.plateau M).Nonempty) (hK : IsCompact (A.plateau M))
    (hpos : A.plateau M ⊆ {x | Positive x}) :
    ∃ (ε : ℝ) (lo hi : State d), 0 < ε ∧ lo ≤ hi ∧ Positive lo ∧
      A.plateau (M - ε) ⊆ Icc lo hi := by
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
  have hsub : A.plateau M ⊆ U := by
    intro x hx i
    constructor
    · have hsmall : lo i < a i i := by dsimp [lo]; linarith [hpos (ha i) i]
      exact hsmall.trans_le (hamin i hx)
    · have hlarge : b i i < hi i := by dsimp [hi]; linarith
      exact (hbmax i hx).trans_lt hlarge
  obtain ⟨ε, hε, hrelax⟩ := A.exists_relaxed_plateau_subset_open hne hK hU hsub
  obtain ⟨c, hc⟩ := hne
  refine ⟨ε, lo, hi, hε, (fun i => ((hsub hc i).1.trans (hsub hc i).2).le), hlo, ?_⟩
  exact fun x hx => ⟨fun i => (hrelax hx i).1.le, fun i => (hrelax hx i).2.le⟩

variable {E : Type*} [Fintype E]

theorem Network.exists_global_positive_of_compact_affine_face_certificate
    (N : Network d E) {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} (hK : IsCompact (A.plateau M))
    (hpos : A.plateau M ⊆ {x | Positive x})
    (hfaces : N.AffineFaceCertificate A ℓ u M) {z : State d} (hz : z ∈ A.plateau M) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧ ∀ t, 0 ≤ t → x t ∈ A.plateau M := by
  obtain ⟨ε, lo, hi, hε, hbox, hlo, hsub⟩ :=
    A.exists_enlarged_positive_box ⟨z, hz⟩ hK hpos
  exact N.exists_global_positive_of_affine_face_certificate hk A hε lo hi hbox hlo
    hsub hfaces hz

theorem Network.positiveWellPosed_of_compact_affine_face_certificate
    (N : Network d E) {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} (hK : IsCompact (A.plateau M))
    (hpos : A.plateau M ⊆ {x | Positive x})
    (hfaces : N.AffineFaceCertificate A ℓ u M) {z : State d} (hz : z ∈ A.plateau M) :
    N.PositiveWellPosed k z := by
  obtain ⟨x, hx, _⟩ := N.exists_global_positive_of_compact_affine_face_certificate hk A
    hK hpos hfaces hz
  exact N.positiveWellPosed_of_exists hk ⟨x, hx⟩

end Endotactic
