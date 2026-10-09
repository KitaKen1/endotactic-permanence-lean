import Endotactic.ClassInvariance
import Endotactic.StrictFaceTrap

/-!
# Class-restricted affine face certificates imply global well-posedness

Strict inward flux is required only on the faces within one stoichiometric
class. Compact separation is likewise performed within that closed class.
The original plateau need only be compact and positive after intersection
with the class. The cutoff trajectory preserves the class before trapping,
so a relative positive box suffices to remove the cutoff.

Construction of these class traps for arbitrary endotactic networks is still
an independent geometric obligation. Nonconserved, merely nonstrict faces
are not covered by the conserved-or-strict certificate here.
-/

namespace Endotactic

open Set

variable {d m : ℕ} {E : Type*} [Fintype E]

def Network.ClassAffineFaceCertificate (N : Network d E) (A : AffineFamily d m)
    (ℓ u M : ℝ) (c : State d) : Prop :=
  ∀ i, (∀ a y, dot (A.slope i) (N.rhs a y) = 0) ∨
    ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ A.plateau M ∩ N.stoichiometricClass c,
        A.value i y = M → 0 < dot (A.slope i) (N.rhs a y)

theorem Network.classAffineFaceCertificate_of_projections (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} (c : State d)
    (hfaces : ∀ i, (∀ e, N.projection (A.slope i) e = 0) ∨
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
        ∀ y ∈ A.plateau M ∩ N.stoichiometricClass c,
          A.value i y = M → 0 < dot (A.slope i) (N.rhs a y)) :
    N.ClassAffineFaceCertificate A ℓ u M c := by
  intro i
  rcases hfaces i with hzero | hstrict
  · exact Or.inl (fun a y => N.dot_rhs_eq_zero_of_projections (A.slope i) hzero a y)
  · exact Or.inr hstrict

theorem Network.classAffineFaceCertificate_of_global (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} (c : State d)
    (hfaces : N.AffineFaceCertificate A ℓ u M) :
    N.ClassAffineFaceCertificate A ℓ u M c := by
  intro i
  rcases hfaces i with hzero | hstrict
  · exact Or.inl hzero
  · exact Or.inr (fun a ha y hy => hstrict a ha y hy.1)

theorem Network.class_affine_branch_strip_of_face (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} (c : State d) (i : Fin m)
    {B : Set (State d)} (hB : IsCompact B)
    (hface : (∀ a y, dot (A.slope i) (N.rhs a y) = 0) ∨
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
        ∀ y ∈ A.plateau M ∩ N.stoichiometricClass c,
          A.value i y = M → 0 < dot (A.slope i) (N.rhs a y)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ B ∩ N.stoichiometricClass c, A.Active i y →
        M - ε < A.value i y → A.value i y < M →
          0 ≤ dot (A.slope i) (N.rhs a y) := by
  rcases hface with hzero | hstrict
  · refine ⟨1, zero_lt_one, ?_⟩
    intro a _ y _ _ _ _
    rw [hzero]
  · let bad : Set ((E → ℝ) × State d) :=
      (Icc (fun _ : E => ℓ) (fun _ => u) ×ˢ (B ∩ N.stoichiometricClass c)) ∩
        {p | A.Active i p.2 ∧ dot (A.slope i) (N.rhs p.1 p.2) ≤ 0}
    have hactive : IsClosed {p : (E → ℝ) × State d | A.Active i p.2} := by
      have heq : {p : (E → ℝ) × State d | A.Active i p.2} =
          ⋂ j, {p | A.value i p.2 ≤ A.value j p.2} := by
        ext p; simp [AffineFamily.Active]
      rw [heq]
      exact isClosed_iInter fun j => isClosed_le
        ((A.continuous_value i).comp continuous_snd)
        ((A.continuous_value j).comp continuous_snd)
    have hflux : IsClosed {p : (E → ℝ) × State d |
        dot (A.slope i) (N.rhs p.1 p.2) ≤ 0} :=
      isClosed_le ((dotCLM (A.slope i)).continuous.comp N.rhs_joint_contDiff.continuous)
        continuous_const
    have hbad : IsCompact bad :=
      (isCompact_Icc.prod (hB.inter_right (N.stoichiometricClass_isClosed c))).inter_right
        (hactive.inter hflux)
    let S : Set ℝ := (fun p : (E → ℝ) × State d => A.value i p.2) '' bad
    have hS : IsCompact S := hbad.image ((A.continuous_value i).comp continuous_snd)
    have hM : M ∈ Sᶜ := by
      intro hm
      obtain ⟨⟨a, y⟩, hp, heq⟩ := hm
      rcases hp with ⟨⟨ha, _, hyC⟩, hai, hf⟩
      have hy : y ∈ A.plateau M := fun j => heq ▸ hai j
      exact (not_lt_of_ge hf) (hstrict a ha y ⟨hy, hyC⟩ heq)
    obtain ⟨ε, hε, hsep⟩ := Metric.isOpen_iff.mp hS.isClosed.isOpen_compl M hM
    refine ⟨ε, hε, ?_⟩
    intro a ha y hy hai hl hu
    by_contra hn
    have hball : A.value i y ∈ Metric.ball M ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    exact (hsep hball) ⟨(a, y), ⟨⟨ha, hy⟩, hai, (lt_of_not_ge hn).le⟩, rfl⟩

variable [Nonempty (Fin m)]

theorem Network.class_affine_strip_of_face_certificate (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} (c : State d) {B : Set (State d)}
    (hB : IsCompact B) (hfaces : N.ClassAffineFaceCertificate A ℓ u M c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ B ∩ N.stoichiometricClass c,
        M - ε < A.minimum y → A.minimum y < M → ∀ i, A.Active i y →
          0 ≤ dot (A.slope i) (N.rhs a y) := by
  have hb := fun i => N.class_affine_branch_strip_of_face A c i hB (hfaces i)
  choose ε hε hs using hb
  let δ := finiteMinimum ε
  have hδ : 0 < δ := by
    obtain ⟨i, hi⟩ := finiteMinimum_attained ε
    change 0 < finiteMinimum ε
    rw [hi]
    exact hε i
  refine ⟨δ, hδ, ?_⟩
  intro a ha y hy hl hu i hai
  have heq := (A.active_iff_minimum_eq i y).mp hai
  have hle : δ ≤ ε i := finiteMinimum_le ε i
  apply hs i a ha y hy hai
  · linarith
  · linarith

theorem Network.exists_global_positive_of_class_affine_face_certificate
    (N : Network d E) {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} (c : State d)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {x | Positive x})
    (hfaces : N.ClassAffineFaceCertificate A ℓ u M c)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ A.plateau M ∩ N.stoichiometricClass c := by
  obtain ⟨ε₀, lo, hi, hε₀, hbox, hlo, hsub⟩ :=
    A.exists_enlarged_positive_box_inter (N.stoichiometricClass_isClosed c)
      (N.stoichiometricClass_convex c) ⟨z, hz⟩ hK hpos
  obtain ⟨δ, hδ, hs⟩ := N.class_affine_strip_of_face_certificate A c
    (B := Icc lo hi) isCompact_Icc hfaces
  let ε := min ε₀ δ
  have hε : 0 < ε := lt_min hε₀ hδ
  have he₀ : ε ≤ ε₀ := min_le_left _ _
  have heδ : ε ≤ δ := min_le_right _ _
  have hsub' : A.plateau (M - ε) ∩ N.stoichiometricClass c ⊆ Icc lo hi := by
    rintro y ⟨hy, hyC⟩
    exact hsub ⟨fun i => (by linarith : M - ε₀ ≤ M - ε).trans (hy i), hyC⟩
  apply N.exists_global_positive_in_class_affine_strip hk A hε c lo hi hbox hlo hsub' hz
  intro t ht y hyC hl hu i hai
  have hy : y ∈ Icc lo hi := hsub'
    ⟨(A.mem_plateau_iff_minimum_ge y (M - ε)).mpr hl.le, hyC⟩
  exact hs _ ⟨fun e => (hk.2 e t ht).1, fun e => (hk.2 e t ht).2⟩ y ⟨hy, hyC⟩
    (by linarith) hu i hai

theorem Network.positiveWellPosed_of_class_affine_face_certificate
    (N : Network d E) {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} (c : State d)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {x | Positive x})
    (hfaces : N.ClassAffineFaceCertificate A ℓ u M c)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    N.PositiveWellPosed k z := by
  obtain ⟨x, hx, _⟩ := N.exists_global_positive_of_class_affine_face_certificate hk A c
    hK hpos hfaces hz
  exact N.positiveWellPosed_of_exists hk ⟨x, hx⟩

end Endotactic
