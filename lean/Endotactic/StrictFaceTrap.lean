import Endotactic.PolyhedralInvariance
import Endotactic.FluxBound

/-!
# A finite face certificate supplies a uniform exterior strip

Each affine face is either a conserved observable (its flux is identically
zero), or has strictly inward flux for every coefficient in the compact rate
box. On a compact ambient state box, the bad-flux set is closed and compact.
Its active-face values avoid the target level, so a positive strip width
separates them from that level. Taking a finite minimum makes the width common
to every active branch and every coefficient.

This converts boundary certificates into positive global integral solutions
of the original field. It assumes an enlarged plateau inside a positive box;
constructing such trap geometry for arbitrary endotactic networks is separate.
No metric projection, Hilbert-space norm change, or pointwise time derivative
of the coefficient path is needed.
-/

namespace Endotactic

open Set

variable {d m : ℕ} {E : Type*} [Fintype E]

/-- A conserved face or a strictly inward face, uniformly over the rate box. -/
def Network.AffineFaceCertificate (N : Network d E) (A : AffineFamily d m)
    (ℓ u M : ℝ) : Prop :=
  ∀ i, (∀ a y, dot (A.slope i) (N.rhs a y) = 0) ∨
    ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u), ∀ y ∈ A.plateau M,
      A.value i y = M → 0 < dot (A.slope i) (N.rhs a y)

theorem Network.dot_rhs_eq_zero_of_projections (N : Network d E) (r : State d)
    (hzero : ∀ e, N.projection r e = 0) (a : E → ℝ) (y : State d) :
    dot r (N.rhs a y) = 0 := by
  rw [dot_rhs]
  simp [hzero]

theorem Network.affineFaceCertificate_of_projections (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ}
    (hfaces : ∀ i, (∀ e, N.projection (A.slope i) e = 0) ∨
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u), ∀ y ∈ A.plateau M,
        A.value i y = M → 0 < dot (A.slope i) (N.rhs a y)) :
    N.AffineFaceCertificate A ℓ u M := by
  intro i
  rcases hfaces i with hzero | hstrict
  · exact Or.inl (fun a y => N.dot_rhs_eq_zero_of_projections (A.slope i) hzero a y)
  · exact Or.inr hstrict

theorem Network.affine_branch_strip_of_face (N : Network d E) (A : AffineFamily d m)
    {ℓ u M : ℝ} (i : Fin m) {B : Set (State d)} (hB : IsCompact B)
    (hface : (∀ a y, dot (A.slope i) (N.rhs a y) = 0) ∨
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u), ∀ y ∈ A.plateau M,
        A.value i y = M → 0 < dot (A.slope i) (N.rhs a y)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u), ∀ y ∈ B,
      A.Active i y → M - ε < A.value i y → A.value i y < M →
        0 ≤ dot (A.slope i) (N.rhs a y) := by
  rcases hface with hzero | hstrict
  · refine ⟨1, zero_lt_one, ?_⟩
    intro a _ y _ _ _ _
    rw [hzero]
  · let bad : Set ((E → ℝ) × State d) :=
      (Icc (fun _ : E => ℓ) (fun _ => u) ×ˢ B) ∩
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
    have hbad : IsCompact bad := (isCompact_Icc.prod hB).inter_right (hactive.inter hflux)
    let S : Set ℝ := (fun p : (E → ℝ) × State d => A.value i p.2) '' bad
    have hS : IsCompact S := hbad.image ((A.continuous_value i).comp continuous_snd)
    have hM : M ∈ Sᶜ := by
      intro hm
      obtain ⟨⟨a, y⟩, hp, heq⟩ := hm
      rcases hp with ⟨⟨ha, _⟩, hai, hf⟩
      have hy : y ∈ A.plateau M := fun j => heq ▸ hai j
      exact (not_lt_of_ge hf) (hstrict a ha y hy heq)
    obtain ⟨ε, hε, hsep⟩ := Metric.isOpen_iff.mp hS.isClosed.isOpen_compl M hM
    refine ⟨ε, hε, ?_⟩
    intro a ha y hy hai hl hu
    by_contra hn
    have hball : A.value i y ∈ Metric.ball M ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    exact (hsep hball) ⟨(a, y), ⟨⟨ha, hy⟩, hai, (lt_of_not_ge hn).le⟩, rfl⟩

variable [Nonempty (Fin m)]

theorem Network.affine_strip_of_face_certificate (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} {B : Set (State d)} (hB : IsCompact B)
    (hfaces : N.AffineFaceCertificate A ℓ u M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u), ∀ y ∈ B,
      M - ε < A.minimum y → A.minimum y < M → ∀ i, A.Active i y →
        0 ≤ dot (A.slope i) (N.rhs a y) := by
  have hb := fun i => N.affine_branch_strip_of_face A i hB (hfaces i)
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

theorem Network.exists_global_positive_of_affine_face_certificate (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (lo hi : State d) (hbox : lo ≤ hi) (hlo : Positive lo)
    (hsub : A.plateau (M - ε₀) ⊆ Icc lo hi)
    (hfaces : N.AffineFaceCertificate A ℓ u M) {z : State d} (hz : z ∈ A.plateau M) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧ ∀ t, 0 ≤ t → x t ∈ A.plateau M := by
  obtain ⟨δ, hδ, hs⟩ := N.affine_strip_of_face_certificate A
    (B := Icc lo hi) isCompact_Icc hfaces
  let ε := min ε₀ δ
  have hε : 0 < ε := lt_min hε₀ hδ
  have he₀ : ε ≤ ε₀ := min_le_left _ _
  have heδ : ε ≤ δ := min_le_right _ _
  have hsub' : A.plateau (M - ε) ⊆ Icc lo hi := by
    intro y hy
    exact hsub (fun i => (by linarith : M - ε₀ ≤ M - ε).trans (hy i))
  apply N.exists_global_positive_in_affine_strip hk A hε lo hi hbox hlo hsub' hz
  intro t ht y hl hu i hai
  have hy : y ∈ Icc lo hi := hsub'
    ((A.mem_plateau_iff_minimum_ge y (M - ε)).mpr hl.le)
  exact hs _ ⟨fun e => (hk.2 e t ht).1, fun e => (hk.2 e t ht).2⟩ y hy
    (by linarith) hu i hai

theorem Network.positiveWellPosed_of_affine_face_certificate (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (lo hi : State d) (hbox : lo ≤ hi) (hlo : Positive lo)
    (hsub : A.plateau (M - ε₀) ⊆ Icc lo hi)
    (hfaces : N.AffineFaceCertificate A ℓ u M) {z : State d} (hz : z ∈ A.plateau M) :
    N.PositiveWellPosed k z := by
  obtain ⟨x, hx, _⟩ := N.exists_global_positive_of_affine_face_certificate hk A
    hε₀ lo hi hbox hlo hsub hfaces hz
  exact N.positiveWellPosed_of_exists hk ⟨x, hx⟩

end Endotactic
