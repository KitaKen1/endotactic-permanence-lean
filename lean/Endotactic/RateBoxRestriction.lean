import Endotactic.AnchorFreeWeakTrap

/-!
# Restrict rate boxes and reduce conjecture endpoints to strict boxes

A larger nondegenerate box may be used to build trapping certificates, then
restricted to the requested box, including a singleton. The weak-face
certificate for the larger box is a real additional obligation: it does not
follow from a certificate for the smaller box.
-/

namespace Endotactic

open Set

variable {d : ℕ} {E : Type*} [Fintype E]

omit [Fintype E] in
theorem AdmissibleRates.mono_box {k : E → ℝ → ℝ} {ℓ u L U : ℝ}
    (hk : AdmissibleRates k ℓ u) (hL : L ≤ ℓ) (hU : u ≤ U) :
    AdmissibleRates k L U :=
  ⟨hk.1, fun e t ht => ⟨hL.trans (hk.2 e t ht).1, (hk.2 e t ht).2.trans hU⟩⟩

theorem Network.UniformPermanent.mono_box (N : Network d E) {ℓ u L U : ℝ}
    {c : State d} {regular : (E → ℝ → ℝ) → Prop}
    (h : N.UniformPermanent L U c regular) (hL : L ≤ ℓ) (hU : u ≤ U) :
    N.UniformPermanent ℓ u c regular := by
  obtain ⟨K, hne, hK, hclass, hperm⟩ := h
  exact ⟨K, hne, hK, hclass, fun k hk hr => hperm k (hk.mono_box hL hU) hr⟩

theorem measurable_conjecture_of_strict_rate_boxes
    (h : ∀ (d m : ℕ), 0 < d → ∀ N : Network d (Fin m), N.IsEndotactic →
      ∀ (ℓ u : ℝ), 0 < ℓ → ℓ < u → ∀ c : State d, Positive c →
        N.UniformPermanent ℓ u c (fun _ => True)) :
    MeasurableExtendedPermanenceConjecture := by
  intro d m hd N hN ℓ u hℓ hlu c hc
  have hwide := h d m hd N hN (ℓ / 2) (u + 1) (half_pos hℓ) (by linarith) c hc
  exact hwide.mono_box N (by linarith) (by linarith)

variable {m : ℕ} [Nonempty (Fin m)]

theorem Network.exists_global_positive_of_wider_weak_class_faces (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u L U M : ℝ} (hk : AdmissibleRates k ℓ u)
    (hL : L ≤ ℓ) (hU : u ≤ U) (hgap : L < U)
    (A : AffineFamily d m) (c : State d)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (hfaces : N.ClassWeakAffineFaceCertificate A L U M c)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ A.plateau M ∩ N.stoichiometricClass c :=
  N.exists_global_positive_of_anchor_free_weak_class_faces (hk.mono_box hL hU) hgap
    A c hK hpos hfaces hz

end Endotactic
