import Endotactic.Network

/-!
# The essential-source shortcut

This replaces graph return paths and cut-flux decompositions by a minimum over
the finite set of reactions with NONZERO projection. It does not assume weak
reversibility or strong endotacticity.
-/

namespace Endotactic

variable {d : ℕ} {E : Type*} (N : Network d E)

def Network.IsEssentialMinimum (r : State d) (e : E) : Prop :=
  N.projection r e ≠ 0 ∧
    ∀ f : E, N.projection r f ≠ 0 → N.sourceLevel r e ≤ N.sourceLevel r f

theorem essentialMinimum_projection_pos (hN : N.IsEndotactic) {r : State d} {e : E}
    (he : N.IsEssentialMinimum r e) : 0 < N.projection r e := by
  rcases he with ⟨hne, hmin⟩
  by_contra h
  have hneg : N.projection r e < 0 := lt_of_le_of_ne (le_of_not_gt h) hne
  obtain ⟨f, hf, hlevel⟩ := hN r e hneg
  have := hmin f (ne_of_gt hf)
  linarith

theorem essentialMinimum_source_lt_of_negative (hN : N.IsEndotactic)
    {r : State d} {e : E} (he : N.IsEssentialMinimum r e) {f : E}
    (hf : N.projection r f < 0) : N.sourceLevel r e < N.sourceLevel r f := by
  obtain ⟨g, hg, hlevel⟩ := hN r f hf
  exact lt_of_le_of_lt (he.2 g (ne_of_gt hg)) hlevel

theorem exists_essentialMinimum [Fintype E] {r : State d}
    (h : ∃ e : E, N.projection r e ≠ 0) :
    ∃ e : E, N.IsEssentialMinimum r e := by
  classical
  let s := Finset.univ.filter fun e => N.projection r e ≠ 0
  have hs : s.Nonempty := by
    obtain ⟨e, he⟩ := h
    exact ⟨e, by simp [s, he]⟩
  obtain ⟨e, he, hmin⟩ := Finset.exists_min_image s (N.sourceLevel r) hs
  refine ⟨e, ?_, ?_⟩
  · simpa [s] using he
  · intro f hf
    exact hmin f (by simp [s, hf])

theorem exists_positive_essential_source [Fintype E] (hN : N.IsEndotactic) {r : State d}
    (h : ∃ e : E, N.projection r e ≠ 0) :
    ∃ e : E, 0 < N.projection r e ∧
      ∀ f : E, N.projection r f < 0 → N.sourceLevel r e < N.sourceLevel r f := by
  obtain ⟨e, he⟩ := exists_essentialMinimum N h
  exact ⟨e, essentialMinimum_projection_pos N hN he,
    fun _ hf => essentialMinimum_source_lt_of_negative N hN he hf⟩

theorem exists_positive_negative_source_gap [Fintype E] (hN : N.IsEndotactic)
    {r : State d} {a : E} (ha : N.IsEssentialMinimum r a) :
    ∃ H : ℝ, 0 < H ∧ ∀ e : E, N.projection r e < 0 →
      H ≤ N.sourceLevel r e - N.sourceLevel r a := by
  classical
  by_cases hex : ∃ e : E, N.projection r e < 0
  · let s := Finset.univ.filter fun e => N.projection r e < 0
    have hs : s.Nonempty := by
      obtain ⟨e, he⟩ := hex
      exact ⟨e, by simp [s, he]⟩
    obtain ⟨e, he, hmin⟩ := Finset.exists_min_image s
      (fun e => N.sourceLevel r e - N.sourceLevel r a) hs
    have hneg : N.projection r e < 0 := by simpa [s] using he
    refine ⟨N.sourceLevel r e - N.sourceLevel r a,
      sub_pos.mpr (essentialMinimum_source_lt_of_negative N hN ha hneg), ?_⟩
    intro f hf
    exact hmin f (by simp [s, hf])
  · refine ⟨1, by norm_num, ?_⟩
    intro e he
    exact False.elim (hex ⟨e, he⟩)

end Endotactic
