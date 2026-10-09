import Endotactic.AffineInductionData

/-!
# Successive choices construct all fixed-minimum support data

The lower-dimensional affine theorem is a strong induction hypothesis. The
next level is chosen from already fixed finite slopes before its new families.
Only the next support rank is replaced; previous families remain unchanged.
This closes data existence conditional on lower dimensions, not the full A.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem AffineSupportPrefix.exists_successor_of_oracle {d k : ℕ} {t b : ℝ} {E : State d → ℝ}
    (P : AffineSupportPrefix d t b E k) (htb : t < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hOracle : SupportFamilyOracle d t b E) :
    Nonempty (AffineSupportPrefix d t b E (k + 1)) := by
  classical
  obtain ⟨β, htβ, hβb, hβprev, hseed, hwidth⟩ := P.exists_next_level htb hE
  have hnew : ∀ U : RaisedSupport d, ∃ C : SupportAffineEntry U,
      0 < C.1 ∧ C.Valid t b E U β :=
    fun U => hOracle U β htβ hβb
  choose C hCpos hCvalid using hnew
  let entries := fun U : RaisedSupport d => if U.val.card = k + 1 then C U else P.entry U
  let levels := Function.update P.level (k + 1) β
  refine ⟨{ entry := entries
            level := levels
            size_pos := ?_
            ambient_cube := ?_
            level_bounds := ?_
            descending := ?_
            selected := ?_
            seed_width := ?_
            next_width := ?_ }⟩
  · intro U
    by_cases hc : U.val.card = k + 1
    · simpa only [entries, if_pos hc] using hCpos U
    · simpa only [entries, if_neg hc] using P.size_pos U
  · intro U
    by_cases hc : U.val.card = k + 1
    · have he : entries U = C U := if_pos hc
      rw [he]
      intro i
      exact extendCoordinates_mem_cube U.embedding ⟨le_rfl, htb.le⟩
        ⟨fun j => htβ.le.trans (((hCvalid U).1 i).1 j), ((hCvalid U).1 i).2⟩
    · have he : entries U = P.entry U := if_neg hc
      rw [he]
      exact P.ambient_cube U
  · intro n hn hnk
    by_cases heq : n = k + 1
    · simpa only [levels, heq, Function.update_self] using And.intro htβ hβb
    · simpa only [levels, Function.update_of_ne heq] using P.level_bounds n hn (by omega)
  · intro n hn hnk
    have hnne : n ≠ k + 1 := by omega
    by_cases heq : n + 1 = k + 1
    · have hnk' : n = k := by omega
      have hlt : β < P.level n := by simpa only [hnk'] using hβprev (by omega)
      simpa only [levels, heq, Function.update_self, Function.update_of_ne hnne] using hlt
    · simpa only [levels, Function.update_of_ne heq, Function.update_of_ne hnne] using
        P.descending n hn (by omega)
  · intro U hk
    by_cases hc : U.val.card = k + 1
    · simpa only [entries, if_pos hc, levels, hc, Function.update_self] using hCvalid U
    · simpa only [entries, if_neg hc, levels, Function.update_of_ne hc] using
        P.selected U (by omega)
  · intro _
    by_cases hk : k = 0
    · subst k
      simpa only [levels, zero_add, Function.update_self] using hseed
    · have hne : 1 ≠ k + 1 := by omega
      simpa only [levels, Function.update_of_ne hne] using P.seed_width (by omega)
  · intro U hk
    have hc : U.val.card ≠ k + 1 := by omega
    have he : entries U = P.entry U := if_neg hc
    rw [he]
    by_cases heq : U.val.card + 1 = k + 1
    · simpa only [levels, heq, Function.update_self] using hwidth U
    · simpa only [levels, Function.update_of_ne heq] using
        P.next_width U (by omega)

theorem AffineSupportPrefix.exists_successor {d k : ℕ} {t b : ℝ} {E : State d → ℝ}
    (P : AffineSupportPrefix d t b E k) (htb : t < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hIH : ∀ n : ℕ, 0 < n → n < d → AffineApproximationInDimension n) :
    Nonempty (AffineSupportPrefix d t b E (k + 1)) :=
  P.exists_successor_of_oracle htb hE (supportFamilyOracle_of_lower_dimensions E hE hIH)

theorem exists_affineSupportPrefix_of_oracle {d : ℕ} {t b : ℝ}
    (E : State d → ℝ) (htb : t < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hOracle : SupportFamilyOracle d t b E) (k : ℕ) :
    Nonempty (AffineSupportPrefix d t b E k) := by
  induction k with
  | zero => exact ⟨AffineSupportPrefix.initial E htb.le⟩
  | succ k ih =>
    obtain ⟨P⟩ := ih
    exact P.exists_successor_of_oracle htb hE hOracle

theorem exists_affineSupportPrefix {d : ℕ} {t b : ℝ} (E : State d → ℝ) (htb : t < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hIH : ∀ n : ℕ, 0 < n → n < d → AffineApproximationInDimension n) (k : ℕ) :
    Nonempty (AffineSupportPrefix d t b E k) :=
  exists_affineSupportPrefix_of_oracle E htb hE
    (supportFamilyOracle_of_lower_dimensions E hE hIH) k

noncomputable def AffineSupportPrefix.toFixedMinimumData {d : ℕ} {t b : ℝ}
    {E : State d → ℝ} (P : AffineSupportPrefix d t b E (d - 1)) (hd : 1 < d) :
    FixedMinimumData d t b E where
  size U := (P.entry U).1
  size_pos := P.size_pos
  block U := (P.entry U).2
  level := P.level
  level_gt U := (P.level_bounds U.val.card U.property.1 (by have := U.property.2; omega)).1
  level_desc U hn := P.descending U.val.card U.property.1 (by omega)
  cube U := (P.selected U (by have := U.property.2; omega)).1
  decay U := (P.selected U (by have := U.property.2; omega)).2.1
  approximation U := (P.selected U (by have := U.property.2; omega)).2.2
  seed_width := P.seed_width (by omega)
  next_width U hn := P.next_width U (by omega)

/-- The supplied-data hypothesis of the assembly theorem is now constructed
from the lower-dimensional induction hypothesis, for arbitrary preselected E. -/
theorem exists_fixedMinimumData_of_oracle {d : ℕ} {t b : ℝ}
    (E : State d → ℝ) (hd : 1 < d) (htb : t < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hOracle : SupportFamilyOracle d t b E) :
    Nonempty (FixedMinimumData d t b E) := by
  obtain ⟨P⟩ := exists_affineSupportPrefix_of_oracle E htb hE hOracle (d - 1)
  exact ⟨P.toFixedMinimumData hd⟩

theorem exists_fixedMinimumData_of_lower_dimensions {d : ℕ} {t b : ℝ}
    (E : State d → ℝ) (hd : 1 < d) (htb : t < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hIH : ∀ n : ℕ, 0 < n → n < d → AffineApproximationInDimension n) :
    Nonempty (FixedMinimumData d t b E) :=
  exists_fixedMinimumData_of_oracle E hd htb hE (supportFamilyOracle_of_lower_dimensions E hE hIH)

end Endotactic
