import Endotactic.CoordinateEmbedding
import Mathlib.Data.Finset.Sort

/-!
# All nonempty proper coordinate supports

The finite subtype contains every raised type. Its ordered embedding has
exactly the specified range. Inserting an omitted coordinate supplies the
next type unless only one coordinate was omitted.
-/

namespace Endotactic

abbrev RaisedSupport (d : ℕ) :=
  {U : Finset (Fin d) // 0 < U.card ∧ U.card < d}

def RaisedSupport.embedding {d : ℕ} (U : RaisedSupport d) : Fin U.val.card ↪ Fin d :=
  (U.val.orderEmbOfFin rfl).toEmbedding

theorem RaisedSupport.embedding_range {d : ℕ} (U : RaisedSupport d) :
    Set.range U.embedding = (U.val : Set (Fin d)) :=
  Finset.range_orderEmbOfFin U.val rfl

theorem RaisedSupport.embedding_mem {d : ℕ} (U : RaisedSupport d)
    (i : Fin U.val.card) : U.embedding i ∈ U.val :=
  Finset.orderEmbOfFin_mem U.val rfl i

theorem RaisedSupport.mem_iff_range {d : ℕ} (U : RaisedSupport d) (j : Fin d) :
    j ∈ U.val ↔ j ∈ Set.range U.embedding := by
  rw [U.embedding_range]
  rfl

def RaisedSupport.singleton {d : ℕ} (hd : 1 < d) (j : Fin d) : RaisedSupport d :=
  ⟨{j}, by simpa using And.intro Nat.zero_lt_one hd⟩

theorem RaisedSupport.singleton_card {d : ℕ} (hd : 1 < d) (j : Fin d) :
    (RaisedSupport.singleton hd j).val.card = 1 := Finset.card_singleton j

def RaisedSupport.insert {d : ℕ} (U : RaisedSupport d) (j : Fin d)
    (hj : j ∉ U.val) (hnext : U.val.card + 1 < d) : RaisedSupport d :=
  ⟨Insert.insert j U.val, by rw [Finset.card_insert_of_notMem hj]; exact ⟨by omega, hnext⟩⟩

theorem RaisedSupport.insert_card {d : ℕ} (U : RaisedSupport d) (j : Fin d)
    (hj : j ∉ U.val) (hnext : U.val.card + 1 < d) :
    (U.insert j hj hnext).val.card = U.val.card + 1 :=
  Finset.card_insert_of_notMem hj

theorem RaisedSupport.omitted_exists {d : ℕ} (U : RaisedSupport d) :
    ∃ j : Fin d, j ∉ U.val := by
  by_contra hn
  have heq : U.val = Finset.univ := Finset.eq_univ_iff_forall.mpr (by simpa using hn)
  have hcard := U.property.2
  simp only [heq, Finset.card_univ, Fintype.card_fin] at hcard
  omega

theorem RaisedSupport.last_omitted_unique {d : ℕ} (U : RaisedSupport d)
    (hlast : U.val.card + 1 = d) (j : Fin d) (hj : j ∉ U.val) :
    ∀ l ∉ U.val, l = j := by
  have hc : U.valᶜ.card = 1 := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨l, hl⟩ := Finset.card_eq_one.mp hc
  have hjl : j = l := by simpa only [hl, Finset.mem_singleton] using
    (Finset.mem_compl.mpr hj)
  intro k hk
  have hkl : k = l := by simpa only [hl, Finset.mem_singleton] using
    (Finset.mem_compl.mpr hk)
  exact hkl.trans hjl.symm

theorem RaisedSupport.last_omitted_eq_minimum {d : ℕ} [NeZero d]
    (U : RaisedSupport d) (hlast : U.val.card + 1 = d)
    {q : State d} {t : ℝ} (hminimum : exponentMinimum q = t)
    (hraised : ∀ j ∈ U.val, t < q j) (j : Fin d) (hj : j ∉ U.val) : q j = t := by
  apply omitted_coordinate_eq_minimum U.embedding j hminimum
  · intro i
    exact hraised _ (U.embedding_mem i)
  · intro l hl
    exact U.last_omitted_unique hlast j hj l ((U.mem_iff_range l).not.mpr hl)

end Endotactic
