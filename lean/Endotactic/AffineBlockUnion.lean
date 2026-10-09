import Endotactic.FiniteLiftTolerance
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual finite unions of scale-dependent affine blocks

A dependent finite label type retains the block and local label, then an
equivalence encodes it as Fin for the existing affine API. No label is dropped,
including duplicates or ties. Global activity implies local block activity;
the converse additionally needs every cross-block comparison.
-/

namespace Endotactic

open Filter Topology Asymptotics

noncomputable def affineBlockLabel {I : Type*} [Fintype I]
    (m : I → ℕ) (b : I) (i : Fin (m b)) : Fin (Fintype.card (Σ b, Fin (m b))) :=
  Fintype.equivFin _ ⟨b, i⟩

noncomputable def ScaledAffineFamily.blockUnion {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) :
    ScaledAffineFamily d (Fintype.card (Σ b, Fin (m b))) where
  slope j := let l := (Fintype.equivFin (Σ b, Fin (m b))).symm j
    (A l.1).slope l.2
  offset j h := let l := (Fintype.equivFin (Σ b, Fin (m b))).symm j
    (A l.1).offset l.2 h

theorem affineBlockLabel_decode {I : Type*} [Fintype I]
    (m : I → ℕ) (b : I) (i : Fin (m b)) :
    (Fintype.equivFin (Σ b, Fin (m b))).symm (affineBlockLabel m b i) = ⟨b, i⟩ :=
  (Fintype.equivFin _).symm_apply_apply _

theorem affineBlockLabel_surjective {I : Type*} [Fintype I] (m : I → ℕ)
    (j : Fin (Fintype.card (Σ b, Fin (m b)))) :
    ∃ b i, affineBlockLabel m b i = j := by
  let l := (Fintype.equivFin (Σ b, Fin (m b))).symm j
  exact ⟨l.1, l.2, (Fintype.equivFin _).apply_symm_apply j⟩

theorem affineBlockLabel_injective {I : Type*} [Fintype I]
    (m : I → ℕ) (b : I) : Function.Injective (affineBlockLabel m b) := by
  intro i j hij
  have heq := (Fintype.equivFin (Σ b, Fin (m b))).injective hij
  exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2

theorem affineBlockLabel_card_pos {I : Type*} [Fintype I]
    (m : I → ℕ) (b : I) (hb : 0 < m b) : 0 < Fintype.card (Σ b, Fin (m b)) :=
  Fintype.card_pos_iff.mpr ⟨⟨b, ⟨0, hb⟩⟩⟩

theorem ScaledAffineFamily.blockUnion_slope {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) (b : I) (i : Fin (m b)) :
    (ScaledAffineFamily.blockUnion m A).slope (affineBlockLabel m b i) = (A b).slope i := by
  change (A ((Fintype.equivFin (Σ b, Fin (m b))).symm (affineBlockLabel m b i)).1).slope
    ((Fintype.equivFin (Σ b, Fin (m b))).symm (affineBlockLabel m b i)).2 = _
  rw [affineBlockLabel_decode]

theorem ScaledAffineFamily.blockUnion_offset {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) (b : I) (i : Fin (m b)) (h : ℝ) :
    (ScaledAffineFamily.blockUnion m A).offset (affineBlockLabel m b i) h =
      (A b).offset i h := by
  change (A ((Fintype.equivFin (Σ b, Fin (m b))).symm (affineBlockLabel m b i)).1).offset
    ((Fintype.equivFin (Σ b, Fin (m b))).symm (affineBlockLabel m b i)).2 h = _
  rw [affineBlockLabel_decode]

theorem ScaledAffineFamily.blockUnion_value {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b))
    (b : I) (i : Fin (m b)) (h : ℝ) (x : State d) :
    ((ScaledAffineFamily.blockUnion m A).atScale h).value (affineBlockLabel m b i) x =
      ((A b).atScale h).value i x := by
  simp only [ScaledAffineFamily.atScale_value, ScaledAffineFamily.blockUnion_slope,
    ScaledAffineFamily.blockUnion_offset]

theorem ScaledAffineFamily.blockUnion_active_iff {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b))
    (b : I) (i : Fin (m b)) (h : ℝ) (x : State d) :
    ((ScaledAffineFamily.blockUnion m A).atScale h).Active (affineBlockLabel m b i) x ↔
      ∀ c j, ((A b).atScale h).value i x ≤ ((A c).atScale h).value j x := by
  constructor
  · intro hi c j
    simpa only [ScaledAffineFamily.blockUnion_value] using hi (affineBlockLabel m c j)
  · intro hi j
    obtain ⟨c, l, rfl⟩ := affineBlockLabel_surjective m j
    simpa only [ScaledAffineFamily.blockUnion_value] using hi c l

theorem ScaledAffineFamily.blockUnion_active_in_block {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b))
    (b : I) (i : Fin (m b)) (h : ℝ) (x : State d)
    (hi : ((ScaledAffineFamily.blockUnion m A).atScale h).Active
      (affineBlockLabel m b i) x) : ((A b).atScale h).Active i x :=
  fun j => (ScaledAffineFamily.blockUnion_active_iff m A b i h x).mp hi b j

theorem ScaledAffineFamily.blockUnion_plateau {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) (h M : ℝ) :
    ((ScaledAffineFamily.blockUnion m A).atScale h).plateau M =
      ⋂ b, ((A b).atScale h).plateau M := by
  ext x
  simp only [Set.mem_iInter, AffineFamily.plateau, Set.mem_ofPred_eq]
  constructor
  · intro hx b i
    simpa only [ScaledAffineFamily.blockUnion_value] using hx (affineBlockLabel m b i)
  · intro hx j
    obtain ⟨b, i, rfl⟩ := affineBlockLabel_surjective m j
    simpa only [ScaledAffineFamily.blockUnion_value] using hx b i

theorem ScaledAffineFamily.blockUnion_slopes_mem {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) (K : Set (State d))
    (hA : ∀ b i, (A b).slope i ∈ K) :
    ∀ j, (ScaledAffineFamily.blockUnion m A).slope j ∈ K := by
  intro j
  obtain ⟨b, i, rfl⟩ := affineBlockLabel_surjective m j
  rw [ScaledAffineFamily.blockUnion_slope]
  exact hA b i

theorem ScaledAffineFamily.blockUnion_offsets_isLittleO {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) (a : ℝ)
    (hA : ∀ b i, IsLittleO (𝓝[>] (0 : ℝ)) ((A b).offset i) (fun h => h ^ a)) :
    ∀ j, IsLittleO (𝓝[>] (0 : ℝ)) ((ScaledAffineFamily.blockUnion m A).offset j)
      (fun h => h ^ a) := by
  intro j
  obtain ⟨b, i, rfl⟩ := affineBlockLabel_surjective m j
  have heq : (ScaledAffineFamily.blockUnion m A).offset (affineBlockLabel m b i) =
      (A b).offset i := funext fun h => ScaledAffineFamily.blockUnion_offset m A b i h
  rw [heq]
  exact hA b i

/-- This closure rule is useful when every block already works on the same
domain. Type-specific construction instead uses cross-block competitors. -/
theorem ScaledAffineFamily.blockUnion_sequentialActivityBound
    {d : ℕ} {I : Type*} [Fintype I] (m : I → ℕ)
    (A : ∀ b, ScaledAffineFamily d (m b)) (K : Set (State d)) (E : State d → ℝ)
    (hA : ∀ b, (A b).HasSequentialActivityBound K (fun i => E ((A b).slope i))) :
    (ScaledAffineFamily.blockUnion m A).HasSequentialActivityBound K
      (fun j => E ((ScaledAffineFamily.blockUnion m A).slope j)) := by
  intro j h p q hpos hh hp hq hactive
  obtain ⟨b, i, rfl⟩ := affineBlockLabel_surjective m j
  change ‖q - (ScaledAffineFamily.blockUnion m A).slope (affineBlockLabel m b i)‖ <
    E ((ScaledAffineFamily.blockUnion m A).slope (affineBlockLabel m b i))
  rw [ScaledAffineFamily.blockUnion_slope]
  exact hA b i h p q hpos hh hp hq (fun n =>
    ScaledAffineFamily.blockUnion_active_in_block m A b i (h n) _ (hactive n))

end Endotactic
