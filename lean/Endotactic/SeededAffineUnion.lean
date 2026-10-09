import Endotactic.AffineBlockUnion
import Endotactic.AffineActiveCompetitors
import Endotactic.FixedMinimumSeeds

/-!
# A genuine union containing the minimum seed and every supplied block

Option I indexes the zero-offset constant-slope seed and all supplied finite
blocks. This constructs the union even for empty I, and transfers its actual
activity into each block. Choosing all required inductive blocks is separate.
-/

namespace Endotactic

open Filter Topology Asymptotics

abbrev seededAffineSizes {I : Type*} (m : I → ℕ) : Option I → ℕ
  | none => 1
  | some b => m b

def seededAffineBlocks {d : ℕ} {I : Type*} (t : ℝ) (m : I → ℕ)
    (A : ∀ b, ScaledAffineFamily d (m b)) :
    ∀ b, ScaledAffineFamily d (seededAffineSizes m b)
  | none => minimumSeedFamily d t
  | some b => A b

noncomputable def seededAffineSeed {I : Type*} [Fintype I] (m : I → ℕ) :
    Fin (Fintype.card (Σ b : Option I, Fin (seededAffineSizes m b))) :=
  affineBlockLabel (seededAffineSizes m) none 0

noncomputable def seededAffineLabel {I : Type*} [Fintype I] (m : I → ℕ)
    (b : I) (i : Fin (m b)) :
    Fin (Fintype.card (Σ b : Option I, Fin (seededAffineSizes m b))) :=
  affineBlockLabel (seededAffineSizes m) (some b) i

noncomputable def ScaledAffineFamily.seededUnion {d : ℕ} {I : Type*} [Fintype I]
    (t : ℝ) (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) :=
  ScaledAffineFamily.blockUnion (seededAffineSizes m) (seededAffineBlocks t m A)

theorem seededAffine_card_pos {I : Type*} [Fintype I] (m : I → ℕ) :
    0 < Fintype.card (Σ b : Option I, Fin (seededAffineSizes m b)) :=
  affineBlockLabel_card_pos (seededAffineSizes m) none (by norm_num [seededAffineSizes])

theorem ScaledAffineFamily.seededUnion_seed_slope {d : ℕ} {I : Type*} [Fintype I]
    (t : ℝ) (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) :
    (ScaledAffineFamily.seededUnion t m A).slope (seededAffineSeed m) = fun _ => t := by
  rw [ScaledAffineFamily.seededUnion, seededAffineSeed, ScaledAffineFamily.blockUnion_slope]
  rfl

theorem ScaledAffineFamily.seededUnion_seed_offset {d : ℕ} {I : Type*} [Fintype I]
    (t : ℝ) (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) (h : ℝ) :
    (ScaledAffineFamily.seededUnion t m A).offset (seededAffineSeed m) h = 0 := by
  rw [ScaledAffineFamily.seededUnion, seededAffineSeed, ScaledAffineFamily.blockUnion_offset]
  rfl

theorem ScaledAffineFamily.seededUnion_block_slope {d : ℕ} {I : Type*} [Fintype I]
    (t : ℝ) (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) (b : I) (i : Fin (m b)) :
    (ScaledAffineFamily.seededUnion t m A).slope (seededAffineLabel m b i) =
      (A b).slope i := by
  rw [ScaledAffineFamily.seededUnion, seededAffineLabel, ScaledAffineFamily.blockUnion_slope]
  rfl

theorem ScaledAffineFamily.seededUnion_block_offset {d : ℕ} {I : Type*} [Fintype I]
    (t : ℝ) (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b))
    (b : I) (i : Fin (m b)) (h : ℝ) :
    (ScaledAffineFamily.seededUnion t m A).offset (seededAffineLabel m b i) h =
      (A b).offset i h := by
  rw [ScaledAffineFamily.seededUnion, seededAffineLabel, ScaledAffineFamily.blockUnion_offset]
  rfl

theorem ScaledAffineFamily.seededUnion_active_in_block {d : ℕ} {I : Type*} [Fintype I]
    (t : ℝ) (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b))
    (b : I) (i : Fin (m b)) (h : ℝ) (x : State d)
    (hi : ((ScaledAffineFamily.seededUnion t m A).atScale h).Active
      (seededAffineLabel m b i) x) : ((A b).atScale h).Active i x :=
  ScaledAffineFamily.blockUnion_active_in_block (seededAffineSizes m)
    (seededAffineBlocks t m A) (some b) i h x hi

theorem ScaledAffineFamily.seededUnion_projected_active
    {k d : ℕ} {I : Type*} [Fintype I] (t : ℝ) (m : I → ℕ)
    (A : ∀ b, ScaledAffineFamily d (m b)) (b : I)
    (B : ScaledAffineFamily k (m b)) (e : Fin k ↪ Fin d) (γ : ℝ → ℝ)
    (hB : A b = B.coordinateLift e t γ) (i : Fin (m b)) (h : ℝ) (p : State d)
    (hi : ((ScaledAffineFamily.seededUnion t m A).atScale h).Active
      (seededAffineLabel m b i) (exponentialPoint h p)) :
    (B.atScale h).Active i (exponentialPoint h (restrictCoordinates e p)) := by
  have hlocal := ScaledAffineFamily.seededUnion_active_in_block t m A b i h _ hi
  rw [hB, B.coordinateLift_exponential_active_iff] at hlocal
  exact hlocal

theorem ScaledAffineFamily.seededUnion_slopes_mem_cube
    {d : ℕ} {I : Type*} [Fintype I] (m : I → ℕ)
    (A : ∀ b, ScaledAffineFamily d (m b)) {a b t : ℝ} (ht : t ∈ Set.Icc a b)
    (hA : ∀ c i, (A c).slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) :
    ∀ j, (ScaledAffineFamily.seededUnion t m A).slope j ∈
      Set.Icc (fun _ => a) (fun _ => b) := by
  apply ScaledAffineFamily.blockUnion_slopes_mem
  intro c i
  cases c with
  | none => exact ⟨fun _ => ht.1, fun _ => ht.2⟩
  | some c => exact hA c i

theorem ScaledAffineFamily.seededUnion_offsets_isLittleO
    {d : ℕ} {I : Type*} [Fintype I] (t : ℝ) (m : I → ℕ)
    (A : ∀ b, ScaledAffineFamily d (m b)) (a : ℝ)
    (hA : ∀ b i, IsLittleO (𝓝[>] (0 : ℝ)) ((A b).offset i) (fun h => h ^ a)) :
    ∀ j, IsLittleO (𝓝[>] (0 : ℝ)) ((ScaledAffineFamily.seededUnion t m A).offset j)
      (fun h => h ^ a) := by
  apply ScaledAffineFamily.blockUnion_offsets_isLittleO
  intro b i
  cases b with
  | none => exact isLittleO_zero _ _
  | some b => exact hA b i

end Endotactic
