import Endotactic.Network
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Convex.Basic

/-!
# Closed convex plateaux cut out by a finite affine family

The elementary plateau properties are proved independently of family
existence. The general affine theorem is proved downstream in
`MinimumBandSelection`, and `EndotacticInitialTrap` constructs compact
positive initial plateaux from it.
-/

namespace Endotactic

structure AffineFamily (d m : ℕ) where
  slope : Fin m → State d
  offset : Fin m → ℝ

def AffineFamily.value {d m : ℕ} (A : AffineFamily d m) (i : Fin m) (x : State d) : ℝ :=
  dot (A.slope i) x + A.offset i

def AffineFamily.Active {d m : ℕ} (A : AffineFamily d m) (i : Fin m) (x : State d) : Prop :=
  ∀ j, A.value i x ≤ A.value j x

def AffineFamily.plateau {d m : ℕ} (A : AffineFamily d m) (M : ℝ) : Set (State d) :=
  {x | ∀ i, M ≤ A.value i x}

theorem AffineFamily.continuous_value {d m : ℕ} (A : AffineFamily d m) (i : Fin m) :
    Continuous (A.value i) := by
  unfold AffineFamily.value dot
  fun_prop

theorem AffineFamily.plateau_isClosed {d m : ℕ} (A : AffineFamily d m) (M : ℝ) :
    IsClosed (A.plateau M) := by
  have heq : A.plateau M = ⋂ i, {x | M ≤ A.value i x} := by
    ext x
    simp [AffineFamily.plateau]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_le continuous_const (A.continuous_value i)

theorem AffineFamily.value_convex_combination {d m : ℕ} (A : AffineFamily d m)
    (i : Fin m) (x y : State d) {a b : ℝ} (hab : a + b = 1) :
    A.value i (a • x + b • y) = a * A.value i x + b * A.value i y := by
  unfold AffineFamily.value dot
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add]
  rw [Finset.sum_add_distrib]
  have hx : (∑ j, A.slope i j * (a * x j)) = a * ∑ j, A.slope i j * x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy : (∑ j, A.slope i j * (b * y j)) = b * ∑ j, A.slope i j * y j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hx, hy]
  nlinarith [congrArg (fun z : ℝ => z * A.offset i) hab]

theorem AffineFamily.plateau_convex {d m : ℕ} (A : AffineFamily d m) (M : ℝ) :
    Convex ℝ (A.plateau M) := by
  intro x hx y hy a b ha hb hab i
  rw [A.value_convex_combination i x y hab]
  have h₁ := mul_le_mul_of_nonneg_left (hx i) ha
  have h₂ := mul_le_mul_of_nonneg_left (hy i) hb
  nlinarith [congrArg (fun z : ℝ => z * M) hab]

theorem AffineFamily.plateau_isCompact_of_subset {d m : ℕ} (A : AffineFamily d m)
    (M : ℝ) {B : Set (State d)} (hB : IsCompact B) (hsub : A.plateau M ⊆ B) :
    IsCompact (A.plateau M) :=
  hB.of_isClosed_subset (A.plateau_isClosed M) hsub

theorem AffineFamily.constant_value {d m : ℕ} (A : AffineFamily d m) (i : Fin m)
    (hslope : ∀ j, A.slope i j = 0) (x : State d) : A.value i x = A.offset i := by
  simp [AffineFamily.value, dot, hslope]

theorem AffineFamily.constant_active_iff_mem_plateau {d m : ℕ} (A : AffineFamily d m)
    (i : Fin m) (hslope : ∀ j, A.slope i j = 0) (x : State d) :
    A.Active i x ↔ x ∈ A.plateau (A.offset i) := by
  simp [AffineFamily.Active, AffineFamily.plateau, A.constant_value i hslope x]

theorem AffineFamily.active_value_lt_of_notin_plateau {d m : ℕ}
    (A : AffineFamily d m) {M : ℝ} {x : State d} {i : Fin m}
    (hi : A.Active i x) (hx : x ∉ A.plateau M) : A.value i x < M := by
  classical
  change ¬ ∀ j, M ≤ A.value j x at hx
  push Not at hx
  obtain ⟨j, hj⟩ := hx
  exact lt_of_le_of_lt (hi j) hj

/-- A conserved affine branch cannot be active below the plateau. -/
theorem AffineFamily.active_value_ne_at_class_representative {d m : ℕ}
    (A : AffineFamily d m) {M : ℝ} {x c : State d} {i : Fin m}
    (hi : A.Active i x) (hx : x ∉ A.plateau M) (hc : c ∈ A.plateau M) :
    A.value i x ≠ A.value i c := by
  have hlt := A.active_value_lt_of_notin_plateau hi hx
  have hge := hc i
  linarith

end Endotactic
