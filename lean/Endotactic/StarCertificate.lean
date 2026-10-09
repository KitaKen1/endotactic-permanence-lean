import Endotactic.Network
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# A known-answer rational boundary certificate

The reversible star `0 ⇄ A`, `2 A ⇄ B`, with all four coefficients in `[1,2]`,
has the candidate polygon
`x ≥ 1/8`, `1/256 ≤ y ≤ 256`, `x + 2*y ≤ 520`.
Every face inequality below holds for ALL states on the face and ALL coefficients
in the box. No numerical sampling or vertex-only polynomial check is used.

These are boundary certificates. Their ODE invariance, positive global
well-posedness and common-set absorption are proved in `StarGlobalExistence`,
`StarInitialTrap` and `StarPermanence`.
-/

namespace Endotactic.StarCertificate

def star : Network 2 (Fin 4) where
  source := ![![0, 0], ![1, 0], ![2, 0], ![0, 1]]
  target := ![![1, 0], ![0, 0], ![0, 1], ![2, 0]]

def fx (a b c d x y : ℝ) : ℝ := a - b * x - 2 * c * x ^ 2 + 2 * d * y
def fy (c d x y : ℝ) : ℝ := c * x ^ 2 - d * y

def RateBox (a b c d : ℝ) : Prop :=
  1 ≤ a ∧ a ≤ 2 ∧ 1 ≤ b ∧ b ≤ 2 ∧ 1 ≤ c ∧ c ≤ 2 ∧ 1 ≤ d ∧ d ≤ 2

def polygon : Set (State 2) :=
  {z | (1 : ℝ) / 8 ≤ z 0 ∧ 1 / 256 ≤ z 1 ∧ z 1 ≤ 256 ∧ z 0 + 2 * z 1 ≤ 520}

theorem polygon_nonempty : polygon.Nonempty := by
  refine ⟨![1, 1], ?_⟩
  norm_num [polygon]

theorem polygon_subset_positive : polygon ⊆ {z | Positive z} := by
  intro z hz i
  fin_cases i
  · have := hz.1
    change 0 < z 0
    linarith
  · have := hz.2.1
    change 0 < z 1
    linarith

theorem polygon_isCompact : IsCompact polygon := by
  have hclosed : IsClosed polygon := by
    change IsClosed ({z : State 2 | (1 : ℝ) / 8 ≤ z 0} ∩
      ({z : State 2 | (1 : ℝ) / 256 ≤ z 1} ∩
        ({z : State 2 | z 1 ≤ 256} ∩ {z : State 2 | z 0 + 2 * z 1 ≤ 520})))
    exact (isClosed_le continuous_const (continuous_apply 0)).inter
      ((isClosed_le continuous_const (continuous_apply 1)).inter
        ((isClosed_le (continuous_apply 1) continuous_const).inter
          (isClosed_le (by fun_prop) continuous_const)))
  apply (isCompact_Icc (a := (![1 / 8, 1 / 256] : State 2))
    (b := ![520, 256])).of_isClosed_subset hclosed
  intro z hz
  constructor
  · intro i
    fin_cases i
    · change (1 : ℝ) / 8 ≤ z 0
      exact hz.1
    · change (1 : ℝ) / 256 ≤ z 1
      exact hz.2.1
  · intro i
    fin_cases i
    · change z 0 ≤ 520
      have := hz.2.2.2
      have := hz.2.1
      linarith
    · change z 1 ≤ 256
      exact hz.2.2.1

theorem rhs_coordinates (a b c d x y : ℝ) :
    star.rhs ![a, b, c, d] ![x, y] = ![fx a b c d x y, fy c d x y] := by
  ext i
  fin_cases i <;>
    simp [star, Network.rhs, Network.vector, realComplex, monomial,
      Fin.sum_univ_succ, Fin.prod_univ_succ, fx, fy] <;> ring

theorem star_endotactic : star.IsEndotactic := by
  intro r e he
  fin_cases e
  · refine ⟨1, ?_, ?_⟩ <;>
      simp [star, Network.projection, Network.vector, Network.sourceLevel,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith
  · refine ⟨0, ?_, ?_⟩ <;>
      simp [star, Network.projection, Network.vector, Network.sourceLevel,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith
  · refine ⟨3, ?_, ?_⟩ <;>
      simp [star, Network.projection, Network.vector, Network.sourceLevel,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith
  · refine ⟨2, ?_, ?_⟩ <;>
      simp [star, Network.projection, Network.vector, Network.sourceLevel,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith

theorem lower_x_face {a b c d y : ℝ} (hk : RateBox a b c d)
    (hy : 1 / 256 ≤ y) : (89 : ℝ) / 128 ≤ fx a b c d (1 / 8) y := by
  rcases hk with ⟨ha, _, _, hb, _, hc, hd, _⟩
  have hy0 : 0 ≤ y := by linarith
  have hdy : y ≤ d * y := by
    simpa using mul_le_mul_of_nonneg_right hd hy0
  unfold fx
  nlinarith

theorem lower_y_face {a b c d x : ℝ} (hk : RateBox a b c d)
    (hx : 1 / 8 ≤ x) : (1 : ℝ) / 128 ≤ fy c d x (1 / 256) := by
  rcases hk with ⟨_, _, _, _, hc, _, _, hd⟩
  have hsq : (1 : ℝ) / 64 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1 / 8)]
  have hcx : x ^ 2 ≤ c * x ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right hc (sq_nonneg x)
  unfold fy
  nlinarith

theorem upper_y_face {a b c d x : ℝ} (hk : RateBox a b c d)
    (hx0 : 0 ≤ x) (hx8 : x ≤ 8) : (128 : ℝ) ≤ -fy c d x 256 := by
  rcases hk with ⟨_, _, _, _, _, hc, hd, _⟩
  have hsq : x ^ 2 ≤ 64 := by
    have hp := mul_nonneg hx0 (show 0 ≤ 8 - x by linarith)
    nlinarith
  have hcx := mul_le_mul_of_nonneg_right hc (sq_nonneg x)
  unfold fy
  nlinarith

theorem mass_identity (a b c d x y : ℝ) :
    fx a b c d x y + 2 * fy c d x y = a - b * x := by
  unfold fx fy
  ring

theorem upper_mass_face {a b c d x y : ℝ} (hk : RateBox a b c d)
    (hy : y ≤ 256) (hface : x + 2 * y = 520) :
    (6 : ℝ) ≤ -(fx a b c d x y + 2 * fy c d x y) := by
  rcases hk with ⟨_, ha, hb, _, _, _, _, _⟩
  have hx8 : 8 ≤ x := by linarith
  have hbx : x ≤ b * x := by
    simpa using mul_le_mul_of_nonneg_right hb (show 0 ≤ x by linarith)
  rw [mass_identity]
  linarith

end Endotactic.StarCertificate
