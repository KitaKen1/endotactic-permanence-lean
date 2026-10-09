import Endotactic.IntegralTrajectory

/-!
# Append a constant cap to an arbitrary finite affine family

The new minimum is `min Q (A.minimum x)`. Its `Q`-plateau is exactly
`A.plateau Q`, and its active branches below `Q` come from the original
family. Thus analytic absorption does not require an a priori upper cap
for the original minimum.
-/

namespace Endotactic

variable {d m : ℕ}

noncomputable def AffineFamily.withCap (A : AffineFamily d m) (Q : ℝ) :
    AffineFamily d (m + 1) where
  slope := Fin.cons 0 A.slope
  offset := Fin.cons Q A.offset

theorem AffineFamily.withCap_value_zero (A : AffineFamily d m) (Q : ℝ) (x : State d) :
    (A.withCap Q).value 0 x = Q := by
  simp [AffineFamily.withCap, AffineFamily.value, dot]

theorem AffineFamily.withCap_value_succ (A : AffineFamily d m) (Q : ℝ)
    (i : Fin m) (x : State d) : (A.withCap Q).value i.succ x = A.value i x := by
  simp [AffineFamily.withCap, AffineFamily.value]

theorem AffineFamily.withCap_plateau (A : AffineFamily d m) (Q : ℝ) :
    (A.withCap Q).plateau Q = A.plateau Q := by
  ext x
  constructor
  · intro hx i
    simpa only [A.withCap_value_succ] using hx i.succ
  · intro hx i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [A.withCap_value_zero]
    · rw [A.withCap_value_succ]
      exact hx j

theorem AffineFamily.withCap_minimum_le (A : AffineFamily d m) (Q : ℝ) (x : State d) :
    (A.withCap Q).minimum x ≤ Q := by
  have hh := finiteMinimum_le (fun i => (A.withCap Q).value i x) 0
  simpa only [AffineFamily.minimum, A.withCap_value_zero] using hh

variable [Nonempty (Fin m)]

theorem AffineFamily.withCap_minimum (A : AffineFamily d m) (Q : ℝ) (x : State d) :
    (A.withCap Q).minimum x = min Q (A.minimum x) := by
  apply le_antisymm
  · apply le_min (A.withCap_minimum_le Q x)
    obtain ⟨i, hi⟩ := finiteMinimum_attained (fun j => A.value j x)
    change A.minimum x = A.value i x at hi
    rw [hi]
    simpa only [AffineFamily.minimum, A.withCap_value_succ] using
      (finiteMinimum_le (fun j => (A.withCap Q).value j x) i.succ)
  · obtain ⟨i, hi⟩ := finiteMinimum_attained (fun j => (A.withCap Q).value j x)
    change (A.withCap Q).minimum x = (A.withCap Q).value i x at hi
    rw [hi]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [A.withCap_value_zero]
      exact min_le_left _ _
    · rw [A.withCap_value_succ]
      exact (min_le_right _ _).trans (finiteMinimum_le (fun j => A.value j x) j)

omit [Nonempty (Fin m)] in
theorem AffineFamily.active_of_withCap_active (A : AffineFamily d m) (Q : ℝ)
    {x : State d} {i : Fin m} (hi : (A.withCap Q).Active i.succ x) : A.Active i x := by
  intro j
  simpa only [A.withCap_value_succ] using hi j.succ

theorem AffineFamily.minimum_lt_of_withCap_active (A : AffineFamily d m) (Q : ℝ)
    {x : State d} {i : Fin m} (hi : (A.withCap Q).Active i.succ x)
    (hmin : (A.withCap Q).minimum x < Q) : A.minimum x < Q := by
  have hh : (A.withCap Q).value i.succ x < Q :=
    ((A.withCap Q).active_iff_minimum_eq i.succ x).mp hi ▸ hmin
  rw [A.withCap_value_succ] at hh
  rw [A.active_iff_minimum_eq i x |>.mp (A.active_of_withCap_active Q hi)]
  exact hh

end Endotactic
