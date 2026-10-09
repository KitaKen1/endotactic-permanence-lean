import Endotactic.AffineBlockUnion
import Endotactic.MovingPowerAsymptotics

/-!
# Common offset shifts and finite power prefixes

A common shift preserves every minimizing label, including ties. Prefix
shifts give actual adjacent differences; their decay follows from finitely
many strict exponent gaps, without continuity of the original offsets.
-/

namespace Endotactic

open Filter Topology Asymptotics

def ScaledAffineFamily.offsetShift {d m : ℕ} (A : ScaledAffineFamily d m)
    (γ : ℝ → ℝ) : ScaledAffineFamily d m where
  slope := A.slope
  offset i h := γ h + A.offset i h

theorem ScaledAffineFamily.offsetShift_slope {d m : ℕ}
    (A : ScaledAffineFamily d m) (γ : ℝ → ℝ) (i : Fin m) :
    (A.offsetShift γ).slope i = A.slope i := rfl

theorem ScaledAffineFamily.offsetShift_value {d m : ℕ}
    (A : ScaledAffineFamily d m) (γ : ℝ → ℝ) (i : Fin m) (h : ℝ) (x : State d) :
    ((A.offsetShift γ).atScale h).value i x = (A.atScale h).value i x + γ h := by
  simp only [ScaledAffineFamily.atScale_value, offsetShift]
  ring

theorem ScaledAffineFamily.offsetShift_active_iff {d m : ℕ}
    (A : ScaledAffineFamily d m) (γ : ℝ → ℝ) (i : Fin m) (h : ℝ) (x : State d) :
    ((A.offsetShift γ).atScale h).Active i x ↔ (A.atScale h).Active i x := by
  change (∀ j, _ ≤ _) ↔ (∀ j, _ ≤ _)
  simp only [A.offsetShift_value, add_le_add_iff_right]

theorem ScaledAffineFamily.offsetShift_sequentialActivityBound {d m : ℕ}
    (A : ScaledAffineFamily d m) (γ : ℝ → ℝ) (K : Set (State d)) (ε : Fin m → ℝ) :
    (A.offsetShift γ).HasSequentialActivityBound K ε ↔
      A.HasSequentialActivityBound K ε := by
  simp only [HasSequentialActivityBound, A.offsetShift_slope, A.offsetShift_active_iff]

theorem ScaledAffineFamily.offsetShift_offsets_isLittleO {d m : ℕ}
    (A : ScaledAffineFamily d m) (γ : ℝ → ℝ) (a : ℝ)
    (hγ : IsLittleO (𝓝[>] (0 : ℝ)) γ (fun h => h ^ a))
    (hA : ∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) :
    ∀ i, IsLittleO (𝓝[>] (0 : ℝ)) ((A.offsetShift γ).offset i) (fun h => h ^ a) :=
  fun i => hγ.add (hA i)

noncomputable def powerPrefixShift (cut : ℕ → ℝ) (k : ℕ) (h : ℝ) : ℝ :=
  -(∑ j ∈ Finset.range k, h ^ cut j)

theorem powerPrefixShift_zero (cut : ℕ → ℝ) (h : ℝ) : powerPrefixShift cut 0 h = 0 := by
  simp [powerPrefixShift]

theorem powerPrefixShift_succ (cut : ℕ → ℝ) (k : ℕ) (h : ℝ) :
    powerPrefixShift cut (k + 1) h = powerPrefixShift cut k h - h ^ cut k := by
  simp only [powerPrefixShift, Finset.sum_range_succ]
  ring

theorem powerPrefixShift_isLittleO (cut : ℕ → ℝ) (k : ℕ) (a : ℝ)
    (hcut : ∀ j < k, a < cut j) :
    IsLittleO (𝓝[>] (0 : ℝ)) (powerPrefixShift cut k) (fun h => h ^ a) := by
  induction k with
  | zero =>
    change IsLittleO (𝓝[>] (0 : ℝ)) (fun h => powerPrefixShift cut 0 h) (fun h => h ^ a)
    simpa only [powerPrefixShift_zero] using
      (isLittleO_zero (fun h : ℝ => h ^ a) (𝓝[>] (0 : ℝ)) :
        IsLittleO (𝓝[>] (0 : ℝ)) (fun _ => (0 : ℝ)) (fun h => h ^ a))
  | succ k ih =>
    have h := (ih (fun j hj => hcut j (by omega))).sub
      (rpow_isLittleO_nhdsGT_zero (hcut k (by omega)))
    change IsLittleO (𝓝[>] (0 : ℝ)) (fun h => powerPrefixShift cut (k + 1) h)
      (fun h => h ^ a)
    simpa only [powerPrefixShift_succ] using h

theorem offset_isLittleO_of_le_power {c : ℝ → ℝ} {a b : ℝ}
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ b)) (hab : a ≤ b) :
    IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ a) := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · simpa only [heq] using hc
  · exact hc.trans (rpow_isLittleO_nhdsGT_zero hlt)

end Endotactic
