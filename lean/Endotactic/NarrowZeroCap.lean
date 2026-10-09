import Endotactic.ScaledZeroCap
import Endotactic.PowerBoxGeometry

/-!
# Narrow zero-cap plateaux and transfer of zero active labels
-/

namespace Endotactic

theorem AffineFamily.active_zero_transfer {d m : ℕ} (A : AffineFamily d m)
    {i j : Fin m} {c z : State d} (hi : ∀ k, A.slope i k = 0)
    (hj : ∀ k, A.slope j k = 0) (hic : A.Active i c) (hjz : A.Active j z) :
    A.Active i z := by
  have hij : A.value i z ≤ A.value j z := by
    simpa only [A.constant_value i hi, A.constant_value j hj] using hic j
  exact fun k => hij.trans (hjz k)

theorem ScaledAffineFamily.zero_cap_plateau_subset_open_power_box {d m : ℕ}
    (A : ScaledAffineFamily d m) {h β : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (i₀ : Fin m) (hi₀ : A.slope i₀ = 0)
    {z : State d} (hz : (A.atScale h).Active i₀ z)
    (hzbox : z ∈ openCoordinateBox (fun _ => h ^ β) (fun _ => (h ^ β)⁻¹))
    (hactive : ∀ p ∈ Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
      (A.atScale h).Active i₀ (exponentialPoint h p) → ‖p‖ < β) :
    (A.atScale h).plateau (A.offset i₀ h) ⊆
      openCoordinateBox (fun _ => h ^ β) (fun _ => (h ^ β)⁻¹) := by
  have hslope : ∀ j, (A.atScale h).slope i₀ j = 0 := fun j => congrFun hi₀ j
  have hzK := ((A.atScale h).constant_active_iff_mem_plateau i₀ hslope z).mp hz
  apply convex_subset_open_box_of_no_boundary ((A.atScale h).plateau_convex _) hzK hzbox
  intro x hx hbox
  by_contra hboundary
  have hxpos : Positive x := powerBox_positive hh hbox
  have hpow := exponentialPoint_logarithmicExponent hh hh1 hxpos
  have hi := ((A.atScale h).constant_active_iff_mem_plateau i₀ hslope x).mpr hx
  have hp := logarithmicExponent_mem_power_cube hh hh1 hβ hbox
  have hpcube : logarithmicExponent h x ∈
      Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) :=
    ⟨fun j => (neg_le_neg hβ1).trans (hp.1 j), fun j => (hp.2 j).trans hβ1⟩
  have hlt := hactive (logarithmicExponent h x) hpcube (hpow.symm ▸ hi)
  exact (not_lt_of_ge (logarithmicExponent_power_boundary_norm hh hh1 hβ hbox hboundary)) hlt

end Endotactic
