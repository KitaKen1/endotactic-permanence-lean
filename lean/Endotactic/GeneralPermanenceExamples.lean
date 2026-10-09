import Endotactic.GeneralPermanence
import Endotactic.DirectionalWallCounterexample
import Endotactic.ConversionPermanence

/-!
# Generic permanence on a nonlinear system and a conserved class

These applications use only the previously checked endotacticity proof,
with no hand-selected absorbing certificate or explicit ODE solution.
-/

namespace Endotactic.GeneralExamples

theorem nonlinear_uniformPermanent {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : ℓ ≤ u)
    {c : State 2} (hc : Positive c) :
    DirectionalWall.network.UniformPermanent ℓ u c (fun _ => True) :=
  DirectionalWall.network.uniformPermanent_of_endotactic DirectionalWall.network_endotactic
    (by norm_num) hℓ ((hℓ.trans_le hu).le) hc

theorem conserved_uniformPermanent {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : ℓ ≤ u)
    {c : State 2} (hc : Positive c) :
    Conversion.conversion.UniformPermanent ℓ u c (fun _ => True) :=
  Conversion.conversion.uniformPermanent_of_endotactic Conversion.isEndotactic
    (by norm_num) hℓ ((hℓ.trans_le hu).le) hc

end Endotactic.GeneralExamples
