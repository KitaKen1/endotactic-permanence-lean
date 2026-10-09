import Endotactic.ScaleTrapConstruction

/-!
# General finite natural-exponent endotactic permanence

The compact absorbing set is chosen before rates and positive initial states
in the class. The scale family and every connection are constructed from
endotacticity and the proved affine approximation theorem. The conclusions
use exactly the previously declared conjecture types.

Independent comparison with the original informal conventions and clean
reproduction remain separate audit tasks; no literature novelty is claimed.
-/

namespace Endotactic

theorem Network.uniformPermanent_of_endotactic {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (hd : 0 < d) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    {c : State d} (hc : Positive c) : N.UniformPermanent ℓ u c (fun _ => True) := by
  obtain ⟨m, hm, ⟨D⟩⟩ := N.exists_scaleTrapFamily hN hd hℓ hu hc
  let : NeZero m := ⟨by omega⟩
  exact D.uniformPermanent

theorem measurable_extended_permanence : MeasurableExtendedPermanenceConjecture := by
  intro d m hd N hN ℓ u hℓ hu c hc
  exact N.uniformPermanent_of_endotactic hN hd hℓ ((hℓ.trans_le hu).le) hc

theorem extended_permanence : ExtendedPermanenceConjecture :=
  measurable_conjecture_implies_extended measurable_extended_permanence

theorem original_extended_permanence : OriginalExtendedPermanenceConjecture :=
  uniform_extended_conjecture_implies_original extended_permanence

end Endotactic
