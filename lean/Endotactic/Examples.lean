import Endotactic.FluxBound

/-! # Definition checks and concrete flux certificates -/

namespace Endotactic.Examples

/-- The network `0 ⇄ A`. -/
def birthDeath : Network 1 (Fin 2) where
  source e := fun _ => if e = 0 then 0 else 1
  target e := fun _ => if e = 0 then 1 else 0

theorem birthDeath_endotactic : birthDeath.IsEndotactic := by
  intro r e he
  fin_cases e
  · refine ⟨1, ?_, ?_⟩ <;>
      simp [birthDeath, Network.projection, Network.vector, Network.sourceLevel,
        realComplex, dot] at * <;> linarith
  · refine ⟨0, ?_, ?_⟩ <;>
      simp [birthDeath, Network.projection, Network.vector, Network.sourceLevel,
        realComplex, dot] at * <;> linarith

/-- A one-way birth reaction fails endotacticity in the opposite direction. -/
def birthOnly : Network 1 (Fin 1) where
  source _ := fun _ => 0
  target _ := fun _ => 1

theorem birthOnly_not_endotactic : ¬ birthOnly.IsEndotactic := by
  intro h
  obtain ⟨e, he, _⟩ := h (fun _ => -1) 0 (by
    norm_num [birthOnly, Network.projection, Network.vector, realComplex, dot])
  norm_num [birthOnly, Network.projection, Network.vector, realComplex, dot] at he

/-- Casting before subtraction preserves a degradation vector. -/
theorem degradation_vector : birthDeath.vector 1 0 = -1 := by
  norm_num [birthDeath, Network.vector, realComplex]

/-- A rational finite-sum witness, with a zero projection deliberately included. -/
theorem explicit_flux_certificate :
    0 < ∑ e : Fin 3,
      (![1, 2, 1] e : ℝ) * (![1, 1 / 100, 7] e : ℝ) * (![1, -2, 0] e : ℝ) := by
  norm_num [Fin.sum_univ_succ]

end Endotactic.Examples
