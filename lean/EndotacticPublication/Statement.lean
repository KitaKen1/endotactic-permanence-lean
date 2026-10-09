import Endotactic.Permanence

/-!
# Shared definitions and the publication answer notation

The proof library uses Endotactic.Network and Endotactic.Permanence.
The FC draft has an independent coordinate-bound presentation.
FC's answer(True) elaborates to True. This identity notation keeps the proof
Mathlib-only; the audit compares compiled types with the actual FC utility.
-/

macro "answer(" t:term ")" : term => pure t
