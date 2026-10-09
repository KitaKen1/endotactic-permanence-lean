module

public import Mathlib

/-!
# Endotactic permanence: complete Mathlib-only Lean4Web proof

Generated from the modular proof by lean/scripts/make_lean4web.py.
Target environment: Lean v4.35.0-rc4 and Mathlib
1f414401f69059aa7eead47b53ee40bd38455eeb.
The checked environment and source hashes are in lean/evidence/build_results.json.

Final FC-style targets:
* EndotacticFC.extended_permanence
* EndotacticFC.measurable_extended_permanence

Both use answer(True) outside all quantifiers. The local identity notation
has the same elaborated type as FC's notation; the modular publication audit
also compares the compiled types against the actual FC utility.

Finite natural exponents, positive coefficient boxes, bounded measurable
rates, positive global well-posedness and eventual coordinate bounds are
formalized. Original-convention review and real-exponent/differential-inclusion
extensions remain separate. No custom project or FC imports are needed.
LeanPool attribution is preserved at the adapted source section; see the
repository's THIRD_PARTY_NOTICES.txt and licenses directory.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

#eval Lean.versionString

-- Source: Endotactic/Network.lean
section
/-!
# Finite reaction networks and endotacticity

Natural exponents are used for ordinary mass-action kinetics. Reaction vectors
are formed AFTER casting both complexes to real vectors; natural subtraction
would incorrectly erase negative coordinates.

The direction convention is: a negative projected reaction must have a positive
projected reaction with a strictly lower source. Sources of zero projected
reactions do not enter the essential-source minimum.
-/

namespace Endotactic

abbrev State (d : ℕ) := Fin d → ℝ
abbrev Complex (d : ℕ) := Fin d → ℕ

def realComplex {d : ℕ} (a : Complex d) : State d := fun i => a i

def dot {d : ℕ} (r x : State d) : ℝ := ∑ i, r i * x i

structure Network (d : ℕ) (E : Type*) where
  source : E → Complex d
  target : E → Complex d

def Network.vector {d : ℕ} {E : Type*} (N : Network d E) (e : E) : State d :=
  realComplex (N.target e) - realComplex (N.source e)

def Network.projection {d : ℕ} {E : Type*} (N : Network d E)
    (r : State d) (e : E) : ℝ := dot r (N.vector e)

def Network.sourceLevel {d : ℕ} {E : Type*} (N : Network d E)
    (r : State d) (e : E) : ℝ := dot r (realComplex (N.source e))

def Network.IsEndotactic {d : ℕ} {E : Type*} (N : Network d E) : Prop :=
  ∀ (r : State d) (e : E), N.projection r e < 0 →
    ∃ f : E, 0 < N.projection r f ∧ N.sourceLevel r f < N.sourceLevel r e

def Network.stoichiometricSubspace {d : ℕ} {E : Type*} (N : Network d E) :
    Submodule ℝ (State d) := Submodule.span ℝ (Set.range N.vector)

def Positive {d : ℕ} (x : State d) : Prop := ∀ i, 0 < x i

def Network.positiveClass {d : ℕ} {E : Type*} (N : Network d E)
    (c : State d) : Set (State d) :=
  {x | Positive x ∧ x - c ∈ N.stoichiometricSubspace}

def monomial {d : ℕ} (x : State d) (a : Complex d) : ℝ := ∏ i, x i ^ a i

def Network.rhs {d : ℕ} {E : Type*} [Fintype E] (N : Network d E)
    (k : E → ℝ) (x : State d) : State d :=
  ∑ e, (k e * monomial x (N.source e)) • N.vector e

theorem dot_sub {d : ℕ} (r x y : State d) : dot r (x - y) = dot r x - dot r y := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

theorem monomial_pos {d : ℕ} {x : State d} (hx : Positive x) (a : Complex d) :
    0 < monomial x a := by
  exact Finset.prod_pos fun i _ => pow_pos (hx i) _

theorem rhs_mem_stoichiometricSubspace {d : ℕ} {E : Type*} [Fintype E]
    (N : Network d E) (k : E → ℝ) (x : State d) :
    N.rhs k x ∈ N.stoichiometricSubspace := by
  apply Submodule.sum_mem
  intro e _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)

end Endotactic
end

-- Source: Endotactic/Permanence.lean
section
/-!
# Precise permanence statements

Solutions are continuous integral solutions on nonnegative time. Interval
integrability is explicit, so Lean's default value for a nonintegrable integral
cannot accidentally satisfy the solution predicate.

The absorbing compact set is chosen BEFORE the rate path and initial state.
The entry time is chosen AFTER them. We do not require one common entry time
over the entire, possibly unbounded positive stoichiometric class.
-/

namespace Endotactic

open MeasureTheory Set

variable {d : ℕ} {E : Type*} [Fintype E]

def AdmissibleRates (k : E → ℝ → ℝ) (ℓ u : ℝ) : Prop :=
  (∀ e, Measurable (k e)) ∧ ∀ e t, 0 ≤ t → ℓ ≤ k e t ∧ k e t ≤ u

/-- A concrete locally finite piecewise differentiability condition. -/
def LocallyPiecewiseDifferentiableRates (k : E → ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ cuts : Finset ℝ,
    ∀ e t, t ∈ Ioo 0 T → t ∉ cuts → DifferentiableAt ℝ (k e) t

def Network.IsIntegralSolution (N : Network d E) (k : E → ℝ → ℝ)
    (x₀ : State d) (x : ℝ → State d) : Prop :=
  ContinuousOn x (Ici 0) ∧ x 0 = x₀ ∧
    (∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun t => N.rhs (fun e => k e t) (x t))
      volume 0 T) ∧
    ∀ t : ℝ, 0 ≤ t →
      x t = x₀ + ∫ s in (0 : ℝ)..t, N.rhs (fun e => k e s) (x s)

def Network.IsGlobalPositiveSolution (N : Network d E) (k : E → ℝ → ℝ)
    (x₀ : State d) (x : ℝ → State d) : Prop :=
  N.IsIntegralSolution k x₀ x ∧ ∀ t : ℝ, 0 ≤ t → Positive (x t)

def Network.PositiveWellPosed (N : Network d E) (k : E → ℝ → ℝ)
    (x₀ : State d) : Prop :=
  ∃ x : ℝ → State d, N.IsGlobalPositiveSolution k x₀ x ∧
    ∀ y : ℝ → State d, N.IsGlobalPositiveSolution k x₀ y →
      ∀ t : ℝ, 0 ≤ t → y t = x t

def EventuallyIn {α : Type*} (x : ℝ → α) (K : Set α) : Prop :=
  ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → x t ∈ K

/-- Common compact absorption for a specified class and a specified rate box.
`regular` allows the original piecewise differentiable formulation and its
measurable-coefficient strengthening to share exactly the same quantifiers. -/
def Network.UniformPermanent (N : Network d E) (ℓ u : ℝ) (c : State d)
    (regular : (E → ℝ → ℝ) → Prop) : Prop :=
  ∃ K : Set (State d), K.Nonempty ∧ IsCompact K ∧ K ⊆ N.positiveClass c ∧
    ∀ k : E → ℝ → ℝ, AdmissibleRates k ℓ u → regular k →
      (∀ x₀ ∈ N.positiveClass c, N.PositiveWellPosed k x₀) ∧
      ∀ x₀ ∈ N.positiveClass c, ∀ x : ℝ → State d,
        N.IsGlobalPositiveSolution k x₀ x → EventuallyIn x K

/-- Permanence for one fixed coefficient path. The compact set is common to
initial points in the class, but may depend on this path, as in CNP Definitions
2.9--2.10. Global positive well-posedness is made explicit here. -/
def Network.PermanentForRates (N : Network d E) (k : E → ℝ → ℝ) (c : State d) : Prop :=
  ∃ K : Set (State d), K.Nonempty ∧ IsCompact K ∧ K ⊆ N.positiveClass c ∧
    (∀ x₀ ∈ N.positiveClass c, N.PositiveWellPosed k x₀) ∧
    ∀ x₀ ∈ N.positiveClass c, ∀ x : ℝ → State d,
      N.IsGlobalPositiveSolution k x₀ x → EventuallyIn x K

/-- The natural-exponent CNP formulation, with the rate path fixed before K.
The rate predicate spells out the chosen locally finite interpretation of
piecewise differentiability; the broader real-exponent formulation is separate. -/
def OriginalExtendedPermanenceConjecture : Prop :=
  ∀ (d m : ℕ), 0 < d → ∀ N : Network d (Fin m),
    N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
      ∀ k : Fin m → ℝ → ℝ, AdmissibleRates k ℓ u →
        LocallyPiecewiseDifferentiableRates k →
          ∀ c : State d, Positive c → N.PermanentForRates k c

/-- A stronger, common-rate-box version of the CNP conjecture. -/
def ExtendedPermanenceConjecture : Prop :=
  ∀ (d m : ℕ), 0 < d → ∀ N : Network d (Fin m),
    N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
      ∀ c : State d, Positive c →
        N.UniformPermanent ℓ u c LocallyPiecewiseDifferentiableRates

/-- This strengthens the regularity assumption in the original CNP formulation.
It is not labelled as an established theorem. -/
def MeasurableExtendedPermanenceConjecture : Prop :=
  ∀ (d m : ℕ), 0 < d → ∀ N : Network d (Fin m),
    N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
      ∀ c : State d, Positive c → N.UniformPermanent ℓ u c (fun _ => True)

theorem UniformPermanent.mono_regularity (N : Network d E) {ℓ u : ℝ} {c : State d}
    {regular₁ regular₂ : (E → ℝ → ℝ) → Prop}
    (h : N.UniformPermanent ℓ u c regular₁)
    (hreg : ∀ k, regular₂ k → regular₁ k) : N.UniformPermanent ℓ u c regular₂ := by
  obtain ⟨K, hKne, hKcompact, hKclass, hK⟩ := h
  exact ⟨K, hKne, hKcompact, hKclass, fun k hk hr => hK k hk (hreg k hr)⟩

theorem measurable_conjecture_implies_extended
    (h : MeasurableExtendedPermanenceConjecture) : ExtendedPermanenceConjecture := by
  intro d m hd N hN ℓ u hℓ hlu c hc
  exact UniformPermanent.mono_regularity N (h d m hd N hN ℓ u hℓ hlu c hc)
    (fun _ _ => trivial)

theorem UniformPermanent.implies_permanentForRates (N : Network d E)
    {ℓ u : ℝ} {c : State d} {regular : (E → ℝ → ℝ) → Prop}
    (h : N.UniformPermanent ℓ u c regular) {k : E → ℝ → ℝ}
    (hk : AdmissibleRates k ℓ u) (hr : regular k) : N.PermanentForRates k c := by
  obtain ⟨K, hKne, hKcompact, hKclass, hK⟩ := h
  exact ⟨K, hKne, hKcompact, hKclass, hK k hk hr⟩

theorem uniform_extended_conjecture_implies_original
    (h : ExtendedPermanenceConjecture) : OriginalExtendedPermanenceConjecture := by
  intro d m hd N hN ℓ u hℓ hlu k hk hr c hc
  exact UniformPermanent.implies_permanentForRates N (h d m hd N hN ℓ u hℓ hlu c hc) hk hr

end Endotactic
end

-- Source: EndotacticPublication/Statement.lean
section
/-!
# Shared definitions and the publication answer notation

The proof library uses Endotactic.Network and Endotactic.Permanence.
The FC draft has an independent coordinate-bound presentation.
FC's answer(True) elaborates to True. This identity notation keeps the proof
Mathlib-only; the audit compares compiled types with the actual FC utility.
-/

macro "answer(" t:term ")" : term => pure t
end

-- Source: Endotactic/AffinePlateau.lean
section
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
end

-- Source: Endotactic/EssentialSource.lean
section
/-!
# The essential-source shortcut

This replaces graph return paths and cut-flux decompositions by a minimum over
the finite set of reactions with NONZERO projection. It does not assume weak
reversibility or strong endotacticity.
-/

namespace Endotactic

variable {d : ℕ} {E : Type*} (N : Network d E)

def Network.IsEssentialMinimum (r : State d) (e : E) : Prop :=
  N.projection r e ≠ 0 ∧
    ∀ f : E, N.projection r f ≠ 0 → N.sourceLevel r e ≤ N.sourceLevel r f

theorem essentialMinimum_projection_pos (hN : N.IsEndotactic) {r : State d} {e : E}
    (he : N.IsEssentialMinimum r e) : 0 < N.projection r e := by
  rcases he with ⟨hne, hmin⟩
  by_contra h
  have hneg : N.projection r e < 0 := lt_of_le_of_ne (le_of_not_gt h) hne
  obtain ⟨f, hf, hlevel⟩ := hN r e hneg
  have := hmin f (ne_of_gt hf)
  linarith

theorem essentialMinimum_source_lt_of_negative (hN : N.IsEndotactic)
    {r : State d} {e : E} (he : N.IsEssentialMinimum r e) {f : E}
    (hf : N.projection r f < 0) : N.sourceLevel r e < N.sourceLevel r f := by
  obtain ⟨g, hg, hlevel⟩ := hN r f hf
  exact lt_of_le_of_lt (he.2 g (ne_of_gt hg)) hlevel

theorem exists_essentialMinimum [Fintype E] {r : State d}
    (h : ∃ e : E, N.projection r e ≠ 0) :
    ∃ e : E, N.IsEssentialMinimum r e := by
  classical
  let s := Finset.univ.filter fun e => N.projection r e ≠ 0
  have hs : s.Nonempty := by
    obtain ⟨e, he⟩ := h
    exact ⟨e, by simp [s, he]⟩
  obtain ⟨e, he, hmin⟩ := Finset.exists_min_image s (N.sourceLevel r) hs
  refine ⟨e, ?_, ?_⟩
  · simpa [s] using he
  · intro f hf
    exact hmin f (by simp [s, hf])

theorem exists_positive_essential_source [Fintype E] (hN : N.IsEndotactic) {r : State d}
    (h : ∃ e : E, N.projection r e ≠ 0) :
    ∃ e : E, 0 < N.projection r e ∧
      ∀ f : E, N.projection r f < 0 → N.sourceLevel r e < N.sourceLevel r f := by
  obtain ⟨e, he⟩ := exists_essentialMinimum N h
  exact ⟨e, essentialMinimum_projection_pos N hN he,
    fun _ hf => essentialMinimum_source_lt_of_negative N hN he hf⟩

theorem exists_positive_negative_source_gap [Fintype E] (hN : N.IsEndotactic)
    {r : State d} {a : E} (ha : N.IsEssentialMinimum r a) :
    ∃ H : ℝ, 0 < H ∧ ∀ e : E, N.projection r e < 0 →
      H ≤ N.sourceLevel r e - N.sourceLevel r a := by
  classical
  by_cases hex : ∃ e : E, N.projection r e < 0
  · let s := Finset.univ.filter fun e => N.projection r e < 0
    have hs : s.Nonempty := by
      obtain ⟨e, he⟩ := hex
      exact ⟨e, by simp [s, he]⟩
    obtain ⟨e, he, hmin⟩ := Finset.exists_min_image s
      (fun e => N.sourceLevel r e - N.sourceLevel r a) hs
    have hneg : N.projection r e < 0 := by simpa [s] using he
    refine ⟨N.sourceLevel r e - N.sourceLevel r a,
      sub_pos.mpr (essentialMinimum_source_lt_of_negative N hN ha hneg), ?_⟩
    intro f hf
    exact hmin f (by simp [s, hf])
  · refine ⟨1, by norm_num, ?_⟩
    intro e he
    exact False.elim (hex ⟨e, he⟩)

end Endotactic
end

-- Source: Endotactic/FluxBound.lean
section
/-!
# A single positive source dominates all negative fluxes

The generic finite-sum lemma separates the ordered reaction geometry from the
analytic monomial comparison. In particular, it holds for every coefficient
vector in a prescribed box, not just sampled coefficient values.
-/

namespace Endotactic

def negativeMass {E : Type*} [Fintype E] (p : E → ℝ) : ℝ :=
  ∑ e, max (-(p e)) 0

theorem weighted_sum_lower_bound {E : Type*} [Fintype E] [DecidableEq E]
    (p μ k : E → ℝ) (a : E) (ℓ u ρ : ℝ)
    (hu : 0 ≤ u) (hμ : ∀ e, 0 ≤ μ e)
    (hk : ∀ e, ℓ ≤ k e ∧ k e ≤ u) (hk0 : ∀ e, 0 ≤ k e)
    (ha : 0 ≤ p a) (hdom : ∀ e, p e < 0 → μ e ≤ ρ * μ a) :
    μ a * (ℓ * p a - u * ρ * negativeMass p) ≤ ∑ e, k e * μ e * p e := by
  have hpoint : ∀ e : E,
      (if e = a then ℓ * μ a * p a else 0) -
        (u * (ρ * μ a)) * max (-(p e)) 0 ≤ k e * μ e * p e := by
    intro e
    by_cases hea : e = a
    · subst e
      have hmul := mul_le_mul_of_nonneg_right (hk a).1
        (mul_nonneg (hμ a) ha)
      simpa [max_eq_right (neg_nonpos.mpr ha), mul_assoc] using hmul
    · simp only [ite_eq_right hea]
      by_cases hpe : p e < 0
      · have hw : k e * μ e ≤ u * (ρ * μ a) := by
          calc
            k e * μ e ≤ u * μ e := mul_le_mul_of_nonneg_right (hk e).2 (hμ e)
            _ ≤ u * (ρ * μ a) := mul_le_mul_of_nonneg_left (hdom e hpe) hu
        have hm := mul_le_mul_of_nonpos_right hw (le_of_lt hpe)
        rw [max_eq_left (neg_nonneg.mpr (le_of_lt hpe))]
        nlinarith only [hm]
      · have hp : 0 ≤ p e := le_of_not_gt hpe
        simp only [max_eq_right (neg_nonpos.mpr hp), mul_zero, sub_zero]
        exact mul_nonneg (mul_nonneg (hk0 e) (hμ e)) hp
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hpoint e)
  have heq : (∑ e : E, ((if e = a then ℓ * μ a * p a else 0) -
      (u * (ρ * μ a)) * max (-(p e)) 0)) =
      μ a * (ℓ * p a - u * ρ * negativeMass p) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.mul_sum]
    unfold negativeMass
    ring
  rwa [heq] at hsum

theorem weighted_sum_pos {E : Type*} [Fintype E] [DecidableEq E]
    (p μ k : E → ℝ) (a : E) (ℓ u ρ : ℝ)
    (hu : 0 ≤ u) (hμ : ∀ e, 0 ≤ μ e)
    (hk : ∀ e, ℓ ≤ k e ∧ k e ≤ u) (hk0 : ∀ e, 0 ≤ k e)
    (ha : 0 ≤ p a) (hμa : 0 < μ a)
    (hdom : ∀ e, p e < 0 → μ e ≤ ρ * μ a)
    (hgap : u * ρ * negativeMass p < ℓ * p a) :
    0 < ∑ e, k e * μ e * p e := by
  exact lt_of_lt_of_le (mul_pos hμa (sub_pos.mpr hgap))
    (weighted_sum_lower_bound p μ k a ℓ u ρ hu hμ hk hk0 ha hdom)

theorem dot_rhs {d : ℕ} {E : Type*} [Fintype E]
    (N : Network d E) (r x : State d) (k : E → ℝ) :
    dot r (N.rhs k x) = ∑ e, k e * monomial x (N.source e) * N.projection r e := by
  simp only [dot, Network.rhs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Network.projection, dot]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem network_flux_pos {d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (N : Network d E) (hN : N.IsEndotactic) (r x : State d) (k : E → ℝ)
    (a : E) (ℓ u ρ : ℝ) (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    (hx : Positive x) (hk : ∀ e, ℓ ≤ k e ∧ k e ≤ u)
    (ha : N.IsEssentialMinimum r a)
    (hdom : ∀ e, N.projection r e < 0 →
      monomial x (N.source e) ≤ ρ * monomial x (N.source a))
    (hgap : u * ρ * negativeMass (N.projection r) < ℓ * N.projection r a) :
    0 < dot r (N.rhs k x) := by
  rw [dot_rhs]
  exact weighted_sum_pos (N.projection r) (fun e => monomial x (N.source e))
    k a ℓ u ρ hu (fun e => (monomial_pos hx _).le) hk
    (fun e => le_trans hℓ.le (hk e).1)
    (essentialMinimum_projection_pos N hN ha).le (monomial_pos hx _)
    hdom hgap

end Endotactic
end

-- Source: Endotactic/MonomialOrder.lean
section
/-!
# Monomial comparison in logarithmic coordinates

For `0 < h < 1`, lower exponent level means a larger monomial. This order
reversal is essential; exchanging it makes the permanence argument false.
-/

namespace Endotactic

noncomputable def exponentialPoint {d : ℕ} (h : ℝ) (p : State d) : State d :=
  fun i => h ^ p i

theorem exponentialPoint_positive {d : ℕ} {h : ℝ} (hh : 0 < h) (p : State d) :
    Positive (exponentialPoint h p) := by
  intro i
  exact Real.rpow_pos_of_pos hh _

theorem monomial_exponentialPoint {d : ℕ} {h : ℝ} (hh : 0 < h)
    (p : State d) (a : Complex d) :
    monomial (exponentialPoint h p) a = h ^ (dot p (realComplex a)) := by
  unfold monomial exponentialPoint dot realComplex
  rw [Real.rpow_sum_of_pos hh]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.rpow_mul hh.le, Real.rpow_natCast]

theorem monomial_domination_of_exponent_gap {d : ℕ} {h H : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (p : State d) (a b : Complex d)
    (hgap : H ≤ dot p (realComplex b) - dot p (realComplex a)) :
    monomial (exponentialPoint h p) b ≤
      h ^ H * monomial (exponentialPoint h p) a := by
  rw [monomial_exponentialPoint hh, monomial_exponentialPoint hh]
  rw [← Real.rpow_add hh]
  exact Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)

/-- A positive flux at an exponential point, under the explicit geometric gaps.
This theorem is conditional on those gaps, not on the general permanence claim. -/
theorem exponentialPoint_flux_pos {d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (N : Network d E) (hN : N.IsEndotactic) (r p : State d) (k : E → ℝ)
    (a : E) (ℓ u h H : ℝ) (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    (hh : 0 < h) (hh1 : h ≤ 1) (hk : ∀ e, ℓ ≤ k e ∧ k e ≤ u)
    (ha : N.IsEssentialMinimum r a)
    (hgap : ∀ e, N.projection r e < 0 →
      H ≤ dot p (realComplex (N.source e)) - dot p (realComplex (N.source a)))
    (hsmall : u * h ^ H * negativeMass (N.projection r) <
      ℓ * N.projection r a) :
    0 < dot r (N.rhs k (exponentialPoint h p)) := by
  apply network_flux_pos N hN r (exponentialPoint h p) k a ℓ u (h ^ H)
    hℓ hu (exponentialPoint_positive hh p) hk ha
  · intro e he
    exact monomial_domination_of_exponent_gap hh hh1 p (N.source a) (N.source e)
      (hgap e he)
  · exact hsmall

end Endotactic
end

-- Source: Endotactic/CompactSequentialExclusion.lean
section
/-!
# Uniform exclusion from sequential compactness

The bad relation need not be continuous or closed. The explicit sequential
hypothesis rules out every bad sequence at scales tending to zero. Compactness
alone does not supply that hypothesis.
-/

namespace Endotactic

open Filter Topology

theorem compact_sequential_exclusion {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] (K : Set X) (hK : IsCompact K) (R : ℝ → X → Prop)
    (hseq : ∀ (h : ℕ → ℝ) (x : ℕ → X) (p : X),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      (∀ n, x n ∈ K) → Tendsto x atTop (𝓝 p) → p ∈ K →
      (∀ n, R (h n) (x n)) → False) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ x ∈ K, ¬ R h x := by
  classical
  by_contra hbad
  push Not at hbad
  have hw : ∀ n : ℕ, ∃ h : ℝ, 0 < h ∧ h < 1 / ((n : ℝ) + 1) ∧
      ∃ x ∈ K, R h x := by
    intro n
    exact hbad (1 / ((n : ℝ) + 1)) (by positivity)
  choose h hh hsmall x hx hR using hw
  have hlim : Tendsto h atTop (𝓝 0) :=
    squeeze_zero (fun n => (hh n).le) (fun n => (hsmall n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨p, hp, φ, hφ, hxp⟩ := hK.tendsto_subseq hx
  exact hseq (h ∘ φ) (x ∘ φ) p (fun n => hh (φ n))
    (hlim.comp hφ.tendsto_atTop) (fun n => hx (φ n)) hxp hp
    (fun n => hR (φ n))

/-- The finite label set is fixed before a common scale threshold is chosen.
Empty label sets are handled without inventing a witness. -/
theorem finite_compact_sequential_exclusion {X I : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [Fintype I]
    (K : Set X) (hK : IsCompact K) (R : I → ℝ → X → Prop)
    (hseq : ∀ i : I, ∀ (h : ℕ → ℝ) (x : ℕ → X) (p : X),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      (∀ n, x n ∈ K) → Tendsto x atTop (𝓝 p) → p ∈ K →
      (∀ n, R i (h n) (x n)) → False) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ x ∈ K, ∀ i : I, ¬ R i h x := by
  classical
  by_cases hI : Nonempty I
  · let : Nonempty I := hI
    choose δ hδ hgood using fun i => compact_sequential_exclusion K hK (R i) (hseq i)
    let s := Finset.univ.image δ
    have hs : s.Nonempty := Finset.univ_nonempty.image δ
    have hmin : 0 < s.min' hs := by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (s.min'_mem hs)
      rw [← hi]
      exact hδ i
    refine ⟨min (s.min' hs) 1, lt_min hmin (by norm_num), min_le_right _ _, ?_⟩
    intro h hh hsmall x hx i
    apply hgood i h hh
      (hsmall.trans_le ((min_le_left _ _).trans
        (s.min'_le _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))) x hx
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    intro h hh hsmall x hx i
    exact (hI ⟨i⟩).elim

end Endotactic
end

-- Source: Endotactic/ScaledAffineActivity.lean
section
/-!
# Scale-dependent offsets, fixed slopes, and uniform activity approximation

Offsets need not be continuous. The sequential approximation is an explicit
hypothesis of the uniformization theorem here. The exact approximation
statement below is proved downstream by `finiteAffineApproximation` in
`MinimumBandSelection`; it is neither an axiom nor an assumed proof input there.
-/

namespace Endotactic

open Filter Topology

structure ScaledAffineFamily (d m : ℕ) where
  slope : Fin m → State d
  offset : Fin m → ℝ → ℝ

def ScaledAffineFamily.atScale {d m : ℕ} (A : ScaledAffineFamily d m) (h : ℝ) :
    AffineFamily d m where
  slope := A.slope
  offset i := A.offset i h

/-- Approaching exponent points may lie outside `K`; only the limiting point
belongs to `K`. Every fixed label remaining active must meet its tolerance. -/
def ScaledAffineFamily.HasSequentialActivityBound {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (ε : Fin m → ℝ) : Prop :=
  ∀ i : Fin m, ∀ (h : ℕ → ℝ) (p : ℕ → State d) (q : State d),
    (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) → Tendsto p atTop (𝓝 q) → q ∈ K →
    (∀ n, (A.atScale (h n)).Active i (exponentialPoint (h n) (p n))) →
      ‖q - A.slope i‖ < ε i

theorem ScaledAffineFamily.atScale_slope {d m : ℕ}
    (A : ScaledAffineFamily d m) (h : ℝ) (i : Fin m) :
    (A.atScale h).slope i = A.slope i := rfl

theorem ScaledAffineFamily.atScale_value {d m : ℕ}
    (A : ScaledAffineFamily d m) (h : ℝ) (i : Fin m) (x : State d) :
    (A.atScale h).value i x = dot (A.slope i) x + A.offset i h := rfl

/-- The uniform activity corollary follows from sequential approximation,
compactness, and a fixed finite label set. Neither tolerance nor offsets need
continuity. All minimizing labels, including ties, are quantified. -/
theorem ScaledAffineFamily.uniformActivityBound_of_sequential {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (hK : IsCompact K)
    (ε : Fin m → ℝ) (hseq : A.HasSequentialActivityBound K ε) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ p ∈ K, ∀ i : Fin m,
        (A.atScale h).Active i (exponentialPoint h p) → ‖p - A.slope i‖ < ε i := by
  let R := fun i h p =>
    (A.atScale h).Active i (exponentialPoint h p) ∧ ε i ≤ ‖p - A.slope i‖
  have hbad : ∀ i : Fin m, ∀ (h : ℕ → ℝ) (p : ℕ → State d) (q : State d),
      (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      (∀ n, p n ∈ K) → Tendsto p atTop (𝓝 q) → q ∈ K →
      (∀ n, R i (h n) (p n)) → False := by
    intro i h p q hh hlim _ hplim hq hR
    have hstrict := hseq i h p q hh hlim hplim hq (fun n => (hR n).1)
    have hnorm : Tendsto (fun n => ‖p n - A.slope i‖) atTop (𝓝 ‖q - A.slope i‖) :=
      (hplim.sub tendsto_const_nhds).norm
    have hle := ge_of_tendsto hnorm (Eventually.of_forall fun n => (hR n).2)
    exact (not_lt_of_ge hle) hstrict
  obtain ⟨h₀, hh₀, hh₀1, hgood⟩ := finite_compact_sequential_exclusion K hK R hbad
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall p hp i hi
  exact lt_of_not_ge (fun hle => hgood h hh hsmall p hp i ⟨hi, hle⟩)

theorem ScaledAffineFamily.norm_close_coordinate {d m : ℕ}
    (A : ScaledAffineFamily d m) {p : State d} {i : Fin m} {ε : ℝ}
    (hclose : ‖p - A.slope i‖ < ε) : ∀ j, |p j - A.slope i j| ≤ ε := by
  intro j
  have hj : |p j - A.slope i j| ≤ ‖p - A.slope i‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (p - A.slope i) j
  exact (hj.trans_lt hclose).le

/-- Formal type of the affine lemma, proved downstream by
`finiteAffineApproximation`. The tolerance is chosen before the finite family and may be
discontinuous. Offsets must decay relative to `h^a` from the positive side. -/
def FiniteAffineApproximationStatement : Prop :=
  ∀ d : ℕ, 0 < d → ∀ a b : ℝ, a < b →
    ∀ E : State d → ℝ, (∀ p ∈ Set.Icc (fun _ => a) (fun _ => b), 0 < E p) →
      ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily d m,
        (∀ i, A.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) ∧
        (∀ i, Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) ∧
        A.HasSequentialActivityBound (Set.Icc (fun _ => a) (fun _ => b))
          (fun i => E (A.slope i))

end Endotactic
end

-- Source: Endotactic/ScaleLimits.lean
section
/-!
# Closed limits of arbitrary relations at vanishing positive scales

No continuity or closedness of the relation is assumed. Local witnesses at
arbitrarily small scales characterize the limit set and prove its closedness.
This is the diagonal-selection step used for affine activity-limit sets.
-/

namespace Endotactic

open Filter Topology

def scaleLimit {X : Type*} [TopologicalSpace X] (R : ℝ → X → Prop) : Set X :=
  {q | ∃ (h : ℕ → ℝ) (x : ℕ → X), (∀ n, 0 < h n) ∧
    Tendsto h atTop (𝓝 0) ∧ Tendsto x atTop (𝓝 q) ∧ ∀ n, R (h n) (x n)}

theorem mem_scaleLimit_of_sequences {X : Type*} [TopologicalSpace X]
    {R : ℝ → X → Prop} {q : X} (h : ℕ → ℝ) (x : ℕ → X)
    (hh : ∀ n, 0 < h n) (hhlim : Tendsto h atTop (𝓝 0))
    (hxlim : Tendsto x atTop (𝓝 q)) (hR : ∀ n, R (h n) (x n)) :
    q ∈ scaleLimit R := ⟨h, x, hh, hhlim, hxlim, hR⟩

theorem scaleLimit_mono {X : Type*} [TopologicalSpace X]
    {R S : ℝ → X → Prop} (hRS : ∀ h x, R h x → S h x) :
    scaleLimit R ⊆ scaleLimit S := by
  rintro q ⟨h, x, hh, hhlim, hxlim, hR⟩
  exact ⟨h, x, hh, hhlim, hxlim, fun n => hRS _ _ (hR n)⟩

theorem mem_scaleLimit_iff_small_witness {X : Type*} [PseudoMetricSpace X]
    {R : ℝ → X → Prop} {q : X} :
    q ∈ scaleLimit R ↔ ∀ δ : ℝ, 0 < δ →
      ∃ h : ℝ, 0 < h ∧ h < δ ∧ ∃ x : X, dist x q < δ ∧ R h x := by
  classical
  constructor
  · rintro ⟨h, x, hh, hhlim, hxlim, hR⟩ δ hδ
    have hhsmall : ∀ᶠ n in atTop, h n < δ := hhlim.eventually (gt_mem_nhds hδ)
    have hxsmall : ∀ᶠ n in atTop, dist (x n) q < δ :=
      (tendsto_iff_dist_tendsto_zero.mp hxlim).eventually (gt_mem_nhds hδ)
    obtain ⟨n, hhn, hxn⟩ := (hhsmall.and hxsmall).exists
    exact ⟨h n, hh n, hhn, x n, hxn, hR n⟩
  · intro hw
    have hw' : ∀ n : ℕ, ∃ h : ℝ, 0 < h ∧ h < 1 / ((n : ℝ) + 1) ∧
        ∃ x : X, dist x q < 1 / ((n : ℝ) + 1) ∧ R h x :=
      fun n => hw _ (by positivity)
    choose h hh hsmall x hx hR using hw'
    have hhlim : Tendsto h atTop (𝓝 0) :=
      squeeze_zero (fun n => (hh n).le) (fun n => (hsmall n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hxlim : Tendsto x atTop (𝓝 q) :=
      tendsto_iff_dist_tendsto_zero.mpr <|
        squeeze_zero (fun n => dist_nonneg) (fun n => (hx n).le)
          tendsto_one_div_add_atTop_nhds_zero_nat
    exact ⟨h, x, hh, hhlim, hxlim, hR⟩

theorem isClosed_scaleLimit {X : Type*} [PseudoMetricSpace X]
    (R : ℝ → X → Prop) : IsClosed (scaleLimit R) := by
  apply isClosed_of_closure_subset
  intro q hq
  apply mem_scaleLimit_iff_small_witness.mpr
  intro δ hδ
  obtain ⟨z, hz, hqz⟩ := Metric.mem_closure_iff.mp hq (δ / 2) (by positivity)
  obtain ⟨h, hh, hsmall, x, hxz, hR⟩ :=
    mem_scaleLimit_iff_small_witness.mp hz (δ / 2) (by positivity)
  refine ⟨h, hh, hsmall.trans (by linarith), x, ?_, hR⟩
  have hdist := dist_triangle x z q
  rw [dist_comm z q] at hdist
  linarith

theorem isCompact_scaleLimit_inter {X : Type*} [PseudoMetricSpace X]
    (R : ℝ → X → Prop) {K : Set X} (hK : IsCompact K) :
    IsCompact (K ∩ scaleLimit R) :=
  hK.inter_right (isClosed_scaleLimit R)

/-- A compact bad set missing one continuous level misses an entire band.
The empty bad set is included. No positive lower bound is assumed in advance. -/
theorem compact_avoids_level_band {X : Type*} [TopologicalSpace X]
    {B : Set X} (hB : IsCompact B) (f : X → ℝ) (hf : Continuous f) (t : ℝ)
    (hlevel : ∀ q ∈ B, f q ≠ t) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ B, ρ ≤ |f q - t| := by
  apply hB.exists_forall_le' ((hf.sub continuous_const).abs.continuousOn)
  intro q hq
  exact abs_pos.mpr (sub_ne_zero.mpr (hlevel q hq))

end Endotactic
end

-- Source: Endotactic/ActivityLimitNeighborhood.lean
section
/-!
# Fixed-level activity bounds extend to nearby levels

The finite union of bad activity-limit sets is compact inside the given
compact exponent domain. A continuous level function separates this bad set
from a level where all labels are already known to satisfy their tolerance.
This proves the nearby-level step, but does not construct the fixed-level
families or their offset shifts in affine approximation A.
-/

namespace Endotactic

open Filter Topology

def ScaledAffineFamily.activityLimit {d m : ℕ}
    (A : ScaledAffineFamily d m) (i : Fin m) : Set (State d) :=
  scaleLimit (fun h p => (A.atScale h).Active i (exponentialPoint h p))

theorem ScaledAffineFamily.isClosed_activityLimit {d m : ℕ}
    (A : ScaledAffineFamily d m) (i : Fin m) : IsClosed (A.activityLimit i) :=
  isClosed_scaleLimit _

theorem ScaledAffineFamily.isCompact_activityLimit_inter {d m : ℕ}
    (A : ScaledAffineFamily d m) (i : Fin m) {K : Set (State d)} (hK : IsCompact K) :
    IsCompact (K ∩ A.activityLimit i) :=
  hK.inter_right (A.isClosed_activityLimit i)

/-- Exact equivalence: approaching exponent points remain unrestricted, and
every fixed active label, including ties, occurs in its own limit set. -/
theorem ScaledAffineFamily.sequentialActivityBound_iff_limits {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (ε : Fin m → ℝ) :
    A.HasSequentialActivityBound K ε ↔
      ∀ i : Fin m, ∀ q ∈ K, q ∈ A.activityLimit i → ‖q - A.slope i‖ < ε i := by
  constructor
  · intro hseq i q hq
    rintro ⟨h, p, hh, hhlim, hplim, hactive⟩
    exact hseq i h p q hh hhlim hplim hq hactive
  · intro hlimits i h p q hh hhlim hplim hq hactive
    exact hlimits i q hq ⟨h, p, hh, hhlim, hplim, hactive⟩

def ScaledAffineFamily.badActivityLimits {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (ε : Fin m → ℝ) :
    Set (State d) := K ∩ {q | ∃ i : Fin m,
      q ∈ A.activityLimit i ∧ ε i ≤ ‖q - A.slope i‖}

theorem ScaledAffineFamily.isCompact_badActivityLimits {d m : ℕ}
    (A : ScaledAffineFamily d m) {K : Set (State d)} (hK : IsCompact K)
    (ε : Fin m → ℝ) : IsCompact (A.badActivityLimits K ε) := by
  apply hK.inter_right
  have hclosed : ∀ i : Fin m,
      IsClosed (A.activityLimit i ∩ {q | ε i ≤ ‖q - A.slope i‖}) := by
    intro i
    exact (A.isClosed_activityLimit i).inter
      (isClosed_le continuous_const ((continuous_id.sub continuous_const).norm))
  convert isClosed_iUnion_of_finite hclosed using 1
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]

theorem ScaledAffineFamily.sequentialActivityBound_iff_bad_empty {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (ε : Fin m → ℝ) :
    A.HasSequentialActivityBound K ε ↔ A.badActivityLimits K ε = ∅ := by
  rw [A.sequentialActivityBound_iff_limits]
  constructor
  · intro hgood
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro q ⟨hq, i, hi, hbad⟩
    exact (not_lt_of_ge hbad) (hgood i q hq hi)
  · intro hempty i q hq hi
    apply lt_of_not_ge
    intro hbad
    have hmem : q ∈ A.badActivityLimits K ε := ⟨hq, i, hi, hbad⟩
    rw [hempty] at hmem
    exact hmem

/-- The fixed finite family is retained. Neither offset nor tolerance needs
continuity. The level function alone is assumed continuous. -/
theorem ScaledAffineFamily.activityLimits_near_level {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (hK : IsCompact K)
    (ε : Fin m → ℝ) (f : State d → ℝ) (hf : Continuous f) (t : ℝ)
    (hfixed : ∀ i : Fin m, ∀ q ∈ K, q ∈ A.activityLimit i → f q = t →
      ‖q - A.slope i‖ < ε i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ K, |f q - t| < ρ →
      ∀ i : Fin m, q ∈ A.activityLimit i → ‖q - A.slope i‖ < ε i := by
  have hlevel : ∀ q ∈ A.badActivityLimits K ε, f q ≠ t := by
    rintro q ⟨hq, i, hi, hbad⟩ heq
    exact (not_lt_of_ge hbad) (hfixed i q hq hi heq)
  obtain ⟨ρ, hρ, hsep⟩ := compact_avoids_level_band
    (A.isCompact_badActivityLimits hK ε) f hf t hlevel
  refine ⟨ρ, hρ, ?_⟩
  intro q hq hnear i hi
  apply lt_of_not_ge
  intro hbad
  exact (not_lt_of_ge (hsep q ⟨hq, i, hi, hbad⟩)) hnear

/-- A narrower closed band is compact and preserves the strict bound. -/
theorem ScaledAffineFamily.sequentialActivityBound_near_level {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (hK : IsCompact K)
    (ε : Fin m → ℝ) (f : State d → ℝ) (hf : Continuous f) (t : ℝ)
    (hfixed : A.HasSequentialActivityBound (K ∩ {q | f q = t}) ε) :
    ∃ ρ : ℝ, 0 < ρ ∧
      A.HasSequentialActivityBound (K ∩ {q | |f q - t| ≤ ρ}) ε := by
  obtain ⟨ρ, hρ, hnear⟩ := A.activityLimits_near_level K hK ε f hf t
    (fun i q hq hi heq =>
      (A.sequentialActivityBound_iff_limits _ _).mp hfixed i q ⟨hq, heq⟩ hi)
  refine ⟨ρ / 2, by positivity, (A.sequentialActivityBound_iff_limits _ _).mpr ?_⟩
  rintro i q ⟨hq, hband⟩ hi
  exact hnear q hq (hband.trans_lt (by linarith)) i hi

/-- Fixed-level sequential approximation now yields one scale threshold on a
nontrivial closed neighborhood of that level, for every active label. -/
theorem ScaledAffineFamily.uniformActivityBound_near_level {d m : ℕ}
    (A : ScaledAffineFamily d m) (K : Set (State d)) (hK : IsCompact K)
    (ε : Fin m → ℝ) (f : State d → ℝ) (hf : Continuous f) (t : ℝ)
    (hfixed : A.HasSequentialActivityBound (K ∩ {q | f q = t}) ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ → ∀ q ∈ K, |f q - t| ≤ ρ →
        ∀ i : Fin m, (A.atScale h).Active i (exponentialPoint h q) →
          ‖q - A.slope i‖ < ε i := by
  obtain ⟨ρ, hρ, hseq⟩ := A.sequentialActivityBound_near_level K hK ε f hf t hfixed
  have hband : IsCompact (K ∩ {q | |f q - t| ≤ ρ}) :=
    hK.inter_right (isClosed_le ((hf.sub continuous_const).abs) continuous_const)
  obtain ⟨h₀, hh₀, hh₀1, hgood⟩ := A.uniformActivityBound_of_sequential _ hband ε hseq
  exact ⟨ρ, hρ, h₀, hh₀, hh₀1, fun h hh hsmall q hq hnear =>
    hgood h hh hsmall q ⟨hq, hnear⟩⟩

end Endotactic
end

-- Source: Endotactic/FiniteMinimum.lean
section
/-!
# Finite minima along absolutely continuous paths

At every point where the minimum and an active branch are differentiable,
their derivatives agree: their difference is nonnegative and vanishes there,
so Fermat's theorem applies. Absolute continuity makes these points full measure.
This avoids a case-by-case derivative formula at ties.
-/

namespace Endotactic

open MeasureTheory Set Filter
open scoped Topology

theorem ac_congrOn {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (heq : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  have hevent : ∀ᶠ E in AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
      𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  apply hf.congr'
  filter_upwards [hevent] with E hE
  apply Finset.sum_congr rfl
  intro i hi
  rw [heq (hE.1 i hi).1, heq (hE.1 i hi).2]

theorem ac_const (c a b : ℝ) : AbsolutelyContinuousOnInterval (fun _ => c) a b := by
  unfold AbsolutelyContinuousOnInterval
  simp only [dist_self, Finset.sum_const_zero]
  exact tendsto_const_nhds

theorem ac_min {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => min (f t) (g t)) a b := by
  have hdist (s t : ℝ) :
      dist (min (f s) (g s)) (min (f t) (g t)) ≤ dist (f s) (f t) + dist (g s) (g t) := by
    have h := lipschitzWith_min.dist_le_mul (f s, g s) (f t, g t)
    simp only [NNReal.coe_one, one_mul, Prod.dist_eq] at h
    exact h.trans (max_le (le_add_of_nonneg_right dist_nonneg)
      (le_add_of_nonneg_left dist_nonneg))
  apply squeeze_zero (fun E => Finset.sum_nonneg fun _ _ => dist_nonneg)
    (fun E => ?_) (by simpa using Tendsto.add hf hg)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => hdist (E.2 i).1 (E.2 i).2

theorem ac_finset_inf {I : Type*} [DecidableEq I] (s : Finset I) (hs : s.Nonempty)
    (f : I → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => s.inf' hs (fun i => f i t)) a b := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hf i (by simp)
  | cons i s hi hs ih =>
    have htail : ∀ j ∈ s, AbsolutelyContinuousOnInterval (f j) a b :=
      fun j hj => hf j (Finset.mem_cons.mpr (Or.inr hj))
    simpa only [Finset.inf'_cons hs] using
      ac_min (hf i (Finset.mem_cons.mpr (Or.inl rfl))) (ih htail)

noncomputable def finiteMinimum {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty f

theorem finiteMinimum_le {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) (i : I) :
    finiteMinimum f ≤ f i :=
  Finset.inf'_le f (Finset.mem_univ i)

theorem finiteMinimum_attained {I : Type*} [Fintype I] [Nonempty I] (f : I → ℝ) :
    ∃ i, finiteMinimum f = f i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty f
  exact ⟨i, hi⟩

theorem finiteMinimum_ac {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => finiteMinimum (fun i => f i t)) a b := by
  classical
  exact ac_finset_inf Finset.univ Finset.univ_nonempty f (fun i _ => hf i)

theorem finiteMinimum_deriv_eq_active {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) {t : ℝ} {i : I}
    (hF : DifferentiableAt ℝ (fun s => finiteMinimum (fun j => f j s)) t)
    (hi : DifferentiableAt ℝ (f i) t)
    (hactive : finiteMinimum (fun j => f j t) = f i t) :
    deriv (fun s => finiteMinimum (fun j => f j s)) t = deriv (f i) t := by
  have hmin : IsLocalMin (fun s => f i s - finiteMinimum (fun j => f j s)) t := by
    apply Filter.Eventually.of_forall
    intro s
    change f i t - finiteMinimum (fun j => f j t) ≤
      f i s - finiteMinimum (fun j => f j s)
    rw [hactive, sub_self]
    exact sub_nonneg.mpr (finiteMinimum_le (fun j => f j s) i)
  have hz := hmin.hasDerivAt_eq_zero (hi.hasDerivAt.sub hF.hasDerivAt)
  linarith

theorem finiteMinimum_ae_deriv_lower_bound {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) {a b δ : ℝ}
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) a b)
    (hbound : ∀ᵐ t ∂volume, t ∈ uIcc a b → ∀ i,
      finiteMinimum (fun j => f j t) = f i t → δ ≤ deriv (f i) t) :
    ∀ᵐ t ∂volume, t ∈ uIcc a b →
      δ ≤ deriv (fun s => finiteMinimum (fun j => f j s)) t := by
  have hbranches : ∀ᵐ t ∂volume, ∀ i, t ∈ uIcc a b → DifferentiableAt ℝ (f i) t :=
    ae_all_iff.mpr fun i => (hf i).ae_differentiableAt
  filter_upwards [(finiteMinimum_ac f hf).ae_differentiableAt, hbranches, hbound]
    with t hF hi hb ht
  obtain ⟨i, hactive⟩ := finiteMinimum_attained (fun j => f j t)
  rw [finiteMinimum_deriv_eq_active f (hF ht) (hi i ht) hactive]
  exact hb ht i hactive

theorem finiteMinimum_ae_deriv_lower_bound_on {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) (P : ℝ → Prop) {a b δ : ℝ}
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) a b)
    (hbound : ∀ᵐ t ∂volume, t ∈ uIcc a b → P t → ∀ i,
      finiteMinimum (fun j => f j t) = f i t → δ ≤ deriv (f i) t) :
    ∀ᵐ t ∂volume, t ∈ uIcc a b → P t →
      δ ≤ deriv (fun s => finiteMinimum (fun j => f j s)) t := by
  have hbranches : ∀ᵐ t ∂volume, ∀ i, t ∈ uIcc a b → DifferentiableAt ℝ (f i) t :=
    ae_all_iff.mpr fun i => (hf i).ae_differentiableAt
  filter_upwards [(finiteMinimum_ac f hf).ae_differentiableAt, hbranches, hbound]
    with t hF hi hb ht hP
  obtain ⟨i, hactive⟩ := finiteMinimum_attained (fun j => f j t)
  rw [finiteMinimum_deriv_eq_active f (hF ht) (hi i ht) hactive]
  exact hb ht hP i hactive

theorem growth_of_ac_deriv_lower_bound {g : ℝ → ℝ} {a b δ : ℝ}
    (hab : a ≤ b) (hg : AbsolutelyContinuousOnInterval g a b)
    (hbound : ∀ᵐ t ∂volume, t ∈ Icc a b → δ ≤ deriv g t) :
    δ * (b - a) ≤ g b - g a := by
  have hb : (fun _ : ℝ => δ) ≤ᵐ[volume.restrict (Icc a b)] deriv g := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hbound] with t ht hb
    exact hb ht
  have hh := intervalIntegral.integral_mono_ae_restrict hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => δ) volume a b)
    hg.intervalIntegrable_deriv hb
  rw [hg.integral_deriv_eq_sub, intervalIntegral.integral_const, smul_eq_mul] at hh
  simpa only [mul_comm] using hh

theorem finiteMinimum_growth {I : Type*} [Fintype I] [Nonempty I]
    (f : I → ℝ → ℝ) {a b δ : ℝ} (hab : a ≤ b)
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) a b)
    (hbound : ∀ᵐ t ∂volume, t ∈ Icc a b → ∀ i,
      finiteMinimum (fun j => f j t) = f i t → δ ≤ deriv (f i) t) :
    δ * (b - a) ≤ finiteMinimum (fun i => f i b) - finiteMinimum (fun i => f i a) := by
  apply growth_of_ac_deriv_lower_bound hab (finiteMinimum_ac f hf)
  simpa only [uIcc_of_le hab] using
    finiteMinimum_ae_deriv_lower_bound f hf (by simpa only [uIcc_of_le hab] using hbound)

end Endotactic
end

-- Source: Endotactic/ZeroSlopeActivity.lean
section
/-!
# Zero slopes near the zero exponent

A pointwise tolerance below half the norm of every nonzero slope forces
all labels active sufficiently near the zero exponent to have zero slope.
The labels are fixed and finite; neither offsets nor tolerance are continuous.
-/

namespace Endotactic

open Filter Topology

noncomputable def zeroForcingTolerance {d : ℕ} (ε : State d → ℝ)
    (r : State d) : ℝ := min (ε r) (if r = 0 then 1 / 2 else ‖r‖ / 2)

theorem zeroForcingTolerance_pos {d : ℕ} {ε : State d → ℝ}
    (hε : ∀ r, 0 < ε r) (r : State d) : 0 < zeroForcingTolerance ε r := by
  classical
  unfold zeroForcingTolerance
  apply lt_min (hε r)
  split_ifs with hr
  · norm_num
  · exact div_pos (norm_pos_iff.mpr hr) (by norm_num)

theorem zeroForcingTolerance_le {d : ℕ} (ε : State d → ℝ) (r : State d) :
    zeroForcingTolerance ε r ≤ ε r := min_le_left _ _

theorem zeroForcingTolerance_zero {d : ℕ} (ε : State d → ℝ) :
    zeroForcingTolerance ε 0 ≤ 1 / 2 := by
  simp [zeroForcingTolerance]

theorem zeroForcingTolerance_nonzero {d : ℕ} (ε : State d → ℝ)
    {r : State d} (hr : r ≠ 0) : zeroForcingTolerance ε r ≤ ‖r‖ / 2 := by
  simpa only [zeroForcingTolerance, ite_eq_right hr] using
    (min_le_right (ε r) (‖r‖ / 2))

theorem ScaledAffineFamily.sequentialActivityBound_tolerance_mono {d m : ℕ}
    (A : ScaledAffineFamily d m) {K : Set (State d)} {ε η : Fin m → ℝ}
    (hseq : A.HasSequentialActivityBound K ε) (hle : ∀ i, ε i ≤ η i) :
    A.HasSequentialActivityBound K η := by
  intro i h p q hh hlim hplim hq hi
  exact (hseq i h p q hh hlim hplim hq hi).trans_le (hle i)

/-- The exponent points in this neighborhood need not belong to `K`. -/
theorem ScaledAffineFamily.exists_zero_active_neighborhood {d m : ℕ}
    [Nonempty (Fin m)] (A : ScaledAffineFamily d m) {K : Set (State d)}
    (hzero : (0 : State d) ∈ K) (ε : Fin m → ℝ)
    (hseq : A.HasSequentialActivityBound K ε)
    (hsmall : ∀ i, A.slope i ≠ 0 → ε i ≤ ‖A.slope i‖ / 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ p : State d, ‖p‖ < δ → ∀ i,
        (A.atScale h).Active i (exponentialPoint h p) → A.slope i = 0 := by
  classical
  have hex : ∀ i : Fin m, ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ p : State d, ‖p‖ < δ →
        (A.atScale h).Active i (exponentialPoint h p) → A.slope i = 0 := by
    intro i
    by_cases hi : A.slope i = 0
    · exact ⟨1, by norm_num, fun _ _ _ _ _ _ => hi⟩
    · have hnot : (0 : State d) ∉ A.activityLimit i := by
        intro hlim
        have hb := (A.sequentialActivityBound_iff_limits K ε).mp hseq i 0 hzero hlim
        simp only [zero_sub, norm_neg] at hb
        have hn := norm_nonneg (A.slope i)
        have he := hsmall i hi
        linarith
      by_contra hbad
      push Not at hbad
      apply hnot
      apply mem_scaleLimit_iff_small_witness.mpr
      intro δ hδ
      obtain ⟨h, hh, hlt, p, hp, hactive, hne⟩ := hbad δ hδ
      exact ⟨h, hh, hlt, p, by simpa only [dist_zero_right] using hp, hactive⟩
  choose δ hδ hgood using hex
  have hmin : 0 < finiteMinimum δ := by
    obtain ⟨i, hi⟩ := finiteMinimum_attained δ
    rw [hi]
    exact hδ i
  refine ⟨finiteMinimum δ, hmin, ?_⟩
  intro h hh hlt p hp i hactive
  exact hgood i h hh (hlt.trans_le (finiteMinimum_le δ i)) p
    (hp.trans_le (finiteMinimum_le δ i)) hactive

end Endotactic
end

-- Source: Endotactic/LogarithmicBox.lean
section
/-!
# Positive boxes and inverse exponential coordinates

For a fixed positive state, its exponent coordinates tend to zero as the
scale tends to zero. Connectedness turns absence of box-boundary points into
containment in the open box when one interior point is known.
-/

namespace Endotactic

open Filter Topology

noncomputable def logarithmicExponent {d : ℕ} (h : ℝ) (x : State d) : State d :=
  fun j => Real.log (x j) / Real.log h

theorem exponentialPoint_logarithmicExponent {d : ℕ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1) {x : State d} (hx : Positive x) :
    exponentialPoint h (logarithmicExponent h x) = x := by
  have hl : Real.log h ≠ 0 := ne_of_lt (Real.log_neg hh hh1)
  ext j
  change h ^ (Real.log (x j) / Real.log h) = x j
  rw [Real.rpow_def_of_pos hh]
  have heq : Real.log h * (Real.log (x j) / Real.log h) = Real.log (x j) := by
    field_simp
  rw [heq, Real.exp_log (hx j)]

theorem tendsto_logarithmicExponent {d : ℕ} (x : State d) :
    Tendsto (fun h => logarithmicExponent h x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro j
  exact Real.tendsto_log_nhdsGT_zero.const_div_atBot (Real.log (x j))

theorem logarithmicExponent_mem_cube {d : ℕ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1) {x : State d}
    (hx : x ∈ Set.Icc (fun _ => h) (fun _ => h⁻¹)) :
    logarithmicExponent h x ∈ Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
  have hl : Real.log h < 0 := Real.log_neg hh hh1
  have hxpos : Positive x := fun j => hh.trans_le (hx.1 j)
  constructor
  · intro j
    apply (le_div_iff_of_neg hl).mpr
    have hb := Real.log_le_log (hxpos j) (hx.2 j)
    rw [Real.log_inv] at hb
    simpa only [neg_one_mul] using hb
  · intro j
    apply (div_le_iff_of_neg hl).mpr
    simpa only [one_mul] using Real.log_le_log hh (hx.1 j)

theorem logarithmicExponent_boundary_norm {d : ℕ} {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1) {x : State d}
    (hx : x ∈ Set.Icc (fun _ => h) (fun _ => h⁻¹))
    (hboundary : ¬ ∀ j, h < x j ∧ x j < h⁻¹) :
    1 ≤ ‖logarithmicExponent h x‖ := by
  classical
  have hl : Real.log h ≠ 0 := ne_of_lt (Real.log_neg hh hh1)
  push Not at hboundary
  obtain ⟨j, hj⟩ := hboundary
  have heq : x j = h ∨ x j = h⁻¹ := by
    by_cases hlow : h < x j
    · exact Or.inr (le_antisymm (hx.2 j) (hj hlow))
    · exact Or.inl (le_antisymm (not_lt.mp hlow) (hx.1 j))
  have hn : |logarithmicExponent h x j| ≤ ‖logarithmicExponent h x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (logarithmicExponent h x) j
  rcases heq with heq | heq
  · simpa only [logarithmicExponent, heq, div_self hl, abs_one] using hn
  · simpa only [logarithmicExponent, heq, Real.log_inv, neg_div, div_self hl,
      abs_neg, abs_one] using hn

def openCoordinateBox {d : ℕ} (lo hi : State d) : Set (State d) :=
  {x | ∀ j, lo j < x j ∧ x j < hi j}

theorem isOpen_openCoordinateBox {d : ℕ} (lo hi : State d) :
    IsOpen (openCoordinateBox lo hi) := by
  have h := isOpen_iInter_of_finite (fun j : Fin d =>
    (isOpen_Ioo : IsOpen (Set.Ioo (lo j) (hi j))).preimage
      (continuous_apply j : Continuous (fun x : State d => x j)))
  convert h using 1
  ext x
  simp only [openCoordinateBox, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage,
    Set.mem_Ioo]

/-- No coercivity or support-function computation is needed. -/
theorem convex_subset_open_box_of_no_boundary {d : ℕ} {K : Set (State d)}
    (hK : Convex ℝ K) {lo hi : State d} {z : State d}
    (hz : z ∈ K) (hzbox : z ∈ openCoordinateBox lo hi)
    (hboundary : ∀ x ∈ K, x ∈ Set.Icc lo hi → x ∈ openCoordinateBox lo hi) :
    K ⊆ openCoordinateBox lo hi := by
  classical
  have hsub : openCoordinateBox lo hi ⊆ Set.Icc lo hi :=
    fun x hx => ⟨fun j => (hx j).1.le, fun j => (hx j).2.le⟩
  have hunion : K ⊆ openCoordinateBox lo hi ∪ (Set.Icc lo hi)ᶜ := by
    intro x hx
    by_cases hb : x ∈ Set.Icc lo hi
    · exact Or.inl (hboundary x hx hb)
    · exact Or.inr hb
  have hdis : Disjoint (openCoordinateBox lo hi) (Set.Icc lo hi)ᶜ := by
    exact Set.disjoint_left.mpr (fun x hx hn => hn (hsub hx))
  rcases IsPreconnected.subset_or_subset (isOpen_openCoordinateBox lo hi)
      isClosed_Icc.isOpen_compl hdis hunion hK.isPreconnected with h | h
  · exact h
  · exact ((h hz) (hsub hzbox)).elim

end Endotactic
end

-- Source: Endotactic/LinearGeometry.lean
section
/-! # Conserved affine branches cannot obstruct ascent outside the plateau -/

namespace Endotactic

def dotLinear {d : ℕ} (r : State d) : State d →ₗ[ℝ] ℝ where
  toFun := dot r
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem dot_eq_of_zero_projections {d : ℕ} {E : Type*} (N : Network d E)
    (r : State d) {x c : State d} (hx : x - c ∈ N.stoichiometricSubspace)
    (hzero : ∀ e, N.projection r e = 0) : dot r x = dot r c := by
  have hsub : N.stoichiometricSubspace ≤ (dotLinear r).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e, rfl⟩
    exact hzero e
  have hh : dot r (x - c) = 0 := hsub hx
  rw [dot_sub] at hh
  linarith

theorem active_direction_has_nonzero_projection {d m : ℕ} {E : Type*}
    (N : Network d E) (A : AffineFamily d m) {x c : State d} {i : Fin m} {M : ℝ}
    (hx : x ∈ N.positiveClass c) (hi : A.Active i x)
    (hout : x ∉ A.plateau M) (hc : c ∈ A.plateau M) :
    ∃ e : E, N.projection (A.slope i) e ≠ 0 := by
  by_contra h
  have hzero : ∀ e, N.projection (A.slope i) e = 0 := by
    simpa only [not_exists, not_not] using h
  have heq := dot_eq_of_zero_projections N (A.slope i) hx.2 hzero
  apply A.active_value_ne_at_class_representative hi hout hc
  simp only [AffineFamily.value]
  rw [heq]

theorem active_direction_has_positive_essential_source {d m : ℕ} {E : Type*}
    [Fintype E] (N : Network d E) (hN : N.IsEndotactic) (A : AffineFamily d m)
    {x c : State d} {i : Fin m} {M : ℝ}
    (hx : x ∈ N.positiveClass c) (hi : A.Active i x)
    (hout : x ∉ A.plateau M) (hc : c ∈ A.plateau M) :
    ∃ e : E, 0 < N.projection (A.slope i) e ∧
      ∀ f : E, N.projection (A.slope i) f < 0 →
        N.sourceLevel (A.slope i) e < N.sourceLevel (A.slope i) f :=
  exists_positive_essential_source N hN
    (active_direction_has_nonzero_projection N A hx hi hout hc)

end Endotactic
end

-- Source: Endotactic/ScalarBarrier.lean
section
/-!
# Scalar growth implies finite-time absorption

These lemmas isolate the final analytic step. In the general permanence proof,
the function is the finite affine minimum along a trajectory. Proving the
appropriate one-sided derivative or absolutely-continuous growth estimate for
that minimum remains a separate obligation.
-/

namespace Endotactic

open Set

set_option backward.isDefEq.respectTransparency false in
theorem growth_of_right_derivative_lower_bound (g g' : ℝ → ℝ) {s t δ : ℝ}
    (hst : s ≤ t) (hg : ContinuousOn g (Icc s t))
    (hg' : ∀ z ∈ Ico s t, HasDerivWithinAt g (g' z) (Ici z) z)
    (hδ : ∀ z ∈ Ico s t, δ ≤ g' z) :
    δ * (t - s) ≤ g t - g s := by
  let : NormedSpace ℝ ℝ := NormedField.toNormedSpace
  have hbound := image_le_of_deriv_right_le_deriv_boundary
    (f := fun z => -g z) (f' := fun z => -g' z) hg.neg
    (fun z hz => (hg' z hz).neg)
    (B := fun z => -g s - δ * (z - s)) (B' := fun _ => -δ)
    (by simp) (by fun_prop)
    (fun z _ => by
      convert ((hasDerivAt_const z (-g s)).sub
        (((hasDerivAt_id z).sub_const s).const_mul δ)).hasDerivWithinAt (s := Ici z)
        using 1 <;> first | rfl | simp)
    (fun z hz => by linarith [hδ z hz])
    (x := t) ⟨hst, le_rfl⟩
  linarith

theorem finite_entry_of_growth (g : ℝ → ℝ) {s M δ : ℝ}
    (hδ : 0 < δ) (hupper : ∀ t, s ≤ t → g t ≤ M)
    (hgrowth : ∀ t, s ≤ t → (∀ z ∈ Icc s t, g z < M) →
      δ * (t - s) ≤ g t - g s) :
    ∃ t : ℝ, s ≤ t ∧ g t = M := by
  by_contra h
  have hlt : ∀ t, s ≤ t → g t < M := by
    intro t ht
    exact lt_of_le_of_ne (hupper t ht) (fun he => h ⟨t, ht, he⟩)
  let t := s + (M - g s + 1) / δ
  have hst : s ≤ t := by
    dsimp [t]
    have hnum : 0 ≤ M - g s + 1 := by linarith [hupper s le_rfl]
    exact le_add_of_nonneg_right (div_nonneg hnum hδ.le)
  have hh := hgrowth t hst (fun z hz => hlt z hz.1)
  have hidentity : δ * (t - s) = M - g s + 1 := by
    dsimp [t]
    rw [add_sub_cancel_left, mul_div_cancel₀ _ hδ.ne']
  rw [hidentity] at hh
  linarith [hupper t hst]

theorem eventual_plateau_of_growth (g : ℝ → ℝ) {s M δ : ℝ}
    (hs : 0 ≤ s) (hδ : 0 < δ) (hupper : ∀ t, s ≤ t → g t ≤ M)
    (hgrowth : ∀ t, s ≤ t → (∀ z ∈ Icc s t, g z < M) →
      δ * (t - s) ≤ g t - g s)
    (hinvariant : ∀ a, s ≤ a → g a = M → ∀ t, a ≤ t → g t = M) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → g t = M := by
  obtain ⟨T, hT, heq⟩ := finite_entry_of_growth g hδ hupper hgrowth
  exact ⟨T, hs.trans hT, hinvariant T hT heq⟩

end Endotactic
end

-- Source: Endotactic/AbsoluteBarrier.lean
section
/-!
# A capped absolutely continuous observable reaches and stays on its plateau

The cap makes its derivative zero almost everywhere on the plateau by Fermat's
theorem. A nonnegative derivative below the cap therefore gives monotonicity;
no separate invariance assumption is needed. A strictly positive lower bound
below the cap then gives finite entry.
-/

namespace Endotactic

open MeasureTheory Set Filter
open scoped Topology

theorem ac_monotone_of_below_cap_deriv_nonneg (g : ℝ → ℝ) {s M : ℝ}
    (hg : ∀ T, s ≤ T → AbsolutelyContinuousOnInterval g s T)
    (hupper : ∀ t, s ≤ t → g t ≤ M)
    (hbelow : ∀ T, s ≤ T → ∀ᵐ t ∂volume,
      t ∈ Icc s T → g t < M → 0 ≤ deriv g t) :
    ∀ a b, s ≤ a → a ≤ b → g a ≤ g b := by
  intro a b hsa hab
  have hsb := hsa.trans hab
  have hac : AbsolutelyContinuousOnInterval g a b := by
    apply (hg b hsb).mono
    simpa only [uIcc_of_le hab, uIcc_of_le hsb] using
      (show Icc a b ⊆ Icc s b from fun _ ht => ⟨hsa.trans ht.1, ht.2⟩)
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ s := by simp [ae_iff, measure_singleton]
  have hd : ∀ᵐ t ∂volume, t ∈ Icc a b → 0 ≤ deriv g t := by
    filter_upwards [hac.ae_differentiableAt, hbelow b hsb, hne]
      with t hdiff hb hts ht
    have hst : s ≤ t := hsa.trans ht.1
    rcases lt_or_eq_of_le (hupper t hst) with hlt | heq
    · exact hb ⟨hst, ht.2⟩ hlt
    · have hmax : IsLocalMax g t := by
        filter_upwards [Ioi_mem_nhds (lt_of_le_of_ne hst hts.symm)] with z hz
        rw [heq]
        exact hupper z hz.le
      rw [hmax.hasDerivAt_eq_zero (hdiff (by simpa only [uIcc_of_le hab] using ht)).hasDerivAt]
  have hh := growth_of_ac_deriv_lower_bound hab hac hd
  linarith

theorem eventual_plateau_of_ac (g : ℝ → ℝ) {s M δ : ℝ}
    (hs : 0 ≤ s) (hδ : 0 < δ)
    (hg : ∀ T, s ≤ T → AbsolutelyContinuousOnInterval g s T)
    (hupper : ∀ t, s ≤ t → g t ≤ M)
    (hbelow : ∀ T, s ≤ T → ∀ᵐ t ∂volume,
      t ∈ Icc s T → g t < M → δ ≤ deriv g t) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t → g t = M := by
  have hmono := ac_monotone_of_below_cap_deriv_nonneg g hg hupper (by
    intro T hT
    filter_upwards [hbelow T hT] with t ht hmem hlt
    exact hδ.le.trans (ht hmem hlt))
  apply eventual_plateau_of_growth g hs hδ hupper
  · intro T hT hlt
    apply growth_of_ac_deriv_lower_bound hT (hg T hT)
    filter_upwards [hbelow T hT] with t ht hmem
    exact ht hmem (hlt t hmem)
  · intro a ha heq t hat
    exact le_antisymm (hupper t (ha.trans hat)) (heq ▸ hmono a t ha hat)

end Endotactic
end

-- Source: Endotactic/IntegralTrajectory.lean
section
/-!
# Affine observables and finite minima of integral trajectories

No differentiability of the rate path is assumed. Interval integrability in the
solution predicate suffices to obtain scalar absolute continuity and the ODE
for each affine observable almost everywhere.
-/

namespace Endotactic

open MeasureTheory Set Filter
open scoped Topology

noncomputable def dotCLM {d : ℕ} (r : State d) : State d →L[ℝ] ℝ :=
  (dotLinear r).toContinuousLinearMap

theorem clm_intervalIntegrable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W)
    {f : ℝ → V} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => L (f t)) volume a b :=
  ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩

variable {d : ℕ} {E : Type*} [Fintype E]
variable {N : Network d E} {k : E → ℝ → ℝ} {x₀ : State d} {x : ℝ → State d}

theorem Network.IsIntegralSolution.dot_integral_eq
    (hx : N.IsIntegralSolution k x₀ x) (r : State d) {t : ℝ} (ht : 0 ≤ t) :
    dot r (x t) = dot r x₀ +
      ∫ s in (0 : ℝ)..t, dot r (N.rhs (fun e => k e s) (x s)) := by
  have h := congrArg (dotCLM r) (hx.2.2.2 t ht)
  rw [map_add, ← (dotCLM r).intervalIntegral_comp_comm (hx.2.2.1 t ht)] at h
  exact h

theorem Network.IsIntegralSolution.dot_intervalIntegrable
    (hx : N.IsIntegralSolution k x₀ x) (r : State d) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun s => dot r (N.rhs (fun e => k e s) (x s))) volume 0 T :=
  clm_intervalIntegrable (dotCLM r) (hx.2.2.1 T hT)

theorem Network.IsIntegralSolution.dot_ac
    (hx : N.IsIntegralSolution k x₀ x) (r : State d) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => dot r (x t)) 0 T := by
  have hp := (hx.dot_intervalIntegrable r hT).absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) (by simp)
  apply ac_congrOn ((ac_const (dot r x₀) 0 T).add hp)
  intro t ht
  have ht' : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
  exact (hx.dot_integral_eq r ht'.1).symm

theorem Network.IsIntegralSolution.dot_ae_hasDerivAt
    (hx : N.IsIntegralSolution k x₀ x) (r : State d) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt (fun s => dot r (x s)) (dot r (N.rhs (fun e => k e t) (x t))) t := by
  have hzero : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have htop : ∀ᵐ t : ℝ ∂volume, t ≠ T := by simp [ae_iff, measure_singleton]
  filter_upwards [(hx.dot_intervalIntegrable r hT).ae_hasDerivAt_integral, hzero, htop]
    with t hp hz ht hmem
  have hlt0 : 0 < t := lt_of_le_of_ne hmem.1 hz.symm
  have hltT : t < T := lt_of_le_of_ne hmem.2 ht
  have hp' := (hp (by simpa only [uIcc_of_le hT] using hmem) 0 (by simp)).const_add (dot r x₀)
  apply hp'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hlt0 hltT] with s hs
  exact hx.dot_integral_eq r hs.1.le

theorem AffineFamily.branch_ac {m : ℕ} (A : AffineFamily d m)
    (hx : N.IsIntegralSolution k x₀ x) (i : Fin m) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => A.value i (x t)) 0 T := by
  exact (hx.dot_ac (A.slope i) hT).add (ac_const (A.offset i) 0 T)

theorem AffineFamily.branch_ae_hasDerivAt {m : ℕ} (A : AffineFamily d m)
    (hx : N.IsIntegralSolution k x₀ x) (i : Fin m) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt (fun s => A.value i (x s))
      (dot (A.slope i) (N.rhs (fun e => k e t) (x t))) t := by
  filter_upwards [hx.dot_ae_hasDerivAt (A.slope i) hT] with t ht hmem
  exact (ht hmem).add_const (A.offset i)

noncomputable def AffineFamily.minimum {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (z : State d) : ℝ := finiteMinimum (fun i => A.value i z)

theorem AffineFamily.active_iff_minimum_eq {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (i : Fin m) (z : State d) :
    A.Active i z ↔ A.minimum z = A.value i z := by
  constructor
  · intro hi
    apply le_antisymm (finiteMinimum_le _ i)
    exact Finset.le_inf' Finset.univ_nonempty _ (fun j _ => hi j)
  · intro hi j
    rw [← hi]
    exact finiteMinimum_le _ j

theorem AffineFamily.minimum_ac {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (hx : N.IsIntegralSolution k x₀ x)
    {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => A.minimum (x t)) 0 T :=
  finiteMinimum_ac (fun i t => A.value i (x t)) (fun i => A.branch_ac hx i hT)

theorem AffineFamily.minimum_growth {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (hx : N.IsIntegralSolution k x₀ x) {a b δ : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hbound : ∀ t ∈ Icc a b, ∀ i, A.Active i (x t) →
      δ ≤ dot (A.slope i) (N.rhs (fun e => k e t) (x t))) :
    δ * (b - a) ≤ A.minimum (x b) - A.minimum (x a) := by
  have hb : 0 ≤ b := ha.trans hab
  apply finiteMinimum_growth (fun i t => A.value i (x t)) hab
  · intro i
    apply (A.branch_ac hx i hb).mono
    simpa only [uIcc_of_le hab, uIcc_of_le hb] using
      (show Icc a b ⊆ Icc 0 b from fun _ ht => ⟨ha.trans ht.1, ht.2⟩)
  · have hderivs : ∀ᵐ t ∂volume, ∀ i, t ∈ Icc 0 b →
        HasDerivAt (fun s => A.value i (x s))
          (dot (A.slope i) (N.rhs (fun e => k e t) (x t))) t :=
      ae_all_iff.mpr fun i => A.branch_ae_hasDerivAt hx i hb
    filter_upwards [hderivs] with t ht hmem i hactive
    rw [(ht i ⟨ha.trans hmem.1, hmem.2⟩).deriv]
    exact hbound t hmem i ((A.active_iff_minimum_eq i (x t)).mpr hactive)

theorem AffineFamily.mem_plateau_iff_minimum_ge {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (z : State d) (M : ℝ) :
    z ∈ A.plateau M ↔ M ≤ A.minimum z := by
  constructor
  · intro hz
    exact Finset.le_inf' Finset.univ_nonempty _ (fun i _ => hz i)
  · intro hz i
    exact hz.trans (finiteMinimum_le _ i)

theorem AffineFamily.minimum_le_constant_branch {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (i : Fin m) (hslope : ∀ j, A.slope i j = 0)
    (z : State d) : A.minimum z ≤ A.offset i := by
  simpa only [AffineFamily.minimum, A.constant_value i hslope z] using
    (finiteMinimum_le (fun j => A.value j z) i)

theorem AffineFamily.minimum_ae_deriv_lower_bound_below {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (hx : N.IsIntegralSolution k x₀ x) {T M δ : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ t ∈ Icc 0 T, A.minimum (x t) < M → ∀ i,
      A.Active i (x t) → δ ≤ dot (A.slope i) (N.rhs (fun e => k e t) (x t))) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T → A.minimum (x t) < M →
      δ ≤ deriv (fun s => A.minimum (x s)) t := by
  have hderivs : ∀ᵐ t ∂volume, ∀ i, t ∈ Icc 0 T →
      HasDerivAt (fun s => A.value i (x s))
        (dot (A.slope i) (N.rhs (fun e => k e t) (x t))) t :=
    ae_all_iff.mpr fun i => A.branch_ae_hasDerivAt hx i hT
  have hb : ∀ᵐ t ∂volume, t ∈ uIcc 0 T → A.minimum (x t) < M → ∀ i,
      finiteMinimum (fun j => A.value j (x t)) = A.value i (x t) →
        δ ≤ deriv (fun s => A.value i (x s)) t := by
    filter_upwards [hderivs] with t ht hmem hlt i hactive
    have hmem' : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using hmem
    rw [(ht i hmem').deriv]
    exact hbound t hmem' hlt i ((A.active_iff_minimum_eq i (x t)).mpr hactive)
  simpa only [AffineFamily.minimum, uIcc_of_le hT] using finiteMinimum_ae_deriv_lower_bound_on
    (fun i t => A.value i (x t)) (fun t => A.minimum (x t) < M)
    (fun i => A.branch_ac hx i hT) hb

/-- The analytic absorption step, conditional on the uniform geometric flux bound.
This neither constructs the family nor establishes existence of the trajectory. -/
theorem AffineFamily.eventuallyIn_plateau {m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (hx : N.IsIntegralSolution k x₀ x) {M δ : ℝ} (hδ : 0 < δ)
    (hcap : ∀ t, 0 ≤ t → A.minimum (x t) ≤ M)
    (hbound : ∀ t, 0 ≤ t → A.minimum (x t) < M → ∀ i,
      A.Active i (x t) → δ ≤ dot (A.slope i) (N.rhs (fun e => k e t) (x t))) :
    EventuallyIn x (A.plateau M) := by
  obtain ⟨T, hT, hstay⟩ := eventual_plateau_of_ac (fun t => A.minimum (x t))
    (s := 0) le_rfl hδ (fun T hT => A.minimum_ac hx hT) hcap (by
      intro T hT
      exact A.minimum_ae_deriv_lower_bound_below hx hT
        (fun t ht => hbound t ht.1))
  refine ⟨T, hT, fun t ht => (A.mem_plateau_iff_minimum_ge (x t) M).mpr ?_⟩
  exact (hstay t ht).ge

end Endotactic
end

-- Source: Endotactic/ScaledZeroCap.lean
section
/-!
# Compact positive plateaux from a zero branch

The constant active branch caps the whole affine minimum. Uniform exclusion
of this branch on the exponent-box boundary, convexity and one interior point
put its entire maximal plateau inside the positive box.
-/

namespace Endotactic

open Filter Topology

theorem AffineFamily.exists_active {d m : ℕ} [Nonempty (Fin m)]
    (A : AffineFamily d m) (x : State d) : ∃ i, A.Active i x := by
  obtain ⟨i, hi⟩ := finiteMinimum_attained (fun j => A.value j x)
  exact ⟨i, (A.active_iff_minimum_eq i x).mpr hi⟩

theorem ScaledAffineFamily.zero_cap_plateau_subset_open_box {d m : ℕ}
    (A : ScaledAffineFamily d m) {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (i₀ : Fin m) (hi₀ : A.slope i₀ = 0) {z : State d}
    (hz : (A.atScale h).Active i₀ z)
    (hzbox : z ∈ openCoordinateBox (fun _ => h) (fun _ => h⁻¹))
    (hactive : ∀ p ∈ Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
      (A.atScale h).Active i₀ (exponentialPoint h p) → ‖p‖ < 1) :
    (A.atScale h).plateau (A.offset i₀ h) ⊆
      openCoordinateBox (fun _ => h) (fun _ => h⁻¹) := by
  have hslope : ∀ j, (A.atScale h).slope i₀ j = 0 :=
    fun j => congrFun hi₀ j
  have hzK := ((A.atScale h).constant_active_iff_mem_plateau i₀ hslope z).mp hz
  apply convex_subset_open_box_of_no_boundary ((A.atScale h).plateau_convex _) hzK hzbox
  intro x hx hbox
  by_contra hboundary
  have hxpos : Positive x := fun j => hh.trans_le (hbox.1 j)
  have hpow := exponentialPoint_logarithmicExponent hh hh1 hxpos
  have hi := ((A.atScale h).constant_active_iff_mem_plateau i₀ hslope x).mpr hx
  have hp := logarithmicExponent_mem_cube hh hh1 hbox
  have hlt := hactive (logarithmicExponent h x) hp (hpow.symm ▸ hi)
  exact (not_lt_of_ge (logarithmicExponent_boundary_norm hh hh1 hbox hboundary)) hlt

theorem ScaledAffineFamily.zero_cap_plateau_compact_positive {d m : ℕ}
    (A : ScaledAffineFamily d m) {h : ℝ} (hh : 0 < h) (hh1 : h < 1)
    (i₀ : Fin m) (hi₀ : A.slope i₀ = 0) {z : State d}
    (hz : (A.atScale h).Active i₀ z)
    (hzbox : z ∈ openCoordinateBox (fun _ => h) (fun _ => h⁻¹))
    (hactive : ∀ p ∈ Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
      (A.atScale h).Active i₀ (exponentialPoint h p) → ‖p‖ < 1) :
    IsCompact ((A.atScale h).plateau (A.offset i₀ h)) ∧
      (A.atScale h).plateau (A.offset i₀ h) ⊆ {x | Positive x} ∧
      (A.atScale h).plateau (A.offset i₀ h) ⊆ Set.Icc (fun _ => h) (fun _ => h⁻¹) := by
  have hsub := A.zero_cap_plateau_subset_open_box hh hh1 i₀ hi₀ hz hzbox hactive
  have hbox : (A.atScale h).plateau (A.offset i₀ h) ⊆
      Set.Icc (fun _ => h) (fun _ => h⁻¹) :=
    fun x hx => ⟨fun j => (hsub hx j).1.le, fun j => (hsub hx j).2.le⟩
  exact ⟨(A.atScale h).plateau_isCompact_of_subset _ isCompact_Icc hbox,
    fun x hx j => hh.trans (hsub hx j).1, hbox⟩

/-- A fixed finite family works for every positive reference point. The scale
threshold is allowed to depend on that point; this is not common absorption. -/
theorem ScaledAffineFamily.exists_small_scale_zero_cap {d m : ℕ}
    [Nonempty (Fin m)] (A : ScaledAffineFamily d m) (ε : State d → ℝ)
    (hseq : A.HasSequentialActivityBound
      (Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
      (fun i => zeroForcingTolerance ε (A.slope i)))
    {z : State d} (hz : Positive z) :
    ∃ H : ℝ, 0 < H ∧ H ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < H →
      ∃ i₀ : Fin m, A.slope i₀ = 0 ∧
        z ∈ (A.atScale h).plateau (A.offset i₀ h) ∧
        IsCompact ((A.atScale h).plateau (A.offset i₀ h)) ∧
        (A.atScale h).plateau (A.offset i₀ h) ⊆ {x | Positive x} ∧
        (A.atScale h).plateau (A.offset i₀ h) ⊆ Set.Icc (fun _ => h) (fun _ => h⁻¹) := by
  have hzero : (0 : State d) ∈ Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) :=
    ⟨fun _ => by norm_num, fun _ => by norm_num⟩
  obtain ⟨δ, hδ, hnear⟩ := A.exists_zero_active_neighborhood hzero _ hseq
    (fun i hi => zeroForcingTolerance_nonzero ε hi)
  obtain ⟨H₁, hH₁, hH₁1, huniform⟩ := A.uniformActivityBound_of_sequential _
    isCompact_Icc _ hseq
  have hevent : ∀ᶠ h in 𝓝[>] (0 : ℝ), ‖logarithmicExponent h z‖ < min δ 1 :=
    (tendsto_logarithmicExponent z).norm.eventually
      (by simpa only [norm_zero] using
        (gt_mem_nhds (lt_min hδ (by norm_num)) :
          ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), x < min δ 1))
  obtain ⟨H₂, hH₂, hlog⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  refine ⟨min H₁ (min δ (min H₂ 1)), lt_min hH₁ (lt_min hδ (lt_min hH₂ (by norm_num))),
    (min_le_left _ _).trans hH₁1, ?_⟩
  intro h hh hlt
  have hlt₁ : h < H₁ := hlt.trans_le (min_le_left _ _)
  have hrest : h < min δ (min H₂ 1) := hlt.trans_le (min_le_right _ _)
  have hltδ : h < δ := hrest.trans_le (min_le_left _ _)
  have hrest₂ : h < min H₂ 1 := hrest.trans_le (min_le_right _ _)
  have hlt₂ : h < H₂ := hrest₂.trans_le (min_le_left _ _)
  have hh1 : h < 1 := hrest₂.trans_le (min_le_right _ _)
  have hnorm := hlog ⟨hh, hlt₂⟩
  have hpδ : ‖logarithmicExponent h z‖ < δ := hnorm.trans_le (min_le_left _ _)
  have hp1 : ‖logarithmicExponent h z‖ < 1 := hnorm.trans_le (min_le_right _ _)
  have hpow := exponentialPoint_logarithmicExponent hh hh1 hz
  obtain ⟨i₀, hi₀⟩ := (A.atScale h).exists_active z
  have hslope := hnear h hh hltδ _ hpδ i₀ (hpow.symm ▸ hi₀)
  have hslope' : ∀ j, (A.atScale h).slope i₀ j = 0 := fun j => congrFun hslope j
  have hzK := ((A.atScale h).constant_active_iff_mem_plateau i₀ hslope' z).mp hi₀
  have hzbox : z ∈ openCoordinateBox (fun _ => h) (fun _ => h⁻¹) := by
    intro j
    have hb : |logarithmicExponent h z j| < 1 :=
      (show |logarithmicExponent h z j| ≤ ‖logarithmicExponent h z‖ by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (logarithmicExponent h z) j).trans_lt hp1
    have hp := abs_lt.mp hb
    have hlower := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hp.2
    have hupper := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hp.1
    have heqj : h ^ logarithmicExponent h z j = z j := congrFun hpow j
    simpa only [Real.rpow_one, Real.rpow_neg_one, heqj] using
      (show h ^ (1 : ℝ) < h ^ logarithmicExponent h z j ∧
        h ^ logarithmicExponent h z j < h ^ (-1 : ℝ) from ⟨hlower, hupper⟩)
  have hactive : ∀ p ∈ Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
      (A.atScale h).Active i₀ (exponentialPoint h p) → ‖p‖ < 1 := by
    intro p hp hi
    have hb := huniform h hh hlt₁ p hp i₀ hi
    rw [hslope, sub_zero] at hb
    exact hb.trans_le (zeroForcingTolerance_zero ε) |>.trans (by norm_num)
  obtain ⟨hcompact, hpos, hbox⟩ :=
    A.zero_cap_plateau_compact_positive hh hh1 i₀ hslope hi₀ hzbox hactive
  exact ⟨i₀, hslope, hzK, hcompact, hpos, hbox⟩

end Endotactic
end

-- Source: Endotactic/ScaleIteration.lean
section
/-!
# Finite termination of square-root scale enlargement

This proves the numerical part only. The implication from one plateau's bounds
to the next plateau's entry still requires the geometric construction.
-/

namespace Endotactic

open Filter Topology

noncomputable def rootScale (h : ℝ) (n : ℕ) : ℝ := h ^ ((1 / 2 : ℝ) ^ n)

theorem rootScale_zero (h : ℝ) : rootScale h 0 = h := by
  simp [rootScale]

theorem rootScale_succ {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    rootScale h (n + 1) = Real.sqrt (rootScale h n) := by
  rw [Real.sqrt_eq_rpow]
  unfold rootScale
  rw [← Real.rpow_mul hh, pow_succ]

theorem rootScale_pos {h : ℝ} (hh : 0 < h) (n : ℕ) : 0 < rootScale h n :=
  Real.rpow_pos_of_pos hh _

theorem rootScale_tendsto_one {h : ℝ} (hh : 0 < h) :
    Tendsto (rootScale h) atTop (𝓝 1) := by
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hr : Tendsto (fun y : ℝ => h ^ y) (𝓝 (0 : ℝ)) (𝓝 (h ^ (0 : ℝ))) :=
    (Real.continuousAt_const_rpow (a := h) (b := 0) hh.ne').tendsto
  change Tendsto (fun n : ℕ => h ^ ((1 / 2 : ℝ) ^ n)) atTop (𝓝 1)
  simpa only [Function.comp_def, Real.rpow_zero] using hr.comp hp

theorem rootScale_crosses_threshold {h target : ℝ} (hh : 0 < h)
    (htarget : target < 1) : ∃ n : ℕ, target < rootScale h n := by
  have hevent : ∀ᶠ n : ℕ in atTop, target < rootScale h n :=
    (rootScale_tendsto_one hh).eventually (eventually_gt_nhds htarget)
  exact hevent.exists

theorem capped_rootScale_reaches_threshold {h target : ℝ} (hh : 0 < h)
    (htarget : target < 1) : ∃ n : ℕ, min (rootScale h n) target = target := by
  obtain ⟨n, hn⟩ := rootScale_crosses_threshold hh htarget
  exact ⟨n, min_eq_right hn.le⟩

end Endotactic
end

-- Source: Endotactic/PowerBoxGeometry.lean
section
/-!
# Narrow power boxes and capped square-root scales
-/

namespace Endotactic

noncomputable def powerBox {d : ℕ} (h β : ℝ) : Set (State d) :=
  Set.Icc (fun _ => h ^ β) (fun _ => (h ^ β)⁻¹)

theorem powerBox_positive {d : ℕ} {h β : ℝ} (hh : 0 < h) :
    powerBox (d := d) h β ⊆ {x | Positive x} :=
  fun _ hx j => (Real.rpow_pos_of_pos hh β).trans_le (hx.1 j)

theorem logarithmicExponent_power_scale {d : ℕ} {h β : ℝ}
    (hh : 0 < h) (hβ : β ≠ 0) (x : State d) :
    logarithmicExponent h x = β • logarithmicExponent (h ^ β) x := by
  ext j
  simp only [logarithmicExponent, Pi.smul_apply, smul_eq_mul, Real.log_rpow hh]
  by_cases hl : Real.log h = 0
  · simp [hl]
  · field_simp

theorem logarithmicExponent_mem_power_cube {d : ℕ} {h β : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hβ : 0 < β) {x : State d}
    (hx : x ∈ powerBox h β) :
    logarithmicExponent h x ∈ Set.Icc (fun _ => -β) (fun _ => β) := by
  have hg := Real.rpow_pos_of_pos hh β
  have hg1 := Real.rpow_lt_one hh.le hh1 hβ
  have hp := logarithmicExponent_mem_cube hg hg1 hx
  rw [logarithmicExponent_power_scale hh hβ.ne' x]
  constructor
  · intro j
    simpa only [Pi.smul_apply, smul_eq_mul, mul_neg_one] using
      mul_le_mul_of_nonneg_left (hp.1 j) hβ.le
  · intro j
    simpa only [Pi.smul_apply, smul_eq_mul, mul_one] using
      mul_le_mul_of_nonneg_left (hp.2 j) hβ.le

theorem logarithmicExponent_power_boundary_norm {d : ℕ} {h β : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hβ : 0 < β) {x : State d}
    (hx : x ∈ powerBox h β)
    (hboundary : x ∉ openCoordinateBox (fun _ => h ^ β) (fun _ => (h ^ β)⁻¹)) :
    β ≤ ‖logarithmicExponent h x‖ := by
  have hg := Real.rpow_pos_of_pos hh β
  have hg1 := Real.rpow_lt_one hh.le hh1 hβ
  have hn := logarithmicExponent_boundary_norm hg hg1 hx hboundary
  rw [logarithmicExponent_power_scale hh hβ.ne' x, norm_smul, Real.norm_eq_abs,
    abs_of_pos hβ]
  nlinarith

theorem logarithmicExponent_norm_lt_mem_open_power_box {d : ℕ} {h β : ℝ}
    (hh : 0 < h) (hh1 : h < 1) {x : State d} (hx : Positive x)
    (hp : ‖logarithmicExponent h x‖ < β) :
    x ∈ openCoordinateBox (fun _ => h ^ β) (fun _ => (h ^ β)⁻¹) := by
  have hpow := exponentialPoint_logarithmicExponent hh hh1 hx
  intro j
  have hb : |logarithmicExponent h x j| < β :=
    (show |logarithmicExponent h x j| ≤ ‖logarithmicExponent h x‖ by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (logarithmicExponent h x) j).trans_lt hp
  have hr := abs_lt.mp hb
  have hlo := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hr.2
  have hhi := Real.rpow_lt_rpow_of_exponent_gt hh hh1 hr.1
  have heq : h ^ logarithmicExponent h x j = x j := congrFun hpow j
  simpa only [heq, Real.rpow_neg hh.le] using And.intro hlo hhi

theorem powerBox_subset_unit_box {d : ℕ} {h β g : ℝ}
    (hh : 0 < h) (hg : 0 < g) (hgh : g ≤ h ^ β) :
    powerBox (d := d) h β ⊆ Set.Icc (fun _ => g) (fun _ => g⁻¹) := by
  intro x hx
  refine ⟨fun j => hgh.trans (hx.1 j), fun j => (hx.2 j).trans ?_⟩
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hh β) hg).mpr hgh

theorem capped_sqrt_le_quarter_power {h H : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    min (Real.sqrt h) H ≤ h ^ (1 / 4 : ℝ) := by
  apply (min_le_left _ _).trans
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_ge hh hh1 (by norm_num)

end Endotactic
end

-- Source: Endotactic/NarrowZeroCap.lean
section
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
end

-- Source: Endotactic/AffineCap.lean
section
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
end

-- Source: Endotactic/KineticsRegularity.lean
section
/-!
# Elementary regularity of mass-action kinetics

The finite polynomial formula directly gives state smoothness and measurable
composition, without importing a general Nemytskii theorem. These conditions do
not by themselves provide a nonlinear time-dependent existence theorem.
-/

namespace Endotactic

open scoped ContDiff

variable {d : ℕ} {E : Type*} [Fintype E]

theorem Network.rhs_contDiff (N : Network d E) (k : E → ℝ) :
    ContDiff ℝ ∞ (N.rhs k) := by
  unfold Network.rhs monomial
  fun_prop

theorem Network.rhs_locallyLipschitzOn (N : Network d E) (k : E → ℝ) :
    LocallyLipschitzOn Set.univ (N.rhs k) := by
  exact ContDiffOn.locallyLipschitzOn convex_univ
    ((N.rhs_contDiff k).of_le (by norm_num)).contDiffOn

theorem Network.rhs_measurable (N : Network d E) (k : E → ℝ → ℝ)
    (x : ℝ → State d) (hk : ∀ e, Measurable (k e)) (hx : Measurable x) :
    Measurable (fun t => N.rhs (fun e => k e t) (x t)) := by
  unfold Network.rhs monomial
  fun_prop

end Endotactic
end

-- Source: Endotactic/UniformKinetics.lean
section
/-!
# Lipschitz constants uniform over compact coefficient sets

Treating coefficients and state as one polynomial map provides a common state
Lipschitz constant on any compact convex product. This is the uniform local
estimate needed by the time-dependent Volterra construction; existence of its
fixed point is a separate obligation.
-/

namespace Endotactic

open Set
open scoped ContDiff NNReal

variable {d : ℕ} {E : Type*} [Fintype E]

theorem Network.rhs_joint_contDiff (N : Network d E) :
    ContDiff ℝ ∞ (fun p : (E → ℝ) × State d => N.rhs p.1 p.2) := by
  unfold Network.rhs monomial
  fun_prop

theorem Network.rhs_uniform_lipschitzOn (N : Network d E)
    {K : Set (E → ℝ)} {B : Set (State d)}
    (hK : IsCompact K) (hB : IsCompact B) (hKconv : Convex ℝ K) (hBconv : Convex ℝ B) :
    ∃ L : ℝ≥0, ∀ k ∈ K, LipschitzOnWith L (N.rhs k) B := by
  obtain ⟨L, hL⟩ := (N.rhs_joint_contDiff.contDiffOn).exists_lipschitzOnWith
    (by simp) (hKconv.prod hBconv) (hK.prod hB)
  refine ⟨L, fun k hk => lipschitzOnWith_iff_dist_le_mul.mpr ?_⟩
  intro x hx y hy
  have hh := hL.dist_le_mul (k, x) (show (k, x) ∈ K ×ˢ B from ⟨hk, hx⟩)
    (k, y) (show (k, y) ∈ K ×ˢ B from ⟨hk, hy⟩)
  simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hh

theorem Network.rhs_uniform_lipschitzOn_box (N : Network d E)
    (klo khi : E → ℝ) (xlo xhi : State d) :
    ∃ L : ℝ≥0, ∀ k ∈ Icc klo khi,
      LipschitzOnWith L (N.rhs k) (Icc xlo xhi) :=
  N.rhs_uniform_lipschitzOn isCompact_Icc isCompact_Icc
    (convex_Icc _ _) (convex_Icc _ _)

end Endotactic
end

-- Source: Endotactic/CompactAbsorption.lean
section
/-!
# Compact initial traps turn strict exterior signs into finite-time absorption

Only pointwise strict flux below `M` is assumed. On a compact state trap and
the compact coefficient box, the closed active sublevel at any `Q < M` has
a positive uniform flux margin. This avoids demanding strict flux on the
original `M`-boundary, or a numerical margin on the entire positive class.

Append a constant cap at `Q` to obtain finite entry into `A.plateau Q`.
The trap and margin may depend on the trajectory or initial point. The target
level may be selected independently of both.
-/

namespace Endotactic

open Set

variable {d m : ℕ} [Nonempty (Fin m)] {E : Type*} [Fintype E]

omit [Nonempty (Fin m)] in
theorem AffineFamily.isClosed_active (A : AffineFamily d m) (i : Fin m) :
    IsClosed {x | A.Active i x} := by
  have heq : {x | A.Active i x} = ⋂ j, {x | A.value i x ≤ A.value j x} := by
    ext x
    simp [AffineFamily.Active]
  rw [heq]
  exact isClosed_iInter fun j => isClosed_le (A.continuous_value i) (A.continuous_value j)

theorem Network.exists_affine_active_margin_on_compact_sublevel (N : Network d E)
    (A : AffineFamily d m) {ℓ u M Q : ℝ} {B : Set (State d)} (hB : IsCompact B)
    (hQ : Q < M)
    (hstrict : ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ B, A.minimum y < M → ∀ i, A.Active i y →
        0 < dot (A.slope i) (N.rhs a y)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ B, A.minimum y ≤ Q → ∀ i, A.Active i y →
        δ ≤ dot (A.slope i) (N.rhs a y) := by
  have hbranch : ∀ i : Fin m, ∃ δ : ℝ, 0 < δ ∧
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
        ∀ y ∈ B, A.Active i y → A.value i y ≤ Q →
          δ ≤ dot (A.slope i) (N.rhs a y) := by
    intro i
    let C : Set ((E → ℝ) × State d) :=
      (Icc (fun _ : E => ℓ) (fun _ => u) ×ˢ B) ∩
        {p | A.Active i p.2 ∧ A.value i p.2 ≤ Q}
    have hC : IsCompact C := (isCompact_Icc.prod hB).inter_right
      (((A.isClosed_active i).preimage continuous_snd).inter
        (isClosed_le ((A.continuous_value i).comp continuous_snd) continuous_const))
    have hc : Continuous (fun p : (E → ℝ) × State d =>
        dot (A.slope i) (N.rhs p.1 p.2)) :=
      (dotCLM (A.slope i)).continuous.comp N.rhs_joint_contDiff.continuous
    obtain ⟨δ, hδ, hb⟩ := hC.exists_forall_le' hc.continuousOn (a := 0) (by
      intro p hp
      have heq := (A.active_iff_minimum_eq i p.2).mp hp.2.1
      exact hstrict p.1 hp.1.1 p.2 hp.1.2 (heq ▸ hp.2.2.trans_lt hQ) i hp.2.1)
    exact ⟨δ, hδ, fun a ha y hy hi hval => hb (a, y) ⟨⟨ha, hy⟩, hi, hval⟩⟩
  choose δ hδ hb using hbranch
  let Δ : ℝ := finiteMinimum δ
  have hΔ : 0 < Δ := by
    obtain ⟨i, hi⟩ := finiteMinimum_attained δ
    change 0 < finiteMinimum δ
    rw [hi]
    exact hδ i
  refine ⟨Δ, hΔ, ?_⟩
  intro a ha y hy hmin i hi
  have hval : A.value i y ≤ Q := (A.active_iff_minimum_eq i y).mp hi ▸ hmin
  exact (finiteMinimum_le δ i).trans (hb i a ha y hy hi hval)

theorem AffineFamily.eventuallyIn_plateau_of_compact_strict_exterior
    (A : AffineFamily d m) {N : Network d E} {k : E → ℝ → ℝ} {ℓ u M Q : ℝ}
    (hk : AdmissibleRates k ℓ u) {z : State d} {x : ℝ → State d}
    (hx : N.IsIntegralSolution k z x) {B : Set (State d)} (hB : IsCompact B)
    (hstay : ∀ t, 0 ≤ t → x t ∈ B) (hQ : Q < M)
    (hstrict : ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ B, A.minimum y < M → ∀ i, A.Active i y →
        0 < dot (A.slope i) (N.rhs a y)) : EventuallyIn x (A.plateau Q) := by
  obtain ⟨δ, hδ, hb⟩ := N.exists_affine_active_margin_on_compact_sublevel A hB hQ hstrict
  have hbound : ∀ t, 0 ≤ t → (A.withCap Q).minimum (x t) < Q → ∀ i,
      (A.withCap Q).Active i (x t) →
        δ ≤ dot ((A.withCap Q).slope i) (N.rhs (fun e => k e t) (x t)) := by
    intro t ht hmin i hi
    have hvalue : (A.withCap Q).value i (x t) < Q :=
      ((A.withCap Q).active_iff_minimum_eq i (x t)).mp hi ▸ hmin
    revert hi hvalue
    refine Fin.cases ?_ (fun j => ?_) i
    · intro _ hv
      rw [A.withCap_value_zero] at hv
      exact False.elim (lt_irrefl Q hv)
    · intro hj _
      have hactive := A.active_of_withCap_active Q hj
      have hsub := (A.minimum_lt_of_withCap_active Q hj hmin).le
      simpa only [AffineFamily.withCap, Fin.cons_succ] using
        hb _ ⟨fun e => (hk.2 e t ht).1, fun e => (hk.2 e t ht).2⟩
          (x t) (hstay t ht) hsub j hactive
  have hh := (A.withCap Q).eventuallyIn_plateau hx hδ
    (fun t _ => A.withCap_minimum_le Q (x t)) hbound
  rwa [A.withCap_plateau] at hh

end Endotactic
end

-- Source: Endotactic/LateCompactAbsorption.lean
section
/-!
# Absorption after an arbitrary entry time

The original integral solution is retained. An arbitrary starting time in the
AC cap barrier avoids translating the rates or the integral equation.
-/

namespace Endotactic

open Set MeasureTheory

variable {d m : ℕ} [Nonempty (Fin m)] {E : Type*} [Fintype E]

theorem AffineFamily.minimum_ae_deriv_lower_bound_below_after
    (A : AffineFamily d m) {N : Network d E} {k : E → ℝ → ℝ}
    {z : State d} {x : ℝ → State d} (hx : N.IsIntegralSolution k z x)
    {s T M δ : ℝ} (hs : 0 ≤ s) (hT : s ≤ T)
    (hbound : ∀ t ∈ Icc s T, A.minimum (x t) < M → ∀ i,
      A.Active i (x t) → δ ≤ dot (A.slope i) (N.rhs (fun e => k e t) (x t))) :
    ∀ᵐ t ∂volume, t ∈ Icc s T → A.minimum (x t) < M →
      δ ≤ deriv (fun r => A.minimum (x r)) t := by
  have hT0 := hs.trans hT
  have hsub : uIcc s T ⊆ uIcc 0 T := by
    simp only [uIcc_of_le hT, uIcc_of_le hT0]
    exact fun _ ht => ⟨hs.trans ht.1, ht.2⟩
  have hderivs : ∀ᵐ t ∂volume, ∀ i, t ∈ Icc 0 T →
      HasDerivAt (fun r => A.value i (x r))
        (dot (A.slope i) (N.rhs (fun e => k e t) (x t))) t :=
    ae_all_iff.mpr fun i => A.branch_ae_hasDerivAt hx i hT0
  have hb : ∀ᵐ t ∂volume, t ∈ uIcc s T → A.minimum (x t) < M → ∀ i,
      finiteMinimum (fun j => A.value j (x t)) = A.value i (x t) →
        δ ≤ deriv (fun r => A.value i (x r)) t := by
    filter_upwards [hderivs] with t ht hmem hlt i hi
    have hmem' : t ∈ Icc s T := by simpa only [uIcc_of_le hT] using hmem
    rw [(ht i ⟨hs.trans hmem'.1, hmem'.2⟩).deriv]
    exact hbound t hmem' hlt i ((A.active_iff_minimum_eq i (x t)).mpr hi)
  simpa only [AffineFamily.minimum, uIcc_of_le hT] using
    finiteMinimum_ae_deriv_lower_bound_on (fun i t => A.value i (x t))
      (fun t => A.minimum (x t) < M)
      (fun i => (A.branch_ac hx i hT0).mono hsub) hb

theorem AffineFamily.eventuallyIn_plateau_after
    (A : AffineFamily d m) {N : Network d E} {k : E → ℝ → ℝ}
    {z : State d} {x : ℝ → State d} (hx : N.IsIntegralSolution k z x)
    {s M δ : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ)
    (hcap : ∀ t, s ≤ t → A.minimum (x t) ≤ M)
    (hbound : ∀ t, s ≤ t → A.minimum (x t) < M → ∀ i,
      A.Active i (x t) → δ ≤ dot (A.slope i) (N.rhs (fun e => k e t) (x t))) :
    EventuallyIn x (A.plateau M) := by
  obtain ⟨T, hT, hstay⟩ := eventual_plateau_of_ac (fun t => A.minimum (x t)) hs hδ
    (fun T hT => (A.minimum_ac hx (hs.trans hT)).mono (by
      simp only [uIcc_of_le hT, uIcc_of_le (hs.trans hT)]
      exact fun _ ht => ⟨hs.trans ht.1, ht.2⟩)) hcap
    (fun T hT => A.minimum_ae_deriv_lower_bound_below_after hx hs hT
      (fun t ht => hbound t ht.1))
  exact ⟨T, hT, fun t ht => (A.mem_plateau_iff_minimum_ge (x t) M).mpr (hstay t ht).ge⟩

theorem AffineFamily.eventuallyIn_plateau_of_eventual_compact_strict_exterior
    (A : AffineFamily d m) {N : Network d E} {k : E → ℝ → ℝ} {ℓ u M Q : ℝ}
    (hk : AdmissibleRates k ℓ u) {z : State d} {x : ℝ → State d}
    (hx : N.IsIntegralSolution k z x) {B : Set (State d)} (hB : IsCompact B)
    (hstay : EventuallyIn x B) (hQ : Q < M)
    (hstrict : ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ B, A.minimum y < M → ∀ i, A.Active i y →
        0 < dot (A.slope i) (N.rhs a y)) : EventuallyIn x (A.plateau Q) := by
  obtain ⟨s, hs, hstay⟩ := hstay
  obtain ⟨δ, hδ, hb⟩ := N.exists_affine_active_margin_on_compact_sublevel A hB hQ hstrict
  have hbound : ∀ t, s ≤ t → (A.withCap Q).minimum (x t) < Q → ∀ i,
      (A.withCap Q).Active i (x t) →
        δ ≤ dot ((A.withCap Q).slope i) (N.rhs (fun e => k e t) (x t)) := by
    intro t ht hmin i hi
    have hvalue : (A.withCap Q).value i (x t) < Q :=
      ((A.withCap Q).active_iff_minimum_eq i (x t)).mp hi ▸ hmin
    revert hi hvalue
    refine Fin.cases ?_ (fun j => ?_) i
    · intro _ hv
      rw [A.withCap_value_zero] at hv
      exact False.elim (lt_irrefl Q hv)
    · intro hj _
      have hactive := A.active_of_withCap_active Q hj
      have hsub := (A.minimum_lt_of_withCap_active Q hj hmin).le
      simpa only [AffineFamily.withCap, Fin.cons_succ] using
        hb _ ⟨fun e => (hk.2 e t (hs.trans ht)).1, fun e => (hk.2 e t (hs.trans ht)).2⟩
          (x t) (hstay t ht) hsub j hactive
  have hh := (A.withCap Q).eventuallyIn_plateau_after hx hs hδ
    (fun t _ => A.withCap_minimum_le Q (x t)) hbound
  rwa [A.withCap_plateau] at hh

end Endotactic
end

-- Source: Endotactic/Stoichiometry.lean
section
/-!
# Stoichiometric-class conservation for integral solutions

Apply the quotient map by the reaction subspace to the integral equation.
The projected right-hand side is identically zero. This avoids having to assume
integrability of each individual reaction summand.
-/

namespace Endotactic

open MeasureTheory Set

theorem intervalIntegral_mem_subspace {d : ℕ} (S : Submodule ℝ (State d))
    {f : ℝ → State d} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (hmem : ∀ t ∈ uIcc a b, f t ∈ S) :
    (∫ t in a..b, f t) ∈ S := by
  let : IsClosed (S : Set (State d)) := S.closed_of_finiteDimensional
  apply (Submodule.Quotient.mk_eq_zero S).mp
  change S.mkQL (∫ t in a..b, f t) = 0
  rw [← S.mkQL.intervalIntegral_comp_comm hf]
  have heq : EqOn (fun t => S.mkQL (f t)) (fun _ => 0) (uIcc a b) := by
    intro t ht
    exact (Submodule.Quotient.mk_eq_zero S).mpr (hmem t ht)
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]

variable {d : ℕ} {E : Type*} [Fintype E]
variable {N : Network d E} {k : E → ℝ → ℝ} {x₀ : State d} {x : ℝ → State d}

theorem Network.IsIntegralSolution.sub_initial_mem
    (hx : N.IsIntegralSolution k x₀ x) {t : ℝ} (ht : 0 ≤ t) :
    x t - x₀ ∈ N.stoichiometricSubspace := by
  rw [hx.2.2.2 t ht, add_sub_cancel_left]
  exact intervalIntegral_mem_subspace N.stoichiometricSubspace (hx.2.2.1 t ht)
    (fun s _ => rhs_mem_stoichiometricSubspace N (fun e => k e s) (x s))

theorem Network.IsGlobalPositiveSolution.mem_positiveClass
    (hx : N.IsGlobalPositiveSolution k x₀ x) {c : State d}
    (h₀ : x₀ ∈ N.positiveClass c) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ N.positiveClass c := by
  refine ⟨hx.2 t ht, ?_⟩
  have hh := N.stoichiometricSubspace.add_mem (hx.1.sub_initial_mem ht) h₀.2
  simpa only [sub_add_sub_cancel] using hh

/-- A conditional assembly theorem. The plateau is chosen before rates and
initial points; the positive growth margin may depend on the trajectory.
Constructing this geometry and proving positive well-posedness remain open. -/
theorem Network.uniformPermanent_of_affine_plateau {m : ℕ} [Nonempty (Fin m)]
    (N : Network d E) (A : AffineFamily d m) (ℓ u M : ℝ) (c : State d)
    (regular : (E → ℝ → ℝ) → Prop)
    (hKne : (A.plateau M ∩ N.positiveClass c).Nonempty)
    (hKcompact : IsCompact (A.plateau M ∩ N.positiveClass c))
    (hcap : ∀ z ∈ N.positiveClass c, A.minimum z ≤ M)
    (hwell : ∀ k, AdmissibleRates k ℓ u → regular k →
      ∀ x₀ ∈ N.positiveClass c, N.PositiveWellPosed k x₀)
    (hflux : ∀ k, AdmissibleRates k ℓ u → regular k →
      ∀ x₀ ∈ N.positiveClass c, ∀ x, N.IsGlobalPositiveSolution k x₀ x →
        ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 ≤ t → A.minimum (x t) < M → ∀ i,
          A.Active i (x t) → δ ≤ dot (A.slope i) (N.rhs (fun e => k e t) (x t))) :
    N.UniformPermanent ℓ u c regular := by
  refine ⟨A.plateau M ∩ N.positiveClass c, hKne, hKcompact,
    fun _ hz => hz.2, ?_⟩
  intro k hk hr
  refine ⟨hwell k hk hr, ?_⟩
  intro x₀ h₀ x hx
  obtain ⟨δ, hδ, hb⟩ := hflux k hk hr x₀ h₀ x hx
  obtain ⟨T, hT, hstay⟩ := A.eventuallyIn_plateau hx.1 hδ
    (fun t ht => hcap (x t) (hx.mem_positiveClass h₀ ht)) hb
  exact ⟨T, hT, fun t ht => ⟨hstay t ht, hx.mem_positiveClass h₀ (hT.trans ht)⟩⟩

end Endotactic
end

-- Source: Endotactic/NonlinearVolterra.lean
section
/-
The interval clamping and continuous extension are adapted from LeanPool:
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0; see licenses/LeanPool-Apache-2.0.txt.
Changes: finite-dimensional nonlinear field, direct short-time contraction,
and integral-solution predicates. See THIRD_PARTY_NOTICES.txt.
-/

/-!
# Short-interval integral solutions with bounded measurable nonlinear kinetics

The continuous-path construction and clamping extension are adapted from
Scott Armstrong and Vlad Vicol's LeanPool linear Volterra implementation
(Apache-2.0, 2026), at commit bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8.
Here the field is nonlinear. A sufficiently short interval makes the Volterra
map itself contractive, so no factorial estimate for iterates is needed.

This module proves a fixed point, not merely measurability or regularity.
Applying it to mass action requires a bounded globally Lipschitz cutoff.
-/

namespace Endotactic

open MeasureTheory Set
open scoped Topology NNReal

def intervalClamp {a b : ℝ} (hab : a ≤ b) (t : ℝ) : Icc a b :=
  ⟨max a (min b t), le_max_left _ _, max_le hab (min_le_left _ _)⟩

def extendIntervalCurve {d : ℕ} {a b : ℝ} (hab : a ≤ b)
    (u : C(Icc a b, State d)) : ℝ → State d := fun t => u (intervalClamp hab t)

theorem continuous_extendIntervalCurve {d : ℕ} {a b : ℝ} (hab : a ≤ b)
    (u : C(Icc a b, State d)) : Continuous (extendIntervalCurve hab u) := by
  apply u.continuous.comp
  exact (show Continuous (fun t : ℝ => max a (min b t)) by fun_prop).subtype_mk _

theorem extendIntervalCurve_eq_of_mem {d : ℕ} {a b : ℝ} (hab : a ≤ b)
    (u : C(Icc a b, State d)) {t : ℝ} (ht : t ∈ Icc a b) :
    extendIntervalCurve hab u t = u ⟨t, ht⟩ := by
  simp [extendIntervalCurve, intervalClamp, max_eq_right ht.1, min_eq_right ht.2]

structure BoundedMeasurableODE (d : ℕ) where
  field : ℝ → State d → State d
  initial : State d
  normBound : ℝ
  lipschitzConstant : ℝ≥0
  measurable : Measurable (fun p : ℝ × State d => field p.1 p.2)
  norm_le : ∀ t z, ‖field t z‖ ≤ normBound
  lipschitz : ∀ t, LipschitzWith lipschitzConstant (field t)

variable {d : ℕ} {a b : ℝ}

def BoundedMeasurableODE.curveRhs (D : BoundedMeasurableODE d) (hab : a ≤ b)
    (u : C(Icc a b, State d)) (t : ℝ) : State d := D.field t (extendIntervalCurve hab u t)

theorem BoundedMeasurableODE.curveRhs_intervalIntegrable (D : BoundedMeasurableODE d)
    (hab : a ≤ b) (u : C(Icc a b, State d)) :
    IntervalIntegrable (D.curveRhs hab u) volume a b := by
  have hm : Measurable (D.curveRhs hab u) :=
    D.measurable.comp (measurable_id.prodMk (continuous_extendIntervalCurve hab u).measurable)
  apply intervalIntegrable_iff.mpr
  apply IntegrableOn.of_bound (s := uIoc a b) (μ := volume)
    (by rw [uIoc_of_le hab]; exact measure_Ioc_lt_top)
    (hm.aestronglyMeasurable.mono_measure Measure.restrict_le_self) D.normBound
  exact Filter.Eventually.of_forall fun t => D.norm_le t _

noncomputable def BoundedMeasurableODE.volterra (D : BoundedMeasurableODE d)
    (hab : a ≤ b) : C(Icc a b, State d) → C(Icc a b, State d) := fun u =>
  ⟨fun t => D.initial + ∫ s in a..(t : ℝ), D.curveRhs hab u s, by
    have hp := intervalIntegral.continuousOn_primitive_interval'
      (D.curveRhs_intervalIntegrable hab u) left_mem_uIcc
    have hsum := (continuousOn_const (c := D.initial)).add hp
    exact continuousOn_iff_continuous_domRestrict.mp
      (show ContinuousOn (fun t : ℝ => D.initial + ∫ s in a..t, D.curveRhs hab u s)
        (Icc a b) by simpa only [Pi.add_def, uIcc_of_le hab] using hsum)⟩

theorem BoundedMeasurableODE.dist_volterra_apply_le (D : BoundedMeasurableODE d)
    (hab : a ≤ b) (u v : C(Icc a b, State d)) (t : Icc a b) :
    dist (D.volterra hab u t) (D.volterra hab v t) ≤
      (D.lipschitzConstant : ℝ) * ((t : ℝ) - a) * dist u v := by
  have hsub : uIcc a (t : ℝ) ⊆ uIcc a b := by
    simpa only [uIcc_of_le hab, uIcc_of_le t.property.1] using
      (show Icc a (t : ℝ) ⊆ Icc a b from fun _ hs => ⟨hs.1, hs.2.trans t.property.2⟩)
  change ‖(D.initial + ∫ s in a..(t : ℝ), D.curveRhs hab u s) -
    (D.initial + ∫ s in a..(t : ℝ), D.curveRhs hab v s)‖ ≤ _
  rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
    ((D.curveRhs_intervalIntegrable hab u).mono_set hsub)
    ((D.curveRhs_intervalIntegrable hab v).mono_set hsub)]
  have hb : ∀ s ∈ uIoc a (t : ℝ),
      ‖D.curveRhs hab u s - D.curveRhs hab v s‖ ≤ (D.lipschitzConstant : ℝ) * dist u v := by
    intro s _
    rw [← dist_eq_norm]
    exact ((D.lipschitz s).dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist (intervalClamp hab s))
        D.lipschitzConstant.coe_nonneg)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [abs_of_nonneg (sub_nonneg.mpr t.property.1)] at hh
  convert hh using 1; ring

theorem BoundedMeasurableODE.volterra_lipschitz (D : BoundedMeasurableODE d)
    (hab : a ≤ b) :
    LipschitzWith (D.lipschitzConstant * ⟨b - a, sub_nonneg.mpr hab⟩) (D.volterra hab) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change dist (D.volterra hab u) (D.volterra hab v) ≤
    (D.lipschitzConstant : ℝ) * (b - a) * dist u v
  have hnonneg : 0 ≤ (D.lipschitzConstant : ℝ) * (b - a) * dist u v := by positivity
  rw [ContinuousMap.dist_le hnonneg]
  intro t
  exact (D.dist_volterra_apply_le hab u v t).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_sub_right t.property.2 a)
        D.lipschitzConstant.coe_nonneg) dist_nonneg)

theorem BoundedMeasurableODE.existsUnique_fixedPoint (D : BoundedMeasurableODE d)
    (hab : a ≤ b) (hshort : (D.lipschitzConstant : ℝ) * (b - a) < 1) :
    ∃! u : C(Icc a b, State d), D.volterra hab u = u := by
  have hc : ContractingWith (D.lipschitzConstant * ⟨b - a, sub_nonneg.mpr hab⟩)
      (D.volterra hab) := ⟨hshort, D.volterra_lipschitz hab⟩
  exact ⟨hc.fixedPoint, hc.fixedPoint_isFixedPt,
    fun v hv => hc.fixedPoint_unique hv⟩

/-- An integral solution on one compact time interval. -/
def IntegralSolutionOn (F : ℝ → State d → State d) (z : State d) (a b : ℝ)
    (x : ℝ → State d) : Prop :=
  ContinuousOn x (Icc a b) ∧ x a = z ∧
    IntervalIntegrable (fun t => F t (x t)) volume a b ∧
    ∀ t ∈ Icc a b, x t = z + ∫ s in a..t, F s (x s)

theorem BoundedMeasurableODE.fixedPoint_integralSolution (D : BoundedMeasurableODE d)
    (hab : a ≤ b) (u : C(Icc a b, State d)) (hu : D.volterra hab u = u) :
    IntegralSolutionOn D.field D.initial a b (extendIntervalCurve hab u) := by
  have heq : ∀ t ∈ Icc a b, extendIntervalCurve hab u t =
      D.initial + ∫ s in a..t, D.field s (extendIntervalCurve hab u s) := by
    intro t ht
    have hh := congrArg (fun w : C(Icc a b, State d) => w ⟨t, ht⟩) hu
    rw [extendIntervalCurve_eq_of_mem hab u ht]
    exact hh.symm
  refine ⟨(continuous_extendIntervalCurve hab u).continuousOn, ?_,
    D.curveRhs_intervalIntegrable hab u, heq⟩
  simpa using heq a ⟨le_rfl, hab⟩

theorem BoundedMeasurableODE.exists_integralSolution (D : BoundedMeasurableODE d)
    (hab : a ≤ b) (hshort : (D.lipschitzConstant : ℝ) * (b - a) < 1) :
    ∃ x : ℝ → State d, Continuous x ∧ IntegralSolutionOn D.field D.initial a b x := by
  obtain ⟨u, hu, _⟩ := D.existsUnique_fixedPoint hab hshort
  exact ⟨extendIntervalCurve hab u, continuous_extendIntervalCurve hab u,
    D.fixedPoint_integralSolution hab u hu⟩

end Endotactic
end

-- Source: Endotactic/BoxKinetics.lean
section
/-!
# Bounded mass-action fields by coordinate clamping

Clamping the state to a finite closed box preserves the field inside the box.
It makes polynomial mass action bounded and globally Lipschitz in state, with
one constant for all admissible rate vectors. Negative times use the rate at
zero, since admissibility only bounds nonnegative times.
-/

namespace Endotactic

open Set MeasureTheory
open scoped NNReal

variable {d : ℕ} {E : Type*} [Fintype E]

def boxClamp (lo hi : State d) (x : State d) : State d :=
  fun i => max (lo i) (min (hi i) (x i))

theorem boxClamp_mem (lo hi : State d) (hbox : lo ≤ hi) (x : State d) :
    boxClamp lo hi x ∈ Icc lo hi := by
  exact ⟨fun i => le_max_left _ _, fun i => max_le (hbox i) (min_le_left _ _)⟩

theorem boxClamp_eq_of_mem (lo hi : State d) {x : State d} (hx : x ∈ Icc lo hi) :
    boxClamp lo hi x = x := by
  funext i
  simp [boxClamp, max_eq_right (hx.1 i), min_eq_right (hx.2 i)]

theorem boxClamp_lipschitz (lo hi : State d) : LipschitzWith 1 (boxClamp lo hi) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  simpa only [boxClamp, NNReal.coe_one, one_mul] using
    (((LipschitzWith.eval i).const_min (hi i)).const_max (lo i)).dist_le_mul x y

def Network.cutoffRhs (N : Network d E) (k : E → ℝ → ℝ) (lo hi : State d)
    (t : ℝ) (x : State d) : State d :=
  N.rhs (fun e => k e (max 0 t)) (boxClamp lo hi x)

theorem Network.cutoffRhs_eq (N : Network d E) (k : E → ℝ → ℝ)
    (lo hi : State d) {t : ℝ} (ht : 0 ≤ t) {x : State d} (hx : x ∈ Icc lo hi) :
    N.cutoffRhs k lo hi t x = N.rhs (fun e => k e t) x := by
  simp [Network.cutoffRhs, max_eq_right ht, boxClamp_eq_of_mem lo hi hx]

theorem Network.cutoffRhs_measurable (N : Network d E) {k : E → ℝ → ℝ}
    {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u) (lo hi : State d) :
    Measurable (fun p : ℝ × State d => N.cutoffRhs k lo hi p.1 p.2) := by
  have hm : Measurable (fun p : ℝ × State d => fun e => k e (max 0 p.1)) :=
    measurable_pi_iff.mpr fun e => (hk.1 e).comp
      ((continuous_const.max continuous_fst).measurable)
  have hc : Measurable (fun p : ℝ × State d => boxClamp lo hi p.2) :=
    (boxClamp_lipschitz lo hi).continuous.measurable.comp measurable_snd
  exact N.rhs_joint_contDiff.continuous.measurable.comp (hm.prodMk hc)

theorem Network.rhs_bounded_on_box (N : Network d E) (ℓ u : ℝ) (lo hi : State d) :
    ∃ R : ℝ, ∀ k ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ x ∈ Icc lo hi, ‖N.rhs k x‖ ≤ R := by
  have hcompact : IsCompact
      (Icc (fun _ : E => ℓ) (fun _ : E => u) ×ˢ Icc lo hi) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨R, hR⟩ := hcompact.exists_bound_of_continuousOn
    (N.rhs_joint_contDiff.continuous.continuousOn :
      ContinuousOn (fun p : (E → ℝ) × State d => N.rhs p.1 p.2)
        (Icc (fun _ => ℓ) (fun _ => u) ×ˢ Icc lo hi))
  exact ⟨R, fun k hk x hx => hR (k, x) ⟨hk, hx⟩⟩

theorem Network.cutoffRhs_uniform_lipschitz (N : Network d E) {k : E → ℝ → ℝ}
    {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u) (lo hi : State d) (hbox : lo ≤ hi) :
    ∃ L : ℝ≥0, ∀ t, LipschitzWith L (N.cutoffRhs k lo hi t) := by
  obtain ⟨L, hL⟩ := N.rhs_uniform_lipschitzOn_box (fun _ => ℓ) (fun _ => u) lo hi
  have hrate : ∀ t : ℝ, (fun e => k e (max 0 t)) ∈ Icc (fun _ => ℓ) (fun _ => u) :=
    fun t => ⟨fun e => (hk.2 e (max 0 t) (le_max_left _ _)).1,
      fun e => (hk.2 e (max 0 t) (le_max_left _ _)).2⟩
  refine ⟨L, fun t => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (N.rhs (fun e => k e (max 0 t)) (boxClamp lo hi x))
    (N.rhs (fun e => k e (max 0 t)) (boxClamp lo hi y)) ≤ (L : ℝ) * dist x y
  have hh := (hL _ (hrate t)).dist_le_mul (boxClamp lo hi x) (boxClamp_mem lo hi hbox x)
    (boxClamp lo hi y) (boxClamp_mem lo hi hbox y)
  have hd : dist (boxClamp lo hi x) (boxClamp lo hi y) ≤ dist x y := by
    simpa only [NNReal.coe_one, one_mul] using (boxClamp_lipschitz lo hi).dist_le_mul x y
  exact hh.trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)

theorem Network.cutoffRhs_bounded_lipschitz (N : Network d E) {k : E → ℝ → ℝ}
    {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u) (lo hi : State d) (hbox : lo ≤ hi) :
    ∃ R : ℝ, ∃ L : ℝ≥0, (∀ t x, ‖N.cutoffRhs k lo hi t x‖ ≤ R) ∧
      ∀ t, LipschitzWith L (N.cutoffRhs k lo hi t) := by
  obtain ⟨R, hR⟩ := N.rhs_bounded_on_box ℓ u lo hi
  obtain ⟨L, hL⟩ := N.cutoffRhs_uniform_lipschitz hk lo hi hbox
  refine ⟨R, L, ?_, hL⟩
  intro t x
  change ‖N.rhs (fun e => k e (max 0 t)) (boxClamp lo hi x)‖ ≤ R
  exact hR _ ⟨fun e => (hk.2 e (max 0 t) (le_max_left _ _)).1,
    fun e => (hk.2 e (max 0 t) (le_max_left _ _)).2⟩ _ (boxClamp_mem lo hi hbox x)

theorem Network.exists_cutoffODE (N : Network d E) {k : E → ℝ → ℝ}
    {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u) (lo hi : State d) (hbox : lo ≤ hi)
    (z : State d) :
    ∃ D : BoundedMeasurableODE d, D.field = N.cutoffRhs k lo hi ∧ D.initial = z := by
  obtain ⟨R, L, hR, hL⟩ := N.cutoffRhs_bounded_lipschitz hk lo hi hbox
  exact ⟨⟨N.cutoffRhs k lo hi, z, R, L, N.cutoffRhs_measurable hk lo hi, hR, hL⟩,
    rfl, rfl⟩

end Endotactic
end

-- Source: Endotactic/LocalExistence.lean
section
/-!
# Positive local integral solutions of measurable mass action

A bounded, globally Lipschitz cutoff has a short-interval Volterra fixed point.
Its displacement bound keeps it inside the cutoff box, so it is an actual
solution of the original mass-action equation. This construction proves local
positivity. It does not establish global positivity or rule out finite escape.
-/

namespace Endotactic

open Set MeasureTheory
open scoped NNReal

variable {d : ℕ} {E : Type*} [Fintype E]

theorem IntegralSolutionOn.dist_initial_le {F : ℝ → State d → State d}
    {z : State d} {a b R : ℝ} {x : ℝ → State d}
    (hx : IntegralSolutionOn F z a b x) (hR : ∀ t y, ‖F t y‖ ≤ R)
    {t : ℝ} (ht : t ∈ Icc a b) : dist (x t) z ≤ R * (t - a) := by
  rw [hx.2.2.2 t ht, dist_eq_norm, add_sub_cancel_left]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s => F s (x s)) (a := a) (b := t) (fun s _ => hR s (x s))
  simpa only [abs_of_nonneg (sub_nonneg.mpr ht.1)] using hh

theorem IntegralSolutionOn.increment_eq {F : ℝ → State d → State d}
    {z : State d} {a b : ℝ} {x : ℝ → State d}
    (hx : IntegralSolutionOn F z a b x) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    x t - x s = ∫ r in s..t, F r (x r) := by
  have hab := hs.1.trans hs.2
  have hint : ∀ r ∈ Icc a b, IntervalIntegrable (fun q => F q (x q)) volume a r := by
    intro r hr
    apply hx.2.2.1.mono_set
    rw [uIcc_of_le hab]
    exact uIcc_subset_Icc ⟨le_rfl, hab⟩ hr
  rw [hx.2.2.2 t ht, hx.2.2.2 s hs, add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left (hint t ht) (hint s hs)

theorem IntegralSolutionOn.dist_le_time {F : ℝ → State d → State d}
    {z : State d} {a b R : ℝ} {x : ℝ → State d}
    (hx : IntegralSolutionOn F z a b x)
    (hR : ∀ r ∈ Icc a b, ‖F r (x r)‖ ≤ R) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    dist (x t) (x s) ≤ R * |t - s| := by
  rw [dist_eq_norm, hx.increment_eq hs ht]
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun r hr => hR r (uIcc_subset_Icc hs ht (uIoc_subset_uIcc hr)))

theorem IntegralSolutionOn.restart {F : ℝ → State d → State d}
    {z : State d} {a b : ℝ} {x : ℝ → State d}
    (hx : IntegralSolutionOn F z a b x) {s : ℝ} (hs : s ∈ Icc a b) :
    IntegralSolutionOn F (x s) s b x := by
  have hab := hs.1.trans hs.2
  have hsub : Icc s b ⊆ Icc a b := fun _ ht => ⟨hs.1.trans ht.1, ht.2⟩
  refine ⟨hx.1.mono hsub, rfl, ?_, ?_⟩
  · apply hx.2.2.1.mono_set
    rw [uIcc_of_le hab, uIcc_of_le hs.2]
    exact hsub
  · intro t ht
    exact (sub_eq_iff_eq_add.mp (hx.increment_eq hs (hsub ht))).trans (add_comm _ _)

theorem exists_short_positive_time (L R ε : ℝ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hε : 0 < ε) : ∃ T : ℝ, 0 < T ∧ L * T < 1 ∧ R * T < ε := by
  obtain ⟨T₁, hT₁, hL₁⟩ := exists_pos_mul_lt (show (0 : ℝ) < 1 by norm_num) L
  obtain ⟨T₂, hT₂, hR₂⟩ := exists_pos_mul_lt hε R
  refine ⟨min T₁ T₂, lt_min hT₁ hT₂, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hL).trans_lt hL₁
  · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hR).trans_lt hR₂

theorem BoundedMeasurableODE.unique_integralSolution (D : BoundedMeasurableODE d)
    {a b : ℝ} (hab : a ≤ b) (hshort : (D.lipschitzConstant : ℝ) * (b - a) < 1)
    {x y : ℝ → State d} (hx : IntegralSolutionOn D.field D.initial a b x)
    (hy : IntegralSolutionOn D.field D.initial a b y) : EqOn x y (Icc a b) := by
  let ux : C(Icc a b, State d) :=
    ⟨fun t => x t, continuousOn_iff_continuous_domRestrict.mp hx.1⟩
  let uy : C(Icc a b, State d) :=
    ⟨fun t => y t, continuousOn_iff_continuous_domRestrict.mp hy.1⟩
  have hfixed : ∀ (z : ℝ → State d) (hz : IntegralSolutionOn D.field D.initial a b z)
      (uz : C(Icc a b, State d)), (∀ t, uz t = z t) → D.volterra hab uz = uz := by
    intro z hz uz huz
    apply ContinuousMap.ext
    intro t
    change D.initial + (∫ s in a..(t : ℝ), D.curveRhs hab uz s) = uz t
    rw [huz, hz.2.2.2 t t.property]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans t.property.2⟩
    unfold BoundedMeasurableODE.curveRhs
    rw [extendIntervalCurve_eq_of_mem hab uz hs', huz]
  obtain ⟨u, _, hu⟩ := D.existsUnique_fixedPoint hab hshort
  have hux : ux = u := hu ux (hfixed x hx ux (fun _ => rfl))
  have huy : uy = u := hu uy (hfixed y hy uy (fun _ => rfl))
  intro t ht
  exact congrArg (fun w : C(Icc a b, State d) => w ⟨t, ht⟩) (hux.trans huy.symm)

theorem Network.exists_positive_local_integralSolution (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (z : State d) (hz : Positive z) :
    ∃ T : ℝ, 0 < T ∧ ∃ x : ℝ → State d, Continuous x ∧
      IntegralSolutionOn (fun t y => N.rhs (fun e => k e t) y) z 0 T x ∧
      ∀ t ∈ Icc 0 T, Positive (x t) := by
  obtain ⟨ε, hε, hεz⟩ := Pi.exists_forall_pos_add_lt (x := fun _ : Fin d => (0 : ℝ)) hz
  have hεz : ∀ i, ε < z i := by simpa using hεz
  let lo : State d := fun i => z i - ε
  let hi : State d := fun i => z i + ε
  have hbox : lo ≤ hi := fun i => by dsimp [lo, hi]; linarith
  obtain ⟨D, hDF, hDz⟩ := N.exists_cutoffODE hk lo hi hbox z
  obtain ⟨T, hT, hLT, hRT⟩ := exists_short_positive_time (D.lipschitzConstant : ℝ)
    (max D.normBound 0) ε D.lipschitzConstant.coe_nonneg (le_max_right _ _) hε
  obtain ⟨x, hxc, hx⟩ := D.exists_integralSolution (a := 0) (b := T) hT.le
    (by simpa using hLT)
  have hclose : ∀ t ∈ Icc 0 T, dist (x t) z < ε := by
    intro t ht
    have hb := hx.dist_initial_le D.norm_le ht
    rw [hDz] at hb
    calc
      dist (x t) z ≤ D.normBound * (t - 0) := hb
      _ ≤ max D.normBound 0 * T := by
        simp only [sub_zero]
        exact mul_le_mul (le_max_left _ _) ht.2 ht.1 (le_max_right _ _)
      _ < ε := hRT
  have hmem : ∀ t ∈ Icc 0 T, x t ∈ Icc lo hi := by
    intro t ht
    have hc : ∀ i, |x t i - z i| < ε := fun i => by
      simpa only [Real.dist_eq] using (dist_le_pi_dist (x t) z i).trans_lt (hclose t ht)
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hh := (abs_lt.mp (hc i)).1
      dsimp [lo]; linarith
    · have hh := (abs_lt.mp (hc i)).2
      dsimp [hi]; linarith
  have hfield : ∀ t ∈ Icc 0 T, D.field t (x t) = N.rhs (fun e => k e t) (x t) := by
    intro t ht
    rw [hDF]
    exact N.cutoffRhs_eq k lo hi ht.1 (hmem t ht)
  refine ⟨T, hT, x, hxc, ?_, ?_⟩
  · refine ⟨hx.1, hDz ▸ hx.2.1, ?_, ?_⟩
    · apply hx.2.2.1.congr
      intro t ht
      apply hfield t
      rw [uIoc_of_le hT.le] at ht
      exact Ioc_subset_Icc_self ht
    · intro t ht
      rw [hx.2.2.2 t ht, hDz]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      exact hfield s ⟨hs.1, hs.2.trans ht.2⟩
  · intro t ht i
    have hh := (hmem t ht).1 i
    dsimp [lo] at hh
    exact (sub_pos.mpr (hεz i)).trans_le hh

end Endotactic
end

-- Source: Endotactic/IntegralUniqueness.lean
section
/-!
# Uniqueness of measurable mass-action integral solutions

The distance of two trajectories is continuous. Apply the differentiable
Grönwall theorem to its integral, rather than to the trajectories themselves.
Thus no pointwise differentiability of the measurable-time field is assumed.
-/

namespace Endotactic

open Set MeasureTheory
open scoped Topology NNReal

variable {d : ℕ} {E : Type*} [Fintype E]

theorem continuous_eq_zero_of_le_integral {u : ℝ → ℝ} {a b L : ℝ}
    (hu : Continuous u) (hn : ∀ t ∈ Icc a b, 0 ≤ u t)
    (hi : ∀ t ∈ Icc a b, u t ≤ L * ∫ s in a..t, u s) :
    ∀ t ∈ Icc a b, u t = 0 := by
  let G : ℝ → ℝ := fun t => ∫ s in a..t, u s
  have hGc : Continuous G := intervalIntegral.continuous_primitive
    (fun s t => hu.intervalIntegrable s t) a
  have hGn : ∀ t ∈ Icc a b, 0 ≤ G t := by
    intro t ht
    apply intervalIntegral.integral_nonneg ht.1
    intro s hs
    exact hn s ⟨hs.1, hs.2.trans ht.2⟩
  have hGzero : ∀ t ∈ Icc a b, G t = 0 :=
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hGc.continuousOn
      (fun t _ => (intervalIntegral.integral_hasDerivAt_right
        (hu.intervalIntegrable a t) (hu.stronglyMeasurableAtFilter volume (𝓝 t))
        hu.continuousAt).hasDerivWithinAt)
      (by simp [G]) (by
        intro t ht
        have ht' : t ∈ Icc a b := ⟨ht.1, ht.2.le⟩
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hn t ht'),
          abs_of_nonneg (hGn t ht')] using hi t ht')
  intro t ht
  apply le_antisymm _ (hn t ht)
  have hh : u t ≤ L * G t := hi t ht
  simpa only [hGzero t ht, mul_zero] using hh

theorem IntegralSolutionOn.eqOn_of_lipschitzOn {F : ℝ → State d → State d}
    {z : State d} {a b : ℝ} (hab : a ≤ b) {x y : ℝ → State d}
    (hx : IntegralSolutionOn F z a b x) (hy : IntegralSolutionOn F z a b y)
    {B : Set (State d)} {L : ℝ≥0}
    (hL : ∀ t ∈ Icc a b, LipschitzOnWith L (F t) B)
    (hxB : MapsTo x (Icc a b) B) (hyB : MapsTo y (Icc a b) B) :
    EqOn x y (Icc a b) := by
  let ux : C(Icc a b, State d) :=
    ⟨fun t => x t, continuousOn_iff_continuous_domRestrict.mp hx.1⟩
  let uy : C(Icc a b, State d) :=
    ⟨fun t => y t, continuousOn_iff_continuous_domRestrict.mp hy.1⟩
  let U : ℝ → ℝ := fun t => dist (extendIntervalCurve hab ux t) (extendIntervalCurve hab uy t)
  have hUc : Continuous U := (continuous_extendIntervalCurve hab ux).dist
    (continuous_extendIntervalCurve hab uy)
  have hUeq : ∀ t ∈ Icc a b, U t = dist (x t) (y t) := by
    intro t ht
    dsimp [U]
    rw [extendIntervalCurve_eq_of_mem hab ux ht, extendIntervalCurve_eq_of_mem hab uy ht]
    rfl
  have hineq : ∀ t ∈ Icc a b, U t ≤ (L : ℝ) * ∫ s in a..t, U s := by
    intro t ht
    have hsub : uIcc a t ⊆ uIcc a b := by
      simpa only [uIcc_of_le hab, uIcc_of_le ht.1] using
        (show Icc a t ⊆ Icc a b from fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩)
    have hf := (hx.2.2.1.mono_set hsub).sub (hy.2.2.1.mono_set hsub)
    rw [hUeq t ht, hx.2.2.2 t ht, hy.2.2.2 t ht, dist_eq_norm,
      add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
        (hx.2.2.1.mono_set hsub) (hy.2.2.1.mono_set hsub)]
    calc
      ‖∫ s in a..t, F s (x s) - F s (y s)‖ ≤
          ∫ s in a..t, ‖F s (x s) - F s (y s)‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in a..t, (L : ℝ) * U s := by
        apply intervalIntegral.integral_mono_on ht.1 hf.norm
          ((hUc.intervalIntegrable a t).const_mul (L : ℝ))
        intro s hs
        have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
        rw [← dist_eq_norm, hUeq s hs']
        exact (hL s hs').dist_le_mul _ (hxB hs') _ (hyB hs')
      _ = (L : ℝ) * ∫ s in a..t, U s := intervalIntegral.integral_const_mul _ _
  have hzero := continuous_eq_zero_of_le_integral hUc
    (fun _ _ => dist_nonneg) hineq
  intro t ht
  exact dist_eq_zero.mp ((hUeq t ht).symm.trans (hzero t ht))

theorem Network.integralSolutionOn_unique (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u T : ℝ} (hk : AdmissibleRates k ℓ u) (hT : 0 ≤ T)
    {z : State d} {x y : ℝ → State d}
    (hx : IntegralSolutionOn (fun t v => N.rhs (fun e => k e t) v) z 0 T x)
    (hy : IntegralSolutionOn (fun t v => N.rhs (fun e => k e t) v) z 0 T y) :
    EqOn x y (Icc 0 T) := by
  obtain ⟨Rx, hRx⟩ := isCompact_Icc.exists_bound_of_continuousOn hx.1
  obtain ⟨Ry, hRy⟩ := isCompact_Icc.exists_bound_of_continuousOn hy.1
  let R : ℝ := max Rx Ry
  have hB : ∀ (v : ℝ → State d), (∀ t ∈ Icc 0 T, ‖v t‖ ≤ R) →
      MapsTo v (Icc 0 T) (Icc (fun _ => -R) (fun _ => R)) := by
    intro v hv t ht
    have hb : ∀ i, |v t i| ≤ ‖v t‖ := fun i => by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (v t) i
    have hh : ∀ i, |v t i| ≤ R := fun i => (hb i).trans (hv t ht)
    exact ⟨fun i => (abs_le.mp (hh i)).1, fun i => (abs_le.mp (hh i)).2⟩
  obtain ⟨L, hL⟩ := N.rhs_uniform_lipschitzOn_box
    (fun _ => ℓ) (fun _ => u) (fun _ => -R) (fun _ => R)
  exact hx.eqOn_of_lipschitzOn hT hy
    (fun t ht => hL _ ⟨fun e => (hk.2 e t ht.1).1, fun e => (hk.2 e t ht.1).2⟩)
    (hB x (fun t ht => (hRx t ht).trans (le_max_left _ _)))
    (hB y (fun t ht => (hRy t ht).trans (le_max_right _ _)))

theorem Network.IsIntegralSolution.eqOn_nonnegative (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    {z : State d} {x y : ℝ → State d}
    (hx : N.IsIntegralSolution k z x) (hy : N.IsIntegralSolution k z y) :
    EqOn x y (Ici 0) := by
  intro t ht
  have hx' : IntegralSolutionOn (fun s v => N.rhs (fun e => k e s) v) z 0 t x :=
    ⟨hx.1.mono (fun _ hs => hs.1), hx.2.1, hx.2.2.1 t ht,
      fun s hs => hx.2.2.2 s hs.1⟩
  have hy' : IntegralSolutionOn (fun s v => N.rhs (fun e => k e s) v) z 0 t y :=
    ⟨hy.1.mono (fun _ hs => hs.1), hy.2.1, hy.2.2.1 t ht,
      fun s hs => hy.2.2.2 s hs.1⟩
  exact N.integralSolutionOn_unique hk ht hx' hy' ⟨ht, le_rfl⟩

theorem Network.positiveWellPosed_of_exists (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u) {z : State d}
    (h : ∃ x, N.IsGlobalPositiveSolution k z x) : N.PositiveWellPosed k z := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hx, fun y hy t ht => Network.IsIntegralSolution.eqOn_nonnegative N hk hy.1 hx.1 ht⟩

theorem Network.exists_unique_positive_local_integralSolution (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (z : State d) (hz : Positive z) :
    ∃ T : ℝ, 0 < T ∧ ∃ x : ℝ → State d, Continuous x ∧
      IntegralSolutionOn (fun t v => N.rhs (fun e => k e t) v) z 0 T x ∧
      (∀ t ∈ Icc 0 T, Positive (x t)) ∧
      ∀ y, IntegralSolutionOn (fun t v => N.rhs (fun e => k e t) v) z 0 T y →
        EqOn y x (Icc 0 T) := by
  obtain ⟨T, hT, x, hxc, hx, hp⟩ := N.exists_positive_local_integralSolution hk z hz
  exact ⟨T, hT, x, hxc, hx, hp, fun y hy => N.integralSolutionOn_unique hk hT.le hy hx⟩

end Endotactic
end

-- Source: Endotactic/GlobalVolterra.lean
section
/-!
# Global bounded-field solutions by an exponentially weighted Volterra map

On bounded continuous paths over `[0,∞)`, conjugate the Volterra map by
`u(t) ↦ exp(c*t) • u(t)`, with `c = L+1`. Its Lipschitz constant is at most
`L/c < 1`, independently of the time horizon. Boundedness of the field makes
the weighted output uniformly bounded. This avoids countable time-step gluing.

The theorem concerns the bounded cutoff field. Recovering the original
mass-action field still requires a proved trapping condition.
-/

namespace Endotactic

open Set MeasureTheory
open scoped Topology NNReal BoundedContinuousFunction

variable {d : ℕ}

def nonnegativeClamp (t : ℝ) : Ici (0 : ℝ) :=
  ⟨max 0 t, show 0 ≤ max 0 t from le_max_left _ _⟩

theorem continuous_nonnegativeClamp : Continuous nonnegativeClamp :=
  (show Continuous (fun t : ℝ => max 0 t) by fun_prop).subtype_mk _

def BoundedMeasurableODE.weightRate (D : BoundedMeasurableODE d) : ℝ :=
  (D.lipschitzConstant : ℝ) + 1

theorem BoundedMeasurableODE.weightRate_ge_one (D : BoundedMeasurableODE d) :
    1 ≤ D.weightRate := by dsimp [weightRate]; linarith [D.lipschitzConstant.coe_nonneg]

theorem BoundedMeasurableODE.weightRate_pos (D : BoundedMeasurableODE d) :
    0 < D.weightRate := lt_of_lt_of_le zero_lt_one D.weightRate_ge_one

theorem BoundedMeasurableODE.normBound_nonneg (D : BoundedMeasurableODE d) :
    0 ≤ D.normBound := (norm_nonneg (D.field 0 0)).trans (D.norm_le 0 0)

noncomputable def BoundedMeasurableODE.inflate (D : BoundedMeasurableODE d)
    (u : Ici (0 : ℝ) →ᵇ State d) (t : ℝ) : State d :=
  Real.exp (D.weightRate * t) • u (nonnegativeClamp t)

theorem BoundedMeasurableODE.continuous_inflate (D : BoundedMeasurableODE d)
    (u : Ici (0 : ℝ) →ᵇ State d) : Continuous (D.inflate u) := by
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    (u.continuous.comp continuous_nonnegativeClamp)

theorem BoundedMeasurableODE.path_intervalIntegrable (D : BoundedMeasurableODE d)
    {x : ℝ → State d} (hx : Continuous x) (a b : ℝ) :
    IntervalIntegrable (fun t => D.field t (x t)) volume a b := by
  have hm := D.measurable.comp (measurable_id.prodMk hx.measurable)
  apply intervalIntegrable_iff.mpr
  apply IntegrableOn.of_bound (s := uIoc a b) (μ := volume)
    (show volume (uIoc a b) < ⊤ from measure_Ioc_lt_top)
    (hm.aestronglyMeasurable.mono_measure Measure.restrict_le_self) D.normBound
  exact Filter.Eventually.of_forall fun t => D.norm_le t _

noncomputable def BoundedMeasurableODE.weightedValue (D : BoundedMeasurableODE d)
    (u : Ici (0 : ℝ) →ᵇ State d) (t : ℝ) : State d :=
  Real.exp (-D.weightRate * t) •
    (D.initial + ∫ s in (0 : ℝ)..t, D.field s (D.inflate u s))

theorem BoundedMeasurableODE.continuous_weightedValue (D : BoundedMeasurableODE d)
    (u : Ici (0 : ℝ) →ᵇ State d) : Continuous (D.weightedValue u) := by
  have hp := intervalIntegral.continuous_primitive
    (D.path_intervalIntegrable (D.continuous_inflate u)) 0
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    (continuous_const.add hp)

theorem exp_weight_mul_time_le_one {c t : ℝ} (hc : 1 ≤ c) (ht : 0 ≤ t) :
    Real.exp (-c * t) * t ≤ 1 := by
  have hh : t ≤ Real.exp (c * t) := by
    have hct : t ≤ c * t := by simpa using mul_le_mul_of_nonneg_right hc ht
    have he := Real.add_one_le_exp (c * t)
    linarith
  calc
    Real.exp (-c * t) * t ≤ Real.exp (-c * t) * Real.exp (c * t) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem BoundedMeasurableODE.weightedValue_norm_le (D : BoundedMeasurableODE d)
    (u : Ici (0 : ℝ) →ᵇ State d) {t : ℝ} (ht : 0 ≤ t) :
    ‖D.weightedValue u t‖ ≤ ‖D.initial‖ + D.normBound := by
  have hi : ‖∫ s in (0 : ℝ)..t, D.field s (D.inflate u s)‖ ≤ D.normBound * t := by
    simpa only [sub_zero, abs_of_nonneg ht] using
      intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun s => D.field s (D.inflate u s)) (a := 0) (b := t)
        (fun s _ => D.norm_le s _)
  have he : Real.exp (-D.weightRate * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr D.weightRate_pos.le) ht)
  rw [weightedValue, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-D.weightRate * t) * ‖D.initial + ∫ s in 0..t, D.field s (D.inflate u s)‖ ≤
        Real.exp (-D.weightRate * t) * (‖D.initial‖ + D.normBound * t) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add_right hi _))
        (Real.exp_pos _).le
    _ = Real.exp (-D.weightRate * t) * ‖D.initial‖ +
        D.normBound * (Real.exp (-D.weightRate * t) * t) := by ring
    _ ≤ 1 * ‖D.initial‖ + D.normBound * 1 := add_le_add
      (mul_le_mul_of_nonneg_right he (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (exp_weight_mul_time_le_one D.weightRate_ge_one ht)
        D.normBound_nonneg)
    _ = ‖D.initial‖ + D.normBound := by ring

noncomputable def BoundedMeasurableODE.weightedVolterra (D : BoundedMeasurableODE d) :
    (Ici (0 : ℝ) →ᵇ State d) → (Ici (0 : ℝ) →ᵇ State d) := fun u =>
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => D.weightedValue u t)
    ((D.continuous_weightedValue u).comp continuous_subtype_val)
    (‖D.initial‖ + D.normBound) (fun t => D.weightedValue_norm_le u t.property)

theorem integral_exp_mul_real {c t : ℝ} (hc : c ≠ 0) :
    (∫ s in (0 : ℝ)..t, Real.exp (c * s)) = (Real.exp (c * t) - 1) / c := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp hc]
  simp only [mul_zero, integral_exp, Real.exp_zero, smul_eq_mul]
  ring

theorem BoundedMeasurableODE.dist_weightedVolterra_apply_le (D : BoundedMeasurableODE d)
    (u v : Ici (0 : ℝ) →ᵇ State d) (t : Ici (0 : ℝ)) :
    dist (D.weightedVolterra u t) (D.weightedVolterra v t) ≤
      ((D.lipschitzConstant : ℝ) / D.weightRate) * dist u v := by
  have hu := D.path_intervalIntegrable (D.continuous_inflate u) 0 t
  have hv := D.path_intervalIntegrable (D.continuous_inflate v) 0 t
  have hd : ∀ s ∈ Icc (0 : ℝ) t,
      ‖D.field s (D.inflate u s) - D.field s (D.inflate v s)‖ ≤
        ((D.lipschitzConstant : ℝ) * dist u v) * Real.exp (D.weightRate * s) := by
    intro s _
    rw [← dist_eq_norm]
    have hh := (D.lipschitz s).dist_le_mul (D.inflate u s) (D.inflate v s)
    unfold inflate at hh
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hh
    calc
      _ ≤ (D.lipschitzConstant : ℝ) *
          (Real.exp (D.weightRate * s) * dist (u (nonnegativeClamp s)) (v (nonnegativeClamp s))) := hh
      _ ≤ (D.lipschitzConstant : ℝ) * (Real.exp (D.weightRate * s) * dist u v) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (BoundedContinuousFunction.dist_coe_le_dist _)
            (Real.exp_pos _).le) D.lipschitzConstant.coe_nonneg
      _ = _ := by ring
  have hexp : Continuous (fun s : ℝ => Real.exp (D.weightRate * s)) := by fun_prop
  have hint : ‖∫ s in (0 : ℝ)..(t : ℝ),
      D.field s (D.inflate u s) - D.field s (D.inflate v s)‖ ≤
        ((D.lipschitzConstant : ℝ) * dist u v) *
          ((Real.exp (D.weightRate * t) - 1) / D.weightRate) := by
    calc
      _ ≤ ∫ s in (0 : ℝ)..(t : ℝ), ‖D.field s (D.inflate u s) - D.field s (D.inflate v s)‖ :=
        intervalIntegral.norm_integral_le_integral_norm t.property
      _ ≤ ∫ s in (0 : ℝ)..(t : ℝ),
          ((D.lipschitzConstant : ℝ) * dist u v) * Real.exp (D.weightRate * s) :=
        intervalIntegral.integral_mono_on t.property (hu.sub hv).norm
          ((hexp.intervalIntegrable 0 t).const_mul _) hd
      _ = _ := by rw [intervalIntegral.integral_const_mul, integral_exp_mul_real D.weightRate_pos.ne']
  change dist (D.weightedValue u t) (D.weightedValue v t) ≤ _
  rw [weightedValue, weightedValue, dist_smul₀, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), dist_eq_norm, add_sub_add_left_eq_sub,
    ← intervalIntegral.integral_sub hu hv]
  have he : Real.exp (-D.weightRate * (t : ℝ)) * Real.exp (D.weightRate * (t : ℝ)) = 1 := by
    rw [← Real.exp_add]; simp
  have hc := D.weightRate_pos
  calc
    _ ≤ Real.exp (-D.weightRate * (t : ℝ)) *
        (((D.lipschitzConstant : ℝ) * dist u v) *
          ((Real.exp (D.weightRate * t) - 1) / D.weightRate)) :=
      mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le
    _ ≤ Real.exp (-D.weightRate * (t : ℝ)) *
        (((D.lipschitzConstant : ℝ) * dist u v) *
          (Real.exp (D.weightRate * t) / D.weightRate)) := by gcongr; linarith
    _ = _ := by
      calc
        _ = ((D.lipschitzConstant : ℝ) / D.weightRate) * dist u v *
            (Real.exp (-D.weightRate * (t : ℝ)) * Real.exp (D.weightRate * (t : ℝ))) := by ring
        _ = _ := by rw [he, mul_one]

noncomputable def BoundedMeasurableODE.weightContraction (D : BoundedMeasurableODE d) : ℝ≥0 :=
  ⟨(D.lipschitzConstant : ℝ) / D.weightRate,
    div_nonneg D.lipschitzConstant.coe_nonneg D.weightRate_pos.le⟩

theorem BoundedMeasurableODE.weightedVolterra_contracting (D : BoundedMeasurableODE d) :
    ContractingWith D.weightContraction D.weightedVolterra := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  · change (D.lipschitzConstant : ℝ) / D.weightRate < 1
    rw [div_lt_one D.weightRate_pos]
    dsimp [weightRate]; linarith
  · apply (BoundedContinuousFunction.dist_le (mul_nonneg D.weightContraction.coe_nonneg dist_nonneg)).mpr
    exact D.dist_weightedVolterra_apply_le u v

/-- An integral solution on all nonnegative times, without a positivity claim. -/
def GlobalIntegralSolution (F : ℝ → State d → State d) (z : State d)
    (x : ℝ → State d) : Prop :=
  ContinuousOn x (Ici 0) ∧ x 0 = z ∧
    (∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun t => F t (x t)) volume 0 T) ∧
    ∀ t : ℝ, 0 ≤ t → x t = z + ∫ s in (0 : ℝ)..t, F s (x s)

theorem GlobalIntegralSolution.on_interval {F : ℝ → State d → State d}
    {z : State d} {x : ℝ → State d} (hx : GlobalIntegralSolution F z x)
    {T : ℝ} (hT : 0 ≤ T) : IntegralSolutionOn F z 0 T x :=
  ⟨hx.1.mono (fun _ ht => ht.1), hx.2.1, hx.2.2.1 T hT,
    fun t ht => hx.2.2.2 t ht.1⟩

theorem BoundedMeasurableODE.exists_global_integralSolution (D : BoundedMeasurableODE d) :
    ∃ x : ℝ → State d, Continuous x ∧ GlobalIntegralSolution D.field D.initial x := by
  let hc := D.weightedVolterra_contracting
  let u : Ici (0 : ℝ) →ᵇ State d := hc.fixedPoint
  have hu : D.weightedVolterra u = u := hc.fixedPoint_isFixedPt
  refine ⟨D.inflate u, D.continuous_inflate u, ?_⟩
  have heq : ∀ t : ℝ, 0 ≤ t → D.inflate u t =
      D.initial + ∫ s in (0 : ℝ)..t, D.field s (D.inflate u s) := by
    intro t ht
    have hh := congrArg (fun w : Ici (0 : ℝ) →ᵇ State d => w ⟨t, ht⟩) hu
    change Real.exp (-D.weightRate * t) •
      (D.initial + ∫ s in (0 : ℝ)..t, D.field s (D.inflate u s)) = u ⟨t, ht⟩ at hh
    unfold inflate
    have hclamp : nonnegativeClamp t = ⟨t, ht⟩ := by
      apply Subtype.ext; exact max_eq_right ht
    rw [hclamp, ← hh, smul_smul]
    have he : Real.exp (D.weightRate * t) * Real.exp (-D.weightRate * t) = 1 := by
      rw [← Real.exp_add]; simp
    rw [he, one_smul]
    rfl
  exact ⟨(D.continuous_inflate u).continuousOn, by simpa using heq 0 le_rfl,
    fun T _ => D.path_intervalIntegrable (D.continuous_inflate u) 0 T, heq⟩

theorem BoundedMeasurableODE.global_integralSolution_unique (D : BoundedMeasurableODE d)
    {x y : ℝ → State d} (hx : GlobalIntegralSolution D.field D.initial x)
    (hy : GlobalIntegralSolution D.field D.initial y) : EqOn x y (Ici 0) := by
  intro t ht
  exact (hx.on_interval ht).eqOn_of_lipschitzOn ht (hy.on_interval ht)
    (B := univ) (L := D.lipschitzConstant)
    (fun s _ => lipschitzOnWith_iff_dist_le_mul.mpr
      (fun z _ w _ => (D.lipschitz s).dist_le_mul z w))
    (fun _ _ => mem_univ _) (fun _ _ => mem_univ _) ⟨ht, le_rfl⟩

end Endotactic
end

-- Source: Endotactic/BoxInvariance.lean
section
/-!
# Box invariance and positive global mass-action solutions

For an absolutely continuous coordinate, cap its negative part at zero.
Nonnegative derivative below zero implies that a nonnegative initial coordinate
stays nonnegative. Applied to both faces, this gives box invariance without
pointwise differentiability of the rate path.

Clamping sends a state outside a coordinate face to that face. Inward face
inequalities therefore imply the required derivative signs everywhere outside
the box. The global cutoff solution is then a positive global solution of the
original field. The face inequalities are explicit hypotheses, not consequences
of general endotacticity proved here.
-/

namespace Endotactic

open Set MeasureTheory Filter
open scoped Topology

variable {d : ℕ} {E : Type*} [Fintype E]

theorem ac_nonnegative_of_deriv_on_negative (f : ℝ → ℝ)
    (hAC : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T) (h0 : 0 ≤ f 0)
    (hderiv : ∀ T, 0 ≤ T → ∀ᵐ t ∂volume,
      t ∈ Icc 0 T → f t < 0 → 0 ≤ deriv f t) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ f t := by
  let g : ℝ → ℝ := fun t => min (f t) 0
  have hg : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval g 0 T :=
    fun T hT => ac_min (hAC T hT) (ac_const 0 0 T)
  have hbelow : ∀ T, 0 ≤ T → ∀ᵐ t ∂volume,
      t ∈ Icc 0 T → g t < 0 → 0 ≤ deriv g t := by
    intro T hT
    filter_upwards [(hAC T hT).ae_differentiableAt, hderiv T hT] with t hdiff hd ht hneg
    have hfneg : f t < 0 := (min_lt_iff.mp hneg).resolve_right (lt_irrefl 0)
    have hdf := (hdiff (by simpa only [uIcc_of_le hT] using ht)).hasDerivAt
    have hlocal : ∀ᶠ s in 𝓝 t, f s < 0 := hdf.continuousAt.eventually (Iio_mem_nhds hfneg)
    have hmin : HasDerivAt g (deriv f t) t :=
      hdf.congr_of_eventuallyEq (hlocal.mono fun s hs => min_eq_left hs.le)
    rw [hmin.deriv]
    exact hd ht hfneg
  have hmono := ac_monotone_of_below_cap_deriv_nonneg g hg
    (fun _ _ => min_le_right _ _) hbelow
  intro t ht
  have hh := hmono 0 t le_rfl ht
  have hg0 : g 0 = 0 := min_eq_right h0
  rw [hg0] at hh
  exact hh.trans (min_le_left _ _)

theorem GlobalIntegralSolution.clm_integral_eq {F : ℝ → State d → State d}
    {z : State d} {x : ℝ → State d} (hx : GlobalIntegralSolution F z x)
    (L : State d →L[ℝ] ℝ) {t : ℝ} (ht : 0 ≤ t) :
    L (x t) = L z + ∫ s in (0 : ℝ)..t, L (F s (x s)) := by
  have hh := congrArg L (hx.2.2.2 t ht)
  rw [map_add, ← L.intervalIntegral_comp_comm (hx.2.2.1 t ht)] at hh
  exact hh

theorem GlobalIntegralSolution.clm_ac {F : ℝ → State d → State d}
    {z : State d} {x : ℝ → State d} (hx : GlobalIntegralSolution F z x)
    (L : State d →L[ℝ] ℝ) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => L (x t)) 0 T := by
  have hp := (clm_intervalIntegrable L (hx.2.2.1 T hT)).absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) (by simp)
  apply ac_congrOn ((ac_const (L z) 0 T).add hp)
  intro t ht
  have ht' : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
  exact (hx.clm_integral_eq L ht'.1).symm

theorem GlobalIntegralSolution.clm_ae_hasDerivAt {F : ℝ → State d → State d}
    {z : State d} {x : ℝ → State d} (hx : GlobalIntegralSolution F z x)
    (L : State d →L[ℝ] ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt (fun s => L (x s)) (L (F t (x t))) t := by
  have hzero : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have htop : ∀ᵐ t : ℝ ∂volume, t ≠ T := by simp [ae_iff, measure_singleton]
  filter_upwards [(clm_intervalIntegrable L (hx.2.2.1 T hT)).ae_hasDerivAt_integral, hzero, htop]
    with t hp hz ht hmem
  have hlt0 : 0 < t := lt_of_le_of_ne hmem.1 hz.symm
  have hltT : t < T := lt_of_le_of_ne hmem.2 ht
  have hp' := (hp (by simpa only [uIcc_of_le hT] using hmem) 0 (by simp)).const_add (L z)
  apply hp'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hlt0 hltT] with s hs
  exact hx.clm_integral_eq L hs.1.le

theorem GlobalIntegralSolution.mem_box_of_outside_sign {F : ℝ → State d → State d}
    {z lo hi : State d} {x : ℝ → State d} (hx : GlobalIntegralSolution F z x)
    (hz : z ∈ Icc lo hi)
    (hlower : ∀ t, 0 ≤ t → ∀ y i, y i < lo i → 0 ≤ F t y i)
    (hupper : ∀ t, 0 ≤ t → ∀ y i, hi i < y i → F t y i ≤ 0) :
    ∀ t, 0 ≤ t → x t ∈ Icc lo hi := by
  have hlow : ∀ i t, 0 ≤ t → 0 ≤ x t i - lo i := by
    intro i
    let L : State d →L[ℝ] ℝ := ContinuousLinearMap.proj i
    apply ac_nonnegative_of_deriv_on_negative
    · intro T hT
      exact (hx.clm_ac L hT).sub (ac_const (lo i) 0 T)
    · rw [hx.2.1]; exact sub_nonneg.mpr (hz.1 i)
    · intro T hT
      filter_upwards [hx.clm_ae_hasDerivAt L hT] with t hd ht hneg
      have hh : HasDerivAt (fun s => x s i - lo i) (F t (x t) i) t := (hd ht).sub_const (lo i)
      rw [hh.deriv]
      exact hlower t ht.1 (x t) i (sub_neg.mp hneg)
  have hhigh : ∀ i t, 0 ≤ t → 0 ≤ hi i - x t i := by
    intro i
    let L : State d →L[ℝ] ℝ := ContinuousLinearMap.proj i
    apply ac_nonnegative_of_deriv_on_negative
    · intro T hT
      exact (ac_const (hi i) 0 T).sub (hx.clm_ac L hT)
    · rw [hx.2.1]; exact sub_nonneg.mpr (hz.2 i)
    · intro T hT
      filter_upwards [hx.clm_ae_hasDerivAt L hT] with t hd ht hneg
      have hh : HasDerivAt (fun s => hi i - x s i) (-F t (x t) i) t := (hd ht).const_sub (hi i)
      rw [hh.deriv]
      exact neg_nonneg.mpr (hupper t ht.1 (x t) i (sub_neg.mp hneg))
  exact fun t ht => ⟨fun i => sub_nonneg.mp (hlow i t ht), fun i => sub_nonneg.mp (hhigh i t ht)⟩

theorem boxClamp_lower_face {lo hi : State d} (hbox : lo ≤ hi) {y : State d}
    (i : Fin d) (hy : y i ≤ lo i) : boxClamp lo hi y i = lo i := by
  simp only [boxClamp, min_eq_right (hy.trans (hbox i)), max_eq_left hy]

theorem boxClamp_upper_face {lo hi : State d} (hbox : lo ≤ hi) {y : State d}
    (i : Fin d) (hy : hi i ≤ y i) : boxClamp lo hi y i = hi i := by
  simp only [boxClamp, min_eq_left hy, max_eq_right (hbox i)]

theorem GlobalIntegralSolution.congr_field {F G : ℝ → State d → State d}
    {z : State d} {x : ℝ → State d} (hx : GlobalIntegralSolution F z x)
    (hFG : ∀ t, 0 ≤ t → F t (x t) = G t (x t)) : GlobalIntegralSolution G z x := by
  refine ⟨hx.1, hx.2.1, ?_, ?_⟩
  · intro T hT
    apply (hx.2.2.1 T hT).congr
    intro t ht
    rw [uIoc_of_le hT] at ht
    exact hFG t ht.1.le
  · intro t ht
    rw [hx.2.2.2 t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact hFG s hs.1

theorem Network.exists_global_cutoff_integralSolution (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (lo hi : State d) (hbox : lo ≤ hi) (z : State d) :
    ∃ x : ℝ → State d, Continuous x ∧ GlobalIntegralSolution (N.cutoffRhs k lo hi) z x := by
  obtain ⟨D, hDF, hDz⟩ := N.exists_cutoffODE hk lo hi hbox z
  obtain ⟨x, hc, hx⟩ := D.exists_global_integralSolution
  rw [hDF, hDz] at hx
  exact ⟨x, hc, hx⟩

theorem Network.exists_global_positive_in_box (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (lo hi : State d) (hbox : lo ≤ hi) (hlo : Positive lo) {z : State d} (hz : z ∈ Icc lo hi)
    (hlower : ∀ t, 0 ≤ t → ∀ y ∈ Icc lo hi, ∀ i, y i = lo i →
      0 ≤ N.rhs (fun e => k e t) y i)
    (hupper : ∀ t, 0 ≤ t → ∀ y ∈ Icc lo hi, ∀ i, y i = hi i →
      N.rhs (fun e => k e t) y i ≤ 0) :
    ∃ x : ℝ → State d, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ Icc lo hi := by
  obtain ⟨x, _, hx⟩ := N.exists_global_cutoff_integralSolution hk lo hi hbox z
  have hstay := hx.mem_box_of_outside_sign hz
    (by
      intro t ht y i hy
      unfold Network.cutoffRhs
      rw [max_eq_right ht]
      exact hlower t ht _ (boxClamp_mem lo hi hbox y) i (boxClamp_lower_face hbox i hy.le))
    (by
      intro t ht y i hy
      unfold Network.cutoffRhs
      rw [max_eq_right ht]
      exact hupper t ht _ (boxClamp_mem lo hi hbox y) i (boxClamp_upper_face hbox i hy.le))
  have hactual : N.IsIntegralSolution k z x := hx.congr_field
    (fun t ht => N.cutoffRhs_eq k lo hi ht (hstay t ht))
  exact ⟨x, ⟨hactual, fun t ht i => (hlo i).trans_le ((hstay t ht).1 i)⟩, hstay⟩

end Endotactic
end

-- Source: Endotactic/PolyhedralInvariance.lean
section
/-!
# Positive global solutions trapped by finite affine inequalities

A derivative sign is needed only in a thin strip below the target level.
Clamping an absolutely continuous scalar at the bottom of that strip makes
its derivative zero at the bottom, by Fermat. The existing negative-part
barrier then rules out crossing the target level.

Applied to a finite affine minimum of a global cutoff trajectory, this proves
polyhedral trapping, including tilted faces. An enlarged plateau contained
in a positive coordinate box makes the cutoff agree with the original field
throughout the strip. The strip flux signs are explicit hypotheses here.
-/

namespace Endotactic

open Set MeasureTheory Filter
open scoped Topology

theorem ac_max {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => max (f t) (g t)) a b := by
  have hdist (s t : ℝ) :
      dist (max (f s) (g s)) (max (f t) (g t)) ≤ dist (f s) (f t) + dist (g s) (g t) := by
    have h := lipschitzWith_max.dist_le_mul (f s, g s) (f t, g t)
    simp only [NNReal.coe_one, one_mul, Prod.dist_eq] at h
    exact h.trans (max_le (le_add_of_nonneg_right dist_nonneg)
      (le_add_of_nonneg_left dist_nonneg))
  apply squeeze_zero (fun E => Finset.sum_nonneg fun _ _ => dist_nonneg)
    (fun E => ?_) (by simpa using Tendsto.add hf hg)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => hdist (E.2 i).1 (E.2 i).2

theorem ac_nonnegative_of_deriv_in_strip (f : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hAC : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval f 0 T) (h0 : 0 ≤ f 0)
    (hderiv : ∀ T, 0 ≤ T → ∀ᵐ t ∂volume,
      t ∈ Icc 0 T → -ε < f t → f t < 0 → 0 ≤ deriv f t) :
    ∀ t, 0 ≤ t → 0 ≤ f t := by
  let g : ℝ → ℝ := fun t => max (f t) (-ε)
  have hg : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval g 0 T :=
    fun T hT => ac_max (hAC T hT) (ac_const (-ε) 0 T)
  have hnonneg := ac_nonnegative_of_deriv_on_negative g hg
    (h0.trans (le_max_left _ _)) (by
      intro T hT
      filter_upwards [(hAC T hT).ae_differentiableAt, (hg T hT).ae_differentiableAt,
        hderiv T hT] with t hdf hdg hd ht hneg
      have ht' : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hT] using ht
      by_cases hf : -ε < f t
      · have hlocal : ∀ᶠ s in 𝓝 t, -ε < f s :=
          (hdf ht').continuousAt.eventually (Ioi_mem_nhds hf)
        have hh : HasDerivAt g (deriv f t) t := (hdf ht').hasDerivAt.congr_of_eventuallyEq
          (hlocal.mono fun s hs => max_eq_left hs.le)
        rw [hh.deriv]
        exact hd ht hf ((le_max_left _ _).trans_lt hneg)
      · have heq : g t = -ε := max_eq_right (le_of_not_gt hf)
        have hmin : IsLocalMin g t := Filter.Eventually.of_forall (fun s => by
          rw [heq]; exact le_max_right _ _)
        rw [hmin.hasDerivAt_eq_zero (hdg ht').hasDerivAt])
  intro t ht
  have hh := hnonneg t ht
  exact (le_max_iff.mp hh).resolve_right (by linarith)

variable {d m : ℕ}
variable {F : ℝ → State d → State d} {z : State d} {x : ℝ → State d}

theorem GlobalIntegralSolution.affine_branch_ac (hx : GlobalIntegralSolution F z x)
    (A : AffineFamily d m) (i : Fin m) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => A.value i (x t)) 0 T :=
  (hx.clm_ac (dotCLM (A.slope i)) hT).add (ac_const (A.offset i) 0 T)

theorem GlobalIntegralSolution.affine_branch_ae_hasDerivAt
    (hx : GlobalIntegralSolution F z x) (A : AffineFamily d m) (i : Fin m)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt (fun s => A.value i (x s))
      (dot (A.slope i) (F t (x t))) t := by
  filter_upwards [hx.clm_ae_hasDerivAt (dotCLM (A.slope i)) hT] with t hd ht
  exact (hd ht).add_const (A.offset i)

variable [Nonempty (Fin m)]

theorem GlobalIntegralSolution.affine_minimum_ac (hx : GlobalIntegralSolution F z x)
    (A : AffineFamily d m) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => A.minimum (x t)) 0 T :=
  finiteMinimum_ac (fun i t => A.value i (x t)) (fun i => hx.affine_branch_ac A i hT)

theorem GlobalIntegralSolution.affine_minimum_ae_deriv_nonneg_on
    (hx : GlobalIntegralSolution F z x) (A : AffineFamily d m) (P : ℝ → Prop)
    {T : ℝ} (hT : 0 ≤ T)
    (hb : ∀ t ∈ Icc 0 T, P t → ∀ i, A.Active i (x t) →
      0 ≤ dot (A.slope i) (F t (x t))) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T → P t → 0 ≤ deriv (fun s => A.minimum (x s)) t := by
  have hd : ∀ᵐ t ∂volume, ∀ i, t ∈ Icc 0 T → HasDerivAt (fun s => A.value i (x s))
      (dot (A.slope i) (F t (x t))) t :=
    ae_all_iff.mpr fun i => hx.affine_branch_ae_hasDerivAt A i hT
  have hbound : ∀ᵐ t ∂volume, t ∈ uIcc 0 T → P t → ∀ i,
      finiteMinimum (fun j => A.value j (x t)) = A.value i (x t) →
        0 ≤ deriv (fun s => A.value i (x s)) t := by
    filter_upwards [hd] with t hds ht hp i hi
    have ht' : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
    rw [(hds i ht').deriv]
    exact hb t ht' hp i ((A.active_iff_minimum_eq i (x t)).mpr hi)
  simpa only [AffineFamily.minimum, uIcc_of_le hT] using
    finiteMinimum_ae_deriv_lower_bound_on (fun i t => A.value i (x t)) P
      (fun i => hx.affine_branch_ac A i hT) hbound

theorem GlobalIntegralSolution.mem_affine_plateau_of_strip
    (hx : GlobalIntegralSolution F z x) (A : AffineFamily d m) {M ε : ℝ}
    (hε : 0 < ε) (hz : z ∈ A.plateau M)
    (hb : ∀ t, 0 ≤ t → M - ε < A.minimum (x t) → A.minimum (x t) < M →
      ∀ i, A.Active i (x t) → 0 ≤ dot (A.slope i) (F t (x t))) :
    ∀ t, 0 ≤ t → x t ∈ A.plateau M := by
  have hn := ac_nonnegative_of_deriv_in_strip (fun t => A.minimum (x t) - M) hε
    (fun T hT => (hx.affine_minimum_ac A hT).sub (ac_const M 0 T))
    (by rw [hx.2.1]; exact sub_nonneg.mpr ((A.mem_plateau_iff_minimum_ge z M).mp hz)) (by
      intro T hT
      have hd := hx.affine_minimum_ae_deriv_nonneg_on A
        (fun t => M - ε < A.minimum (x t) ∧ A.minimum (x t) < M) hT
        (fun t ht hp => hb t ht.1 hp.1 hp.2)
      filter_upwards [hd, (hx.affine_minimum_ac A hT).ae_differentiableAt]
        with t hds hdiff ht hl hu
      have hh := (hdiff (by simpa only [uIcc_of_le hT] using ht)).hasDerivAt.sub_const M
      rw [hh.deriv]
      exact hds ht ⟨by linarith, by linarith⟩)
  exact fun t ht => (A.mem_plateau_iff_minimum_ge (x t) M).mpr (sub_nonneg.mp (hn t ht))

variable {E : Type*} [Fintype E]

theorem Network.exists_global_positive_in_affine_strip (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M ε : ℝ} (hε : 0 < ε)
    (lo hi : State d) (hbox : lo ≤ hi) (hlo : Positive lo)
    (hsub : A.plateau (M - ε) ⊆ Icc lo hi) {z : State d} (hz : z ∈ A.plateau M)
    (hflux : ∀ t, 0 ≤ t → ∀ y, M - ε < A.minimum y → A.minimum y < M →
      ∀ i, A.Active i y → 0 ≤ dot (A.slope i) (N.rhs (fun e => k e t) y)) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧ ∀ t, 0 ≤ t → x t ∈ A.plateau M := by
  obtain ⟨x, _, hx⟩ := N.exists_global_cutoff_integralSolution hk lo hi hbox z
  have hstay := hx.mem_affine_plateau_of_strip A hε hz (by
    intro t ht hl hu i ha
    have hy : x t ∈ Icc lo hi := hsub
      ((A.mem_plateau_iff_minimum_ge (x t) (M - ε)).mpr hl.le)
    rw [N.cutoffRhs_eq k lo hi ht hy]
    exact hflux t ht (x t) hl hu i ha)
  have hxbox : ∀ t, 0 ≤ t → x t ∈ Icc lo hi := by
    intro t ht
    apply hsub
    exact fun i => (sub_le_self M hε.le).trans (hstay t ht i)
  have hactual : N.IsIntegralSolution k z x := hx.congr_field
    (fun t ht => N.cutoffRhs_eq k lo hi ht (hxbox t ht))
  exact ⟨x, ⟨hactual, fun t ht i => (hlo i).trans_le ((hxbox t ht).1 i)⟩, hstay⟩

end Endotactic
end

-- Source: Endotactic/StrictFaceTrap.lean
section
/-!
# A finite face certificate supplies a uniform exterior strip

Each affine face is either a conserved observable (its flux is identically
zero), or has strictly inward flux for every coefficient in the compact rate
box. On a compact ambient state box, the bad-flux set is closed and compact.
Its active-face values avoid the target level, so a positive strip width
separates them from that level. Taking a finite minimum makes the width common
to every active branch and every coefficient.

This converts boundary certificates into positive global integral solutions
of the original field. It assumes an enlarged plateau inside a positive box;
constructing such trap geometry for arbitrary endotactic networks is separate.
No metric projection, Hilbert-space norm change, or pointwise time derivative
of the coefficient path is needed.
-/

namespace Endotactic

open Set

variable {d m : ℕ} {E : Type*} [Fintype E]

/-- A conserved face or a strictly inward face, uniformly over the rate box. -/
def Network.AffineFaceCertificate (N : Network d E) (A : AffineFamily d m)
    (ℓ u M : ℝ) : Prop :=
  ∀ i, (∀ a y, dot (A.slope i) (N.rhs a y) = 0) ∨
    ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u), ∀ y ∈ A.plateau M,
      A.value i y = M → 0 < dot (A.slope i) (N.rhs a y)

theorem Network.dot_rhs_eq_zero_of_projections (N : Network d E) (r : State d)
    (hzero : ∀ e, N.projection r e = 0) (a : E → ℝ) (y : State d) :
    dot r (N.rhs a y) = 0 := by
  rw [dot_rhs]
  simp [hzero]

theorem Network.affineFaceCertificate_of_projections (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ}
    (hfaces : ∀ i, (∀ e, N.projection (A.slope i) e = 0) ∨
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u), ∀ y ∈ A.plateau M,
        A.value i y = M → 0 < dot (A.slope i) (N.rhs a y)) :
    N.AffineFaceCertificate A ℓ u M := by
  intro i
  rcases hfaces i with hzero | hstrict
  · exact Or.inl (fun a y => N.dot_rhs_eq_zero_of_projections (A.slope i) hzero a y)
  · exact Or.inr hstrict

theorem Network.affine_branch_strip_of_face (N : Network d E) (A : AffineFamily d m)
    {ℓ u M : ℝ} (i : Fin m) {B : Set (State d)} (hB : IsCompact B)
    (hface : (∀ a y, dot (A.slope i) (N.rhs a y) = 0) ∨
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u), ∀ y ∈ A.plateau M,
        A.value i y = M → 0 < dot (A.slope i) (N.rhs a y)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u), ∀ y ∈ B,
      A.Active i y → M - ε < A.value i y → A.value i y < M →
        0 ≤ dot (A.slope i) (N.rhs a y) := by
  rcases hface with hzero | hstrict
  · refine ⟨1, zero_lt_one, ?_⟩
    intro a _ y _ _ _ _
    rw [hzero]
  · let bad : Set ((E → ℝ) × State d) :=
      (Icc (fun _ : E => ℓ) (fun _ => u) ×ˢ B) ∩
        {p | A.Active i p.2 ∧ dot (A.slope i) (N.rhs p.1 p.2) ≤ 0}
    have hactive : IsClosed {p : (E → ℝ) × State d | A.Active i p.2} := by
      have heq : {p : (E → ℝ) × State d | A.Active i p.2} =
          ⋂ j, {p | A.value i p.2 ≤ A.value j p.2} := by
        ext p; simp [AffineFamily.Active]
      rw [heq]
      exact isClosed_iInter fun j => isClosed_le
        ((A.continuous_value i).comp continuous_snd)
        ((A.continuous_value j).comp continuous_snd)
    have hflux : IsClosed {p : (E → ℝ) × State d |
        dot (A.slope i) (N.rhs p.1 p.2) ≤ 0} :=
      isClosed_le ((dotCLM (A.slope i)).continuous.comp N.rhs_joint_contDiff.continuous)
        continuous_const
    have hbad : IsCompact bad := (isCompact_Icc.prod hB).inter_right (hactive.inter hflux)
    let S : Set ℝ := (fun p : (E → ℝ) × State d => A.value i p.2) '' bad
    have hS : IsCompact S := hbad.image ((A.continuous_value i).comp continuous_snd)
    have hM : M ∈ Sᶜ := by
      intro hm
      obtain ⟨⟨a, y⟩, hp, heq⟩ := hm
      rcases hp with ⟨⟨ha, _⟩, hai, hf⟩
      have hy : y ∈ A.plateau M := fun j => heq ▸ hai j
      exact (not_lt_of_ge hf) (hstrict a ha y hy heq)
    obtain ⟨ε, hε, hsep⟩ := Metric.isOpen_iff.mp hS.isClosed.isOpen_compl M hM
    refine ⟨ε, hε, ?_⟩
    intro a ha y hy hai hl hu
    by_contra hn
    have hball : A.value i y ∈ Metric.ball M ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    exact (hsep hball) ⟨(a, y), ⟨⟨ha, hy⟩, hai, (lt_of_not_ge hn).le⟩, rfl⟩

variable [Nonempty (Fin m)]

theorem Network.affine_strip_of_face_certificate (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} {B : Set (State d)} (hB : IsCompact B)
    (hfaces : N.AffineFaceCertificate A ℓ u M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u), ∀ y ∈ B,
      M - ε < A.minimum y → A.minimum y < M → ∀ i, A.Active i y →
        0 ≤ dot (A.slope i) (N.rhs a y) := by
  have hb := fun i => N.affine_branch_strip_of_face A i hB (hfaces i)
  choose ε hε hs using hb
  let δ := finiteMinimum ε
  have hδ : 0 < δ := by
    obtain ⟨i, hi⟩ := finiteMinimum_attained ε
    change 0 < finiteMinimum ε
    rw [hi]
    exact hε i
  refine ⟨δ, hδ, ?_⟩
  intro a ha y hy hl hu i hai
  have heq := (A.active_iff_minimum_eq i y).mp hai
  have hle : δ ≤ ε i := finiteMinimum_le ε i
  apply hs i a ha y hy hai
  · linarith
  · linarith

theorem Network.exists_global_positive_of_affine_face_certificate (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (lo hi : State d) (hbox : lo ≤ hi) (hlo : Positive lo)
    (hsub : A.plateau (M - ε₀) ⊆ Icc lo hi)
    (hfaces : N.AffineFaceCertificate A ℓ u M) {z : State d} (hz : z ∈ A.plateau M) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧ ∀ t, 0 ≤ t → x t ∈ A.plateau M := by
  obtain ⟨δ, hδ, hs⟩ := N.affine_strip_of_face_certificate A
    (B := Icc lo hi) isCompact_Icc hfaces
  let ε := min ε₀ δ
  have hε : 0 < ε := lt_min hε₀ hδ
  have he₀ : ε ≤ ε₀ := min_le_left _ _
  have heδ : ε ≤ δ := min_le_right _ _
  have hsub' : A.plateau (M - ε) ⊆ Icc lo hi := by
    intro y hy
    exact hsub (fun i => (by linarith : M - ε₀ ≤ M - ε).trans (hy i))
  apply N.exists_global_positive_in_affine_strip hk A hε lo hi hbox hlo hsub' hz
  intro t ht y hl hu i hai
  have hy : y ∈ Icc lo hi := hsub'
    ((A.mem_plateau_iff_minimum_ge y (M - ε)).mpr hl.le)
  exact hs _ ⟨fun e => (hk.2 e t ht).1, fun e => (hk.2 e t ht).2⟩ y hy
    (by linarith) hu i hai

theorem Network.positiveWellPosed_of_affine_face_certificate (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (lo hi : State d) (hbox : lo ≤ hi) (hlo : Positive lo)
    (hsub : A.plateau (M - ε₀) ⊆ Icc lo hi)
    (hfaces : N.AffineFaceCertificate A ℓ u M) {z : State d} (hz : z ∈ A.plateau M) :
    N.PositiveWellPosed k z := by
  obtain ⟨x, hx, _⟩ := N.exists_global_positive_of_affine_face_certificate hk A
    hε₀ lo hi hbox hlo hsub hfaces hz
  exact N.positiveWellPosed_of_exists hk ⟨x, hx⟩

end Endotactic
end

-- Source: Endotactic/AffineRobustness.lean
section
/-!
# Compact affine plateaux have robust positive bounding boxes

A nonempty compact plateau stays inside any open neighborhood after a small
common relaxation of its finitely many inequalities. To control points far
away, scale the segment from a point in the original plateau to a relaxed
point until it reaches a fixed sphere. Convexity preserves the relaxed
inequalities, and compact separation excludes that sphere.

Consequently a compact positive plateau automatically has a slightly enlarged
plateau inside a positive coordinate box. The face-certificate global solution
API no longer requires a separate enlarged-box witness. The existence of the
compact positive plateau and its inward face certificates remains a hypothesis.
-/

namespace Endotactic

open Set

variable {d m : ℕ} [Nonempty (Fin m)]

theorem AffineFamily.continuous_minimum (A : AffineFamily d m) :
    Continuous A.minimum := by
  exact Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun i _ => A.continuous_value i)

theorem AffineFamily.compact_disjoint_plateau_gap (A : AffineFamily d m) {M : ℝ}
    {S : Set (State d)} (hS : IsCompact S) (hdis : Disjoint S (A.plateau M)) :
    ∃ ε : ℝ, 0 < ε ∧ Disjoint S (A.plateau (M - ε)) := by
  by_cases hne : S.Nonempty
  · obtain ⟨x, hx, hmax⟩ := hS.exists_isMaxOn hne A.continuous_minimum.continuousOn
    have hlt : A.minimum x < M := by
      by_contra hn
      exact Set.disjoint_left.mp hdis hx
        ((A.mem_plateau_iff_minimum_ge x M).mpr (le_of_not_gt hn))
    refine ⟨(M - A.minimum x) / 2, by linarith, Set.disjoint_left.mpr ?_⟩
    intro y hy hp
    have hle : A.minimum y ≤ A.minimum x := hmax hy
    have hge := (A.mem_plateau_iff_minimum_ge y _).mp hp
    linarith
  · exact ⟨1, zero_lt_one, by simp [Set.not_nonempty_iff_eq_empty.mp hne]⟩

theorem AffineFamily.exists_relaxed_plateau_subset_open (A : AffineFamily d m) {M : ℝ}
    (hne : (A.plateau M).Nonempty) (hK : IsCompact (A.plateau M))
    {U : Set (State d)} (hU : IsOpen U) (hsub : A.plateau M ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ A.plateau (M - ε) ⊆ U := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (continuous_id.dist continuous_const).continuousOn
  let R : ℝ := max B 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hball : A.plateau M ⊆ Metric.ball c R := by
    intro y hy
    rw [Metric.mem_ball]
    have hb := hB y hy
    rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] at hb
    exact hb.trans_lt (by dsimp [R]; linarith [le_max_left B 0])
  let bad : Set (State d) := (Metric.closedBall c R ∩ Uᶜ) ∪ Metric.sphere c R
  have hbad : IsCompact bad :=
    ((isCompact_closedBall c R).inter_right hU.isClosed_compl).union
      (isCompact_sphere c R)
  have hdis : Disjoint bad (A.plateau M) := by
    apply Set.disjoint_left.mpr
    intro y hy hp
    rcases hy with hy | hy
    · exact hy.2 (hsub hp)
    · have heq := Metric.mem_sphere.mp hy
      have hlt := Metric.mem_ball.mp (hball hp)
      linarith
  obtain ⟨ε, hε, hgap⟩ := A.compact_disjoint_plateau_gap hbad hdis
  refine ⟨ε, hε, ?_⟩
  intro x hx
  by_contra hn
  by_cases hnear : dist x c < R
  · exact Set.disjoint_left.mp hgap
      (Or.inl ⟨Metric.mem_closedBall.mpr hnear.le, hn⟩) hx
  · have hd : 0 < dist x c := hR.trans_le (le_of_not_gt hnear)
    let s : ℝ := R / dist x c
    have hs : 0 ≤ s := le_of_lt (div_pos hR hd)
    have hs₁ : s ≤ 1 := (div_le_one hd).mpr (le_of_not_gt hnear)
    let y : State d := (1 - s) • c + s • x
    have hc' : c ∈ A.plateau (M - ε) :=
      fun i => (sub_le_self M hε.le).trans (hc i)
    have hy : y ∈ A.plateau (M - ε) :=
      A.plateau_convex (M - ε) hc' hx (sub_nonneg.mpr hs₁) hs (by ring)
    have heq : y - c = s • (x - c) := by
      ext i
      simp only [y, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hdist : dist y c = R := by
      rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs,
        ← dist_eq_norm]
      exact div_mul_cancel₀ R (ne_of_gt hd)
    exact Set.disjoint_left.mp hgap
      (Or.inr (Metric.mem_sphere.mpr hdist)) hy

theorem AffineFamily.exists_enlarged_positive_box (A : AffineFamily d m) {M : ℝ}
    (hne : (A.plateau M).Nonempty) (hK : IsCompact (A.plateau M))
    (hpos : A.plateau M ⊆ {x | Positive x}) :
    ∃ (ε : ℝ) (lo hi : State d), 0 < ε ∧ lo ≤ hi ∧ Positive lo ∧
      A.plateau (M - ε) ⊆ Icc lo hi := by
  have hmin := fun i : Fin d => hK.exists_isMinOn hne
    (continuous_apply i).continuousOn
  have hmax := fun i : Fin d => hK.exists_isMaxOn hne
    (continuous_apply i).continuousOn
  choose a ha hamin using hmin
  choose b hb hbmax using hmax
  let lo : State d := fun i => a i i / 2
  let hi : State d := fun i => b i i + 1
  have hlo : Positive lo := fun i => half_pos (hpos (ha i) i)
  let U : Set (State d) := {x | ∀ i, lo i < x i ∧ x i < hi i}
  have hU : IsOpen U := by
    have heq : U = ⋂ i, {x | lo i < x i ∧ x i < hi i} := by
      ext x; simp [U]
    rw [heq]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (continuous_apply i)).inter
        (isOpen_lt (continuous_apply i) continuous_const)
  have hsub : A.plateau M ⊆ U := by
    intro x hx i
    constructor
    · have hsmall : lo i < a i i := by dsimp [lo]; linarith [hpos (ha i) i]
      exact hsmall.trans_le (hamin i hx)
    · have hlarge : b i i < hi i := by dsimp [hi]; linarith
      exact (hbmax i hx).trans_lt hlarge
  obtain ⟨ε, hε, hrelax⟩ := A.exists_relaxed_plateau_subset_open hne hK hU hsub
  obtain ⟨c, hc⟩ := hne
  refine ⟨ε, lo, hi, hε, (fun i => ((hsub hc i).1.trans (hsub hc i).2).le), hlo, ?_⟩
  exact fun x hx => ⟨fun i => (hrelax hx i).1.le, fun i => (hrelax hx i).2.le⟩

variable {E : Type*} [Fintype E]

theorem Network.exists_global_positive_of_compact_affine_face_certificate
    (N : Network d E) {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} (hK : IsCompact (A.plateau M))
    (hpos : A.plateau M ⊆ {x | Positive x})
    (hfaces : N.AffineFaceCertificate A ℓ u M) {z : State d} (hz : z ∈ A.plateau M) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧ ∀ t, 0 ≤ t → x t ∈ A.plateau M := by
  obtain ⟨ε, lo, hi, hε, hbox, hlo, hsub⟩ :=
    A.exists_enlarged_positive_box ⟨z, hz⟩ hK hpos
  exact N.exists_global_positive_of_affine_face_certificate hk A hε lo hi hbox hlo
    hsub hfaces hz

theorem Network.positiveWellPosed_of_compact_affine_face_certificate
    (N : Network d E) {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} (hK : IsCompact (A.plateau M))
    (hpos : A.plateau M ⊆ {x | Positive x})
    (hfaces : N.AffineFaceCertificate A ℓ u M) {z : State d} (hz : z ∈ A.plateau M) :
    N.PositiveWellPosed k z := by
  obtain ⟨x, hx, _⟩ := N.exists_global_positive_of_compact_affine_face_certificate hk A
    hK hpos hfaces hz
  exact N.positiveWellPosed_of_exists hk ⟨x, hx⟩

end Endotactic
end

-- Source: Endotactic/RelativeAffineRobustness.lean
section
/-!
# Robust relaxation within a closed convex set

Only the intersection of the original plateau with the closed convex set needs
to be compact. Radial clipping preserves both the relaxed affine inequalities
and membership of that convex set. For stoichiometric affine classes this
avoids bounding the entire ambient plateau.
-/

namespace Endotactic

open Set

variable {d m : ℕ} [Nonempty (Fin m)]

theorem AffineFamily.exists_relaxed_plateau_inter_subset_open (A : AffineFamily d m)
    {M : ℝ} {C : Set (State d)} (hC : IsClosed C) (hconv : Convex ℝ C)
    (hne : (A.plateau M ∩ C).Nonempty) (hK : IsCompact (A.plateau M ∩ C))
    {U : Set (State d)} (hU : IsOpen U) (hsub : A.plateau M ∩ C ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ A.plateau (M - ε) ∩ C ⊆ U := by
  obtain ⟨c, hc, hcC⟩ := hne
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (continuous_id.dist continuous_const).continuousOn
  let R : ℝ := max B 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hball : A.plateau M ∩ C ⊆ Metric.ball c R := by
    intro y hy
    rw [Metric.mem_ball]
    have hb := hB y hy
    rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] at hb
    exact hb.trans_lt (by dsimp [R]; linarith [le_max_left B 0])
  let bad : Set (State d) :=
    ((Metric.closedBall c R ∩ Uᶜ) ∪ Metric.sphere c R) ∩ C
  have hbad : IsCompact bad :=
    (((isCompact_closedBall c R).inter_right hU.isClosed_compl).union
      (isCompact_sphere c R)).inter_right hC
  have hdis : Disjoint bad (A.plateau M) := by
    apply Set.disjoint_left.mpr
    intro y hy hp
    rcases hy with ⟨hy | hy, hyC⟩
    · exact hy.2 (hsub ⟨hp, hyC⟩)
    · have heq := Metric.mem_sphere.mp hy
      have hlt := Metric.mem_ball.mp (hball ⟨hp, hyC⟩)
      linarith
  obtain ⟨ε, hε, hgap⟩ := A.compact_disjoint_plateau_gap hbad hdis
  refine ⟨ε, hε, ?_⟩
  rintro x ⟨hx, hxC⟩
  by_contra hn
  by_cases hnear : dist x c < R
  · exact Set.disjoint_left.mp hgap
      ⟨Or.inl ⟨Metric.mem_closedBall.mpr hnear.le, hn⟩, hxC⟩ hx
  · have hd : 0 < dist x c := hR.trans_le (le_of_not_gt hnear)
    let s : ℝ := R / dist x c
    have hs : 0 ≤ s := le_of_lt (div_pos hR hd)
    have hs₁ : s ≤ 1 := (div_le_one hd).mpr (le_of_not_gt hnear)
    let y : State d := (1 - s) • c + s • x
    have hc' : c ∈ A.plateau (M - ε) :=
      fun i => (sub_le_self M hε.le).trans (hc i)
    have hy : y ∈ A.plateau (M - ε) :=
      A.plateau_convex (M - ε) hc' hx (sub_nonneg.mpr hs₁) hs (by ring)
    have hyC : y ∈ C := hconv hcC hxC (sub_nonneg.mpr hs₁) hs (by ring)
    have heq : y - c = s • (x - c) := by
      ext i
      simp only [y, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hdist : dist y c = R := by
      rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs,
        ← dist_eq_norm]
      exact div_mul_cancel₀ R (ne_of_gt hd)
    exact Set.disjoint_left.mp hgap
      ⟨Or.inr (Metric.mem_sphere.mpr hdist), hyC⟩ hy

theorem AffineFamily.exists_enlarged_positive_box_inter (A : AffineFamily d m)
    {M : ℝ} {C : Set (State d)} (hC : IsClosed C) (hconv : Convex ℝ C)
    (hne : (A.plateau M ∩ C).Nonempty) (hK : IsCompact (A.plateau M ∩ C))
    (hpos : A.plateau M ∩ C ⊆ {x | Positive x}) :
    ∃ (ε : ℝ) (lo hi : State d), 0 < ε ∧ lo ≤ hi ∧ Positive lo ∧
      A.plateau (M - ε) ∩ C ⊆ Icc lo hi := by
  have hmin := fun i : Fin d => hK.exists_isMinOn hne
    (continuous_apply i).continuousOn
  have hmax := fun i : Fin d => hK.exists_isMaxOn hne
    (continuous_apply i).continuousOn
  choose a ha hamin using hmin
  choose b hb hbmax using hmax
  let lo : State d := fun i => a i i / 2
  let hi : State d := fun i => b i i + 1
  have hlo : Positive lo := fun i => half_pos (hpos (ha i) i)
  let U : Set (State d) := {x | ∀ i, lo i < x i ∧ x i < hi i}
  have hU : IsOpen U := by
    have heq : U = ⋂ i, {x | lo i < x i ∧ x i < hi i} := by
      ext x; simp [U]
    rw [heq]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (continuous_apply i)).inter
        (isOpen_lt (continuous_apply i) continuous_const)
  have hsub : A.plateau M ∩ C ⊆ U := by
    intro x hx i
    constructor
    · have hsmall : lo i < a i i := by dsimp [lo]; linarith [hpos (ha i) i]
      exact hsmall.trans_le (hamin i hx)
    · have hlarge : b i i < hi i := by dsimp [hi]; linarith
      exact (hbmax i hx).trans_lt hlarge
  obtain ⟨ε, hε, hrelax⟩ :=
    A.exists_relaxed_plateau_inter_subset_open hC hconv hne hK hU hsub
  obtain ⟨c, hc⟩ := hne
  refine ⟨ε, lo, hi, hε, (fun i => ((hsub hc i).1.trans (hsub hc i).2).le), hlo, ?_⟩
  exact fun x hx => ⟨fun i => (hrelax hx i).1.le, fun i => (hrelax hx i).2.le⟩

end Endotactic
end

-- Source: Endotactic/ClassInvariance.lean
section
/-!
# Stoichiometric classes are preserved even before removing the cutoff

Clamping the state need not preserve its class, but the mass-action velocity
always belongs to the reaction span. Applying the quotient map to the cutoff
integral equation therefore preserves the affine class. No state projection,
orthogonal norm, or individual reaction-term integrability is needed.
-/

namespace Endotactic

open Set MeasureTheory

variable {d : ℕ} {E : Type*}

def Network.stoichiometricClass (N : Network d E) (c : State d) : Set (State d) :=
  {y | y - c ∈ N.stoichiometricSubspace}

theorem Network.stoichiometricClass_isClosed (N : Network d E) (c : State d) :
    IsClosed (N.stoichiometricClass c) :=
  N.stoichiometricSubspace.closed_of_finiteDimensional.preimage
    (continuous_id.sub continuous_const)

theorem Network.stoichiometricClass_convex (N : Network d E) (c : State d) :
    Convex ℝ (N.stoichiometricClass c) := by
  intro x hx y hy a b _ _ hab
  change (a • x + b • y) - c ∈ N.stoichiometricSubspace
  have heq : (a • x + b • y) - c = a • (x - c) + b • (y - c) := by
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun z : ℝ => z * c i) hab]
  rw [heq]
  exact N.stoichiometricSubspace.add_mem
    (N.stoichiometricSubspace.smul_mem a hx) (N.stoichiometricSubspace.smul_mem b hy)

theorem Network.positiveClass_eq (N : Network d E) (c : State d) :
    N.positiveClass c = {x | Positive x} ∩ N.stoichiometricClass c := rfl

variable [Fintype E]

theorem Network.cutoffRhs_mem_stoichiometricSubspace (N : Network d E)
    (k : E → ℝ → ℝ) (lo hi : State d) (t : ℝ) (y : State d) :
    N.cutoffRhs k lo hi t y ∈ N.stoichiometricSubspace :=
  rhs_mem_stoichiometricSubspace N _ _

theorem GlobalIntegralSolution.sub_initial_mem {F : ℝ → State d → State d}
    {z : State d} {x : ℝ → State d} (hx : GlobalIntegralSolution F z x)
    (S : Submodule ℝ (State d)) (hF : ∀ t, 0 ≤ t → ∀ y, F t y ∈ S)
    {t : ℝ} (ht : 0 ≤ t) : x t - z ∈ S := by
  rw [hx.2.2.2 t ht, add_sub_cancel_left]
  exact intervalIntegral_mem_subspace S (hx.2.2.1 t ht) (by
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact hF s hs.1 (x s))

omit [Fintype E] in
theorem GlobalIntegralSolution.mem_stoichiometricClass
    {F : ℝ → State d → State d} {z c : State d} {x : ℝ → State d}
    (hx : GlobalIntegralSolution F z x) (N : Network d E)
    (hF : ∀ t, 0 ≤ t → ∀ y, F t y ∈ N.stoichiometricSubspace)
    (hz : z ∈ N.stoichiometricClass c) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ N.stoichiometricClass c := by
  have hh := N.stoichiometricSubspace.add_mem (hx.sub_initial_mem _ hF ht) hz
  change x t - c ∈ N.stoichiometricSubspace
  simpa only [sub_add_sub_cancel] using hh

variable {m : ℕ} [Nonempty (Fin m)]

theorem Network.exists_global_positive_in_class_affine_strip (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M ε : ℝ} (hε : 0 < ε)
    (c lo hi : State d) (hbox : lo ≤ hi) (hlo : Positive lo)
    (hsub : A.plateau (M - ε) ∩ N.stoichiometricClass c ⊆ Icc lo hi)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c)
    (hflux : ∀ t, 0 ≤ t → ∀ y ∈ N.stoichiometricClass c,
      M - ε < A.minimum y → A.minimum y < M → ∀ i, A.Active i y →
        0 ≤ dot (A.slope i) (N.rhs (fun e => k e t) y)) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ A.plateau M ∩ N.stoichiometricClass c := by
  obtain ⟨x, _, hx⟩ := N.exists_global_cutoff_integralSolution hk lo hi hbox z
  have hclass : ∀ t, 0 ≤ t → x t ∈ N.stoichiometricClass c :=
    fun t ht => hx.mem_stoichiometricClass N
      (fun s _ y => N.cutoffRhs_mem_stoichiometricSubspace k lo hi s y) hz.2 ht
  have hstay := hx.mem_affine_plateau_of_strip A hε hz.1 (by
    intro t ht hl hu i ha
    have hy : x t ∈ Icc lo hi := hsub
      ⟨(A.mem_plateau_iff_minimum_ge (x t) (M - ε)).mpr hl.le, hclass t ht⟩
    rw [N.cutoffRhs_eq k lo hi ht hy]
    exact hflux t ht (x t) (hclass t ht) hl hu i ha)
  have hxbox : ∀ t, 0 ≤ t → x t ∈ Icc lo hi := by
    intro t ht
    exact hsub ⟨fun i => (sub_le_self M hε.le).trans (hstay t ht i), hclass t ht⟩
  have hactual : N.IsIntegralSolution k z x := hx.congr_field
    (fun t ht => N.cutoffRhs_eq k lo hi ht (hxbox t ht))
  exact ⟨x, ⟨hactual, fun t ht i => (hlo i).trans_le ((hxbox t ht).1 i)⟩,
    fun t ht => ⟨hstay t ht, hclass t ht⟩⟩

end Endotactic
end

-- Source: Endotactic/ClassFaceTrap.lean
section
/-!
# Class-restricted affine face certificates imply global well-posedness

Strict inward flux is required only on the faces within one stoichiometric
class. Compact separation is likewise performed within that closed class.
The original plateau need only be compact and positive after intersection
with the class. The cutoff trajectory preserves the class before trapping,
so a relative positive box suffices to remove the cutoff.

Construction of these class traps for arbitrary endotactic networks is still
an independent geometric obligation. Nonconserved, merely nonstrict faces
are not covered by the conserved-or-strict certificate here.
-/

namespace Endotactic

open Set

variable {d m : ℕ} {E : Type*} [Fintype E]

def Network.ClassAffineFaceCertificate (N : Network d E) (A : AffineFamily d m)
    (ℓ u M : ℝ) (c : State d) : Prop :=
  ∀ i, (∀ a y, dot (A.slope i) (N.rhs a y) = 0) ∨
    ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ A.plateau M ∩ N.stoichiometricClass c,
        A.value i y = M → 0 < dot (A.slope i) (N.rhs a y)

theorem Network.classAffineFaceCertificate_of_projections (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} (c : State d)
    (hfaces : ∀ i, (∀ e, N.projection (A.slope i) e = 0) ∨
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
        ∀ y ∈ A.plateau M ∩ N.stoichiometricClass c,
          A.value i y = M → 0 < dot (A.slope i) (N.rhs a y)) :
    N.ClassAffineFaceCertificate A ℓ u M c := by
  intro i
  rcases hfaces i with hzero | hstrict
  · exact Or.inl (fun a y => N.dot_rhs_eq_zero_of_projections (A.slope i) hzero a y)
  · exact Or.inr hstrict

theorem Network.classAffineFaceCertificate_of_global (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} (c : State d)
    (hfaces : N.AffineFaceCertificate A ℓ u M) :
    N.ClassAffineFaceCertificate A ℓ u M c := by
  intro i
  rcases hfaces i with hzero | hstrict
  · exact Or.inl hzero
  · exact Or.inr (fun a ha y hy => hstrict a ha y hy.1)

theorem Network.class_affine_branch_strip_of_face (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} (c : State d) (i : Fin m)
    {B : Set (State d)} (hB : IsCompact B)
    (hface : (∀ a y, dot (A.slope i) (N.rhs a y) = 0) ∨
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
        ∀ y ∈ A.plateau M ∩ N.stoichiometricClass c,
          A.value i y = M → 0 < dot (A.slope i) (N.rhs a y)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ B ∩ N.stoichiometricClass c, A.Active i y →
        M - ε < A.value i y → A.value i y < M →
          0 ≤ dot (A.slope i) (N.rhs a y) := by
  rcases hface with hzero | hstrict
  · refine ⟨1, zero_lt_one, ?_⟩
    intro a _ y _ _ _ _
    rw [hzero]
  · let bad : Set ((E → ℝ) × State d) :=
      (Icc (fun _ : E => ℓ) (fun _ => u) ×ˢ (B ∩ N.stoichiometricClass c)) ∩
        {p | A.Active i p.2 ∧ dot (A.slope i) (N.rhs p.1 p.2) ≤ 0}
    have hactive : IsClosed {p : (E → ℝ) × State d | A.Active i p.2} := by
      have heq : {p : (E → ℝ) × State d | A.Active i p.2} =
          ⋂ j, {p | A.value i p.2 ≤ A.value j p.2} := by
        ext p; simp [AffineFamily.Active]
      rw [heq]
      exact isClosed_iInter fun j => isClosed_le
        ((A.continuous_value i).comp continuous_snd)
        ((A.continuous_value j).comp continuous_snd)
    have hflux : IsClosed {p : (E → ℝ) × State d |
        dot (A.slope i) (N.rhs p.1 p.2) ≤ 0} :=
      isClosed_le ((dotCLM (A.slope i)).continuous.comp N.rhs_joint_contDiff.continuous)
        continuous_const
    have hbad : IsCompact bad :=
      (isCompact_Icc.prod (hB.inter_right (N.stoichiometricClass_isClosed c))).inter_right
        (hactive.inter hflux)
    let S : Set ℝ := (fun p : (E → ℝ) × State d => A.value i p.2) '' bad
    have hS : IsCompact S := hbad.image ((A.continuous_value i).comp continuous_snd)
    have hM : M ∈ Sᶜ := by
      intro hm
      obtain ⟨⟨a, y⟩, hp, heq⟩ := hm
      rcases hp with ⟨⟨ha, _, hyC⟩, hai, hf⟩
      have hy : y ∈ A.plateau M := fun j => heq ▸ hai j
      exact (not_lt_of_ge hf) (hstrict a ha y ⟨hy, hyC⟩ heq)
    obtain ⟨ε, hε, hsep⟩ := Metric.isOpen_iff.mp hS.isClosed.isOpen_compl M hM
    refine ⟨ε, hε, ?_⟩
    intro a ha y hy hai hl hu
    by_contra hn
    have hball : A.value i y ∈ Metric.ball M ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    exact (hsep hball) ⟨(a, y), ⟨⟨ha, hy⟩, hai, (lt_of_not_ge hn).le⟩, rfl⟩

variable [Nonempty (Fin m)]

theorem Network.class_affine_strip_of_face_certificate (N : Network d E)
    (A : AffineFamily d m) {ℓ u M : ℝ} (c : State d) {B : Set (State d)}
    (hB : IsCompact B) (hfaces : N.ClassAffineFaceCertificate A ℓ u M c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
      ∀ y ∈ B ∩ N.stoichiometricClass c,
        M - ε < A.minimum y → A.minimum y < M → ∀ i, A.Active i y →
          0 ≤ dot (A.slope i) (N.rhs a y) := by
  have hb := fun i => N.class_affine_branch_strip_of_face A c i hB (hfaces i)
  choose ε hε hs using hb
  let δ := finiteMinimum ε
  have hδ : 0 < δ := by
    obtain ⟨i, hi⟩ := finiteMinimum_attained ε
    change 0 < finiteMinimum ε
    rw [hi]
    exact hε i
  refine ⟨δ, hδ, ?_⟩
  intro a ha y hy hl hu i hai
  have heq := (A.active_iff_minimum_eq i y).mp hai
  have hle : δ ≤ ε i := finiteMinimum_le ε i
  apply hs i a ha y hy hai
  · linarith
  · linarith

theorem Network.exists_global_positive_of_class_affine_face_certificate
    (N : Network d E) {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} (c : State d)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {x | Positive x})
    (hfaces : N.ClassAffineFaceCertificate A ℓ u M c)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ A.plateau M ∩ N.stoichiometricClass c := by
  obtain ⟨ε₀, lo, hi, hε₀, hbox, hlo, hsub⟩ :=
    A.exists_enlarged_positive_box_inter (N.stoichiometricClass_isClosed c)
      (N.stoichiometricClass_convex c) ⟨z, hz⟩ hK hpos
  obtain ⟨δ, hδ, hs⟩ := N.class_affine_strip_of_face_certificate A c
    (B := Icc lo hi) isCompact_Icc hfaces
  let ε := min ε₀ δ
  have hε : 0 < ε := lt_min hε₀ hδ
  have he₀ : ε ≤ ε₀ := min_le_left _ _
  have heδ : ε ≤ δ := min_le_right _ _
  have hsub' : A.plateau (M - ε) ∩ N.stoichiometricClass c ⊆ Icc lo hi := by
    rintro y ⟨hy, hyC⟩
    exact hsub ⟨fun i => (by linarith : M - ε₀ ≤ M - ε).trans (hy i), hyC⟩
  apply N.exists_global_positive_in_class_affine_strip hk A hε c lo hi hbox hlo hsub' hz
  intro t ht y hyC hl hu i hai
  have hy : y ∈ Icc lo hi := hsub'
    ⟨(A.mem_plateau_iff_minimum_ge y (M - ε)).mpr hl.le, hyC⟩
  exact hs _ ⟨fun e => (hk.2 e t ht).1, fun e => (hk.2 e t ht).2⟩ y ⟨hy, hyC⟩
    (by linarith) hu i hai

theorem Network.positiveWellPosed_of_class_affine_face_certificate
    (N : Network d E) {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} (c : State d)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {x | Positive x})
    (hfaces : N.ClassAffineFaceCertificate A ℓ u M c)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    N.PositiveWellPosed k z := by
  obtain ⟨x, hx, _⟩ := N.exists_global_positive_of_class_affine_face_certificate hk A c
    hK hpos hfaces hz
  exact N.positiveWellPosed_of_exists hk ⟨x, hx⟩

end Endotactic
end

-- Source: Endotactic/CompactTrapPermanence.lean
section
/-!
# Pointwise exterior signs and compact initial traps imply permanence

Choose a slightly relaxed target once, using relative affine robustness to
preserve positivity and compactness in the stoichiometric class. Each initial
point may have its own compact invariant trap. Pointwise strict flux outside
the original target then supplies a common positive margin on each trap below
the relaxed level, without any numerical margin or global upper-cap hypothesis.

The final certificate theorem constructs actual positive global solutions
from class-restricted strict/conserved face certificates. General endotacticity
has not yet been shown to construct the target and these traps.
-/

namespace Endotactic

open Set

variable {d m : ℕ} [Nonempty (Fin m)] {E : Type*} [Fintype E]

theorem Network.integralSolution_mem_of_trapped_solution (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    {z : State d} {x : ℝ → State d} (hx : N.IsIntegralSolution k z x)
    {B : Set (State d)} (htrap : ∃ y, N.IsIntegralSolution k z y ∧
      ∀ t, 0 ≤ t → y t ∈ B) {t : ℝ} (ht : 0 ≤ t) : x t ∈ B := by
  obtain ⟨y, hy, hstay⟩ := htrap
  rw [hx.eqOn_nonnegative N hk hy ht]
  exact hstay t ht

theorem Network.uniformPermanent_of_compact_strict_exterior (N : Network d E)
    (A : AffineFamily d m) (ℓ u M : ℝ) (c : State d)
    (regular : (E → ℝ → ℝ) → Prop)
    (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (hwell : ∀ k, AdmissibleRates k ℓ u → regular k →
      ∀ z ∈ N.positiveClass c, N.PositiveWellPosed k z)
    (htraps : ∀ z ∈ N.positiveClass c, ∃ B : Set (State d), IsCompact B ∧
      (∀ k, AdmissibleRates k ℓ u → regular k →
        ∀ x, N.IsGlobalPositiveSolution k z x → ∀ t, 0 ≤ t → x t ∈ B) ∧
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
        ∀ y ∈ B, A.minimum y < M → ∀ i, A.Active i y →
          0 < dot (A.slope i) (N.rhs a y)) : N.UniformPermanent ℓ u c regular := by
  obtain ⟨ε, lo, hi, hε, _, hlo, hsub⟩ :=
    A.exists_enlarged_positive_box_inter (N.stoichiometricClass_isClosed c)
      (N.stoichiometricClass_convex c) hne hK hpos
  let Q : ℝ := M - ε
  let K : Set (State d) := A.plateau Q ∩ N.stoichiometricClass c
  have hQ : Q < M := sub_lt_self M hε
  have hne' : K.Nonempty := by
    obtain ⟨y, hy, hyC⟩ := hne
    exact ⟨y, (fun i => (sub_le_self M hε.le).trans (hy i)), hyC⟩
  have hcompact : IsCompact K := isCompact_Icc.of_isClosed_subset
    ((A.plateau_isClosed Q).inter (N.stoichiometricClass_isClosed c)) hsub
  have hclass : K ⊆ N.positiveClass c := by
    intro y hy
    exact ⟨fun i => (hlo i).trans_le ((hsub hy).1 i), hy.2⟩
  refine ⟨K, hne', hcompact, hclass, ?_⟩
  intro k hk hr
  refine ⟨hwell k hk hr, ?_⟩
  intro z hz x hx
  obtain ⟨B, hB, hstay, hstrict⟩ := htraps z hz
  obtain ⟨T, hT, hentry⟩ := A.eventuallyIn_plateau_of_compact_strict_exterior hk hx.1 hB
    (hstay k hk hr x hx) hQ hstrict
  exact ⟨T, hT, fun t ht => ⟨hentry t ht,
    (hx.mem_positiveClass hz (hT.trans ht)).2⟩⟩

theorem Network.uniformPermanent_of_compact_affine_traps {n : ℕ} [Nonempty (Fin n)]
    (N : Network d E) (A : AffineFamily d m) (ℓ u M : ℝ) (c : State d)
    (regular : (E → ℝ → ℝ) → Prop)
    (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty)
    (hK : IsCompact (A.plateau M ∩ N.stoichiometricClass c))
    (hpos : A.plateau M ∩ N.stoichiometricClass c ⊆ {y | Positive y})
    (htraps : ∀ z ∈ N.positiveClass c,
      ∃ (B : AffineFamily d n) (L : ℝ),
        z ∈ B.plateau L ∩ N.stoichiometricClass c ∧
        IsCompact (B.plateau L ∩ N.stoichiometricClass c) ∧
        (B.plateau L ∩ N.stoichiometricClass c ⊆ {y | Positive y}) ∧
        N.ClassAffineFaceCertificate B ℓ u L c ∧
        ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
          ∀ y ∈ B.plateau L ∩ N.stoichiometricClass c,
            A.minimum y < M → ∀ i, A.Active i y →
              0 < dot (A.slope i) (N.rhs a y)) : N.UniformPermanent ℓ u c regular := by
  apply N.uniformPermanent_of_compact_strict_exterior A ℓ u M c regular hne hK hpos
  · intro k hk _ z hz
    obtain ⟨B, L, hzB, hB, hBp, hfaces, _⟩ := htraps z hz
    exact N.positiveWellPosed_of_class_affine_face_certificate hk B c hB hBp hfaces hzB
  · intro z hz
    obtain ⟨B, L, hzB, hB, hBp, hfaces, hstrict⟩ := htraps z hz
    refine ⟨B.plateau L ∩ N.stoichiometricClass c, hB, ?_, hstrict⟩
    intro k hk _ x hx t ht
    obtain ⟨y, hy, hstay⟩ := N.exists_global_positive_of_class_affine_face_certificate hk
      B c hB hBp hfaces hzB
    exact N.integralSolution_mem_of_trapped_solution hk hx.1 ⟨y, hy.1, hstay⟩ ht

end Endotactic
end

-- Source: Endotactic/DirectionalDominance.lean
section
/-!
# Eventual positive flux along any fixed nonconserved exponent ray

The threshold is uniform over all coefficients in the box, but depends on the
direction. Uniform control over ALL active plateau directions remains the hard
geometric step of the general theorem.
-/

namespace Endotactic

open Filter Topology

theorem fixed_direction_eventual_positive_flux {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (r : State d) (hnonzero : ∃ e : E, N.projection r e ≠ 0)
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hlu : ℓ ≤ u) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
        0 < dot r (N.rhs k (exponentialPoint h r)) := by
  obtain ⟨a, ha⟩ := exists_essentialMinimum N hnonzero
  obtain ⟨H, hH, hgap⟩ := exists_positive_negative_source_gap N hN ha
  have hpositive : 0 < ℓ * N.projection r a :=
    mul_pos hℓ (essentialMinimum_projection_pos N hN ha)
  have hlimit : Tendsto (fun h : ℝ => u * h ^ H * negativeMass (N.projection r))
      (𝓝 0) (𝓝 0) := by
    have hr : Tendsto (fun h : ℝ => h ^ H) (𝓝 0) (𝓝 0) := by
      simpa only [Real.zero_rpow hH.ne'] using
        (Real.continuousAt_rpow_const 0 H (.inr hH.le)).tendsto
    simpa only [mul_zero, zero_mul] using
      (hr.const_mul u).mul_const (negativeMass (N.projection r))
  have hevent : ∀ᶠ h : ℝ in 𝓝 0,
      u * h ^ H * negativeMass (N.projection r) < ℓ * N.projection r a :=
    hlimit.eventually (eventually_lt_nhds hpositive)
  obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨min ε 1, lt_min hε (by norm_num), ?_⟩
  intro h hh hh₀ k hk
  have hhε : h < ε := lt_of_lt_of_le hh₀ (min_le_left _ _)
  have hh1 : h ≤ 1 := (lt_of_lt_of_le hh₀ (min_le_right _ _)).le
  apply exponentialPoint_flux_pos N hN r r k a ℓ u h H hℓ
    (hℓ.le.trans hlu) hh hh1 hk ha
  · simpa only [Network.sourceLevel] using hgap
  · exact hsmall (by simpa [Real.dist_eq, abs_of_pos hh] using hhε)

end Endotactic
end

-- Source: Endotactic/UniformDirectionalCertificate.lean
section
/-!
# Uniform flux from moving-direction certificates

A certificate records the gap in exponent space and bounds negative projected
mass relative to one positive pivot. No lower bound on the magnitude of the
direction is needed. The existence of uniformly bounded certificates over all
active directions is a separate geometric obligation.
-/

namespace Endotactic

open Filter Topology

theorem negativeMass_nonneg {E : Type*} [Fintype E] (p : E → ℝ) :
    0 ≤ negativeMass p :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem projection_smul_direction {d : ℕ} {E : Type*} (N : Network d E)
    (s : ℝ) (r : State d) (e : E) :
    N.projection (s • r) e = s * N.projection r e := by
  simp only [Network.projection, dot, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [Finset.mul_sum]

theorem negativeMass_smul {E : Type*} [Fintype E] (p : E → ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    negativeMass (fun e => s * p e) = s * negativeMass p := by
  unfold negativeMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hp : 0 ≤ p e
  · simp [max_eq_right (neg_nonpos.mpr hp),
      max_eq_right (neg_nonpos.mpr (mul_nonneg hs hp))]
  · have hp' : p e ≤ 0 := (lt_of_not_ge hp).le
    rw [max_eq_left (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hs hp')),
      max_eq_left (neg_nonneg.mpr hp')]
    ring

/-- Finite data sufficient for an inward flux; it need not certify an essential
minimum, nor assume endotacticity when the data have already been verified. -/
structure Network.DirectionalCertificate {d : ℕ} {E : Type*} [Fintype E]
    (N : Network d E) (r p : State d) (H B : ℝ) where
  pivot : E
  positive : 0 < N.projection r pivot
  relative_mass : negativeMass (N.projection r) ≤ B * N.projection r pivot
  gap : ∀ e, N.projection r e < 0 →
    H ≤ N.sourceLevel p e - N.sourceLevel p pivot

def Network.DirectionalCertificate.weaken {d : ℕ} {E : Type*} [Fintype E]
    {N : Network d E} {r p : State d} {H B H' B' : ℝ}
    (C : N.DirectionalCertificate r p H B) (hH : H' ≤ H) (hB : B ≤ B') :
    N.DirectionalCertificate r p H' B' where
  pivot := C.pivot
  positive := C.positive
  relative_mass := C.relative_mass.trans
    (mul_le_mul_of_nonneg_right hB C.positive.le)
  gap e he := hH.trans (C.gap e he)

def Network.DirectionalCertificate.smul_direction {d : ℕ} {E : Type*}
    [Fintype E] {N : Network d E} {r p : State d} {H B s : ℝ}
    (C : N.DirectionalCertificate r p H B) (hs : 0 < s) :
    N.DirectionalCertificate (s • r) p H B := by
  refine ⟨C.pivot, ?_, ?_, ?_⟩
  · rw [projection_smul_direction]
    exact mul_pos hs C.positive
  · have heq : N.projection (s • r) = fun e => s * N.projection r e :=
      funext (projection_smul_direction N s r)
    rw [heq, negativeMass_smul _ hs.le]
    have h := mul_le_mul_of_nonneg_left C.relative_mass hs.le
    nlinarith only [h]
  · intro e he
    rw [projection_smul_direction] at he
    exact C.gap e (by nlinarith only [he, hs])

theorem exponentialPoint_flux_pos_of_directionalCertificate {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (r p : State d)
    (k : E → ℝ) {ℓ u h H B : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    (hh : 0 < h) (hh1 : h ≤ 1) (hk : ∀ e, ℓ ≤ k e ∧ k e ≤ u)
    (C : N.DirectionalCertificate r p H B) (hsmall : u * h ^ H * B < ℓ) :
    0 < dot r (N.rhs k (exponentialPoint h p)) := by
  rw [dot_rhs]
  apply weighted_sum_pos (N.projection r)
    (fun e => monomial (exponentialPoint h p) (N.source e)) k C.pivot ℓ u (h ^ H)
    hu (fun e => (monomial_pos (exponentialPoint_positive hh p) _).le) hk
    (fun e => hℓ.le.trans (hk e).1) C.positive.le
    (monomial_pos (exponentialPoint_positive hh p) _)
  · intro e he
    exact monomial_domination_of_exponent_gap hh hh1 p _ _ (C.gap e he)
  · calc
      u * h ^ H * negativeMass (N.projection r) ≤
          u * h ^ H * (B * N.projection r C.pivot) :=
        mul_le_mul_of_nonneg_left C.relative_mass
          (mul_nonneg hu (Real.rpow_nonneg hh.le _))
      _ = (u * h ^ H * B) * N.projection r C.pivot := by ring
      _ < ℓ * N.projection r C.pivot :=
        mul_lt_mul_of_pos_right hsmall C.positive

/-- One threshold for every direction, exponent point, and coefficient vector
with the specified common geometric bounds. -/
theorem exists_uniform_directional_flux_threshold {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) {ℓ u H B : ℝ}
    (hℓ : 0 < ℓ) (hu : 0 ≤ u) (hH : 0 < H) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ r p : State d, N.DirectionalCertificate r p H B →
        ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
          0 < dot r (N.rhs k (exponentialPoint h p)) := by
  have hlimit : Tendsto (fun h : ℝ => u * h ^ H * B) (𝓝 0) (𝓝 0) := by
    have hr : Tendsto (fun h : ℝ => h ^ H) (𝓝 0) (𝓝 0) := by
      simpa only [Real.zero_rpow hH.ne'] using
        (Real.continuousAt_rpow_const 0 H (.inr hH.le)).tendsto
    simpa only [mul_zero, zero_mul] using (hr.const_mul u).mul_const B
  obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp
    (hlimit.eventually (eventually_lt_nhds hℓ))
  refine ⟨min ε 1, lt_min hε (by norm_num), min_le_right _ _, ?_⟩
  intro h hh hh₀ r p C k hk
  have hhε : h < ε := hh₀.trans_le (min_le_left _ _)
  exact exponentialPoint_flux_pos_of_directionalCertificate N r p k hℓ hu hh
    (hh₀.le.trans (min_le_right _ _)) hk C
    (hsmall (by simpa [Real.dist_eq, abs_of_pos hh] using hhε))

/-- Endotacticity supplies a certificate in each fixed direction, but its
parameters are not asserted to be uniform as the direction changes. -/
theorem exists_fixed_directionalCertificate {d : ℕ} {E : Type*}
    [Fintype E] (N : Network d E) (hN : N.IsEndotactic) (r : State d)
    (hnonzero : ∃ e : E, N.projection r e ≠ 0) :
    ∃ H B : ℝ, 0 < H ∧ 0 ≤ B ∧ Nonempty (N.DirectionalCertificate r r H B) := by
  obtain ⟨a, ha⟩ := exists_essentialMinimum N hnonzero
  obtain ⟨H, hH, hgap⟩ := exists_positive_negative_source_gap N hN ha
  have hpos := essentialMinimum_projection_pos N hN ha
  refine ⟨H, negativeMass (N.projection r) / N.projection r a, hH,
    div_nonneg (negativeMass_nonneg _) hpos.le, ⟨⟨a, hpos, ?_, hgap⟩⟩⟩
  rw [div_mul_cancel₀ _ hpos.ne']

end Endotactic
end

-- Source: Endotactic/GeometryMargins.lean
section
/-! # Transfer of strict source gaps from an active slope to exponent space -/

namespace Endotactic

def l1 {d : ℕ} (v : State d) : ℝ := ∑ i, |v i|

theorem dot_error_le {d : ℕ} (p r v : State d) {ε : ℝ}
    (hclose : ∀ i, |p i - r i| ≤ ε) :
    |dot p v - dot r v| ≤ ε * l1 v := by
  have heq : dot p v - dot r v = ∑ i, (p i - r i) * v i := by
    simp [dot, sub_mul, Finset.sum_sub_distrib]
  rw [heq]
  calc
    |∑ i, (p i - r i) * v i| ≤ ∑ i, |(p i - r i) * v i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ε * |v i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hclose i) (abs_nonneg _)
    _ = ε * l1 v := by rw [← Finset.mul_sum]; rfl

theorem dot_gap_transfer {d : ℕ} (p r v : State d) {ε H : ℝ}
    (hclose : ∀ i, |p i - r i| ≤ ε)
    (herror : ε * l1 v ≤ dot r v / 2)
    (hH : H ≤ dot r v / 2) : H ≤ dot p v := by
  have h := dot_error_le p r v hclose
  have := (abs_le.mp h).1
  linarith

theorem source_gap_transfer {d : ℕ} {E : Type*} (N : Network d E)
    (p r : State d) (a e : E) {ε H : ℝ}
    (hclose : ∀ i, |p i - r i| ≤ ε)
    (herror : ε * l1 (realComplex (N.source e) - realComplex (N.source a)) ≤
      (N.sourceLevel r e - N.sourceLevel r a) / 2)
    (hH : H ≤ (N.sourceLevel r e - N.sourceLevel r a) / 2) :
    H ≤ N.sourceLevel p e - N.sourceLevel p a := by
  have h := dot_gap_transfer p r
    (realComplex (N.source e) - realComplex (N.source a)) hclose
    (by simpa [dot_sub, Network.sourceLevel] using herror)
    (by simpa [dot_sub, Network.sourceLevel] using hH)
  simpa [dot_sub, Network.sourceLevel] using h

end Endotactic
end

-- Source: Endotactic/FiniteDirectionalCover.lean
section
/-!
# A finite certificate cover, rather than finite sampling

The cover hypothesis quantifies over every pair of directions and exponent
points in the region. Its existence is not inferred from pointwise dominance or
compactness alone. Positive scaling of directions does not change its bounds.
-/

namespace Endotactic

def Network.DirectionalCertificate.transfer_exponent {d : ℕ} {E : Type*}
    [Fintype E] {N : Network d E} {r p : State d} {H B ε : ℝ}
    (C : N.DirectionalCertificate r r H B)
    (hclose : ∀ i, |p i - r i| ≤ ε)
    (herror : ∀ e, N.projection r e < 0 →
      ε * l1 (realComplex (N.source e) - realComplex (N.source C.pivot)) ≤ H / 2) :
    N.DirectionalCertificate r p (H / 2) B where
  pivot := C.pivot
  positive := C.positive
  relative_mass := C.relative_mass
  gap e he := source_gap_transfer N p r C.pivot e hclose
    ((herror e he).trans (by linarith only [C.gap e he]))
    (by linarith only [C.gap e he])

/-- Arbitrarily many direction/exponent pairs are covered by finitely many
verified parameter bounds. Every pair must have a certificate in some chart. -/
theorem finite_directional_cover_eventual_flux {d : ℕ} {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I] [Nonempty I]
    (N : Network d E) (Q : Set (State d × State d)) (H B : I → ℝ)
    (hH : ∀ i, 0 < H i) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    (hcover : ∀ q ∈ Q, ∃ i, Nonempty (N.DirectionalCertificate q.1 q.2 (H i) (B i))) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ q ∈ Q, ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
        0 < dot q.1 (N.rhs k (exponentialPoint h q.2)) := by
  classical
  let hs := Finset.univ.image H
  let bs := Finset.univ.image B
  have hhs : hs.Nonempty := Finset.univ_nonempty.image H
  have hbs : bs.Nonempty := Finset.univ_nonempty.image B
  let H₀ := hs.min' hhs
  let B₀ := bs.max' hbs
  have hH₀ : 0 < H₀ := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hs.min'_mem hhs)
    change 0 < hs.min' hhs
    rw [← hi]
    exact hH i
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ :=
    exists_uniform_directional_flux_threshold N (B := B₀) hℓ hu hH₀
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall q hq k hk
  obtain ⟨i, ⟨C⟩⟩ := hcover q hq
  apply hflux h hh hsmall q.1 q.2
    (C.weaken (hs.min'_le _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      (bs.le_max' _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))) k hk

/-- Certificates may cover rays of arbitrary positive magnitude without a new
threshold or a positive lower bound on the norm of each direction. -/
theorem finite_directional_cover_scaled_eventual_flux {d : ℕ} {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I] [Nonempty I]
    (N : Network d E) (Q : Set (State d × State d)) (H B : I → ℝ)
    (hH : ∀ i, 0 < H i) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    (hcover : ∀ q ∈ Q, ∃ i, Nonempty (N.DirectionalCertificate q.1 q.2 (H i) (B i))) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ q ∈ Q, ∀ s : ℝ, 0 < s →
        ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
          0 < dot (s • q.1) (N.rhs k (exponentialPoint h q.2)) := by
  let R : Set (State d × State d) :=
    {v | ∃ q ∈ Q, ∃ s : ℝ, 0 < s ∧ v = (s • q.1, q.2)}
  have hR : ∀ v ∈ R, ∃ i, Nonempty (N.DirectionalCertificate v.1 v.2 (H i) (B i)) := by
    rintro v ⟨q, hq, s, hs, rfl⟩
    obtain ⟨i, ⟨C⟩⟩ := hcover q hq
    exact ⟨i, ⟨C.smul_direction hs⟩⟩
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ :=
    finite_directional_cover_eventual_flux N R H B hH hℓ hu hR
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall q hq s hs k hk
  exact hflux h hh hsmall (s • q.1, q.2) ⟨q, hq, s, hs, rfl⟩ k hk

end Endotactic
end

-- Source: Endotactic/FiniteSlopeDominance.lean
section
/-!
# The bridge from finite active-slope approximation to uniform flux

Each nonconserved slope has a positive tolerance for perturbing the exponent
point. For any fixed finite set of slopes these tolerances give one common
scale threshold. Constructing an affine family with the required activity
approximation is still a separate, unproved geometric step.
-/

namespace Endotactic

theorem l1_nonneg {d : ℕ} (v : State d) : 0 ≤ l1 v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem exists_directional_exponent_tolerance {d : ℕ} {E : Type*}
    [Fintype E] {N : Network d E} {r : State d} {H B : ℝ}
    (C : N.DirectionalCertificate r r H B) (hH : 0 < H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : State d, (∀ i, |p i - r i| ≤ ε) →
      Nonempty (N.DirectionalCertificate r p (H / 2) B) := by
  classical
  let L := ∑ e : E, l1 (realComplex (N.source e) - realComplex (N.source C.pivot))
  have hL : 0 ≤ L := Finset.sum_nonneg fun _ _ => l1_nonneg _
  let ε := H / (2 * (L + 1))
  have hden : 0 < 2 * (L + 1) := by positivity
  have hε : 0 < ε := div_pos hH hden
  have heq : ε * (2 * (L + 1)) = H := div_mul_cancel₀ H hden.ne'
  have hsmall : ε * L ≤ H / 2 := by nlinarith only [heq, hε]
  refine ⟨ε, hε, ?_⟩
  intro p hclose
  refine ⟨C.transfer_exponent hclose ?_⟩
  intro e _
  have heL : l1 (realComplex (N.source e) - realComplex (N.source C.pivot)) ≤ L :=
    Finset.single_le_sum (fun f _ => l1_nonneg
      (realComplex (N.source f) - realComplex (N.source C.pivot))) (Finset.mem_univ e)
  exact (mul_le_mul_of_nonneg_left heL hε.le).trans hsmall

/-- These tolerances can be selected pointwise before an affine family is
constructed. No continuity in the slope, nor positive infimum, is claimed. -/
theorem exists_fixed_slope_tolerantCertificate {d : ℕ} {E : Type*}
    [Fintype E] (N : Network d E) (hN : N.IsEndotactic) (r : State d)
    (hnonzero : ∃ e : E, N.projection r e ≠ 0) :
    ∃ ε H B : ℝ, 0 < ε ∧ 0 < H ∧ 0 ≤ B ∧
      ∀ p : State d, (∀ i, |p i - r i| ≤ ε) →
        Nonempty (N.DirectionalCertificate r p H B) := by
  obtain ⟨H, B, hH, hB, ⟨C⟩⟩ := exists_fixed_directionalCertificate N hN r hnonzero
  obtain ⟨ε, hε, hC⟩ := exists_directional_exponent_tolerance C hH
  exact ⟨ε, H / 2, B, hε, by positivity, hB, hC⟩

/-- Fixed finite slopes, moving exponent points, and all coefficients share
one threshold once every relevant point stays within its slope's tolerance. -/
theorem finite_slopes_tolerant_eventual_flux {d : ℕ} {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I] [Nonempty I]
    (N : Network d E) (hN : N.IsEndotactic) (r : I → State d)
    (hnonzero : ∀ i, ∃ e : E, N.projection (r i) e ≠ 0)
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ ε : I → ℝ, (∀ i, 0 < ε i) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ i : I, ∀ p : State d, (∀ j, |p j - r i j| ≤ ε i) →
          ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
            0 < dot (r i) (N.rhs k (exponentialPoint h p)) := by
  classical
  choose ε H B hε hH hB hC using
    fun i => exists_fixed_slope_tolerantCertificate N hN (r i) (hnonzero i)
  let Q : Set (State d × State d) :=
    {q | ∃ i : I, q.1 = r i ∧ ∀ j, |q.2 j - r i j| ≤ ε i}
  have hcover : ∀ q ∈ Q, ∃ i, Nonempty (N.DirectionalCertificate q.1 q.2 (H i) (B i)) := by
    rintro q ⟨i, hi, hp⟩
    exact ⟨i, hi.symm ▸ hC i q.2 hp⟩
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ :=
    finite_directional_cover_eventual_flux N Q H B hH hℓ hu hcover
  refine ⟨ε, hε, h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall i p hp k hk
  exact hflux h hh hsmall (r i, p) ⟨i, rfl, hp⟩ k hk

end Endotactic
end

-- Source: Endotactic/ActivityFluxBridge.lean
section
/-!
# From the affine approximation target to all-active flux

The slope tolerance is chosen pointwise before the finite affine family.
Conserved slopes are allowed and excluded automatically on exterior class
branches. The final theorem assumes the affine approximation statement
explicitly. `AffineApproximationExistence` supplies the proved statement
downstream, so its flux-family APIs no longer require an affine oracle.
-/

namespace Endotactic

open Filter Topology

def Network.IsSlopeTolerance {d : ℕ} {E : Type*} [Fintype E]
    (N : Network d E) (ε : State d → ℝ) : Prop :=
  ∀ r : State d, 0 < ε r ∧
    ((∃ e : E, N.projection r e ≠ 0) → ∃ H B : ℝ, 0 < H ∧
      ∀ p : State d, (∀ j, |p j - r j| ≤ ε r) →
        Nonempty (N.DirectionalCertificate r p H B))

/-- A possibly discontinuous tolerance function is selected before the affine
family. Conserved directions receive an arbitrary positive tolerance. -/
theorem Network.exists_slopeTolerance {d : ℕ} {E : Type*} [Fintype E]
    (N : Network d E) (hN : N.IsEndotactic) :
    ∃ ε : State d → ℝ, N.IsSlopeTolerance ε := by
  classical
  have hex : ∀ r : State d, ∃ ε : ℝ, 0 < ε ∧
      ((∃ e : E, N.projection r e ≠ 0) → ∃ H B : ℝ, 0 < H ∧
        ∀ p : State d, (∀ j, |p j - r j| ≤ ε) →
          Nonempty (N.DirectionalCertificate r p H B)) := by
    intro r
    by_cases hr : ∃ e : E, N.projection r e ≠ 0
    · obtain ⟨ε, H, B, hε, hH, _, hC⟩ := exists_fixed_slope_tolerantCertificate N hN r hr
      exact ⟨ε, hε, fun _ => ⟨H, B, hH, hC⟩⟩
    · exact ⟨1, by norm_num, fun h => (hr h).elim⟩
  choose ε hε hC using hex
  exact ⟨ε, fun r => ⟨hε r, hC r⟩⟩

theorem Network.finite_slopes_flux_of_tolerance {d : ℕ} {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I] [Nonempty I]
    (N : Network d E) (r : I → State d) (ε : State d → ℝ)
    (hε : N.IsSlopeTolerance ε) (hnonzero : ∀ i, ∃ e, N.projection (r i) e ≠ 0)
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ i : I, ∀ p : State d, (∀ j, |p j - r i j| ≤ ε (r i)) →
        ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
          0 < dot (r i) (N.rhs k (exponentialPoint h p)) := by
  classical
  choose H B hH hC using fun i => (hε (r i)).2 (hnonzero i)
  let Q : Set (State d × State d) :=
    {q | ∃ i : I, q.1 = r i ∧ ∀ j, |q.2 j - r i j| ≤ ε (r i)}
  have hcover : ∀ q ∈ Q, ∃ i, Nonempty (N.DirectionalCertificate q.1 q.2 (H i) (B i)) := by
    rintro q ⟨i, hi, hp⟩
    exact ⟨i, hi.symm ▸ hC i q.2 hp⟩
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ :=
    finite_directional_cover_eventual_flux N Q H B hH hℓ hu hcover
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall i p hp k hk
  exact hflux h hh hsmall (r i, p) ⟨i, rfl, hp⟩ k hk

/-- Conserved labels need no flux certificate. All nonconserved active labels,
including ties, share the threshold after the family has been fixed. -/
theorem Network.uniform_active_flux_of_sequentialActivityBound {d m : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (A : ScaledAffineFamily d m)
    (K : Set (State d)) (hK : IsCompact K) (ε : State d → ℝ)
    (hε : N.IsSlopeTolerance ε)
    (hseq : A.HasSequentialActivityBound K (fun i => ε (A.slope i)))
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ p ∈ K, ∀ i : Fin m,
        (A.atScale h).Active i (exponentialPoint h p) →
        (∃ e, N.projection (A.slope i) e ≠ 0) →
        ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
          0 < dot (A.slope i) (N.rhs k (exponentialPoint h p)) := by
  classical
  let I := {i : Fin m // ∃ e, N.projection (A.slope i) e ≠ 0}
  by_cases hI : Nonempty I
  · let : Nonempty I := hI
    obtain ⟨h₁, hh₁, hh₁1, hclose⟩ :=
      A.uniformActivityBound_of_sequential K hK (fun i => ε (A.slope i)) hseq
    obtain ⟨h₂, hh₂, _, hflux⟩ := N.finite_slopes_flux_of_tolerance
      (fun i : I => A.slope i.val) ε hε (fun i => i.property) hℓ hu
    refine ⟨min h₁ h₂, lt_min hh₁ hh₂, (min_le_left _ _).trans hh₁1, ?_⟩
    intro h hh hsmall p hp i hi hnonzero k hk
    apply hflux h hh (hsmall.trans_le (min_le_right _ _)) ⟨i, hnonzero⟩ p
      (A.norm_close_coordinate
        (hclose h hh (hsmall.trans_le (min_le_left _ _)) p hp i hi)) k hk
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    intro h hh hsmall p hp i hi hnonzero
    exact (hI ⟨⟨i, hnonzero⟩⟩).elim

/-- The class representative need not lie in the plateau: a single feasible
point of the original class carrier rules out conserved exterior branches. -/
theorem active_direction_has_nonzero_projection_of_carrier_nonempty
    {d m : ℕ} {E : Type*} (N : Network d E) (A : AffineFamily d m)
    {c x : State d} {M : ℝ} {i : Fin m}
    (hx : x ∈ N.positiveClass c) (hi : A.Active i x) (hout : x ∉ A.plateau M)
    (hne : (A.plateau M ∩ N.stoichiometricClass c).Nonempty) :
    ∃ e, N.projection (A.slope i) e ≠ 0 := by
  by_contra h
  have hzero : ∀ e, N.projection (A.slope i) e = 0 := by
    simpa only [not_exists, not_not] using h
  obtain ⟨y, hy, hyC⟩ := hne
  have hxq := dot_eq_of_zero_projections N (A.slope i) hx.2 hzero
  have hyq := dot_eq_of_zero_projections N (A.slope i) hyC hzero
  have hlt := A.active_value_lt_of_notin_plateau hi hout
  have hge := hy i
  simp only [AffineFamily.value] at hlt hge
  rw [hxq] at hlt
  rw [hyq] at hge
  linarith

/-- Outside a nonempty original plateau carrier in a stoichiometric class,
conservation rules out every zero-projection active label automatically. -/
theorem Network.uniform_exterior_active_flux_of_sequentialActivityBound
    {d m : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (N : Network d E) (A : ScaledAffineFamily d m)
    (K : Set (State d)) (hK : IsCompact K) (ε : State d → ℝ)
    (hε : N.IsSlopeTolerance ε)
    (hseq : A.HasSequentialActivityBound K (fun i => ε (A.slope i)))
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ p ∈ K, ∀ c : State d, ∀ M : ℝ,
        exponentialPoint h p ∈ N.positiveClass c →
        exponentialPoint h p ∉ (A.atScale h).plateau M →
        ((A.atScale h).plateau M ∩ N.stoichiometricClass c).Nonempty →
        ∀ i : Fin m, (A.atScale h).Active i (exponentialPoint h p) →
          ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
            0 < dot (A.slope i) (N.rhs k (exponentialPoint h p)) := by
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ :=
    N.uniform_active_flux_of_sequentialActivityBound A K hK ε hε hseq hℓ hu
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall p hp c M hx hout hne i hi k hk
  exact hflux h hh hsmall p hp i hi
    (active_direction_has_nonzero_projection_of_carrier_nonempty N (A.atScale h)
      hx hi hout hne) k hk

/-- A checked conditional reduction from the precise affine research target to
uniform all-active inward flux on an exponent cube. The affine target remains
an explicit hypothesis, and compact class carriers/absorption are not derived. -/
theorem Network.uniform_active_flux_of_affineApproximation {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (hA : FiniteAffineApproximationStatement) (hd : 0 < d) {a b ℓ u : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily d m,
      (∀ i, A.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) ∧
      (∀ i, Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ p ∈ Set.Icc (fun _ => a) (fun _ => b), ∀ i : Fin m,
          (A.atScale h).Active i (exponentialPoint h p) →
          (∃ e, N.projection (A.slope i) e ≠ 0) →
          ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
            0 < dot (A.slope i) (N.rhs k (exponentialPoint h p)) := by
  obtain ⟨ε, hε⟩ := N.exists_slopeTolerance hN
  obtain ⟨m, hm, A, hslope, hoffset, hseq⟩ := hA d hd a b hab ε
    (fun p _ => (hε p).1)
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ :=
    N.uniform_active_flux_of_sequentialActivityBound A _ isCompact_Icc ε hε hseq hℓ hu
  exact ⟨m, hm, A, hslope, hoffset, h₀, hh₀, hh₀1, hflux⟩

end Endotactic
end

-- Source: Endotactic/ScaleTrapPermanence.lean
section
/-!
# A fixed scale family reaches a common compact target

Quarter-power boxes fit in the next capped square-root scale's exponent box.
Late compact absorption connects the plateaux without assuming nestedness.
The final set is chosen before both rate paths and positive initial states.
-/

namespace Endotactic

open Set

structure ScaleTrapFamily {d m : ℕ} {E : Type*} [Fintype E]
    (N : Network d E) (ℓ u : ℝ) (c : State d) where
  family : ScaledAffineFamily d m
  threshold : ℝ
  threshold_pos : 0 < threshold
  threshold_lt_one : threshold < 1
  level : ℝ → ℝ
  relaxed : ℝ → ℝ
  reference : ∀ h ∈ Ioc 0 threshold, c ∈ (family.atScale h).plateau (level h)
  gap : ∀ h ∈ Ioc 0 threshold, relaxed h < level h
  compact : ∀ h ∈ Ioc 0 threshold, IsCompact ((family.atScale h).plateau (relaxed h))
  box : ∀ h ∈ Ioc 0 threshold,
    (family.atScale h).plateau (relaxed h) ⊆ powerBox h (1 / 4 : ℝ)
  capture : ∀ z : State d, Positive z → ∃ h ∈ Ioc 0 threshold,
    z ∈ (family.atScale h).plateau (relaxed h)
  flux : ∀ h ∈ Ioc 0 threshold,
    ∀ y ∈ Icc (fun _ => h) (fun _ => h⁻¹), ∀ i : Fin m,
      (family.atScale h).Active i y → (∃ e, N.projection (family.slope i) e ≠ 0) →
      ∀ a ∈ Icc (fun _ : E => ℓ) (fun _ => u),
        0 < dot (family.slope i) (N.rhs a y)

theorem capped_rootScale_succ {h H : ℝ} (hh : 0 < h) (hH1 : H ≤ 1) (n : ℕ) :
    min (rootScale h (n + 1)) H = Real.sqrt (min (rootScale h n) H) ⊓ H := by
  rw [rootScale_succ hh.le]
  by_cases hu : rootScale h n ≤ H
  · rw [min_eq_left hu]
  · have hHu := le_of_not_ge hu
    have hHH : H ≤ Real.sqrt H := Real.le_sqrt_self_iff.mpr hH1
    have hHs : H ≤ Real.sqrt (rootScale h n) := hHH.trans (Real.sqrt_le_sqrt hHu)
    rw [min_eq_right hHu, min_eq_right hHs]
    exact (min_eq_right hHH).symm

variable {d m : ℕ} {E : Type*} [Fintype E]
variable {N : Network d E} {ℓ u : ℝ} {c : State d}

theorem ScaleTrapFamily.faceCertificate (D : ScaleTrapFamily (m := m) N ℓ u c)
    {h : ℝ} (hh : h ∈ Ioc 0 D.threshold) :
    N.AffineFaceCertificate (D.family.atScale h) ℓ u (D.relaxed h) := by
  classical
  apply N.affineFaceCertificate_of_projections
  intro i
  by_cases hi : ∀ e, N.projection (D.family.slope i) e = 0
  · exact Or.inl hi
  · push Not at hi
    refine Or.inr ?_
    intro a ha y hy heq
    have hbox := D.box h hh hy
    have hsmall : h ≤ h ^ (1 / 4 : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge hh.1 (hh.2.trans D.threshold_lt_one.le)
          (by norm_num : (1 / 4 : ℝ) ≤ 1)
    have hunit := powerBox_subset_unit_box hh.1 hh.1 hsmall hbox
    have hactive : (D.family.atScale h).Active i y := fun j => heq ▸ hy j
    exact D.flux h hh y hunit i hactive hi a ha

theorem ScaleTrapFamily.eventual_step [Nonempty (Fin m)]
    (D : ScaleTrapFamily (m := m) N ℓ u c) {h : ℝ} (hh : h ∈ Ioc 0 D.threshold)
    {k : E → ℝ → ℝ} (hk : AdmissibleRates k ℓ u) {z : State d}
    (hz : z ∈ N.positiveClass c) {x : ℝ → State d} (hx : N.IsGlobalPositiveSolution k z x)
    (hstay : EventuallyIn x ((D.family.atScale h).plateau (D.relaxed h))) :
    EventuallyIn x ((D.family.atScale (min (Real.sqrt h) D.threshold)).plateau
      (D.relaxed (min (Real.sqrt h) D.threshold))) := by
  let g := min (Real.sqrt h) D.threshold
  have hg : g ∈ Ioc 0 D.threshold :=
    ⟨lt_min (Real.sqrt_pos.mpr hh.1) D.threshold_pos, min_le_right _ _⟩
  let B := (D.family.atScale h).plateau (D.relaxed h) ∩ N.stoichiometricClass c
  have hB : IsCompact B := (D.compact h hh).inter_right (N.stoichiometricClass_isClosed c)
  have hstayB : EventuallyIn x B := by
    obtain ⟨T, hT, hb⟩ := hstay
    exact ⟨T, hT, fun t ht => ⟨hb t ht, (hx.mem_positiveClass hz (hT.trans ht)).2⟩⟩
  have hgh : g ≤ h ^ (1 / 4 : ℝ) :=
    capped_sqrt_le_quarter_power hh.1 (hh.2.trans D.threshold_lt_one.le)
  have hcarrier : ((D.family.atScale g).plateau (D.level g) ∩
      N.stoichiometricClass c).Nonempty :=
    ⟨c, D.reference g hg, by change c - c ∈ N.stoichiometricSubspace; simp⟩
  apply (D.family.atScale g).eventuallyIn_plateau_of_eventual_compact_strict_exterior
    hk hx.1 hB hstayB (D.gap g hg)
  intro a ha y hy hmin i hi
  have hpower := D.box h hh hy.1
  have hypos := powerBox_positive hh.1 hpower
  have hunit := powerBox_subset_unit_box hh.1 hg.1 hgh hpower
  have hout : y ∉ (D.family.atScale g).plateau (D.level g) := by
    rw [(D.family.atScale g).mem_plateau_iff_minimum_ge]
    exact not_le.mpr hmin
  have hnonzero := active_direction_has_nonzero_projection_of_carrier_nonempty N
    (D.family.atScale g) ⟨hypos, hy.2⟩ hi hout hcarrier
  exact D.flux g hg y hunit i hi hnonzero a ha

theorem ScaleTrapFamily.uniformPermanent [Nonempty (Fin m)]
    (D : ScaleTrapFamily (m := m) N ℓ u c) : N.UniformPermanent ℓ u c (fun _ => True) := by
  let K := (D.family.atScale D.threshold).plateau (D.relaxed D.threshold) ∩
    N.stoichiometricClass c
  have hH : D.threshold ∈ Ioc 0 D.threshold := ⟨D.threshold_pos, le_rfl⟩
  have hpos : ∀ h ∈ Ioc 0 D.threshold,
      (D.family.atScale h).plateau (D.relaxed h) ⊆ {y | Positive y} :=
    fun h hh y hy => powerBox_positive hh.1 (D.box h hh hy)
  have hc : c ∈ K := ⟨fun i => (D.gap _ hH).le.trans (D.reference _ hH i),
    by change c - c ∈ N.stoichiometricSubspace; simp⟩
  refine ⟨K, ⟨c, hc⟩, (D.compact _ hH).inter_right (N.stoichiometricClass_isClosed c),
    (fun y hy => ⟨hpos _ hH hy.1, hy.2⟩), ?_⟩
  intro k hk _
  have htrap : ∀ z ∈ N.positiveClass c, ∃ h ∈ Ioc 0 D.threshold,
      ∃ x, N.IsGlobalPositiveSolution k z x ∧
        ∀ t, 0 ≤ t → x t ∈ (D.family.atScale h).plateau (D.relaxed h) := by
    intro z hz
    obtain ⟨h, hh, hzh⟩ := D.capture z hz.1
    exact ⟨h, hh, N.exists_global_positive_of_compact_affine_face_certificate hk
      (D.family.atScale h) (D.compact h hh) (hpos h hh) (D.faceCertificate hh) hzh⟩
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨h, hh, x, hx, _⟩ := htrap z hz
    exact N.positiveWellPosed_of_exists hk ⟨x, hx⟩
  · intro z hz x hx
    obtain ⟨h, hh, y, hy, hstay⟩ := htrap z hz
    have hinitial : EventuallyIn x ((D.family.atScale h).plateau (D.relaxed h)) :=
      ⟨0, le_rfl, fun t ht => by
        rw [Network.IsIntegralSolution.eqOn_nonnegative N hk hx.1 hy.1 ht]
        exact hstay t ht⟩
    have hiter : ∀ n : ℕ, EventuallyIn x
        ((D.family.atScale (min (rootScale h n) D.threshold)).plateau
          (D.relaxed (min (rootScale h n) D.threshold))) := by
      intro n
      induction n with
      | zero => simpa only [rootScale_zero, min_eq_left hh.2] using hinitial
      | succ n ih =>
        have hn : min (rootScale h n) D.threshold ∈ Ioc 0 D.threshold :=
          ⟨lt_min (rootScale_pos hh.1 n) D.threshold_pos, min_le_right _ _⟩
        simpa only [capped_rootScale_succ hh.1 D.threshold_lt_one.le n] using
          D.eventual_step hn hk hz hx ih
    obtain ⟨n, hn⟩ := capped_rootScale_reaches_threshold hh.1 D.threshold_lt_one
    have hfinal := hiter n
    rw [hn] at hfinal
    obtain ⟨T, hT, hentry⟩ := hfinal
    exact ⟨T, hT, fun t ht => ⟨hentry t ht, (hx.mem_positiveClass hz (hT.trans ht)).2⟩⟩

end Endotactic
end

-- Source: Endotactic/ExponentMinimum.lean
section
/-!
# Continuous minimum exponent and the nearby-minimum activity theorem

The cube includes its boundary. In a positive dimension, the minimum of its
coordinates is continuous and the top minimum stratum is a singleton.
-/

namespace Endotactic

noncomputable def exponentMinimum {d : ℕ} [NeZero d] (p : State d) : ℝ :=
  finiteMinimum p

theorem exponentMinimum_le_coordinate {d : ℕ} [NeZero d] (p : State d) (i : Fin d) :
    exponentMinimum p ≤ p i := finiteMinimum_le p i

theorem exponentMinimum_attained {d : ℕ} [NeZero d] (p : State d) :
    ∃ i : Fin d, exponentMinimum p = p i := finiteMinimum_attained p

theorem continuous_exponentMinimum {d : ℕ} [NeZero d] :
    Continuous (exponentMinimum : State d → ℝ) := by
  apply Continuous.finset_inf'_apply Finset.univ_nonempty
  intro i _
  exact continuous_apply i

theorem exponentMinimum_mem_interval {d : ℕ} [NeZero d] {a b : ℝ} {p : State d}
    (hp : p ∈ Set.Icc (fun _ => a) (fun _ => b)) :
    exponentMinimum p ∈ Set.Icc a b := by
  obtain ⟨i, hi⟩ := exponentMinimum_attained p
  rw [hi]
  exact ⟨hp.1 i, hp.2 i⟩

theorem exponentMinimum_eq_top_iff {d : ℕ} [NeZero d] {b : ℝ} {p : State d}
    (hp : p ≤ fun _ => b) : exponentMinimum p = b ↔ p = fun _ => b := by
  constructor
  · intro heq
    funext i
    apply le_antisymm (hp i)
    rw [← heq]
    exact exponentMinimum_le_coordinate p i
  · rintro rfl
    obtain ⟨i, hi⟩ := exponentMinimum_attained (fun _ : Fin d => b)
    exact hi

/-- This is the original fixed-minimum-to-neighborhood step with the closed
cube and a common scale threshold. Its fixed-stratum guarantee is an explicit
input; constructing those families and combining them remains separate. -/
theorem ScaledAffineFamily.uniformActivityBound_near_minimum {d m : ℕ} [NeZero d]
    (A : ScaledAffineFamily d m) (a b : ℝ) (ε : Fin m → ℝ) (t : ℝ)
    (hfixed : A.HasSequentialActivityBound
      (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = t}) ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => a) (fun _ => b), |exponentMinimum q - t| ≤ ρ →
          ∀ i : Fin m, (A.atScale h).Active i (exponentialPoint h q) →
            ‖q - A.slope i‖ < ε i :=
  A.uniformActivityBound_near_level _ isCompact_Icc ε exponentMinimum
    continuous_exponentMinimum t hfixed

/-- Pass the extended fixed-minimum family directly to the checked flux API.
The tolerance must already be the one certifying this network's fixed slopes. -/
theorem Network.uniform_active_flux_near_minimum {d m : ℕ} [NeZero d] {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (A : ScaledAffineFamily d m)
    (a b : ℝ) (ε : State d → ℝ) (hε : N.IsSlopeTolerance ε) (t : ℝ)
    (hfixed : A.HasSequentialActivityBound
      (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = t})
      (fun i => ε (A.slope i))) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => a) (fun _ => b), |exponentMinimum q - t| ≤ ρ →
          ∀ i : Fin m, (A.atScale h).Active i (exponentialPoint h q) →
            (∃ e, N.projection (A.slope i) e ≠ 0) →
            ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
              0 < dot (A.slope i) (N.rhs k (exponentialPoint h q)) := by
  obtain ⟨ρ, hρ, hseq⟩ := A.sequentialActivityBound_near_level _ isCompact_Icc
    (fun i => ε (A.slope i)) exponentMinimum continuous_exponentMinimum t hfixed
  have hband : IsCompact (Set.Icc (fun _ : Fin d => a) (fun _ => b) ∩
      {q | |exponentMinimum q - t| ≤ ρ}) :=
    isCompact_Icc.inter_right (isClosed_le
      ((continuous_exponentMinimum.sub continuous_const).abs) continuous_const)
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ :=
    N.uniform_active_flux_of_sequentialActivityBound A _ hband ε hε hseq hℓ hu
  exact ⟨ρ, hρ, h₀, hh₀, hh₀1, fun h hh hsmall q hq hnear =>
    hflux h hh hsmall q ⟨hq, hnear⟩⟩

/-- On a nonempty original class carrier, conservation eliminates every
exterior zero-projection active label after nearby-minimum extension. -/
theorem Network.uniform_exterior_active_flux_near_minimum
    {d m : ℕ} [NeZero d] {E : Type*} [Fintype E] [DecidableEq E]
    (N : Network d E) (A : ScaledAffineFamily d m) (a b : ℝ)
    (ε : State d → ℝ) (hε : N.IsSlopeTolerance ε) (t : ℝ)
    (hfixed : A.HasSequentialActivityBound
      (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = t})
      (fun i => ε (A.slope i))) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => a) (fun _ => b), |exponentMinimum q - t| ≤ ρ →
          ∀ c : State d, ∀ M : ℝ,
            exponentialPoint h q ∈ N.positiveClass c →
            exponentialPoint h q ∉ (A.atScale h).plateau M →
            ((A.atScale h).plateau M ∩ N.stoichiometricClass c).Nonempty →
            ∀ i : Fin m, (A.atScale h).Active i (exponentialPoint h q) →
              ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
                0 < dot (A.slope i) (N.rhs k (exponentialPoint h q)) := by
  obtain ⟨ρ, hρ, h₀, hh₀, hh₀1, hflux⟩ :=
    N.uniform_active_flux_near_minimum A a b ε hε t hfixed hℓ hu
  refine ⟨ρ, hρ, h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall q hq hnear c M hx hout hne i hi k hk
  exact hflux h hh hsmall q hq hnear i hi
    (active_direction_has_nonzero_projection_of_carrier_nonempty N (A.atScale h)
      hx hi hout hne) k hk

end Endotactic
end

-- Source: Endotactic/CoordinateEmbedding.lean
section
/-!
# Restrict and extend exponent coordinates

An injective coordinate map records the raised-coordinate type. Extension
sets every other slope coordinate to the common minimum t. The norm is the
ambient sup norm; projected and omitted-coordinate errors suffice separately.
-/

namespace Endotactic

open Filter Topology

def restrictCoordinates {k d : ℕ} (e : Fin k ↪ Fin d) (p : State d) : State k :=
  fun j => p (e j)

noncomputable def extendCoordinates {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (r : State k) : State d := Function.extend e r (fun _ => t)

theorem extendCoordinates_apply {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (r : State k) (j : Fin k) : extendCoordinates e t r (e j) = r j :=
  e.injective.extend_apply r (fun _ => t) j

theorem extendCoordinates_apply_outside {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (r : State k) {j : Fin d} (hj : j ∉ Set.range e) :
    extendCoordinates e t r j = t := Function.extend_apply' _ _ _ hj

theorem restrict_extendCoordinates {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (r : State k) : restrictCoordinates e (extendCoordinates e t r) = r := by
  funext j
  exact extendCoordinates_apply e t r j

theorem restrictCoordinates_exponentialPoint {k d : ℕ} (e : Fin k ↪ Fin d)
    (h : ℝ) (p : State d) :
    restrictCoordinates e (exponentialPoint h p) =
      exponentialPoint h (restrictCoordinates e p) := rfl

theorem continuous_restrictCoordinates {k d : ℕ} (e : Fin k ↪ Fin d) :
    Continuous (restrictCoordinates e) := continuous_pi fun j => continuous_apply (e j)

theorem tendsto_restrictCoordinates {k d : ℕ} (e : Fin k ↪ Fin d)
    {p : ℕ → State d} {q : State d} (hp : Tendsto p atTop (𝓝 q)) :
    Tendsto (fun n => restrictCoordinates e (p n)) atTop (𝓝 (restrictCoordinates e q)) :=
  ((continuous_restrictCoordinates e).tendsto q).comp hp

theorem restrictCoordinates_mem_cube {k d : ℕ} (e : Fin k ↪ Fin d)
    {a b : ℝ} {p : State d} (hp : p ∈ Set.Icc (fun _ => a) (fun _ => b)) :
    restrictCoordinates e p ∈ Set.Icc (fun _ => a) (fun _ => b) :=
  ⟨fun j => hp.1 (e j), fun j => hp.2 (e j)⟩

theorem extendCoordinates_mem_cube {k d : ℕ} (e : Fin k ↪ Fin d)
    {a b t : ℝ} {r : State k} (ht : t ∈ Set.Icc a b)
    (hr : r ∈ Set.Icc (fun _ => a) (fun _ => b)) :
    extendCoordinates e t r ∈ Set.Icc (fun _ => a) (fun _ => b) := by
  have hc : ∀ j, a ≤ extendCoordinates e t r j ∧ extendCoordinates e t r j ≤ b := by
    intro j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      rw [extendCoordinates_apply]
      exact ⟨hr.1 i, hr.2 i⟩
    · rw [extendCoordinates_apply_outside e t r hj]
      exact ht
  exact ⟨fun j => (hc j).1, fun j => (hc j).2⟩

theorem norm_sub_extendCoordinates_lt {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (r : State k) (q : State d) {ε : ℝ} (hε : 0 < ε)
    (hin : ‖restrictCoordinates e q - r‖ < ε)
    (hout : ∀ j ∉ Set.range e, |q j - t| < ε) :
    ‖q - extendCoordinates e t r‖ < ε := by
  apply (pi_norm_lt_iff hε).mpr
  intro j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    have hi := (norm_le_pi_norm (restrictCoordinates e q - r) i).trans_lt hin
    simpa only [Pi.sub_apply, restrictCoordinates, extendCoordinates_apply] using hi
  · simpa only [Pi.sub_apply, Real.norm_eq_abs,
      extendCoordinates_apply_outside e t r hj] using hout j hj

/-- Both lifted slopes have the same omitted coordinates, so these terms
cancel without any approximation or assumption on the state. -/
theorem dot_extendCoordinates_sub {k d : ℕ} (e : Fin k ↪ Fin d)
    (t : ℝ) (r s : State k) (x : State d) :
    dot (extendCoordinates e t r) x - dot (extendCoordinates e t s) x =
      dot r (restrictCoordinates e x) - dot s (restrictCoordinates e x) := by
  classical
  simp only [dot, ← Finset.sum_sub_distrib]
  have hsum : (∑ j ∈ Finset.univ.map e,
      (extendCoordinates e t r j * x j - extendCoordinates e t s j * x j)) =
      ∑ j : Fin d, (extendCoordinates e t r j * x j -
        extendCoordinates e t s j * x j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have ho : j ∉ Set.range e := by
      rintro ⟨i, rfl⟩
      exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    rw [extendCoordinates_apply_outside e t r ho,
      extendCoordinates_apply_outside e t s ho, sub_self]
  rw [← hsum, Finset.sum_map]
  simp only [extendCoordinates_apply, restrictCoordinates]

/-- At the last raised-coordinate type the only omitted coordinate must
attain the minimum. This conclusion uses the strict lower bound on every
raised coordinate, rather than assuming the omitted value equals t. -/
theorem omitted_coordinate_eq_minimum {k d : ℕ} [NeZero d]
    (e : Fin k ↪ Fin d) (j : Fin d) {q : State d} {t : ℝ}
    (hminimum : exponentMinimum q = t) (hraised : ∀ i, t < q (e i))
    (hunique : ∀ l ∉ Set.range e, l = j) : q j = t := by
  obtain ⟨l, hl⟩ := exponentMinimum_attained q
  have hout : l ∉ Set.range e := by
    rintro ⟨i, rfl⟩
    exact (ne_of_gt (hraised i)) (hl.symm.trans hminimum)
  rw [← hunique l hout]
  exact hl.symm.trans hminimum

theorem extendCoordinates_minimum {k d : ℕ} [NeZero d]
    (e : Fin k ↪ Fin d) (t : ℝ) (r : State k)
    (hr : ∀ i, t ≤ r i) (j : Fin d) (hj : j ∉ Set.range e) :
    exponentMinimum (extendCoordinates e t r) = t := by
  apply le_antisymm
  · simpa only [extendCoordinates_apply_outside e t r hj] using
      exponentMinimum_le_coordinate (extendCoordinates e t r) j
  · obtain ⟨l, hl⟩ := exponentMinimum_attained (extendCoordinates e t r)
    rw [hl]
    by_cases ho : l ∈ Set.range e
    · obtain ⟨i, rfl⟩ := ho
      simpa only [extendCoordinates_apply] using hr i
    · rw [extendCoordinates_apply_outside e t r ho]

end Endotactic
end

-- Source: Endotactic/RaisedCoordinateSupports.lean
section
/-!
# All nonempty proper coordinate supports

The finite subtype contains every raised type. Its ordered embedding has
exactly the specified range. Inserting an omitted coordinate supplies the
next type unless only one coordinate was omitted.
-/

namespace Endotactic

abbrev RaisedSupport (d : ℕ) :=
  {U : Finset (Fin d) // 0 < U.card ∧ U.card < d}

def RaisedSupport.embedding {d : ℕ} (U : RaisedSupport d) : Fin U.val.card ↪ Fin d :=
  (U.val.orderEmbOfFin rfl).toEmbedding

theorem RaisedSupport.embedding_range {d : ℕ} (U : RaisedSupport d) :
    Set.range U.embedding = (U.val : Set (Fin d)) :=
  Finset.range_orderEmbOfFin U.val rfl

theorem RaisedSupport.embedding_mem {d : ℕ} (U : RaisedSupport d)
    (i : Fin U.val.card) : U.embedding i ∈ U.val :=
  Finset.orderEmbOfFin_mem U.val rfl i

theorem RaisedSupport.mem_iff_range {d : ℕ} (U : RaisedSupport d) (j : Fin d) :
    j ∈ U.val ↔ j ∈ Set.range U.embedding := by
  rw [U.embedding_range]
  rfl

def RaisedSupport.singleton {d : ℕ} (hd : 1 < d) (j : Fin d) : RaisedSupport d :=
  ⟨{j}, by simpa using And.intro Nat.zero_lt_one hd⟩

theorem RaisedSupport.singleton_card {d : ℕ} (hd : 1 < d) (j : Fin d) :
    (RaisedSupport.singleton hd j).val.card = 1 := Finset.card_singleton j

def RaisedSupport.insert {d : ℕ} (U : RaisedSupport d) (j : Fin d)
    (hj : j ∉ U.val) (hnext : U.val.card + 1 < d) : RaisedSupport d :=
  ⟨Insert.insert j U.val, by rw [Finset.card_insert_of_notMem hj]; exact ⟨by omega, hnext⟩⟩

theorem RaisedSupport.insert_card {d : ℕ} (U : RaisedSupport d) (j : Fin d)
    (hj : j ∉ U.val) (hnext : U.val.card + 1 < d) :
    (U.insert j hj hnext).val.card = U.val.card + 1 :=
  Finset.card_insert_of_notMem hj

theorem RaisedSupport.omitted_exists {d : ℕ} (U : RaisedSupport d) :
    ∃ j : Fin d, j ∉ U.val := by
  by_contra hn
  have heq : U.val = Finset.univ := Finset.eq_univ_iff_forall.mpr (by simpa using hn)
  have hcard := U.property.2
  simp only [heq, Finset.card_univ, Fintype.card_fin] at hcard
  omega

theorem RaisedSupport.last_omitted_unique {d : ℕ} (U : RaisedSupport d)
    (hlast : U.val.card + 1 = d) (j : Fin d) (hj : j ∉ U.val) :
    ∀ l ∉ U.val, l = j := by
  have hc : U.valᶜ.card = 1 := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨l, hl⟩ := Finset.card_eq_one.mp hc
  have hjl : j = l := by simpa only [hl, Finset.mem_singleton] using
    (Finset.mem_compl.mpr hj)
  intro k hk
  have hkl : k = l := by simpa only [hl, Finset.mem_singleton] using
    (Finset.mem_compl.mpr hk)
  exact hkl.trans hjl.symm

theorem RaisedSupport.last_omitted_eq_minimum {d : ℕ} [NeZero d]
    (U : RaisedSupport d) (hlast : U.val.card + 1 = d)
    {q : State d} {t : ℝ} (hminimum : exponentMinimum q = t)
    (hraised : ∀ j ∈ U.val, t < q j) (j : Fin d) (hj : j ∉ U.val) : q j = t := by
  apply omitted_coordinate_eq_minimum U.embedding j hminimum
  · intro i
    exact hraised _ (U.embedding_mem i)
  · intro l hl
    exact U.last_omitted_unique hlast j hj l ((U.mem_iff_range l).not.mpr hl)

end Endotactic
end

-- Source: Endotactic/MovingPowerAsymptotics.lean
section
/-!
# Moving exponent comparisons at vanishing positive scales

Strict gaps are imposed only on limiting exponents. Joint continuity of real
power at a zero base and a positive exponent avoids a separate logarithmic or
quantitative gap argument. Neither the scale nor the exponent is monotone.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem moving_rpow_ratio_tendsto_zero {I : Type*} {l : Filter I}
    {h p q : I → ℝ} {p₀ q₀ : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 p₀)) (hq : Tendsto q l (𝓝 q₀)) (hgap : q₀ < p₀) :
    Tendsto (fun x => h x ^ p x / h x ^ q x) l (𝓝 0) := by
  have hd : Tendsto (fun x => h x ^ (p x - q x)) l (𝓝 0) := by
    simpa only [Real.zero_rpow (sub_pos.mpr hgap).ne'] using
      hh.rpow (hp.sub hq) (Or.inr (sub_pos.mpr hgap))
  apply hd.congr'
  filter_upwards [hpos] with x hx
  exact Real.rpow_sub hx _ _

theorem moving_rpow_isLittleO {I : Type*} {l : Filter I}
    {h p q : I → ℝ} {p₀ q₀ : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 p₀)) (hq : Tendsto q l (𝓝 q₀)) (hgap : q₀ < p₀) :
    IsLittleO l (fun x => h x ^ p x) (fun x => h x ^ q x) := by
  apply isLittleO_of_tendsto' _ (moving_rpow_ratio_tendsto_zero hh hpos hp hq hgap)
  filter_upwards [hpos] with x hx
  exact fun hzero => ((Real.rpow_pos_of_pos hx _).ne' hzero).elim

theorem moving_rpow_ratio_tendsto_atTop {I : Type*} {l : Filter I}
    {h p q : I → ℝ} {p₀ q₀ : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 p₀)) (hq : Tendsto q l (𝓝 q₀)) (hgap : p₀ < q₀) :
    Tendsto (fun x => h x ^ p x / h x ^ q x) l atTop := by
  have hz := moving_rpow_ratio_tendsto_zero hh hpos hq hp hgap
  have hgt : Tendsto (fun x => h x ^ q x / h x ^ p x) l (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hz, ?_⟩
    filter_upwards [hpos] with x hx
    exact div_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hx _)
  convert hgt.inv_tendsto_nhdsGT_zero using 1
  ext x
  simp

theorem rpow_isLittleO_nhdsGT_zero {a b : ℝ} (hab : a < b) :
    IsLittleO (𝓝[>] (0 : ℝ)) (fun h : ℝ => h ^ b) (fun h : ℝ => h ^ a) :=
  moving_rpow_isLittleO nhdsWithin_le_nhds
    (self_mem_nhdsWithin : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Set.Ioi 0)
    tendsto_const_nhds tendsto_const_nhds hab

theorem offset_isLittleO_along_scales {I : Type*} {l : Filter I}
    {h : I → ℝ} {c : ℝ → ℝ} {a : ℝ}
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ a))
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x) :
    IsLittleO l (fun x => c (h x)) (fun x => h x ^ a) :=
  hc.comp_tendsto (tendsto_nhdsWithin_iff.mpr ⟨hh, hpos⟩)

theorem moving_weighted_power_sum_isLittleO {I J : Type*} {l : Filter I}
    (s : Finset J) (w : J → ℝ) {h : I → ℝ} {p : J → I → ℝ}
    {p₀ : J → ℝ} {q : ℝ} (hh : Tendsto h l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : ∀ j ∈ s, Tendsto (p j) l (𝓝 (p₀ j))) (hgap : ∀ j ∈ s, q < p₀ j) :
    IsLittleO l (fun x => ∑ j ∈ s, w j * h x ^ p j x) (fun x => h x ^ q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using isLittleO_zero (fun x => h x ^ q) l
  | @insert j s hjs ih =>
    have hj := (moving_rpow_isLittleO hh hpos (hp j (by simp))
      tendsto_const_nhds (hgap j (by simp))).const_mul_left (w j)
    have hs := ih (fun k hk => hp k (Finset.mem_insert_of_mem hk))
      (fun k hk => hgap k (Finset.mem_insert_of_mem hk))
    simpa only [Finset.sum_insert hjs] using hj.add hs

end Endotactic
end

-- Source: Endotactic/OffsetDecayNeighborhood.lean
section
/-!
# Improve offset decay by shrinking a minimum neighborhood

Offsets bounded by powers with exponents strictly above the fixed minimum are
little-o of a common slightly raised power. All label thresholds are finite;
no continuity or globally uniform tolerance is required.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem shifted_power_offset_isBigO {c : ℝ → ℝ} {β : ℝ}
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β)) :
    IsBigO (𝓝[>] (0 : ℝ)) (fun h => -(h ^ β) + c h) (fun h => h ^ β) :=
  (isBigO_refl (fun h : ℝ => h ^ β) _).neg_left.add hc.isBigO

theorem offset_isLittleO_of_powerBound {c : ℝ → ℝ} {q β : ℝ}
    (hc : IsBigO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β)) (hq : q < β) :
    IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ q) :=
  hc.trans_isLittleO (rpow_isLittleO_nhdsGT_zero hq)

/-- The empty-label case is included. In nonempty families the radius is
bounded by half the smallest strictly positive exponent gap. -/
theorem exists_common_offset_decay {I : Type*} [Fintype I]
    (c : I → ℝ → ℝ) (β : I → ℝ) (t : ℝ) {R : ℝ} (hR : 0 < R)
    (hβ : ∀ i, t < β i)
    (hc : ∀ i, IsBigO (𝓝[>] (0 : ℝ)) (c i) (fun h => h ^ β i)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      ∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (c i) (fun h => h ^ (t + ρ)) := by
  classical
  by_cases hI : Nonempty I
  · let : Nonempty I := hI
    let s := Finset.univ.image (fun i => β i - t)
    have hs : s.Nonempty := Finset.univ_nonempty.image _
    have hmin : 0 < s.min' hs := by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (s.min'_mem hs)
      rw [← hi]
      exact sub_pos.mpr (hβ i)
    refine ⟨min R (s.min' hs / 2), lt_min hR (by positivity), min_le_left _ _, ?_⟩
    intro i
    apply offset_isLittleO_of_powerBound (hc i)
    have hi : s.min' hs ≤ β i - t :=
      s.min'_le _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hρ := min_le_right R (s.min' hs / 2)
    linarith
  · exact ⟨R, hR, le_rfl, fun i => (hI ⟨i⟩).elim⟩

theorem ScaledAffineFamily.sequentialActivityBound_mono {d m : ℕ}
    (A : ScaledAffineFamily d m) {K L : Set (State d)} {ε : Fin m → ℝ}
    (hL : A.HasSequentialActivityBound L ε) (hKL : K ⊆ L) :
    A.HasSequentialActivityBound K ε := by
  intro i h p q hh hhlim hplim hq hi
  exact hL i h p q hh hhlim hplim (hKL hq) hi

/-- Both sequential approximation and improved offset decay hold on the same
closed band after shrinking it. The family and slopes are retained. -/
theorem ScaledAffineFamily.sequentialActivityBound_near_level_with_decay
    {d m : ℕ} (A : ScaledAffineFamily d m) (K : Set (State d)) (hK : IsCompact K)
    (ε : Fin m → ℝ) (f : State d → ℝ) (hf : Continuous f) (t : ℝ)
    (hfixed : A.HasSequentialActivityBound (K ∩ {q | f q = t}) ε)
    (β : Fin m → ℝ) (hβ : ∀ i, t < β i)
    (hc : ∀ i, IsBigO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ β i)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ (t + ρ))) ∧
      A.HasSequentialActivityBound (K ∩ {q | |f q - t| ≤ ρ}) ε := by
  obtain ⟨R, hR, hseq⟩ := A.sequentialActivityBound_near_level K hK ε f hf t hfixed
  obtain ⟨ρ, hρ, hρR, hdecay⟩ := exists_common_offset_decay A.offset β t hR hβ hc
  refine ⟨ρ, hρ, hdecay, A.sequentialActivityBound_mono hseq ?_⟩
  rintro q ⟨hq, hband⟩
  exact ⟨hq, hband.trans hρR⟩

theorem ScaledAffineFamily.sequentialActivityBound_near_minimum_with_decay
    {d m : ℕ} [NeZero d] (A : ScaledAffineFamily d m) (a b : ℝ)
    (ε : Fin m → ℝ) (t : ℝ)
    (hfixed : A.HasSequentialActivityBound
      (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = t}) ε)
    (β : Fin m → ℝ) (hβ : ∀ i, t < β i)
    (hc : ∀ i, IsBigO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ β i)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ (t + ρ))) ∧
      A.HasSequentialActivityBound
        (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | |exponentMinimum q - t| ≤ ρ}) ε :=
  A.sequentialActivityBound_near_level_with_decay _ isCompact_Icc ε exponentMinimum
    continuous_exponentMinimum t hfixed β hβ hc

end Endotactic
end

-- Source: Endotactic/AffinePowerComparison.lean
section
/-!
# Power comparisons needed by raised-coordinate affine labels

The first comparison forces a raised coordinate's limiting exponent to lie
above the offset exponent. The second makes a competitor with a stronger
negative offset strictly smaller. These prove the comparison steps without
assuming that a whole inductive label family has already been constructed.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem exponent_ge_of_power_upper_bound {I : Type*} {l : Filter I} [l.NeBot]
    {h p c : I → ℝ} {p₀ β w : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 p₀)) (hw : 0 < w)
    (hc : IsLittleO l c (fun x => h x ^ β))
    (hupper : ∀ᶠ x in l, w * h x ^ p x ≤ h x ^ β - c x) : β ≤ p₀ := by
  by_contra hbad
  have hgap : p₀ < β := lt_of_not_ge hbad
  have hlarge := (moving_rpow_ratio_tendsto_atTop hh hpos hp
    tendsto_const_nhds hgap).eventually_gt_atTop (2 / w)
  have hsmall : ∀ᶠ x in l, -1 < c x / h x ^ β :=
    hc.tendsto_div_nhds_zero.eventually (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0))
  obtain ⟨x, hx, hux, hlx, hsx⟩ := (hpos.and (hupper.and (hlarge.and hsmall))).exists
  have hb : 0 < h x ^ β := Real.rpow_pos_of_pos hx _
  have hdiv : w * (h x ^ p x / h x ^ β) ≤ 1 - c x / h x ^ β := by
    simpa only [sub_div, div_self hb.ne', mul_div_assoc] using
      div_le_div_of_nonneg_right hux hb.le
  have htwo : 2 < w * (h x ^ p x / h x ^ β) := by
    have hm := mul_lt_mul_of_pos_left hlx hw
    simpa only [mul_div_cancel₀ _ hw.ne'] using hm
  linarith

theorem raised_coordinate_limits_ge_of_sum_bound {I J : Type*} {l : Filter I} [l.NeBot]
    (s : Finset J) (w : J → ℝ) {h c : I → ℝ} {p : J → I → ℝ}
    {p₀ : J → ℝ} {β : ℝ} (hh : Tendsto h l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < h x) (hw : ∀ j ∈ s, 0 < w j)
    (hp : ∀ j ∈ s, Tendsto (p j) l (𝓝 (p₀ j)))
    (hc : IsLittleO l c (fun x => h x ^ β))
    (hupper : ∀ᶠ x in l, (∑ j ∈ s, w j * h x ^ p j x) ≤ h x ^ β - c x) :
    ∀ j ∈ s, β ≤ p₀ j := by
  intro j hj
  apply exponent_ge_of_power_upper_bound hh hpos (hp j hj) (hw j hj) hc
  filter_upwards [hpos, hupper] with x hx hux
  exact (Finset.single_le_sum (fun k hk =>
    mul_nonneg (hw k hk).le (Real.rpow_pos_of_pos hx (p k x)).le) hj).trans hux

theorem negative_power_offset_ratio_tendsto {I : Type*} {l : Filter I}
    {h c : I → ℝ} {β : ℝ} (hpos : ∀ᶠ x in l, 0 < h x)
    (hc : IsLittleO l c (fun x => h x ^ β)) :
    Tendsto (fun x => (-(h x ^ β) + c x) / h x ^ β) l (𝓝 (-1)) := by
  have hlim := tendsto_const_nhds.add hc.tendsto_div_nhds_zero
    (f := fun _ : I => (-1 : ℝ))
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [hpos] with x hx
  have hb : h x ^ β ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  simp only [add_div, neg_div, div_self hb]

theorem eventually_lt_of_normalized_limits {I : Type*} {l : Filter I}
    {f g s : I → ℝ} {a b : ℝ} (hs : ∀ᶠ x in l, 0 < s x)
    (hf : Tendsto (fun x => f x / s x) l (𝓝 a))
    (hg : Tendsto (fun x => g x / s x) l (𝓝 b)) (hab : a < b) :
    ∀ᶠ x in l, f x < g x := by
  filter_upwards [hs, hf.eventually_lt hg hab] with x hx hlt
  exact (div_lt_div_iff_of_pos_right hx).mp hlt

/-- A negative offset with a strictly smaller exponent beats the lower bound
of the old label. All remainders are controlled along the actual scale filter. -/
theorem stronger_negative_power_eventually_lt {I : Type*} {l : Filter I}
    {h c d : I → ℝ} {γ β : ℝ} (hh : Tendsto h l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < h x) (hgap : γ < β)
    (hc : IsLittleO l c (fun x => h x ^ γ))
    (hd : IsLittleO l d (fun x => h x ^ β)) :
    ∀ᶠ x in l, -(h x ^ γ) + c x < -(h x ^ β) + d x := by
  have hp : IsLittleO l (fun x => h x ^ β) (fun x => h x ^ γ) :=
    moving_rpow_isLittleO hh hpos tendsto_const_nhds tendsto_const_nhds hgap
  have hold : IsLittleO l (fun x => -(h x ^ β) + d x) (fun x => h x ^ γ) :=
    hp.neg_left.add (hd.trans hp)
  exact eventually_lt_of_normalized_limits
    (hpos.mono fun x hx => Real.rpow_pos_of_pos hx _)
    (negative_power_offset_ratio_tendsto hpos hc) hold.tendsto_div_nhds_zero
    (by norm_num)

theorem zero_label_beaten_by_negative_power {I : Type*} {l : Filter I}
    {h c : I → ℝ} {β : ℝ} (hpos : ∀ᶠ x in l, 0 < h x)
    (hc : IsLittleO l c (fun x => h x ^ β)) :
    ∀ᶠ x in l, -(h x ^ β) + c x < 0 :=
  eventually_lt_of_normalized_limits
    (hpos.mono fun x hx => Real.rpow_pos_of_pos hx _)
    (negative_power_offset_ratio_tendsto hpos hc)
    (by simpa only [zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : I => (0 : ℝ)) l (𝓝 0)))
    (by norm_num)

/-- All raised terms are little-o of the competitor's negative offset when
their limiting exponents are strictly above its exponent. The old branch only
needs a lower bound; its raised terms need not be asymptotically negligible. -/
theorem raised_competitor_eventually_beats_lower_bound
    {I J : Type*} {l : Filter I} (s : Finset J) (w : J → ℝ)
    {h c d old : I → ℝ} {p : J → I → ℝ} {p₀ : J → ℝ} {γ β : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x) (hgap : γ < β)
    (hp : ∀ j ∈ s, Tendsto (p j) l (𝓝 (p₀ j))) (hraised : ∀ j ∈ s, γ < p₀ j)
    (hc : IsLittleO l c (fun x => h x ^ γ))
    (hd : IsLittleO l d (fun x => h x ^ β))
    (hold : ∀ᶠ x in l, -(h x ^ β) + d x ≤ old x) :
    ∀ᶠ x in l, (∑ j ∈ s, w j * h x ^ p j x) - h x ^ γ + c x < old x := by
  have hrem := (moving_weighted_power_sum_isLittleO s w hh hpos hp hraised).add hc
  have hbeat := stronger_negative_power_eventually_lt hh hpos hgap hrem hd
  filter_upwards [hbeat, hold] with x hbx hox
  linarith

theorem raised_competitor_eventually_beats_zero
    {I J : Type*} {l : Filter I} (s : Finset J) (w : J → ℝ)
    {h c : I → ℝ} {p : J → I → ℝ} {p₀ : J → ℝ} {γ : ℝ}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : ∀ j ∈ s, Tendsto (p j) l (𝓝 (p₀ j))) (hraised : ∀ j ∈ s, γ < p₀ j)
    (hc : IsLittleO l c (fun x => h x ^ γ)) :
    ∀ᶠ x in l, (∑ j ∈ s, w j * h x ^ p j x) - h x ^ γ + c x < 0 := by
  have hrem := (moving_weighted_power_sum_isLittleO s w hh hpos hp hraised).add hc
  have hbeat := zero_label_beaten_by_negative_power hpos hrem
  filter_upwards [hbeat] with x hbx
  linarith

theorem dot_exponential_increment_on_coordinates {d : ℕ} (r : State d)
    (t h : ℝ) (p : State d) (U : Finset (Fin d))
    (houtside : ∀ j ∉ U, r j = t) :
    dot r (exponentialPoint h p) - dot (fun _ => t) (exponentialPoint h p) =
      ∑ j ∈ U, (r j - t) * h ^ p j := by
  classical
  simp only [dot, exponentialPoint, ← Finset.sum_sub_distrib, ← sub_mul]
  exact (Finset.sum_subset (Finset.subset_univ U)
    (fun j _ hj => by rw [houtside j hj, sub_self, zero_mul])).symm

/-- Actual activity comparison with the type-zero seed supplies the sum
bound. The raised-coordinate conclusion does not assume it as separate data. -/
theorem ScaledAffineFamily.raised_coordinate_limits_ge {d m : ℕ}
    {I : Type*} {l : Filter I} [l.NeBot]
    (A : ScaledAffineFamily d m) (i seed : Fin m) (U : Finset (Fin d))
    (t β : ℝ) (c : ℝ → ℝ)
    (hseed : A.slope seed = fun _ => t) (hseedoffset : ∀ h, A.offset seed h = 0)
    (houtside : ∀ j ∉ U, A.slope i j = t)
    (hraised : ∀ j ∈ U, t < A.slope i j)
    (hoffset : ∀ h, A.offset i h = -(h ^ β) + c h)
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q))
    (hactive : ∀ᶠ x in l, (A.atScale (h x)).Active i (exponentialPoint (h x) (p x))) :
    ∀ j ∈ U, β ≤ q j := by
  apply raised_coordinate_limits_ge_of_sum_bound U (fun j => A.slope i j - t)
    hh hpos (fun j hj => sub_pos.mpr (hraised j hj))
    (fun j _ => (continuous_apply j).tendsto q |>.comp hp)
    (offset_isLittleO_along_scales hc hh hpos)
  filter_upwards [hactive] with x hx
  have hs := hx seed
  simp only [ScaledAffineFamily.atScale_value,
    hseed, hseedoffset, add_zero, hoffset] at hs
  simp only [Function.comp_apply]
  rw [← dot_exponential_increment_on_coordinates (A.slope i) t (h x) (p x) U houtside]
  linarith

end Endotactic
end

-- Source: Endotactic/AffineCoordinateLift.lean
section
/-!
# Lift lower-dimensional affine families without losing any active label

The common offset γ and common omitted-coordinate contribution cancel in all
pairwise comparisons. Thus a lifted active label is exactly a projected active
label, including ties. The lower-dimensional bound and omitted-coordinate
bound are explicit inputs; this module does not construct all inductive types.
-/

namespace Endotactic

open Filter Topology Asymptotics

noncomputable def ScaledAffineFamily.coordinateLift {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (t : ℝ) (γ : ℝ → ℝ) :
    ScaledAffineFamily d m where
  slope i := extendCoordinates e t (B.slope i)
  offset i h := γ h + B.offset i h

theorem ScaledAffineFamily.coordinateLift_value_sub {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (t : ℝ) (γ : ℝ → ℝ)
    (h : ℝ) (i j : Fin m) (x : State d) :
    ((B.coordinateLift e t γ).atScale h).value i x -
        ((B.coordinateLift e t γ).atScale h).value j x =
      (B.atScale h).value i (restrictCoordinates e x) -
        (B.atScale h).value j (restrictCoordinates e x) := by
  simp only [ScaledAffineFamily.atScale_value, ScaledAffineFamily.coordinateLift]
  have heq := dot_extendCoordinates_sub e t (B.slope i) (B.slope j) x
  linarith

theorem ScaledAffineFamily.coordinateLift_active_iff {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (t : ℝ) (γ : ℝ → ℝ)
    (h : ℝ) (i : Fin m) (x : State d) :
    ((B.coordinateLift e t γ).atScale h).Active i x ↔
      (B.atScale h).Active i (restrictCoordinates e x) := by
  change (∀ j, _ ≤ _) ↔ ∀ j, _ ≤ _
  have heq := B.coordinateLift_value_sub e t γ h i
  constructor <;> intro hi j
  · have hj := hi j
    have hd := heq j x
    linarith
  · have hj := hi j
    have hd := heq j x
    linarith

theorem ScaledAffineFamily.coordinateLift_exponential_active_iff {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (t : ℝ) (γ : ℝ → ℝ)
    (h : ℝ) (i : Fin m) (p : State d) :
    ((B.coordinateLift e t γ).atScale h).Active i (exponentialPoint h p) ↔
      (B.atScale h).Active i (exponentialPoint h (restrictCoordinates e p)) := by
  rw [B.coordinateLift_active_iff, restrictCoordinates_exponentialPoint]

theorem ScaledAffineFamily.coordinateLift_slopes_mem_cube {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (γ : ℝ → ℝ)
    {a b t : ℝ} (ht : t ∈ Set.Icc a b)
    (hB : ∀ i, B.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) :
    ∀ i, (B.coordinateLift e t γ).slope i ∈ Set.Icc (fun _ => a) (fun _ => b) :=
  fun i => extendCoordinates_mem_cube e ht (hB i)

theorem ScaledAffineFamily.coordinateLift_offset_isLittleO {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (t a : ℝ) (γ : ℝ → ℝ)
    (hγ : IsLittleO (𝓝[>] (0 : ℝ)) γ (fun h => h ^ a))
    (hB : ∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (B.offset i) (fun h => h ^ a)) :
    ∀ i, IsLittleO (𝓝[>] (0 : ℝ)) ((B.coordinateLift e t γ).offset i)
      (fun h => h ^ a) := fun i => hγ.add (hB i)

/-- The sup-norm estimate at an actual active limit. Approaching points may
be outside either cube; only the projected limit must be in the lower set. -/
theorem ScaledAffineFamily.coordinateLift_active_limit_norm_lt {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (t : ℝ) (γ : ℝ → ℝ)
    (L : Set (State k)) (ε : Fin m → ℝ) (hB : B.HasSequentialActivityBound L ε)
    (i : Fin m) {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q)) (hq : restrictCoordinates e q ∈ L)
    (hactive : ∀ n, ((B.coordinateLift e t γ).atScale (h n)).Active i
      (exponentialPoint (h n) (p n)))
    (hout : ∀ j ∉ Set.range e, |q j - t| < ε i) :
    ‖q - (B.coordinateLift e t γ).slope i‖ < ε i := by
  have hin := hB i h (fun n => restrictCoordinates e (p n)) (restrictCoordinates e q)
    hpos hh (tendsto_restrictCoordinates e hp) hq
    (fun n => (B.coordinateLift_exponential_active_iff e t γ (h n) i (p n)).mp
      (hactive n))
  exact norm_sub_extendCoordinates_lt e t (B.slope i) q
    (lt_of_le_of_lt (norm_nonneg _) hin) hin hout

theorem ScaledAffineFamily.coordinateLift_sequentialActivityBound {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d) (t : ℝ) (γ : ℝ → ℝ)
    (K : Set (State d)) (L : Set (State k)) (ε : Fin m → ℝ)
    (hB : B.HasSequentialActivityBound L ε)
    (hprojection : ∀ q ∈ K, restrictCoordinates e q ∈ L)
    (hout : ∀ q ∈ K, ∀ i : Fin m, ∀ j ∉ Set.range e, |q j - t| < ε i) :
    (B.coordinateLift e t γ).HasSequentialActivityBound K ε := by
  intro i h p q hpos hh hp hq hactive
  exact B.coordinateLift_active_limit_norm_lt e t γ L ε hB i hpos hh hp
    (hprojection q hq) hactive (hout q hq i)

/-- The last type has no omitted-coordinate error. Its value t follows from
the minimum condition and strict raised gap t<β. Neither B's existence nor
the existence of every type is asserted here. -/
theorem ScaledAffineFamily.coordinateLift_last_minimum_stratum {k d m : ℕ}
    [NeZero d] (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d)
    (j : Fin d) (hunique : ∀ l ∉ Set.range e, l = j)
    (t β b : ℝ) (htβ : t < β) (γ : ℝ → ℝ) (ε : Fin m → ℝ)
    (hε : ∀ i, 0 < ε i)
    (hB : B.HasSequentialActivityBound (Set.Icc (fun _ => β) (fun _ => b)) ε) :
    (B.coordinateLift e t γ).HasSequentialActivityBound
      {q | q ≤ (fun _ => b) ∧ exponentMinimum q = t ∧ ∀ i, β ≤ q (e i)} ε := by
  apply B.coordinateLift_sequentialActivityBound e t γ _ _ ε hB
  · intro q hq
    exact ⟨hq.2.2, fun i => hq.1 (e i)⟩
  · intro q hq i l hl
    have hj := omitted_coordinate_eq_minimum e j hq.2.1
      (fun i => htβ.trans_le (hq.2.2 i)) hunique
    rw [hunique l hl, hj, sub_self, abs_zero]
    exact hε i

end Endotactic
end

-- Source: Endotactic/FiniteLiftTolerance.lean
section
/-!
# Finite tolerance selection and omitted-coordinate errors

Only the tolerance at the already fixed finite slopes is used. No continuity
of the original tolerance function, or positive lower bound over a cube, is
assumed. The omitted-coordinate upper bound still needs the competing types.
-/

namespace Endotactic

open Filter Topology

theorem exists_common_positive_width {I : Type*} [Fintype I]
    (ε : I → ℝ) (hε : ∀ i, 0 < ε i) {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧ ∀ i, δ < ε i := by
  classical
  by_cases hI : Nonempty I
  · let : Nonempty I := hI
    let s := Finset.univ.image ε
    have hs : s.Nonempty := Finset.univ_nonempty.image _
    have hm : 0 < s.min' hs := by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (s.min'_mem hs)
      rw [← hi]
      exact hε i
    refine ⟨min R (s.min' hs) / 2, by positivity, ?_, ?_⟩
    · have hc := min_le_left R (s.min' hs)
      have hp : 0 < min R (s.min' hs) := lt_min hR hm
      linarith
    · intro i
      have hi := s.min'_le (ε i) (Finset.mem_image_of_mem ε (Finset.mem_univ i))
      have hc := min_le_right R (s.min' hs)
      have hp : 0 < min R (s.min' hs) := lt_min hR hm
      linarith
  · exact ⟨R / 2, by positivity, by linarith, fun i => (hI ⟨i⟩).elim⟩

theorem ScaledAffineFamily.exists_next_lift_level {k d m : ℕ}
    (B : ScaledAffineFamily k m) (e : Fin k ↪ Fin d)
    (E : State d → ℝ) {t β : ℝ} (htβ : t < β)
    (hE : ∀ i, 0 < E (extendCoordinates e t (B.slope i))) :
    ∃ η : ℝ, t < η ∧ η < β ∧
      ∀ i, η - t < E (extendCoordinates e t (B.slope i)) := by
  obtain ⟨δ, hδ, hδβ, hδε⟩ := exists_common_positive_width
    (fun i => E (extendCoordinates e t (B.slope i))) hE (sub_pos.mpr htβ)
  refine ⟨t + δ, by linarith, by linarith, ?_⟩
  intro i
  simpa using hδε i

theorem coordinate_error_lt_of_minimum_upper {d : ℕ} [NeZero d]
    {q : State d} {t η ε : ℝ} (hminimum : exponentMinimum q = t)
    (hgap : η - t < ε) (j : Fin d) (hupper : q j ≤ η) : |q j - t| < ε := by
  have hlower : t ≤ q j := hminimum ▸ exponentMinimum_le_coordinate q j
  rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

/-- Once the competing types have bounded omitted exponents by η, both
coordinate blocks combine into the strict ambient sup-norm tolerance. -/
theorem ScaledAffineFamily.coordinateLift_active_limit_of_minimum_upper
    {k d m : ℕ} [NeZero d] (B : ScaledAffineFamily k m)
    (e : Fin k ↪ Fin d) (t : ℝ) (γ : ℝ → ℝ)
    (L : Set (State k)) (ε : Fin m → ℝ) (hB : B.HasSequentialActivityBound L ε)
    (i : Fin m) {h : ℕ → ℝ} {p : ℕ → State d} {q : State d} {η : ℝ}
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q)) (hq : restrictCoordinates e q ∈ L)
    (hactive : ∀ n, ((B.coordinateLift e t γ).atScale (h n)).Active i
      (exponentialPoint (h n) (p n))) (hminimum : exponentMinimum q = t)
    (hgap : η - t < ε i) (hupper : ∀ j ∉ Set.range e, q j ≤ η) :
    ‖q - (B.coordinateLift e t γ).slope i‖ < ε i := by
  apply B.coordinateLift_active_limit_norm_lt e t γ L ε hB i hpos hh hp hq hactive
  intro j hj
  exact coordinate_error_lt_of_minimum_upper hminimum hgap j (hupper j hj)

end Endotactic
end

-- Source: Endotactic/AffineBlockUnion.lean
section
/-!
# Actual finite unions of scale-dependent affine blocks

A dependent finite label type retains the block and local label, then an
equivalence encodes it as Fin for the existing affine API. No label is dropped,
including duplicates or ties. Global activity implies local block activity;
the converse additionally needs every cross-block comparison.
-/

namespace Endotactic

open Filter Topology Asymptotics

noncomputable def affineBlockLabel {I : Type*} [Fintype I]
    (m : I → ℕ) (b : I) (i : Fin (m b)) : Fin (Fintype.card (Σ b, Fin (m b))) :=
  Fintype.equivFin _ ⟨b, i⟩

noncomputable def ScaledAffineFamily.blockUnion {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) :
    ScaledAffineFamily d (Fintype.card (Σ b, Fin (m b))) where
  slope j := let l := (Fintype.equivFin (Σ b, Fin (m b))).symm j
    (A l.1).slope l.2
  offset j h := let l := (Fintype.equivFin (Σ b, Fin (m b))).symm j
    (A l.1).offset l.2 h

theorem affineBlockLabel_decode {I : Type*} [Fintype I]
    (m : I → ℕ) (b : I) (i : Fin (m b)) :
    (Fintype.equivFin (Σ b, Fin (m b))).symm (affineBlockLabel m b i) = ⟨b, i⟩ :=
  (Fintype.equivFin _).symm_apply_apply _

theorem affineBlockLabel_surjective {I : Type*} [Fintype I] (m : I → ℕ)
    (j : Fin (Fintype.card (Σ b, Fin (m b)))) :
    ∃ b i, affineBlockLabel m b i = j := by
  let l := (Fintype.equivFin (Σ b, Fin (m b))).symm j
  exact ⟨l.1, l.2, (Fintype.equivFin _).apply_symm_apply j⟩

theorem affineBlockLabel_injective {I : Type*} [Fintype I]
    (m : I → ℕ) (b : I) : Function.Injective (affineBlockLabel m b) := by
  intro i j hij
  have heq := (Fintype.equivFin (Σ b, Fin (m b))).injective hij
  exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2

theorem affineBlockLabel_card_pos {I : Type*} [Fintype I]
    (m : I → ℕ) (b : I) (hb : 0 < m b) : 0 < Fintype.card (Σ b, Fin (m b)) :=
  Fintype.card_pos_iff.mpr ⟨⟨b, ⟨0, hb⟩⟩⟩

theorem ScaledAffineFamily.blockUnion_slope {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) (b : I) (i : Fin (m b)) :
    (ScaledAffineFamily.blockUnion m A).slope (affineBlockLabel m b i) = (A b).slope i := by
  change (A ((Fintype.equivFin (Σ b, Fin (m b))).symm (affineBlockLabel m b i)).1).slope
    ((Fintype.equivFin (Σ b, Fin (m b))).symm (affineBlockLabel m b i)).2 = _
  rw [affineBlockLabel_decode]

theorem ScaledAffineFamily.blockUnion_offset {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) (b : I) (i : Fin (m b)) (h : ℝ) :
    (ScaledAffineFamily.blockUnion m A).offset (affineBlockLabel m b i) h =
      (A b).offset i h := by
  change (A ((Fintype.equivFin (Σ b, Fin (m b))).symm (affineBlockLabel m b i)).1).offset
    ((Fintype.equivFin (Σ b, Fin (m b))).symm (affineBlockLabel m b i)).2 h = _
  rw [affineBlockLabel_decode]

theorem ScaledAffineFamily.blockUnion_value {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b))
    (b : I) (i : Fin (m b)) (h : ℝ) (x : State d) :
    ((ScaledAffineFamily.blockUnion m A).atScale h).value (affineBlockLabel m b i) x =
      ((A b).atScale h).value i x := by
  simp only [ScaledAffineFamily.atScale_value, ScaledAffineFamily.blockUnion_slope,
    ScaledAffineFamily.blockUnion_offset]

theorem ScaledAffineFamily.blockUnion_active_iff {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b))
    (b : I) (i : Fin (m b)) (h : ℝ) (x : State d) :
    ((ScaledAffineFamily.blockUnion m A).atScale h).Active (affineBlockLabel m b i) x ↔
      ∀ c j, ((A b).atScale h).value i x ≤ ((A c).atScale h).value j x := by
  constructor
  · intro hi c j
    simpa only [ScaledAffineFamily.blockUnion_value] using hi (affineBlockLabel m c j)
  · intro hi j
    obtain ⟨c, l, rfl⟩ := affineBlockLabel_surjective m j
    simpa only [ScaledAffineFamily.blockUnion_value] using hi c l

theorem ScaledAffineFamily.blockUnion_active_in_block {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b))
    (b : I) (i : Fin (m b)) (h : ℝ) (x : State d)
    (hi : ((ScaledAffineFamily.blockUnion m A).atScale h).Active
      (affineBlockLabel m b i) x) : ((A b).atScale h).Active i x :=
  fun j => (ScaledAffineFamily.blockUnion_active_iff m A b i h x).mp hi b j

theorem ScaledAffineFamily.blockUnion_plateau {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) (h M : ℝ) :
    ((ScaledAffineFamily.blockUnion m A).atScale h).plateau M =
      ⋂ b, ((A b).atScale h).plateau M := by
  ext x
  simp only [Set.mem_iInter, AffineFamily.plateau, Set.mem_ofPred_eq]
  constructor
  · intro hx b i
    simpa only [ScaledAffineFamily.blockUnion_value] using hx (affineBlockLabel m b i)
  · intro hx j
    obtain ⟨b, i, rfl⟩ := affineBlockLabel_surjective m j
    simpa only [ScaledAffineFamily.blockUnion_value] using hx b i

theorem ScaledAffineFamily.blockUnion_slopes_mem {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) (K : Set (State d))
    (hA : ∀ b i, (A b).slope i ∈ K) :
    ∀ j, (ScaledAffineFamily.blockUnion m A).slope j ∈ K := by
  intro j
  obtain ⟨b, i, rfl⟩ := affineBlockLabel_surjective m j
  rw [ScaledAffineFamily.blockUnion_slope]
  exact hA b i

theorem ScaledAffineFamily.blockUnion_offsets_isLittleO {d : ℕ} {I : Type*} [Fintype I]
    (m : I → ℕ) (A : ∀ b, ScaledAffineFamily d (m b)) (a : ℝ)
    (hA : ∀ b i, IsLittleO (𝓝[>] (0 : ℝ)) ((A b).offset i) (fun h => h ^ a)) :
    ∀ j, IsLittleO (𝓝[>] (0 : ℝ)) ((ScaledAffineFamily.blockUnion m A).offset j)
      (fun h => h ^ a) := by
  intro j
  obtain ⟨b, i, rfl⟩ := affineBlockLabel_surjective m j
  have heq : (ScaledAffineFamily.blockUnion m A).offset (affineBlockLabel m b i) =
      (A b).offset i := funext fun h => ScaledAffineFamily.blockUnion_offset m A b i h
  rw [heq]
  exact hA b i

/-- This closure rule is useful when every block already works on the same
domain. Type-specific construction instead uses cross-block competitors. -/
theorem ScaledAffineFamily.blockUnion_sequentialActivityBound
    {d : ℕ} {I : Type*} [Fintype I] (m : I → ℕ)
    (A : ∀ b, ScaledAffineFamily d (m b)) (K : Set (State d)) (E : State d → ℝ)
    (hA : ∀ b, (A b).HasSequentialActivityBound K (fun i => E ((A b).slope i))) :
    (ScaledAffineFamily.blockUnion m A).HasSequentialActivityBound K
      (fun j => E ((ScaledAffineFamily.blockUnion m A).slope j)) := by
  intro j h p q hpos hh hp hq hactive
  obtain ⟨b, i, rfl⟩ := affineBlockLabel_surjective m j
  change ‖q - (ScaledAffineFamily.blockUnion m A).slope (affineBlockLabel m b i)‖ <
    E ((ScaledAffineFamily.blockUnion m A).slope (affineBlockLabel m b i))
  rw [ScaledAffineFamily.blockUnion_slope]
  exact hA b i h p q hpos hh hp hq (fun n =>
    ScaledAffineFamily.blockUnion_active_in_block m A b i (h n) _ (hactive n))

end Endotactic
end

-- Source: Endotactic/AffineActiveCompetitors.lean
section
/-!
# Actual active-label comparisons bound omitted limiting exponents

The competitors are labels of the same supplied affine family. Their negative
power offsets beat the old branch when every exponent on the competitor's
support is too large. Activity gives the contradictory reverse inequality.
Existence and coverage of all required competing supports remain separate.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem ScaledAffineFamily.eventually_competitor_value_lt
    {d m : ℕ} {I : Type*} {l : Filter I}
    (A : ScaledAffineFamily d m) (i competitor : Fin m) (V : Finset (Fin d))
    (t β η : ℝ) (c drem : ℝ → ℝ) (hgap : η < β)
    (holdSlope : ∀ j, t ≤ A.slope i j)
    (holdOffset : ∀ h, A.offset i h = -(h ^ β) + c h)
    (hcompOutside : ∀ j ∉ V, A.slope competitor j = t)
    (hcompOffset : ∀ h, A.offset competitor h = -(h ^ η) + drem h)
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β))
    (hd : IsLittleO (𝓝[>] (0 : ℝ)) drem (fun h => h ^ η))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q)) (hq : ∀ j ∈ V, η < q j) :
    ∀ᶠ x in l, (A.atScale (h x)).value competitor (exponentialPoint (h x) (p x)) <
      (A.atScale (h x)).value i (exponentialPoint (h x) (p x)) := by
  let old := fun x => (A.atScale (h x)).value i (exponentialPoint (h x) (p x)) -
    dot (fun _ => t) (exponentialPoint (h x) (p x))
  have hlower : ∀ᶠ x in l, -(h x ^ β) + c (h x) ≤ old x := by
    filter_upwards [hpos] with x hx
    have hn : 0 ≤ dot (A.slope i) (exponentialPoint (h x) (p x)) -
        dot (fun _ => t) (exponentialPoint (h x) (p x)) := by
      rw [dot_exponential_increment_on_coordinates _ _ _ _ Finset.univ (by simp)]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (sub_nonneg.mpr (holdSlope j))
        (Real.rpow_pos_of_pos hx _).le
    dsimp [old]
    rw [ScaledAffineFamily.atScale_value, holdOffset]
    linarith
  have hbeat := raised_competitor_eventually_beats_lower_bound V
    (fun j => A.slope competitor j - t) hh hpos hgap
    (fun j _ => (continuous_apply j).tendsto q |>.comp hp) hq
    (offset_isLittleO_along_scales hd hh hpos)
    (offset_isLittleO_along_scales hc hh hpos) hlower
  filter_upwards [hbeat] with x hx
  have heq := dot_exponential_increment_on_coordinates (A.slope competitor)
    t (h x) (p x) V hcompOutside
  simp only [Function.comp_apply] at hx
  dsimp [old] at hx
  rw [ScaledAffineFamily.atScale_value, hcompOffset]
  linarith

theorem ScaledAffineFamily.active_omitted_coordinate_le
    {d m : ℕ} {I : Type*} {l : Filter I} [l.NeBot]
    (A : ScaledAffineFamily d m) (i competitor : Fin m) (V : Finset (Fin d))
    (j : Fin d) (_hj : j ∈ V) (t β η : ℝ) (c drem : ℝ → ℝ) (hgap : η < β)
    (holdSlope : ∀ k, t ≤ A.slope i k)
    (holdOffset : ∀ h, A.offset i h = -(h ^ β) + c h)
    (hcompOutside : ∀ k ∉ V, A.slope competitor k = t)
    (hcompOffset : ∀ h, A.offset competitor h = -(h ^ η) + drem h)
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β))
    (hd : IsLittleO (𝓝[>] (0 : ℝ)) drem (fun h => h ^ η))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q)) (hq : ∀ k ∈ V, k ≠ j → η < q k)
    (hactive : ∀ᶠ x in l, (A.atScale (h x)).Active i (exponentialPoint (h x) (p x))) :
    q j ≤ η := by
  by_contra hbad
  have hlarge : η < q j := lt_of_not_ge hbad
  have hall : ∀ k ∈ V, η < q k := by
    intro k hk
    by_cases hkj : k = j
    · simpa only [hkj] using hlarge
    · exact hq k hk hkj
  have hbeat := A.eventually_competitor_value_lt i competitor V t β η c drem hgap
    holdSlope holdOffset hcompOutside hcompOffset hc hd hh hpos hp hall
  obtain ⟨x, hbx, hax⟩ := (hbeat.and hactive).exists
  exact (not_lt_of_ge (hax competitor)) hbx

theorem ScaledAffineFamily.eventually_competitor_value_lt_seed
    {d m : ℕ} {I : Type*} {l : Filter I}
    (A : ScaledAffineFamily d m) (seed competitor : Fin m) (V : Finset (Fin d))
    (t η : ℝ) (drem : ℝ → ℝ)
    (hseed : A.slope seed = fun _ => t) (hseedOffset : ∀ h, A.offset seed h = 0)
    (hcompOutside : ∀ k ∉ V, A.slope competitor k = t)
    (hcompOffset : ∀ h, A.offset competitor h = -(h ^ η) + drem h)
    (hd : IsLittleO (𝓝[>] (0 : ℝ)) drem (fun h => h ^ η))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q)) (hq : ∀ k ∈ V, η < q k) :
    ∀ᶠ x in l, (A.atScale (h x)).value competitor (exponentialPoint (h x) (p x)) <
      (A.atScale (h x)).value seed (exponentialPoint (h x) (p x)) := by
  have hbeat := raised_competitor_eventually_beats_zero V
    (fun k => A.slope competitor k - t) hh hpos
    (fun k _ => (continuous_apply k).tendsto q |>.comp hp) hq
    (offset_isLittleO_along_scales hd hh hpos)
  filter_upwards [hbeat] with x hx
  have heq := dot_exponential_increment_on_coordinates (A.slope competitor)
    t (h x) (p x) V hcompOutside
  simp only [Function.comp_apply] at hx
  simp only [ScaledAffineFamily.atScale_value, hseed, hseedOffset, add_zero, hcompOffset]
  linarith

theorem ScaledAffineFamily.seed_active_omitted_coordinate_le
    {d m : ℕ} {I : Type*} {l : Filter I} [l.NeBot]
    (A : ScaledAffineFamily d m) (seed competitor : Fin m) (j : Fin d)
    (t η : ℝ) (drem : ℝ → ℝ)
    (hseed : A.slope seed = fun _ => t) (hseedOffset : ∀ h, A.offset seed h = 0)
    (hcompOutside : ∀ k ∉ ({j} : Finset (Fin d)), A.slope competitor k = t)
    (hcompOffset : ∀ h, A.offset competitor h = -(h ^ η) + drem h)
    (hd : IsLittleO (𝓝[>] (0 : ℝ)) drem (fun h => h ^ η))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q))
    (hactive : ∀ᶠ x in l, (A.atScale (h x)).Active seed
      (exponentialPoint (h x) (p x))) : q j ≤ η := by
  by_contra hbad
  have hall : ∀ k ∈ ({j} : Finset (Fin d)), η < q k := by
    intro k hk
    simpa only [Finset.mem_singleton.mp hk] using lt_of_not_ge hbad
  have hbeat := A.eventually_competitor_value_lt_seed seed competitor {j} t η drem
    hseed hseedOffset hcompOutside hcompOffset hd hh hpos hp hall
  obtain ⟨x, hbx, hax⟩ := (hbeat.and hactive).exists
  exact (not_lt_of_ge (hax competitor)) hbx

/-- This theorem derives both exponent bounds from the actual active label:
the seed supplies q>=β on U, and the larger-support competitor supplies q_j<=η.
No omitted-coordinate upper bound is an input. -/
theorem ScaledAffineFamily.active_omitted_coordinate_le_of_raised_type
    {d m : ℕ} {I : Type*} {l : Filter I} [l.NeBot]
    (A : ScaledAffineFamily d m) (i seed competitor : Fin m) (U : Finset (Fin d))
    (j : Fin d) (t β η : ℝ) (c drem : ℝ → ℝ) (hgap : η < β)
    (hseed : A.slope seed = fun _ => t) (hseedOffset : ∀ h, A.offset seed h = 0)
    (houtside : ∀ k ∉ U, A.slope i k = t) (hraised : ∀ k ∈ U, t < A.slope i k)
    (holdOffset : ∀ h, A.offset i h = -(h ^ β) + c h)
    (hcompOutside : ∀ k ∉ insert j U, A.slope competitor k = t)
    (hcompOffset : ∀ h, A.offset competitor h = -(h ^ η) + drem h)
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β))
    (hd : IsLittleO (𝓝[>] (0 : ℝ)) drem (fun h => h ^ η))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q))
    (hactive : ∀ᶠ x in l, (A.atScale (h x)).Active i (exponentialPoint (h x) (p x))) :
    q j ≤ η := by
  classical
  have hU := A.raised_coordinate_limits_ge i seed U t β c hseed hseedOffset
    houtside hraised holdOffset hc hh hpos hp hactive
  apply A.active_omitted_coordinate_le i competitor (insert j U) j
    (Finset.mem_insert_self j U) t β η c drem hgap _ holdOffset
    hcompOutside hcompOffset hc hd hh hpos hp _ hactive
  · intro k
    by_cases hk : k ∈ U
    · exact (hraised k hk).le
    · rw [houtside k hk]
  · intro k hk hkj
    exact hgap.trans_le (hU k ((Finset.mem_insert.mp hk).resolve_left hkj))

end Endotactic
end

-- Source: Endotactic/ScaledActivityExamples.lean
section
/-!
# Actual tied labels, discontinuous offsets, and a failed approximation

The successful family has two parallel labels tied at every positive scale;
one offset is discontinuous at zero. Its sequential guarantee is proved on a
nonempty exponent neighborhood, and the flux bridge is actually instantiated.
The failed singleton family shows that finiteness and compactness alone do not
imply the sequential activity approximation assumed by the bridge.
-/

namespace Endotactic.ActivityExamples

open Filter Topology

noncomputable def parallelFamily {d : ℕ} (r : State d) : ScaledAffineFamily d 2 := by
  classical
  exact {
    slope := fun _ => r
    offset := fun i h => if i = 0 then 0 else if h = 0 then 1 else 0 }

theorem parallelFamily_value {d : ℕ} (r : State d) {h : ℝ} (hh : h ≠ 0)
    (i : Fin 2) (x : State d) :
    ((parallelFamily r).atScale h).value i x = dot r x := by
  classical
  simp [ScaledAffineFamily.atScale_value, parallelFamily, hh]

theorem parallelFamily_all_active {d : ℕ} (r : State d) {h : ℝ} (hh : h ≠ 0)
    (i : Fin 2) (x : State d) : ((parallelFamily r).atScale h).Active i x := by
  intro j
  rw [parallelFamily_value r hh, parallelFamily_value r hh]

theorem parallelFamily_has_sequential_bound {d : ℕ} (r : State d)
    {ε : ℝ} (hε : 0 < ε) :
    (parallelFamily r).HasSequentialActivityBound (Metric.closedBall r (ε / 2))
      (fun _ => ε) := by
  intro i h p q _ _ _ hq _
  have hnorm : ‖q - r‖ ≤ ε / 2 := by
    simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hq
  change ‖q - r‖ < ε
  exact hnorm.trans_lt (by linarith)

theorem parallelFamily_offset_not_continuous {d : ℕ} (r : State d) :
    ¬ ContinuousAt ((parallelFamily r).offset 1) 0 := by
  classical
  intro hc
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hvalue : ∀ n : ℕ,
      (parallelFamily r).offset 1 (1 / ((n : ℝ) + 1)) = 0 := by
    intro n
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    change (if (1 : Fin 2) = 0 then (0 : ℝ)
      else if 1 / ((n : ℝ) + 1) = 0 then 1 else 0) = 0
    rw [ite_eq_right (by decide), ite_eq_right hn.ne']
  have hzero : Tendsto (fun n : ℕ => (parallelFamily r).offset 1 (1 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa only [hvalue] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hone := hc.tendsto.comp hlim
  have heq := tendsto_nhds_unique hone hzero
  norm_num [parallelFamily] at heq

/-- A genuine nonempty exponent neighborhood and all tied labels satisfy the
new uniform-flux bridge. This is a local family example, not general affine A. -/
theorem exists_parallelFamily_uniform_flux {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (r : State d) (hnonzero : ∃ e, N.projection r e ≠ 0)
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ ε : ℝ, 0 < ε ∧ (Metric.closedBall r (ε / 2)).Nonempty ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ p ∈ Metric.closedBall r (ε / 2), ∀ i : Fin 2,
          ((parallelFamily r).atScale h).Active i (exponentialPoint h p) ∧
          ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
            0 < dot ((parallelFamily r).slope i) (N.rhs k (exponentialPoint h p)) := by
  obtain ⟨ε, hε⟩ := N.exists_slopeTolerance hN
  have hseq : (parallelFamily r).HasSequentialActivityBound
      (Metric.closedBall r (ε r / 2)) (fun i => ε ((parallelFamily r).slope i)) :=
    parallelFamily_has_sequential_bound r (hε r).1
  obtain ⟨h₀, hh₀, hh₀1, hflux⟩ := N.uniform_active_flux_of_sequentialActivityBound
    (parallelFamily r) _ (isCompact_closedBall r _) ε hε hseq hℓ hu
  refine ⟨ε r, (hε r).1, ⟨r, Metric.mem_closedBall_self
    (div_nonneg (hε r).1.le (by norm_num))⟩,
    h₀, hh₀, hh₀1, ?_⟩
  intro h hh hsmall p hp i
  have hi := parallelFamily_all_active r hh.ne' i (exponentialPoint h p)
  exact ⟨hi, hflux h hh hsmall p hp i hi hnonzero⟩

def badFamily : ScaledAffineFamily 1 1 where
  slope _ := 1
  offset _ _ := 0

theorem badFamily_slope_mem_cube (i : Fin 1) :
    badFamily.slope i ∈ Set.Icc (0 : State 1) 1 := by
  simp [badFamily, Set.mem_Icc]

theorem badFamily_offset_littleO (a : ℝ) (i : Fin 1) :
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) (badFamily.offset i) (fun h => h ^ a) :=
  Asymptotics.isLittleO_zero _ _

theorem badFamily_not_sequential :
    ¬ badFamily.HasSequentialActivityBound (Set.Icc (0 : State 1) 1)
      (fun _ => 1 / 2) := by
  intro hseq
  have hpositive : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hclose := hseq 0 (fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun _ => 0) 0
    hpositive tendsto_one_div_add_atTop_nhds_zero_nat tendsto_const_nhds
    (by simp) (fun _ j => by fin_cases j; exact le_rfl)
  norm_num [badFamily] at hclose

theorem badFamily_no_uniform_activity :
    ¬ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ p ∈ Set.Icc (0 : State 1) 1, ∀ i : Fin 1,
        (badFamily.atScale h).Active i (exponentialPoint h p) →
          ‖p - badFamily.slope i‖ < 1 / 2 := by
  rintro ⟨h₀, hh₀, hbound⟩
  have hclose := hbound (h₀ / 2) (by positivity) (by linarith) 0 (by simp) 0
    (fun j => by fin_cases j; exact le_rfl)
  norm_num [badFamily] at hclose

end Endotactic.ActivityExamples
end

-- Source: Endotactic/FixedMinimumSeeds.lean
section
/-!
# Genuine fixed-minimum seed families and discontinuous-offset limit sets

The singleton family gives the fixed-minimum starting cases in dimension one
and at the top of any cube. Neighborhood extension is actually instantiated.
These are local stratum families, not the globally combined affine family A.
-/

namespace Endotactic

open Filter Topology

def minimumSeedFamily (d : ℕ) (t : ℝ) : ScaledAffineFamily d 1 where
  slope _ := fun _ => t
  offset _ _ := 0

theorem minimumSeedFamily_activityLimit (d : ℕ) (t : ℝ) (i : Fin 1) :
    (minimumSeedFamily d t).activityLimit i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  refine mem_scaleLimit_of_sequences (fun n : ℕ => 1 / ((n : ℝ) + 1))
    (fun _ => q) (fun _ => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat tendsto_const_nhds ?_
  intro n j
  have hji : j = i := Subsingleton.elim _ _
  rw [hji]

theorem minimumSeedFamily_offset_littleO (d : ℕ) (t a : ℝ) (i : Fin 1) :
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ)) ((minimumSeedFamily d t).offset i)
      (fun h => h ^ a) := Asymptotics.isLittleO_zero _ _

/-- Any positive tolerance works on each one-dimensional minimum stratum.
The sequences approaching that stratum may lie outside the cube. -/
theorem minimumSeedFamily_oneDim_fixedMinimum (a b t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (minimumSeedFamily 1 t).HasSequentialActivityBound
      (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = t})
      (fun _ => ε) := by
  intro i h p q _ _ _ hq _
  have hqt : q = fun _ => t := by
    obtain ⟨j, hj⟩ := exponentMinimum_attained q
    funext k
    have hkj : k = j := Subsingleton.elim _ _
    rw [hkj, ← hj]
    exact hq.2
  change ‖q - (fun _ => t)‖ < ε
  rw [hqt, sub_self, norm_zero]
  exact hε

/-- In any positive dimension, the cube's top minimum stratum is a singleton.
This is an actual seed construction; only positivity of the chosen tolerance
at that one slope is required. -/
theorem minimumSeedFamily_top_fixedMinimum {d : ℕ} [NeZero d]
    (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (minimumSeedFamily d b).HasSequentialActivityBound
      (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = b})
      (fun _ => ε) := by
  intro i h p q _ _ _ hq _
  have hqt := (exponentMinimum_eq_top_iff hq.1.2).mp hq.2
  change ‖q - (fun _ => b)‖ < ε
  rw [hqt, sub_self, norm_zero]
  exact hε

theorem minimumSeedFamily_oneDim_nearby_uniform (a b t : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => a) (fun _ => b), |exponentMinimum q - t| ≤ ρ →
          ∀ i : Fin 1,
            ((minimumSeedFamily 1 t).atScale h).Active i (exponentialPoint h q) →
              ‖q - (minimumSeedFamily 1 t).slope i‖ < ε :=
  (minimumSeedFamily 1 t).uniformActivityBound_near_minimum a b (fun _ => ε) t
    (minimumSeedFamily_oneDim_fixedMinimum a b t hε)

theorem minimumSeedFamily_top_nearby_uniform {d : ℕ} [NeZero d]
    (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => a) (fun _ => b), |exponentMinimum q - b| ≤ ρ →
          ∀ i : Fin 1,
            ((minimumSeedFamily d b).atScale h).Active i (exponentialPoint h q) →
              ‖q - (minimumSeedFamily d b).slope i‖ < ε :=
  (minimumSeedFamily d b).uniformActivityBound_near_minimum a b (fun _ => ε) b
    (minimumSeedFamily_top_fixedMinimum a b hε)

/-- Both tied labels of the already checked discontinuous-offset family have
the whole ambient exponent space as their closed activity-limit set. This
instantiates the limit-set API without a hidden continuity assumption. -/
theorem ActivityExamples.parallelFamily_activityLimit {d : ℕ} (r : State d)
    (i : Fin 2) : (ActivityExamples.parallelFamily r).activityLimit i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  refine mem_scaleLimit_of_sequences (fun n : ℕ => 1 / ((n : ℝ) + 1))
    (fun _ => q) (fun _ => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat tendsto_const_nhds ?_
  intro n
  exact ActivityExamples.parallelFamily_all_active r (by positivity) i _

end Endotactic
end

-- Source: Endotactic/SeededAffineUnion.lean
section
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
end

-- Source: Endotactic/FixedMinimumAssembly.lean
section
/-!
# Assemble every raised support into a fixed-minimum approximation

The input records lower-dimensional families and descending levels, not the
desired ambient conclusion. All supports and competitors are present in the
actual finite union. Activity derives both the projected cube membership and
the omitted-coordinate bounds. Constructing this data by induction remains a
separate existence obligation.
-/

namespace Endotactic

open Filter Topology Asymptotics

structure FixedMinimumData (d : ℕ) (t b : ℝ) (E : State d → ℝ) where
  size : RaisedSupport d → ℕ
  size_pos : ∀ U, 0 < size U
  level : ℕ → ℝ
  level_gt : ∀ U : RaisedSupport d, t < level U.val.card
  level_desc : ∀ U : RaisedSupport d, U.val.card + 1 < d →
    level (U.val.card + 1) < level U.val.card
  block : ∀ U : RaisedSupport d, ScaledAffineFamily U.val.card (size U)
  cube : ∀ U i, (block U).slope i ∈
    Set.Icc (fun _ => level U.val.card) (fun _ => b)
  decay : ∀ U i, IsLittleO (𝓝[>] (0 : ℝ)) ((block U).offset i)
    (fun h => h ^ level U.val.card)
  approximation : ∀ U, (block U).HasSequentialActivityBound
    (Set.Icc (fun _ => level U.val.card) (fun _ => b))
    (fun i => E (extendCoordinates U.embedding t ((block U).slope i)))
  seed_width : level 1 - t < E (fun _ => t)
  next_width : ∀ U : RaisedSupport d, U.val.card + 1 < d → ∀ i,
    level (U.val.card + 1) - t <
      E (extendCoordinates U.embedding t ((block U).slope i))

noncomputable def FixedMinimumData.lift {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) :=
  (D.block U).coordinateLift U.embedding t (fun h => -(h ^ D.level U.val.card))

noncomputable def FixedMinimumData.family {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) :=
  ScaledAffineFamily.seededUnion t D.size D.lift

noncomputable def FixedMinimumData.label {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) (i : Fin (D.size U)) :=
  seededAffineLabel D.size U i

theorem FixedMinimumData.family_label_slope {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) (i : Fin (D.size U)) :
    D.family.slope (D.label U i) =
      extendCoordinates U.embedding t ((D.block U).slope i) :=
  ScaledAffineFamily.seededUnion_block_slope t D.size D.lift U i

theorem FixedMinimumData.family_label_offset {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) (i : Fin (D.size U)) (h : ℝ) :
    D.family.offset (D.label U i) h = -(h ^ D.level U.val.card) +
      (D.block U).offset i h :=
  ScaledAffineFamily.seededUnion_block_offset t D.size D.lift U i h

theorem FixedMinimumData.family_label_outside {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) (i : Fin (D.size U))
    (j : Fin d) (hj : j ∉ U.val) : D.family.slope (D.label U i) j = t := by
  rw [D.family_label_slope]
  exact extendCoordinates_apply_outside U.embedding t _ ((U.mem_iff_range j).not.mp hj)

theorem FixedMinimumData.family_label_raised {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) (i : Fin (D.size U))
    (j : Fin d) (hj : j ∈ U.val) : t < D.family.slope (D.label U i) j := by
  obtain ⟨k, rfl⟩ := (U.mem_iff_range j).mp hj
  rw [D.family_label_slope, extendCoordinates_apply]
  exact (D.level_gt U).trans_le ((D.cube U i).1 k)

theorem FixedMinimumData.active_raised_limits {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) (i : Fin (D.size U))
    {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q))
    (hactive : ∀ n, (D.family.atScale (h n)).Active (D.label U i)
      (exponentialPoint (h n) (p n))) :
    ∀ j ∈ U.val, D.level U.val.card ≤ q j :=
  D.family.raised_coordinate_limits_ge (D.label U i) (seededAffineSeed D.size)
    U.val t (D.level U.val.card) ((D.block U).offset i)
    (ScaledAffineFamily.seededUnion_seed_slope t D.size D.lift)
    (ScaledAffineFamily.seededUnion_seed_offset t D.size D.lift)
    (D.family_label_outside U i) (D.family_label_raised U i)
    (D.family_label_offset U i) (D.decay U i) hh (Eventually.of_forall hpos) hp
    (Eventually.of_forall hactive)

theorem FixedMinimumData.active_omitted_upper {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (U : RaisedSupport d) (i : Fin (D.size U))
    (hnext : U.val.card + 1 < d) (j : Fin d) (hj : j ∉ U.val)
    {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q))
    (hactive : ∀ n, (D.family.atScale (h n)).Active (D.label U i)
      (exponentialPoint (h n) (p n))) : q j ≤ D.level (U.val.card + 1) := by
  let V := U.insert j hj hnext
  let k : Fin (D.size V) := ⟨0, D.size_pos V⟩
  have hcard : V.val.card = U.val.card + 1 := U.insert_card j hj hnext
  apply D.family.active_omitted_coordinate_le_of_raised_type
    (l := atTop) (h := h) (p := p) (q := q) (D.label U i)
    (seededAffineSeed D.size) (D.label V k) U.val j t (D.level U.val.card)
    (D.level (U.val.card + 1)) ((D.block U).offset i) ((D.block V).offset k)
    (D.level_desc U hnext)
    (ScaledAffineFamily.seededUnion_seed_slope t D.size D.lift)
    (ScaledAffineFamily.seededUnion_seed_offset t D.size D.lift)
    (D.family_label_outside U i) (D.family_label_raised U i)
    (D.family_label_offset U i)
  · exact D.family_label_outside V k
  · intro a
    rw [D.family_label_offset]
    simp only [hcard]
  · exact D.decay U i
  · simpa only [hcard] using D.decay V k
  · exact hh
  · exact Eventually.of_forall hpos
  · exact hp
  · exact Eventually.of_forall hactive

theorem FixedMinimumData.seed_active_upper {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (hd : 1 < d) (j : Fin d)
    {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q))
    (hactive : ∀ n, (D.family.atScale (h n)).Active (seededAffineSeed D.size)
      (exponentialPoint (h n) (p n))) : q j ≤ D.level 1 := by
  let U := RaisedSupport.singleton hd j
  let i : Fin (D.size U) := ⟨0, D.size_pos U⟩
  have hcard : U.val.card = 1 := RaisedSupport.singleton_card hd j
  apply D.family.seed_active_omitted_coordinate_le
    (l := atTop) (h := h) (p := p) (q := q) (seededAffineSeed D.size)
    (D.label U i) j t (D.level 1) ((D.block U).offset i)
    (ScaledAffineFamily.seededUnion_seed_slope t D.size D.lift)
    (ScaledAffineFamily.seededUnion_seed_offset t D.size D.lift)
  · exact D.family_label_outside U i
  · intro a
    rw [D.family_label_offset]
    simp only [hcard]
  · simpa only [hcard] using D.decay U i
  · exact hh
  · exact Eventually.of_forall hpos
  · exact hp
  · exact Eventually.of_forall hactive

theorem FixedMinimumData.block_active_limit {d : ℕ} [NeZero d]
    {t b : ℝ} {E : State d → ℝ} (D : FixedMinimumData d t b E)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (U : RaisedSupport d) (i : Fin (D.size U))
    {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q)) (hq : q ≤ fun _ => b)
    (hminimum : exponentMinimum q = t)
    (hactive : ∀ n, (D.family.atScale (h n)).Active (D.label U i)
      (exponentialPoint (h n) (p n))) :
    ‖q - D.family.slope (D.label U i)‖ < E (D.family.slope (D.label U i)) := by
  have hU := D.active_raised_limits U i hpos hh hp hactive
  have hcube : restrictCoordinates U.embedding q ∈
      Set.Icc (fun _ => D.level U.val.card) (fun _ => b) :=
    ⟨fun k => hU _ (U.embedding_mem k), fun k => hq (U.embedding k)⟩
  have hlocal : ∀ n, ((D.lift U).atScale (h n)).Active i
      (exponentialPoint (h n) (p n)) := fun n =>
    ScaledAffineFamily.seededUnion_active_in_block t D.size D.lift U i (h n) _ (hactive n)
  rw [D.family_label_slope]
  apply (D.block U).coordinateLift_active_limit_norm_lt U.embedding t
    (fun h => -(h ^ D.level U.val.card)) _ _ (D.approximation U) i hpos hh hp hcube hlocal
  intro j hj
  have hjU : j ∉ U.val := (U.mem_iff_range j).not.mpr hj
  by_cases hnext : U.val.card + 1 < d
  · exact coordinate_error_lt_of_minimum_upper hminimum (D.next_width U hnext i) j
      (D.active_omitted_upper U i hnext j hjU hpos hh hp hactive)
  · have hlast : U.val.card + 1 = d := by have := U.property.2; omega
    have heq := U.last_omitted_eq_minimum hlast hminimum
      (fun k hk => (D.level_gt U).trans_le (hU k hk)) j hjU
    rw [heq, sub_self, abs_zero]
    exact hE _ (extendCoordinates_mem_cube U.embedding
      ⟨le_rfl, (hminimum ▸ exponentMinimum_le_coordinate q j).trans (hq j)⟩
      ⟨fun k => (D.level_gt U).le.trans ((D.cube U i).1 k), (D.cube U i).2⟩)

/-- All labels of the actual union, including the seed and all ties, satisfy
the strict approximation bound on the fixed-minimum cube. -/
theorem FixedMinimumData.sequentialActivityBound {d : ℕ} [NeZero d]
    {t b : ℝ} {E : State d → ℝ} (D : FixedMinimumData d t b E) (hd : 1 < d)
    (htb : t ≤ b) (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r) :
    D.family.HasSequentialActivityBound
      (Set.Icc (fun _ => t) (fun _ => b) ∩ {q | exponentMinimum q = t})
      (fun j => E (D.family.slope j)) := by
  intro j h p q hpos hh hp hq hactive
  obtain ⟨c, i, rfl⟩ := affineBlockLabel_surjective (seededAffineSizes D.size) j
  cases c with
  | none =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change ‖q - D.family.slope (seededAffineSeed D.size)‖ <
      E (D.family.slope (seededAffineSeed D.size))
    rw [FixedMinimumData.family, ScaledAffineFamily.seededUnion_seed_slope]
    rw [pi_norm_lt_iff (hE _ ⟨fun _ => le_rfl, fun _ => htb⟩)]
    intro k
    change |q k - t| < E (fun _ => t)
    exact coordinate_error_lt_of_minimum_upper hq.2 D.seed_width k
      (D.seed_active_upper hd k hpos hh hp hactive)
  | some U => exact D.block_active_limit hE U i hpos hh hp hq.1.2 hq.2 hactive

theorem FixedMinimumData.slopes_mem_cube {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) (htb : t ≤ b) :
    ∀ j, D.family.slope j ∈ Set.Icc (fun _ => t) (fun _ => b) := by
  apply ScaledAffineFamily.seededUnion_slopes_mem_cube D.size D.lift ⟨le_rfl, htb⟩
  intro U i
  exact extendCoordinates_mem_cube U.embedding ⟨le_rfl, htb⟩
    ⟨fun k => (D.level_gt U).le.trans ((D.cube U i).1 k), (D.cube U i).2⟩

theorem FixedMinimumData.offsets_isLittleO {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) :
    ∀ j, IsLittleO (𝓝[>] (0 : ℝ)) (D.family.offset j) (fun h => h ^ t) := by
  apply ScaledAffineFamily.seededUnion_offsets_isLittleO t D.size D.lift
  intro U i
  exact offset_isLittleO_of_powerBound (shifted_power_offset_isBigO (D.decay U i))
    (D.level_gt U)

theorem FixedMinimumData.slopes_minimum {d : ℕ} [NeZero d]
    {t b : ℝ} {E : State d → ℝ} (D : FixedMinimumData d t b E) :
    ∀ j, exponentMinimum (D.family.slope j) = t := by
  intro j
  obtain ⟨c, i, rfl⟩ := affineBlockLabel_surjective (seededAffineSizes D.size) j
  cases c with
  | none =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change exponentMinimum (D.family.slope (seededAffineSeed D.size)) = t
    rw [FixedMinimumData.family, ScaledAffineFamily.seededUnion_seed_slope]
    obtain ⟨k, hk⟩ := exponentMinimum_attained (fun _ : Fin d => t)
    exact hk
  | some U =>
    change exponentMinimum (D.family.slope (D.label U i)) = t
    rw [D.family_label_slope]
    obtain ⟨k, hk⟩ := U.omitted_exists
    exact extendCoordinates_minimum U.embedding t _
      (fun l => (D.level_gt U).le.trans ((D.cube U i).1 l)) k
      ((U.mem_iff_range k).not.mp hk)

/-- The original cube may start below t. The minimum condition supplies the
lower bound t on the limit; approaching vectors remain unrestricted. -/
theorem FixedMinimumData.sequentialActivityBound_on_cube {d : ℕ} [NeZero d]
    {t b : ℝ} {E : State d → ℝ} (D : FixedMinimumData d t b E) (a : ℝ) (hd : 1 < d)
    (htb : t ≤ b) (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r) :
    D.family.HasSequentialActivityBound
      (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = t})
      (fun j => E (D.family.slope j)) := by
  apply D.family.sequentialActivityBound_mono (D.sequentialActivityBound hd htb hE)
  intro q hq
  exact ⟨⟨fun j => hq.2 ▸ exponentMinimum_le_coordinate q j, hq.1.2⟩, hq.2⟩

theorem FixedMinimumData.offset_power_bounds {d : ℕ} {t b : ℝ} {E : State d → ℝ}
    (D : FixedMinimumData d t b E) :
    ∀ j, ∃ β : ℝ, t < β ∧ IsBigO (𝓝[>] (0 : ℝ)) (D.family.offset j)
      (fun h => h ^ β) := by
  intro j
  obtain ⟨c, i, rfl⟩ := affineBlockLabel_surjective (seededAffineSizes D.size) j
  cases c with
  | none =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    refine ⟨t + 1, by linarith, ?_⟩
    have hz : D.family.offset (seededAffineSeed D.size) = fun _ => 0 :=
      funext (ScaledAffineFamily.seededUnion_seed_offset t D.size D.lift)
    change IsBigO _ (D.family.offset (seededAffineSeed D.size)) _
    rw [hz]
    exact isBigO_zero _ _
  | some U =>
    refine ⟨D.level U.val.card, D.level_gt U, ?_⟩
    have heq : D.family.offset (D.label U i) =
        fun h => -(h ^ D.level U.val.card) + (D.block U).offset i h :=
      funext (D.family_label_offset U i)
    change IsBigO _ (D.family.offset (D.label U i)) _
    rw [heq]
    exact shifted_power_offset_isBigO (D.decay U i)

/-- The same all-support family works on a nearby closed minimum band and
its offsets decay at the improved exponent t+ρ, for one positive ρ. -/
theorem FixedMinimumData.near_minimum_with_decay {d : ℕ} [NeZero d]
    {t b : ℝ} {E : State d → ℝ} (D : FixedMinimumData d t b E) (a : ℝ) (hd : 1 < d)
    (htb : t ≤ b) (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (D.family.offset i) (fun h => h ^ (t + ρ))) ∧
      D.family.HasSequentialActivityBound
        (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | |exponentMinimum q - t| ≤ ρ})
        (fun j => E (D.family.slope j)) := by
  choose β hβ hc using D.offset_power_bounds
  exact D.family.sequentialActivityBound_near_minimum_with_decay a b _ t
    (D.sequentialActivityBound_on_cube a hd htb hE) β hβ hc

theorem FixedMinimumData.uniformActivityBound_near_minimum {d : ℕ} [NeZero d]
    {t b : ℝ} {E : State d → ℝ} (D : FixedMinimumData d t b E) (hd : 1 < d)
    (htb : t ≤ b) (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => t) (fun _ => b), |exponentMinimum q - t| ≤ ρ →
          ∀ i, (D.family.atScale h).Active i (exponentialPoint h q) →
            ‖q - D.family.slope i‖ < E (D.family.slope i) :=
  D.family.uniformActivityBound_near_minimum t b _ t (D.sequentialActivityBound hd htb hE)

end Endotactic
end

-- Source: Endotactic/AffineInductionData.lean
section
/-!
# Dimension-wise induction and finite staged support data

Unselected entries are harmless seed placeholders. Every entry has an ambient
cube slope, but only selected ranks have the lower-dimensional approximation.
Choosing a level after the finite entries prevents a circular tolerance choice.
-/

namespace Endotactic

open Filter Topology Asymptotics

def AffineApproximationInDimension (d : ℕ) : Prop :=
  ∀ a b : ℝ, a < b → ∀ E : State d → ℝ,
    (∀ p ∈ Set.Icc (fun _ => a) (fun _ => b), 0 < E p) →
      ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily d m,
        (∀ i, A.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) ∧
        (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) ∧
        A.HasSequentialActivityBound (Set.Icc (fun _ => a) (fun _ => b))
          (fun i => E (A.slope i))

theorem finiteAffineApproximation_iff_dimensions : FiniteAffineApproximationStatement ↔
    ∀ d : ℕ, 0 < d → AffineApproximationInDimension d := Iff.rfl

abbrev SupportAffineEntry {d : ℕ} (U : RaisedSupport d) :=
  Σ m : ℕ, ScaledAffineFamily U.val.card m

def SupportAffineEntry.Valid {d : ℕ} (t b : ℝ) (E : State d → ℝ)
    (U : RaisedSupport d) (β : ℝ) (C : SupportAffineEntry U) : Prop :=
  (∀ i, C.2.slope i ∈ Set.Icc (fun _ => β) (fun _ => b)) ∧
  (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (C.2.offset i) (fun h => h ^ β)) ∧
  C.2.HasSequentialActivityBound (Set.Icc (fun _ => β) (fun _ => b))
    (fun i => E (extendCoordinates U.embedding t (C.2.slope i)))

theorem exists_support_entry_of_lower_dimensions {d : ℕ} {t β b : ℝ}
    (E : State d → ℝ) (htβ : t < β) (hβb : β < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hIH : ∀ k : ℕ, 0 < k → k < d → AffineApproximationInDimension k)
    (U : RaisedSupport d) :
    ∃ C : SupportAffineEntry U, 0 < C.1 ∧ C.Valid t b E U β := by
  have htol : ∀ r ∈ Set.Icc (fun _ : Fin U.val.card => β) (fun _ => b),
      0 < E (extendCoordinates U.embedding t r) := by
    intro r hr
    exact hE _ (extendCoordinates_mem_cube U.embedding ⟨le_rfl, htβ.le.trans hβb.le⟩
      ⟨fun j => htβ.le.trans (hr.1 j), hr.2⟩)
  obtain ⟨m, hm, B, hc, ho, ha⟩ := hIH U.val.card U.property.1 U.property.2
    β b hβb (fun r => E (extendCoordinates U.embedding t r)) htol
  exact ⟨⟨m, B⟩, hm, hc, ho, ha⟩

/-- A reaction-specific or known-answer route may supply just these support
families for the actual pullback of E, instead of the universal lower theorem. -/
def SupportFamilyOracle (d : ℕ) (t b : ℝ) (E : State d → ℝ) : Prop :=
  ∀ U : RaisedSupport d, ∀ β : ℝ, t < β → β < b →
    ∃ C : SupportAffineEntry U, 0 < C.1 ∧ C.Valid t b E U β

theorem supportFamilyOracle_of_lower_dimensions {d : ℕ} {t b : ℝ}
    (E : State d → ℝ)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hIH : ∀ k : ℕ, 0 < k → k < d → AffineApproximationInDimension k) :
    SupportFamilyOracle d t b E := by
  intro U β htβ hβb
  exact exists_support_entry_of_lower_dimensions E htβ hβb hE hIH U

structure AffineSupportPrefix (d : ℕ) (t b : ℝ) (E : State d → ℝ) (k : ℕ) where
  entry : ∀ U : RaisedSupport d, SupportAffineEntry U
  size_pos : ∀ U, 0 < (entry U).1
  ambient_cube : ∀ U i, extendCoordinates U.embedding t ((entry U).2.slope i) ∈
    Set.Icc (fun _ => t) (fun _ => b)
  level : ℕ → ℝ
  level_bounds : ∀ n, 1 ≤ n → n ≤ k → t < level n ∧ level n < b
  descending : ∀ n, 1 ≤ n → n + 1 ≤ k → level (n + 1) < level n
  selected : ∀ U : RaisedSupport d, U.val.card ≤ k →
    (entry U).Valid t b E U (level U.val.card)
  seed_width : 1 ≤ k → level 1 - t < E (fun _ => t)
  next_width : ∀ U : RaisedSupport d, U.val.card + 1 ≤ k → ∀ i,
    level (U.val.card + 1) - t <
      E (extendCoordinates U.embedding t ((entry U).2.slope i))

noncomputable def AffineSupportPrefix.initial {d : ℕ} {t b : ℝ}
    (E : State d → ℝ) (htb : t ≤ b) : AffineSupportPrefix d t b E 0 where
  entry U := ⟨1, minimumSeedFamily U.val.card t⟩
  size_pos _ := by norm_num
  ambient_cube U _ := extendCoordinates_mem_cube U.embedding ⟨le_rfl, htb⟩
    ⟨fun _ => le_rfl, fun _ => htb⟩
  level _ := b
  level_bounds _ hpos hzero := by omega
  descending _ hpos hzero := by omega
  selected U hzero := by have := U.property.1; omega
  seed_width hzero := by omega
  next_width _ hzero := by omega

/-- One level works for the seed and all finite stored slopes. It is chosen
before the next rank's lower-dimensional families, with no regularity of E. -/
theorem AffineSupportPrefix.exists_next_level {d k : ℕ} {t b : ℝ} {E : State d → ℝ}
    (P : AffineSupportPrefix d t b E k) (htb : t < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r) :
    ∃ β : ℝ, t < β ∧ β < b ∧ (0 < k → β < P.level k) ∧
      β - t < E (fun _ => t) ∧ ∀ U i,
        β - t < E (extendCoordinates U.embedding t ((P.entry U).2.slope i)) := by
  classical
  let I := Σ U : RaisedSupport d, Fin (P.entry U).1
  let ε : Option I → ℝ
    | none => E (fun _ => t)
    | some l => E (extendCoordinates l.1.embedding t ((P.entry l.1).2.slope l.2))
  have hε : ∀ i, 0 < ε i := by
    intro i
    cases i with
    | none => exact hE _ ⟨fun _ => le_rfl, fun _ => htb.le⟩
    | some l => exact hE _ (P.ambient_cube l.1 l.2)
  let R := if k = 0 then b else P.level k
  have htR : t < R := by
    by_cases hk : k = 0
    · simpa [R, hk] using htb
    · simpa [R, hk] using (P.level_bounds k (by omega) le_rfl).1
  obtain ⟨δ, hδ, hδR, hδε⟩ := exists_common_positive_width ε hε (sub_pos.mpr htR)
  refine ⟨t + δ, by linarith, ?_, ?_, ?_, ?_⟩
  · by_cases hk : k = 0
    · simp only [R, ite_eq_left hk] at hδR
      linarith
    · have hb := (P.level_bounds k (by omega) le_rfl).2
      simp only [R, ite_eq_right hk] at hδR
      linarith
  · intro hk
    have hk0 : k ≠ 0 := by omega
    simp only [R, ite_eq_right hk0] at hδR
    linarith
  · simpa [ε] using hδε none
  · intro U i
    simpa [ε] using hδε (some ⟨U, i⟩)

end Endotactic
end

-- Source: Endotactic/AffineSupportInduction.lean
section
/-!
# Successive choices construct all fixed-minimum support data

The lower-dimensional affine theorem is a strong induction hypothesis. The
next level is chosen from already fixed finite slopes before its new families.
Only the next support rank is replaced; previous families remain unchanged.
This closes data existence conditional on lower dimensions, not the full A.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem AffineSupportPrefix.exists_successor_of_oracle {d k : ℕ} {t b : ℝ} {E : State d → ℝ}
    (P : AffineSupportPrefix d t b E k) (htb : t < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hOracle : SupportFamilyOracle d t b E) :
    Nonempty (AffineSupportPrefix d t b E (k + 1)) := by
  classical
  obtain ⟨β, htβ, hβb, hβprev, hseed, hwidth⟩ := P.exists_next_level htb hE
  have hnew : ∀ U : RaisedSupport d, ∃ C : SupportAffineEntry U,
      0 < C.1 ∧ C.Valid t b E U β :=
    fun U => hOracle U β htβ hβb
  choose C hCpos hCvalid using hnew
  let entries := fun U : RaisedSupport d => if U.val.card = k + 1 then C U else P.entry U
  let levels := Function.update P.level (k + 1) β
  refine ⟨{ entry := entries
            level := levels
            size_pos := ?_
            ambient_cube := ?_
            level_bounds := ?_
            descending := ?_
            selected := ?_
            seed_width := ?_
            next_width := ?_ }⟩
  · intro U
    by_cases hc : U.val.card = k + 1
    · simpa only [entries, ite_eq_left hc] using hCpos U
    · simpa only [entries, ite_eq_right hc] using P.size_pos U
  · intro U
    by_cases hc : U.val.card = k + 1
    · have he : entries U = C U := ite_eq_left hc
      rw [he]
      intro i
      exact extendCoordinates_mem_cube U.embedding ⟨le_rfl, htb.le⟩
        ⟨fun j => htβ.le.trans (((hCvalid U).1 i).1 j), ((hCvalid U).1 i).2⟩
    · have he : entries U = P.entry U := ite_eq_right hc
      rw [he]
      exact P.ambient_cube U
  · intro n hn hnk
    by_cases heq : n = k + 1
    · simpa only [levels, heq, Function.update_self] using And.intro htβ hβb
    · simpa only [levels, Function.update_of_ne heq] using P.level_bounds n hn (by omega)
  · intro n hn hnk
    have hnne : n ≠ k + 1 := by omega
    by_cases heq : n + 1 = k + 1
    · have hnk' : n = k := by omega
      have hlt : β < P.level n := by simpa only [hnk'] using hβprev (by omega)
      simpa only [levels, heq, Function.update_self, Function.update_of_ne hnne] using hlt
    · simpa only [levels, Function.update_of_ne heq, Function.update_of_ne hnne] using
        P.descending n hn (by omega)
  · intro U hk
    by_cases hc : U.val.card = k + 1
    · simpa only [entries, ite_eq_left hc, levels, hc, Function.update_self] using hCvalid U
    · simpa only [entries, ite_eq_right hc, levels, Function.update_of_ne hc] using
        P.selected U (by omega)
  · intro _
    by_cases hk : k = 0
    · subst k
      simpa only [levels, zero_add, Function.update_self] using hseed
    · have hne : 1 ≠ k + 1 := by omega
      simpa only [levels, Function.update_of_ne hne] using P.seed_width (by omega)
  · intro U hk
    have hc : U.val.card ≠ k + 1 := by omega
    have he : entries U = P.entry U := ite_eq_right hc
    rw [he]
    by_cases heq : U.val.card + 1 = k + 1
    · simpa only [levels, heq, Function.update_self] using hwidth U
    · simpa only [levels, Function.update_of_ne heq] using
        P.next_width U (by omega)

theorem AffineSupportPrefix.exists_successor {d k : ℕ} {t b : ℝ} {E : State d → ℝ}
    (P : AffineSupportPrefix d t b E k) (htb : t < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hIH : ∀ n : ℕ, 0 < n → n < d → AffineApproximationInDimension n) :
    Nonempty (AffineSupportPrefix d t b E (k + 1)) :=
  P.exists_successor_of_oracle htb hE (supportFamilyOracle_of_lower_dimensions E hE hIH)

theorem exists_affineSupportPrefix_of_oracle {d : ℕ} {t b : ℝ}
    (E : State d → ℝ) (htb : t < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hOracle : SupportFamilyOracle d t b E) (k : ℕ) :
    Nonempty (AffineSupportPrefix d t b E k) := by
  induction k with
  | zero => exact ⟨AffineSupportPrefix.initial E htb.le⟩
  | succ k ih =>
    obtain ⟨P⟩ := ih
    exact P.exists_successor_of_oracle htb hE hOracle

theorem exists_affineSupportPrefix {d : ℕ} {t b : ℝ} (E : State d → ℝ) (htb : t < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hIH : ∀ n : ℕ, 0 < n → n < d → AffineApproximationInDimension n) (k : ℕ) :
    Nonempty (AffineSupportPrefix d t b E k) :=
  exists_affineSupportPrefix_of_oracle E htb hE
    (supportFamilyOracle_of_lower_dimensions E hE hIH) k

noncomputable def AffineSupportPrefix.toFixedMinimumData {d : ℕ} {t b : ℝ}
    {E : State d → ℝ} (P : AffineSupportPrefix d t b E (d - 1)) (hd : 1 < d) :
    FixedMinimumData d t b E where
  size U := (P.entry U).1
  size_pos := P.size_pos
  block U := (P.entry U).2
  level := P.level
  level_gt U := (P.level_bounds U.val.card U.property.1 (by have := U.property.2; omega)).1
  level_desc U hn := P.descending U.val.card U.property.1 (by omega)
  cube U := (P.selected U (by have := U.property.2; omega)).1
  decay U := (P.selected U (by have := U.property.2; omega)).2.1
  approximation U := (P.selected U (by have := U.property.2; omega)).2.2
  seed_width := P.seed_width (by omega)
  next_width U hn := P.next_width U (by omega)

/-- The supplied-data hypothesis of the assembly theorem is now constructed
from the lower-dimensional induction hypothesis, for arbitrary preselected E. -/
theorem exists_fixedMinimumData_of_oracle {d : ℕ} {t b : ℝ}
    (E : State d → ℝ) (hd : 1 < d) (htb : t < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hOracle : SupportFamilyOracle d t b E) :
    Nonempty (FixedMinimumData d t b E) := by
  obtain ⟨P⟩ := exists_affineSupportPrefix_of_oracle E htb hE hOracle (d - 1)
  exact ⟨P.toFixedMinimumData hd⟩

theorem exists_fixedMinimumData_of_lower_dimensions {d : ℕ} {t b : ℝ}
    (E : State d → ℝ) (hd : 1 < d) (htb : t < b)
    (hE : ∀ r ∈ Set.Icc (fun _ => t) (fun _ => b), 0 < E r)
    (hIH : ∀ n : ℕ, 0 < n → n < d → AffineApproximationInDimension n) :
    Nonempty (FixedMinimumData d t b E) :=
  exists_fixedMinimumData_of_oracle E hd htb hE (supportFamilyOracle_of_lower_dimensions E hE hIH)

end Endotactic
end

-- Source: Endotactic/FixedMinimumExistence.lean
section
/-!
# Fixed-minimum families exist under the lower-dimensional induction hypothesis

Dimension one and the cube's top use the actual seed. The other cases now
construct every block and level, rather than accepting FixedMinimumData as an
input. This module retains minimum combination as an explicit input;
`MinimumBandSelection` supplies its proof downstream and closes full A.
-/

namespace Endotactic

open Filter Topology Asymptotics

structure FixedMinimumApproximation (d : ℕ) [NeZero d] (a b t : ℝ) (E : State d → ℝ) where
  size : ℕ
  size_pos : 0 < size
  family : ScaledAffineFamily d size
  seed : Fin size
  seed_slope : family.slope seed = fun _ => t
  seed_offset : ∀ h, family.offset seed h = 0
  cube : ∀ i, family.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)
  minimum : ∀ i, exponentMinimum (family.slope i) = t
  power_bound : ∀ i, ∃ β : ℝ, t < β ∧
    IsBigO (𝓝[>] (0 : ℝ)) (family.offset i) (fun h => h ^ β)
  approximation : family.HasSequentialActivityBound
    (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | exponentMinimum q = t})
    (fun i => E (family.slope i))

theorem exists_seed_fixedMinimumApproximation {d : ℕ} [NeZero d]
    {a b t : ℝ} (E : State d → ℝ) (ht : t ∈ Set.Icc a b)
    (hE : ∀ r ∈ Set.Icc (fun _ => a) (fun _ => b), 0 < E r)
    (hcase : d = 1 ∨ t = b) : Nonempty (FixedMinimumApproximation d a b t E) := by
  have htol : 0 < E (fun _ => t) := hE _ ⟨fun _ => ht.1, fun _ => ht.2⟩
  refine ⟨{ size := 1
            size_pos := by norm_num
            family := minimumSeedFamily d t
            seed := 0
            seed_slope := rfl
            seed_offset := fun _ => rfl
            cube := fun _ => ⟨fun _ => ht.1, fun _ => ht.2⟩
            minimum := ?_
            power_bound := ?_
            approximation := ?_ }⟩
  · intro i
    obtain ⟨j, hj⟩ := exponentMinimum_attained (fun _ : Fin d => t)
    exact hj
  · intro i
    refine ⟨t + 1, by linarith, ?_⟩
    exact isBigO_zero _ _
  · rcases hcase with hd | htop
    · subst d
      exact minimumSeedFamily_oneDim_fixedMinimum a b t htol
    · subst t
      exact minimumSeedFamily_top_fixedMinimum a b htol

theorem exists_fixedMinimumApproximation_of_lower_dimensions {d : ℕ} [NeZero d]
    {a b : ℝ} (E : State d → ℝ)
    (hE : ∀ r ∈ Set.Icc (fun _ => a) (fun _ => b), 0 < E r)
    (hIH : ∀ n : ℕ, 0 < n → n < d → AffineApproximationInDimension n)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    Nonempty (FixedMinimumApproximation d a b t E) := by
  by_cases hcase : d = 1 ∨ t = b
  · exact exists_seed_fixedMinimumApproximation E ht hE hcase
  · have hd0 : d ≠ 0 := NeZero.ne d
    have hd : 1 < d := by omega
    have htb : t < b := lt_of_le_of_ne ht.2 (fun heq => hcase (Or.inr heq))
    have hEt : ∀ r ∈ Set.Icc (fun _ : Fin d => t) (fun _ => b), 0 < E r := by
      intro r hr
      exact hE r ⟨fun j => ht.1.trans (hr.1 j), hr.2⟩
    obtain ⟨D⟩ := exists_fixedMinimumData_of_lower_dimensions E hd htb hEt hIH
    exact ⟨{ size := _
             size_pos := seededAffine_card_pos D.size
             family := D.family
             seed := seededAffineSeed D.size
             seed_slope := ScaledAffineFamily.seededUnion_seed_slope t D.size D.lift
             seed_offset := ScaledAffineFamily.seededUnion_seed_offset t D.size D.lift
             cube := fun i => ⟨fun j => ht.1.trans ((D.slopes_mem_cube htb.le i).1 j),
               (D.slopes_mem_cube htb.le i).2⟩
             minimum := D.slopes_minimum
             power_bound := D.offset_power_bounds
             approximation := D.sequentialActivityBound_on_cube a hd htb.le hEt }⟩

theorem FixedMinimumApproximation.offsets_isLittleO {d : ℕ} [NeZero d]
    {a b t : ℝ} {E : State d → ℝ} (D : FixedMinimumApproximation d a b t E) :
    ∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (D.family.offset i) (fun h => h ^ t) := by
  intro i
  obtain ⟨β, htβ, hc⟩ := D.power_bound i
  exact offset_isLittleO_of_powerBound hc htβ

theorem FixedMinimumApproximation.near_minimum_with_decay {d : ℕ} [NeZero d]
    {a b t : ℝ} {E : State d → ℝ} (D : FixedMinimumApproximation d a b t E) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (D.family.offset i) (fun h => h ^ (t + ρ))) ∧
      D.family.HasSequentialActivityBound
        (Set.Icc (fun _ => a) (fun _ => b) ∩ {q | |exponentMinimum q - t| ≤ ρ})
        (fun i => E (D.family.slope i)) := by
  choose β hβ hc using D.power_bound
  exact D.family.sequentialActivityBound_near_minimum_with_decay a b _ t
    D.approximation β hβ hc

theorem FixedMinimumApproximation.uniform_near_minimum {d : ℕ} [NeZero d]
    {a b t : ℝ} {E : State d → ℝ} (D : FixedMinimumApproximation d a b t E) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ q ∈ Set.Icc (fun _ => a) (fun _ => b), |exponentMinimum q - t| ≤ ρ →
          ∀ i, (D.family.atScale h).Active i (exponentialPoint h q) →
            ‖q - D.family.slope i‖ < E (D.family.slope i) :=
  D.family.uniformActivityBound_near_minimum a b _ t D.approximation

def FixedMinimumApproximationInDimension (d : ℕ) [NeZero d] : Prop :=
  ∀ a b : ℝ, a < b → ∀ E : State d → ℝ,
    (∀ p ∈ Set.Icc (fun _ => a) (fun _ => b), 0 < E p) →
      ∀ t ∈ Set.Icc a b, Nonempty (FixedMinimumApproximation d a b t E)

theorem fixedMinimumApproximation_of_lower_dimensions {d : ℕ} [NeZero d]
    (hIH : ∀ n : ℕ, 0 < n → n < d → AffineApproximationInDimension n) :
    FixedMinimumApproximationInDimension d := by
  intro a b _ E hE t ht
  exact exists_fixedMinimumApproximation_of_lower_dimensions E hE hIH t ht

/-- The global combination type retains all active labels at interval cuts.
It is proved downstream by `affineMinimumCombination`; it is not an axiom. -/
def AffineMinimumCombinationStatement : Prop :=
  ∀ d : ℕ, ∀ (_ : NeZero d), FixedMinimumApproximationInDimension d →
    AffineApproximationInDimension d

/-- Strong induction is closed once the minimum-combination theorem is
provided. The generic combination hypothesis is explicit in this type, and
`MinimumBandSelection` supplies it downstream without additional assumptions. -/
theorem finiteAffineApproximation_of_minimumCombination
    (hcombine : AffineMinimumCombinationStatement) : FiniteAffineApproximationStatement := by
  apply finiteAffineApproximation_iff_dimensions.mpr
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    let : NeZero d := ⟨by omega⟩
    exact hcombine d inferInstance (fixedMinimumApproximation_of_lower_dimensions
      (fun n hn hnd => ih n hnd hn))

end Endotactic
end

-- Source: Endotactic/AffineOffsetShift.lean
section
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
end

-- Source: Endotactic/AffineShiftComparisons.lean
section
/-!
# Adjacent shifted seeds confine the limiting minimum

These comparisons are with labels in the actual global family. The lower
bound uses positive slope differences; the upper bound uses moving powers.
Both conclusions are non-strict, so cut ties remain valid labels.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem ScaledAffineFamily.active_minimum_le_of_next_seed
    {d m : ℕ} [NeZero d] {I : Type*} {l : Filter I} [l.NeBot]
    (A : ScaledAffineFamily d m) (i seed : Fin m) (s β : ℝ) (γ c : ℝ → ℝ)
    (hseed : A.slope seed = fun _ => s)
    (hoffset : ∀ h, A.offset i h = γ h + c h)
    (hseedoffset : ∀ h, A.offset seed h = γ h - h ^ β)
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q))
    (hactive : ∀ᶠ x in l, (A.atScale (h x)).Active i (exponentialPoint (h x) (p x))) :
    exponentMinimum q ≤ β := by
  classical
  by_contra hbad
  have hgap : β < exponentMinimum q := lt_of_not_ge hbad
  have hsum := moving_weighted_power_sum_isLittleO Finset.univ
    (fun j => A.slope i j - s) hh hpos
    (fun j _ => (continuous_apply j).tendsto q |>.comp hp)
    (fun j _ => hgap.trans_le (exponentMinimum_le_coordinate q j))
  have hrem := hsum.add (offset_isLittleO_along_scales hc hh hpos)
  have hbeat := zero_label_beaten_by_negative_power hpos hrem.neg_left
  obtain ⟨x, hx, hbx⟩ := (hactive.and hbeat).exists
  have hs := hx seed
  simp only [ScaledAffineFamily.atScale_value, hseed, hoffset, hseedoffset] at hs
  have heq := dot_exponential_increment_on_coordinates (A.slope i) s (h x) (p x)
    Finset.univ (by simp)
  simp only [Function.comp_apply] at hbx
  linarith

theorem ScaledAffineFamily.active_minimum_ge_of_previous_seed
    {d m : ℕ} [NeZero d] {I : Type*} {l : Filter I} [l.NeBot]
    (A : ScaledAffineFamily d m) (i seed : Fin m) (s β : ℝ) (γ c : ℝ → ℝ)
    (hseed : A.slope seed = fun _ => s) (hraised : ∀ j, s < A.slope i j)
    (hoffset : ∀ h, A.offset i h = γ h - h ^ β + c h)
    (hseedoffset : ∀ h, A.offset seed h = γ h)
    (hc : IsLittleO (𝓝[>] (0 : ℝ)) c (fun h => h ^ β))
    {h : I → ℝ} {p : I → State d} {q : State d}
    (hh : Tendsto h l (𝓝 0)) (hpos : ∀ᶠ x in l, 0 < h x)
    (hp : Tendsto p l (𝓝 q))
    (hactive : ∀ᶠ x in l, (A.atScale (h x)).Active i (exponentialPoint (h x) (p x))) :
    β ≤ exponentMinimum q := by
  classical
  have hcoords : ∀ j ∈ (Finset.univ : Finset (Fin d)), β ≤ q j := by
    apply raised_coordinate_limits_ge_of_sum_bound Finset.univ (fun j => A.slope i j - s)
      hh hpos (fun j _ => sub_pos.mpr (hraised j))
      (fun j _ => (continuous_apply j).tendsto q |>.comp hp)
      (offset_isLittleO_along_scales hc hh hpos)
    filter_upwards [hactive] with x hx
    have hs := hx seed
    simp only [ScaledAffineFamily.atScale_value, hseed, hoffset, hseedoffset] at hs
    have heq := dot_exponential_increment_on_coordinates (A.slope i) s (h x) (p x)
      Finset.univ (by simp)
    simp only [Function.comp_apply]
    linarith
  obtain ⟨j, hj⟩ := exponentMinimum_attained q
  rw [hj]
  exact hcoords j (Finset.mem_univ j)

end Endotactic
end

-- Source: Endotactic/MinimumShiftChain.lean
section
/-!
# Global assembly from a finite ordered minimum-band certificate

The input specifies local families, radii and interleaving cuts. It does not
assume the desired global activity conclusion. Prefix shifts and actual
adjacent seeds prove that conclusion, retaining every boundary tie. Existence
of an ordered certificate from arbitrary local neighborhoods is proved
downstream by `MinimumBandSelection`.
-/

namespace Endotactic

open Filter Topology Asymptotics

structure MinimumShiftChain (d n : ℕ) [NeZero d] (a b : ℝ) (E : State d → ℝ) where
  center : Fin (n + 1) → ℝ
  center_mem : ∀ j, center j ∈ Set.Icc a b
  block : ∀ j, FixedMinimumApproximation d a b (center j) E
  radius : Fin (n + 1) → ℝ
  radius_pos : ∀ j, 0 < radius j
  cut : ℕ → ℝ
  cut_between : ∀ k (hk : k < n),
    center ⟨k, by omega⟩ < cut k ∧ cut k < center ⟨k + 1, by omega⟩
  band_left : ∀ j, center j - radius j ≤ if j.val = 0 then a else cut (j.val - 1)
  band_right : ∀ j, (if j.val = n then b else cut j.val) ≤ center j + radius j
  decay : ∀ j i, IsLittleO (𝓝[>] (0 : ℝ)) ((block j).family.offset i)
    (fun h => h ^ (center j + radius j))
  approximation : ∀ j, (block j).family.HasSequentialActivityBound
    (Set.Icc (fun _ => a) (fun _ => b) ∩
      {q | |exponentMinimum q - center j| ≤ radius j})
    (fun i => E ((block j).family.slope i))

abbrev MinimumShiftChain.size {d n : ℕ} [NeZero d] {a b : ℝ} {E : State d → ℝ}
    (D : MinimumShiftChain d n a b E) (j : Fin (n + 1)) := (D.block j).size

noncomputable def MinimumShiftChain.shiftedBlock {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E) (j : Fin (n + 1)) :=
  (D.block j).family.offsetShift (powerPrefixShift D.cut j.val)

noncomputable def MinimumShiftChain.family {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E) :=
  ScaledAffineFamily.blockUnion D.size D.shiftedBlock

noncomputable def MinimumShiftChain.label {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E)
    (j : Fin (n + 1)) (i : Fin (D.size j)) := affineBlockLabel D.size j i

theorem MinimumShiftChain.family_label_slope {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E)
    (j : Fin (n + 1)) (i : Fin (D.size j)) :
    D.family.slope (D.label j i) = (D.block j).family.slope i :=
  ScaledAffineFamily.blockUnion_slope D.size D.shiftedBlock j i

theorem MinimumShiftChain.family_label_offset {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E)
    (j : Fin (n + 1)) (i : Fin (D.size j)) (h : ℝ) :
    D.family.offset (D.label j i) h =
      powerPrefixShift D.cut j.val h + (D.block j).family.offset i h :=
  ScaledAffineFamily.blockUnion_offset D.size D.shiftedBlock j i h

theorem MinimumShiftChain.active_in_block {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E)
    (j : Fin (n + 1)) (i : Fin (D.size j)) (h : ℝ) (x : State d)
    (hi : (D.family.atScale h).Active (D.label j i) x) :
    ((D.block j).family.atScale h).Active i x := by
  exact ((D.block j).family.offsetShift_active_iff _ i h x).mp
    (ScaledAffineFamily.blockUnion_active_in_block D.size D.shiftedBlock j i h x hi)

theorem MinimumShiftChain.active_minimum_upper {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E)
    (j : Fin (n + 1)) (i : Fin (D.size j)) (hj : j.val < n)
    {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ k, 0 < h k) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q))
    (hactive : ∀ k, (D.family.atScale (h k)).Active (D.label j i)
      (exponentialPoint (h k) (p k))) : exponentMinimum q ≤ D.cut j.val := by
  let next : Fin (n + 1) := ⟨j.val + 1, by omega⟩
  apply D.family.active_minimum_le_of_next_seed (D.label j i)
    (D.label next (D.block next).seed) (D.center next) (D.cut j.val)
    (powerPrefixShift D.cut j.val) ((D.block j).family.offset i)
    _ _ _ _ hh (Eventually.of_forall hpos) hp (Eventually.of_forall hactive)
  · rw [D.family_label_slope, (D.block next).seed_slope]
  · exact D.family_label_offset j i
  · intro h
    rw [D.family_label_offset, (D.block next).seed_offset, add_zero]
    exact powerPrefixShift_succ D.cut j.val h
  · apply offset_isLittleO_of_le_power (D.decay j i)
    have hb := D.band_right j
    rw [ite_eq_right (by omega : j.val ≠ n)] at hb
    exact hb

theorem MinimumShiftChain.active_minimum_lower {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E)
    (j : Fin (n + 1)) (i : Fin (D.size j)) (hj : 0 < j.val)
    {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ k, 0 < h k) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q))
    (hactive : ∀ k, (D.family.atScale (h k)).Active (D.label j i)
      (exponentialPoint (h k) (p k))) : D.cut (j.val - 1) ≤ exponentMinimum q := by
  let prev : Fin (n + 1) := ⟨j.val - 1, by omega⟩
  have hcut := D.cut_between (j.val - 1) (by omega)
  have hpred : j.val - 1 + 1 = j.val := by omega
  have hcenter : D.center prev < D.cut (j.val - 1) ∧
      D.cut (j.val - 1) < D.center j := by
    simpa only [hpred] using hcut
  apply D.family.active_minimum_ge_of_previous_seed (D.label j i)
    (D.label prev (D.block prev).seed) (D.center prev) (D.cut (j.val - 1))
    (powerPrefixShift D.cut (j.val - 1)) ((D.block j).family.offset i)
    _ _ _ _ _ hh (Eventually.of_forall hpos) hp (Eventually.of_forall hactive)
  · rw [D.family_label_slope, (D.block prev).seed_slope]
  · intro k
    rw [D.family_label_slope]
    have hm := exponentMinimum_le_coordinate ((D.block j).family.slope i) k
    rw [(D.block j).minimum i] at hm
    exact (hcenter.1.trans hcenter.2).trans_le hm
  · intro h
    rw [D.family_label_offset]
    have hs := powerPrefixShift_succ D.cut (j.val - 1) h
    rw [hpred] at hs
    rw [hs]
  · intro h
    rw [D.family_label_offset, (D.block prev).seed_offset, add_zero]
  · exact offset_isLittleO_of_le_power (D.decay j i)
      (hcenter.2.le.trans (le_add_of_nonneg_right (D.radius_pos j).le))

theorem MinimumShiftChain.active_limit_in_band {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E)
    (j : Fin (n + 1)) (i : Fin (D.size j))
    {h : ℕ → ℝ} {p : ℕ → State d} {q : State d}
    (hpos : ∀ k, 0 < h k) (hh : Tendsto h atTop (𝓝 0))
    (hp : Tendsto p atTop (𝓝 q))
    (hq : q ∈ Set.Icc (fun _ => a) (fun _ => b))
    (hactive : ∀ k, (D.family.atScale (h k)).Active (D.label j i)
      (exponentialPoint (h k) (p k))) :
    |exponentMinimum q - D.center j| ≤ D.radius j := by
  have hqm := exponentMinimum_mem_interval hq
  have hlow : (if j.val = 0 then a else D.cut (j.val - 1)) ≤ exponentMinimum q := by
    split_ifs with hj
    · exact hqm.1
    · exact D.active_minimum_lower j i (by omega) hpos hh hp hactive
  have hupp : exponentMinimum q ≤ (if j.val = n then b else D.cut j.val) := by
    split_ifs with hj
    · exact hqm.2
    · exact D.active_minimum_upper j i (by omega) hpos hh hp hactive
  have hl := (D.band_left j).trans hlow
  have hr := hupp.trans (D.band_right j)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem MinimumShiftChain.sequentialActivityBound {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E) :
    D.family.HasSequentialActivityBound (Set.Icc (fun _ => a) (fun _ => b))
      (fun i => E (D.family.slope i)) := by
  intro l h p q hpos hh hp hq hactive
  obtain ⟨j, i, rfl⟩ := affineBlockLabel_surjective D.size l
  change ‖q - D.family.slope (D.label j i)‖ < E (D.family.slope (D.label j i))
  rw [D.family_label_slope]
  exact D.approximation j i h p q hpos hh hp
    ⟨hq, D.active_limit_in_band j i hpos hh hp hq hactive⟩
    (fun k => D.active_in_block j i (h k) _ (hactive k))

theorem MinimumShiftChain.slopes_mem_cube {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E) :
    ∀ l, D.family.slope l ∈ Set.Icc (fun _ => a) (fun _ => b) := by
  intro l
  obtain ⟨j, i, rfl⟩ := affineBlockLabel_surjective D.size l
  rw [show affineBlockLabel D.size j i = D.label j i from rfl, D.family_label_slope]
  exact (D.block j).cube i

theorem MinimumShiftChain.offsets_isLittleO {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E) :
    ∀ l, IsLittleO (𝓝[>] (0 : ℝ)) (D.family.offset l) (fun h => h ^ a) := by
  apply ScaledAffineFamily.blockUnion_offsets_isLittleO
  intro j
  apply ScaledAffineFamily.offsetShift_offsets_isLittleO
  · apply powerPrefixShift_isLittleO
    intro k hk
    exact (D.center_mem ⟨k, by omega⟩).1.trans_lt
      (D.cut_between k (by omega)).1
  · intro i
    exact offset_isLittleO_of_le_power (D.decay j i)
      ((D.center_mem j).1.trans (le_add_of_nonneg_right (D.radius_pos j).le))

theorem MinimumShiftChain.affine_approximation {d n : ℕ} [NeZero d]
    {a b : ℝ} {E : State d → ℝ} (D : MinimumShiftChain d n a b E) :
    ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily d m,
      (∀ i, A.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) ∧
      A.HasSequentialActivityBound (Set.Icc (fun _ => a) (fun _ => b))
        (fun i => E (A.slope i)) :=
  ⟨_, affineBlockLabel_card_pos D.size 0 (D.block 0).size_pos, D.family,
    D.slopes_mem_cube, D.offsets_isLittleO, D.sequentialActivityBound⟩

def MinimumShiftChainExistenceInDimension (d : ℕ) [NeZero d] : Prop :=
  ∀ a b : ℝ, a < b → ∀ E : State d → ℝ,
    (∀ r ∈ Set.Icc (fun _ => a) (fun _ => b), 0 < E r) →
      ∃ n : ℕ, Nonempty (MinimumShiftChain d n a b E)

theorem affineApproximation_of_minimumShiftChainExistence {d : ℕ} [NeZero d]
    (hchain : MinimumShiftChainExistenceInDimension d) : AffineApproximationInDimension d := by
  intro a b hab E hE
  obtain ⟨n, ⟨D⟩⟩ := hchain a b hab E hE
  exact D.affine_approximation

theorem affineMinimumCombination_of_orderedChainExistence
    (hchain : ∀ d : ℕ, ∀ (_ : NeZero d), FixedMinimumApproximationInDimension d →
      MinimumShiftChainExistenceInDimension d) : AffineMinimumCombinationStatement := by
  intro d hd hlocal
  let : NeZero d := hd
  exact affineApproximation_of_minimumShiftChainExistence (hchain d hd hlocal)

end Endotactic
end

-- Source: Endotactic/MinimumBandReduction.lean
section
/-!
# Reduce the remaining affine existence gap to a pure interval lemma

The radius function is only pointwise positive on [a,b]. This target assumes
no continuity or global lower bound of the radius. If its finite ordered
certificate exists, the checked local induction and offset shifts prove the
exact full affine statement. `MinimumBandSelection` proves the interval target
downstream; this module supplies the independent type and generic reduction.
-/

namespace Endotactic

open Filter Topology Asymptotics

structure OrderedMinimumBandChain (n : ℕ) (a b : ℝ) (ρ : ℝ → ℝ) where
  center : Fin (n + 1) → ℝ
  center_mem : ∀ j, center j ∈ Set.Icc a b
  cut : ℕ → ℝ
  cut_between : ∀ k (hk : k < n),
    center ⟨k, by omega⟩ < cut k ∧ cut k < center ⟨k + 1, by omega⟩
  band_left : ∀ j, center j - ρ (center j) ≤ if j.val = 0 then a else cut (j.val - 1)
  band_right : ∀ j, (if j.val = n then b else cut j.val) ≤ center j + ρ (center j)

/-- This interval target has only real intervals and an arbitrary positive
radius function. It has no affine family, tolerance, ODE or network input.
It is proved downstream by `minimumBandSelection`. -/
def MinimumBandSelectionStatement : Prop :=
  ∀ a b : ℝ, a < b → ∀ ρ : ℝ → ℝ,
    (∀ t ∈ Set.Icc a b, 0 < ρ t) →
      ∃ n : ℕ, Nonempty (OrderedMinimumBandChain n a b ρ)

theorem affineMinimumCombination_of_bandSelection
    (hselect : MinimumBandSelectionStatement) : AffineMinimumCombinationStatement := by
  classical
  intro d hd hlocal a b hab E hE
  let : NeZero d := hd
  let block : ∀ t : Set.Icc a b, FixedMinimumApproximation d a b t.val E :=
    fun t => Classical.choice (hlocal a b hab E hE t.val t.property)
  have hnear := fun t : Set.Icc a b => (block t).near_minimum_with_decay
  choose radius hpos hdecay happrox using hnear
  let ρ : ℝ → ℝ := fun t => if ht : t ∈ Set.Icc a b then radius ⟨t, ht⟩ else 1
  have hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t := by
    intro t ht
    simpa only [ρ, dite_eq_left ht] using hpos ⟨t, ht⟩
  obtain ⟨n, ⟨S⟩⟩ := hselect a b hab ρ hρ
  let D : MinimumShiftChain d n a b E := {
    center := S.center
    center_mem := S.center_mem
    block := fun j => block ⟨S.center j, S.center_mem j⟩
    radius := fun j => ρ (S.center j)
    radius_pos := fun j => hρ (S.center j) (S.center_mem j)
    cut := S.cut
    cut_between := S.cut_between
    band_left := S.band_left
    band_right := S.band_right
    decay := fun j => by
      simpa only [ρ, dite_eq_left (S.center_mem j)] using hdecay ⟨S.center j, S.center_mem j⟩
    approximation := fun j => by
      simpa only [ρ, dite_eq_left (S.center_mem j)] using happrox ⟨S.center j, S.center_mem j⟩ }
  exact D.affine_approximation

theorem finiteAffineApproximation_of_minimumBandSelection
    (hselect : MinimumBandSelectionStatement) : FiniteAffineApproximationStatement :=
  finiteAffineApproximation_of_minimumCombination
    (affineMinimumCombination_of_bandSelection hselect)

end Endotactic
end

-- Source: Endotactic/FiniteMinimumBandCover.lean
section
/-!
# Compact finite band covers and pruning by minimum cardinality

Every center lies in the original interval. Pointwise positivity alone gives
an open cover. A cover of minimum finite cardinality cannot contain a band
contained in another band. No radius continuity or uniform lower bound is used.
-/

namespace Endotactic

open Filter Topology

def CoversMinimumBands (a b : ℝ) (ρ : ℝ → ℝ) (s : Finset ℝ) : Prop :=
  (∀ t ∈ s, t ∈ Set.Icc a b) ∧
    ∀ x ∈ Set.Icc a b, ∃ t ∈ s, t - ρ t < x ∧ x < t + ρ t

theorem exists_finite_minimum_band_cover {a b : ℝ} (ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) :
    ∃ s : Finset ℝ, CoversMinimumBands a b ρ s := by
  classical
  let U : Set.Icc a b → Set ℝ := fun t => Set.Ioo (t.val - ρ t.val) (t.val + ρ t.val)
  have hcover : Set.Icc a b ⊆ ⋃ t, U t := by
    intro x hx
    apply Set.mem_iUnion.mpr
    exact ⟨⟨x, hx⟩, ⟨by dsimp [U]; linarith [hρ x hx],
      by dsimp [U]; linarith [hρ x hx]⟩⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover U (fun _ => isOpen_Ioo) hcover
  refine ⟨s.image Subtype.val, ?_, ?_⟩
  · intro t ht
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ht
    exact u.property
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := (by simpa only [Set.mem_iUnion, exists_prop] using hs hx :
      ∃ t : Set.Icc a b, t ∈ s ∧ x ∈ U t)
    exact ⟨t.val, Finset.mem_image.mpr ⟨t, ht, rfl⟩, hxt⟩

theorem CoversMinimumBands.nonempty {a b : ℝ} {ρ : ℝ → ℝ} {s : Finset ℝ}
    (hs : CoversMinimumBands a b ρ s) (hab : a ≤ b) : s.Nonempty := by
  obtain ⟨t, ht, _⟩ := hs.2 a ⟨le_rfl, hab⟩
  exact ⟨t, ht⟩

theorem exists_pruned_minimum_band_cover {a b : ℝ} (ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) :
    ∃ s : Finset ℝ, CoversMinimumBands a b ρ s ∧
      ∀ t ∈ s, ∀ u ∈ s, t ≠ u → ¬ (u - ρ u ≤ t - ρ t ∧ t + ρ t ≤ u + ρ u) := by
  classical
  obtain ⟨s₀, hs₀⟩ := exists_finite_minimum_band_cover ρ hρ
  have hex : ∃ k : ℕ, ∃ s : Finset ℝ, s.card = k ∧ CoversMinimumBands a b ρ s :=
    ⟨s₀.card, s₀, rfl, hs₀⟩
  obtain ⟨s, hcard, hs⟩ := Nat.find_spec hex
  refine ⟨s, hs, ?_⟩
  intro t ht u hu htu hcontained
  have herase : CoversMinimumBands a b ρ (s.erase t) := by
    refine ⟨fun v hv => hs.1 v (Finset.mem_of_mem_erase hv), ?_⟩
    intro x hx
    obtain ⟨v, hv, hleft, hright⟩ := hs.2 x hx
    by_cases hvt : v = t
    · subst v
      exact ⟨u, Finset.mem_erase.mpr ⟨htu.symm, hu⟩,
        hcontained.1.trans_lt hleft, hright.trans_le hcontained.2⟩
    · exact ⟨v, Finset.mem_erase.mpr ⟨hvt, hv⟩, hleft, hright⟩
  have hmin : Nat.find hex ≤ (s.erase t).card :=
    Nat.find_min' hex ⟨s.erase t, rfl, herase⟩
  have hsmall := Finset.card_erase_lt_of_mem ht
  omega

theorem minimum_band_endpoints_strict_of_noncontainment (ρ : ℝ → ℝ)
    {t u : ℝ} (htu : t < u)
    (hforward : ¬ (u - ρ u ≤ t - ρ t ∧ t + ρ t ≤ u + ρ u))
    (hbackward : ¬ (t - ρ t ≤ u - ρ u ∧ u + ρ u ≤ t + ρ t)) :
    t - ρ t < u - ρ u ∧ t + ρ t < u + ρ u := by
  constructor
  · by_contra hbad
    apply hforward
    exact ⟨le_of_not_gt hbad, by linarith⟩
  · by_contra hbad
    apply hbackward
    exact ⟨by linarith, le_of_not_gt hbad⟩

end Endotactic
end

-- Source: Endotactic/OrderedMinimumBandCover.lean
section
/-!
# Sort a pruned open band cover and certify adjacent overlap

Minimal-cardinality pruning makes both endpoint orders agree with the center
order. Coverage then excludes a gap between adjacent bands and places the
two interval endpoints inside the first and last band.
-/

namespace Endotactic

structure OrderedOpenMinimumBandCover (n : ℕ) (a b : ℝ) (ρ : ℝ → ℝ) where
  center : Fin (n + 1) → ℝ
  center_mem : ∀ j, center j ∈ Set.Icc a b
  center_strict : StrictMono center
  left_strict : StrictMono (fun j => center j - ρ (center j))
  right_strict : StrictMono (fun j => center j + ρ (center j))
  cover : ∀ x ∈ Set.Icc a b, ∃ j,
    center j - ρ (center j) < x ∧ x < center j + ρ (center j)

theorem exists_ordered_open_minimum_band_cover {a b : ℝ} (hab : a ≤ b) (ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) :
    ∃ n : ℕ, Nonempty (OrderedOpenMinimumBandCover n a b ρ) := by
  classical
  obtain ⟨s, hs, hprune⟩ := exists_pruned_minimum_band_cover ρ hρ
  have hcard0 : 0 < s.card := Finset.card_pos.mpr (hs.nonempty hab)
  let n := s.card - 1
  have hcard : s.card = n + 1 := by dsimp [n]; omega
  let f : Fin (n + 1) ↪o ℝ := s.orderEmbOfFin hcard
  have hmem : ∀ j, f j ∈ s := fun j => Finset.orderEmbOfFin_mem s hcard j
  have hends : ∀ i j, i < j → f i - ρ (f i) < f j - ρ (f j) ∧
      f i + ρ (f i) < f j + ρ (f j) := by
    intro i j hij
    have hf := f.strictMono hij
    exact minimum_band_endpoints_strict_of_noncontainment ρ hf
      (hprune (f i) (hmem i) (f j) (hmem j) (ne_of_lt hf))
      (hprune (f j) (hmem j) (f i) (hmem i) (ne_of_gt hf))
  refine ⟨n, ⟨{
    center := f
    center_mem := fun j => hs.1 (f j) (hmem j)
    center_strict := f.strictMono
    left_strict := fun _ _ hij => (hends _ _ hij).1
    right_strict := fun _ _ hij => (hends _ _ hij).2
    cover := ?_ }⟩⟩
  intro x hx
  obtain ⟨t, ht, hleft, hright⟩ := hs.2 x hx
  have htrange : t ∈ Set.range f := by
    change t ∈ Set.range (s.orderEmbOfFin hcard)
    rw [Finset.range_orderEmbOfFin]
    exact ht
  obtain ⟨j, rfl⟩ := htrange
  exact ⟨j, hleft, hright⟩

theorem OrderedOpenMinimumBandCover.first_contains_left {n : ℕ} {a b : ℝ} {ρ : ℝ → ℝ}
    (D : OrderedOpenMinimumBandCover n a b ρ) (hab : a ≤ b) :
    D.center 0 - ρ (D.center 0) < a := by
  obtain ⟨j, hj, _⟩ := D.cover a ⟨le_rfl, hab⟩
  exact (D.left_strict.monotone (Fin.zero_le j)).trans_lt hj

theorem OrderedOpenMinimumBandCover.last_contains_right {n : ℕ} {a b : ℝ} {ρ : ℝ → ℝ}
    (D : OrderedOpenMinimumBandCover n a b ρ) (hab : a ≤ b) :
    b < D.center (Fin.last n) + ρ (D.center (Fin.last n)) := by
  obtain ⟨j, _, hj⟩ := D.cover b ⟨hab, le_rfl⟩
  exact hj.trans_le (D.right_strict.monotone (Fin.le_last j))

theorem OrderedOpenMinimumBandCover.adjacent_overlap {n : ℕ} {a b : ℝ} {ρ : ℝ → ℝ}
    (D : OrderedOpenMinimumBandCover n a b ρ)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) (k : ℕ) (hk : k < n) :
    D.center ⟨k + 1, by omega⟩ - ρ (D.center ⟨k + 1, by omega⟩) <
      D.center ⟨k, by omega⟩ + ρ (D.center ⟨k, by omega⟩) := by
  let i : Fin (n + 1) := ⟨k, by omega⟩
  let next : Fin (n + 1) := ⟨k + 1, by omega⟩
  by_contra hbad
  have hgap : D.center i + ρ (D.center i) ≤ D.center next - ρ (D.center next) :=
    le_of_not_gt hbad
  have hposi := hρ (D.center i) (D.center_mem i)
  have hposnext := hρ (D.center next) (D.center_mem next)
  have hx : D.center i + ρ (D.center i) ∈ Set.Icc a b := by
    have hi := (D.center_mem i).1
    have hn := (D.center_mem next).2
    constructor <;> linarith
  obtain ⟨j, hleft, hright⟩ := D.cover _ hx
  by_cases hji : j.val ≤ k
  · have hjle : j ≤ i := hji
    have hr := D.right_strict.monotone hjle
    linarith
  · have hnj : next ≤ j := by change k + 1 ≤ j.val; omega
    have hl := D.left_strict.monotone hnj
    linarith

theorem OrderedOpenMinimumBandCover.exists_adjacent_cut {n : ℕ} {a b : ℝ} {ρ : ℝ → ℝ}
    (D : OrderedOpenMinimumBandCover n a b ρ)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) (k : ℕ) (hk : k < n) :
    ∃ q : ℝ,
      D.center ⟨k, by omega⟩ < q ∧ q < D.center ⟨k + 1, by omega⟩ ∧
      D.center ⟨k + 1, by omega⟩ - ρ (D.center ⟨k + 1, by omega⟩) < q ∧
      q < D.center ⟨k, by omega⟩ + ρ (D.center ⟨k, by omega⟩) := by
  let i : Fin (n + 1) := ⟨k, by omega⟩
  let next : Fin (n + 1) := ⟨k + 1, by omega⟩
  have hc : D.center i < D.center next := D.center_strict (by change k < k + 1; omega)
  have hpi := hρ (D.center i) (D.center_mem i)
  have hpn := hρ (D.center next) (D.center_mem next)
  have ho := D.adjacent_overlap hρ k hk
  have hgap : max (D.center i) (D.center next - ρ (D.center next)) <
      min (D.center next) (D.center i + ρ (D.center i)) := by
    apply lt_min
    · exact max_lt_iff.mpr ⟨hc, by linarith⟩
    · exact max_lt_iff.mpr ⟨by linarith, ho⟩
  obtain ⟨q, hlow, hupp⟩ := exists_between hgap
  exact ⟨q, (le_max_left _ _).trans_lt hlow,
    hupp.trans_le (min_le_left _ _), (le_max_right _ _).trans_lt hlow,
    hupp.trans_le (min_le_right _ _)⟩

end Endotactic
end

-- Source: Endotactic/MinimumBandSelection.lean
section
/-!
# Pointwise positive bands admit the required ordered cuts

The compact cover/pruning/order proof closes the pure interval obligation.
Its cut construction includes the one-band case without special assumptions.
The exact full affine existence statement then follows by the checked strong
induction and actual shifted-family construction.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem OrderedOpenMinimumBandCover.exists_ordered_chain {n : ℕ} {a b : ℝ} {ρ : ℝ → ℝ}
    (D : OrderedOpenMinimumBandCover n a b ρ) (hab : a ≤ b)
    (hρ : ∀ t ∈ Set.Icc a b, 0 < ρ t) : Nonempty (OrderedMinimumBandChain n a b ρ) := by
  classical
  have hex := fun k : Fin n => D.exists_adjacent_cut hρ k.val k.isLt
  choose cut hcl hcu hbl hbu using hex
  let q : ℕ → ℝ := fun k => if hk : k < n then cut ⟨k, hk⟩ else b
  refine ⟨{ center := D.center
            center_mem := D.center_mem
            cut := q
            cut_between := ?_
            band_left := ?_
            band_right := ?_ }⟩
  · intro k hk
    dsimp only [q]
    rw [dite_eq_left hk]
    exact ⟨hcl ⟨k, hk⟩, hcu ⟨k, hk⟩⟩
  · intro j
    by_cases hj : j.val = 0
    · rw [ite_eq_left hj]
      have heq : j = 0 := Fin.ext hj
      rw [heq]
      exact (D.first_contains_left hab).le
    · have hk : j.val - 1 < n := by omega
      have hpred : j.val - 1 + 1 = j.val := by omega
      rw [ite_eq_right hj]
      dsimp only [q]
      rw [dite_eq_left hk]
      have h := hbl ⟨j.val - 1, hk⟩
      simpa only [hpred] using h.le
  · intro j
    by_cases hj : j.val = n
    · rw [ite_eq_left hj]
      have heq : j = Fin.last n := Fin.ext hj
      rw [heq]
      exact (D.last_contains_right hab).le
    · have hk : j.val < n := by omega
      rw [ite_eq_right hj]
      dsimp only [q]
      rw [dite_eq_left hk]
      exact (hbu ⟨j.val, hk⟩).le

theorem minimumBandSelection : MinimumBandSelectionStatement := by
  intro a b hab ρ hρ
  obtain ⟨n, ⟨D⟩⟩ := exists_ordered_open_minimum_band_cover hab.le ρ hρ
  exact ⟨n, D.exists_ordered_chain hab.le hρ⟩

theorem affineMinimumCombination : AffineMinimumCombinationStatement :=
  affineMinimumCombination_of_bandSelection minimumBandSelection

theorem finiteAffineApproximation : FiniteAffineApproximationStatement :=
  finiteAffineApproximation_of_minimumBandSelection minimumBandSelection

end Endotactic
end

-- Source: Endotactic/AffineApproximationExistence.lean
section
/-!
# Unconditional affine approximation and endotactic active-flux families

The exact affine theorem is now proved, so no affine-existence oracle is an
input to these APIs. Compact positive class carriers and exterior geometry
are still separate requirements of the eventual permanence theorem.
-/

namespace Endotactic

open Filter Topology Asymptotics

theorem exists_uniform_affine_approximation {d : ℕ} (hd : 0 < d)
    {a b : ℝ} (hab : a < b) (E : State d → ℝ)
    (hE : ∀ r ∈ Set.Icc (fun _ => a) (fun _ => b), 0 < E r) :
    ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily d m,
      (∀ i, A.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) ∧
      A.HasSequentialActivityBound (Set.Icc (fun _ => a) (fun _ => b))
        (fun i => E (A.slope i)) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ p ∈ Set.Icc (fun _ => a) (fun _ => b), ∀ i,
          (A.atScale h).Active i (exponentialPoint h p) → ‖p - A.slope i‖ < E (A.slope i) := by
  obtain ⟨m, hm, A, hcube, hdecay, hseq⟩ := finiteAffineApproximation d hd a b hab E hE
  exact ⟨m, hm, A, hcube, hdecay, hseq,
    A.uniformActivityBound_of_sequential _ isCompact_Icc _ hseq⟩

theorem Network.exists_uniform_active_flux_family {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (hd : 0 < d) {a b ℓ u : ℝ} (hab : a < b) (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily d m,
      (∀ i, A.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ p ∈ Set.Icc (fun _ => a) (fun _ => b), ∀ i,
          (A.atScale h).Active i (exponentialPoint h p) →
          (∃ e, N.projection (A.slope i) e ≠ 0) →
          ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
            0 < dot (A.slope i) (N.rhs k (exponentialPoint h p)) :=
  N.uniform_active_flux_of_affineApproximation hN finiteAffineApproximation hd hab hℓ hu

theorem Network.exists_uniform_exterior_active_flux_family {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (hd : 0 < d) {a b ℓ u : ℝ} (hab : a < b) (hℓ : 0 < ℓ) (hu : 0 ≤ u) :
    ∃ m : ℕ, 0 < m ∧ ∃ A : ScaledAffineFamily d m,
      (∀ i, A.slope i ∈ Set.Icc (fun _ => a) (fun _ => b)) ∧
      (∀ i, IsLittleO (𝓝[>] (0 : ℝ)) (A.offset i) (fun h => h ^ a)) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ p ∈ Set.Icc (fun _ => a) (fun _ => b), ∀ c : State d, ∀ M : ℝ,
          exponentialPoint h p ∈ N.positiveClass c →
          exponentialPoint h p ∉ (A.atScale h).plateau M →
          ((A.atScale h).plateau M ∩ N.stoichiometricClass c).Nonempty →
          ∀ i, (A.atScale h).Active i (exponentialPoint h p) →
            ∀ k : E → ℝ, (∀ e, ℓ ≤ k e ∧ k e ≤ u) →
              0 < dot (A.slope i) (N.rhs k (exponentialPoint h p)) := by
  obtain ⟨ε, hε⟩ := N.exists_slopeTolerance hN
  obtain ⟨m, hm, A, hcube, hdecay, hseq⟩ := finiteAffineApproximation d hd a b hab ε
    (fun r _ => (hε r).1)
  exact ⟨m, hm, A, hcube, hdecay,
    N.uniform_exterior_active_flux_of_sequentialActivityBound A _ isCompact_Icc ε hε hseq hℓ hu⟩

end Endotactic
end

-- Source: Endotactic/ScaleTrapConstruction.lean
section
/-!
# General endotactic scale-trap family construction

Tolerance is selected before the finite family. Each scale gets a positive
relaxation staying in its quarter-power box. No offset continuity, common
positive tolerance infimum, nestedness or carrier oracle is assumed.
-/

namespace Endotactic

open Set Filter Topology

theorem Network.exists_scaleTrapFamily {d : ℕ} {E : Type*}
    [Fintype E] [DecidableEq E] (N : Network d E) (hN : N.IsEndotactic)
    (hd : 0 < d) {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 0 ≤ u)
    {c : State d} (hc : Positive c) :
    ∃ m : ℕ, 0 < m ∧ Nonempty (ScaleTrapFamily (m := m) N ℓ u c) := by
  classical
  obtain ⟨εN, hεN⟩ := N.exists_slopeTolerance hN
  let η : State d → ℝ := fun r => min (εN r) (1 / 8 : ℝ)
  have hη : ∀ r, 0 < η r := fun r => lt_min (hεN r).1 (by norm_num)
  obtain ⟨m, hm, A, _, _, hseq⟩ := finiteAffineApproximation d hd (-1) 1 (by norm_num)
    (zeroForcingTolerance η) (fun r _ => zeroForcingTolerance_pos hη r)
  let : NeZero m := ⟨by omega⟩
  have hseqN := A.sequentialActivityBound_tolerance_mono hseq
    (fun i => (zeroForcingTolerance_le η (A.slope i)).trans (min_le_left _ _))
  obtain ⟨F, hF, _, hflux⟩ := N.uniform_active_flux_of_sequentialActivityBound
    A _ isCompact_Icc εN hεN hseqN hℓ hu
  obtain ⟨C, hC, _, hcapc⟩ := A.exists_small_scale_zero_cap η hseq hc
  obtain ⟨U, hU, _, huniform⟩ := A.uniformActivityBound_of_sequential _ isCompact_Icc _ hseq
  have hevent : ∀ᶠ h in 𝓝[>] (0 : ℝ), ‖logarithmicExponent h c‖ < (1 / 4 : ℝ) :=
    (tendsto_logarithmicExponent c).norm.eventually
      (by simpa only [norm_zero] using
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4) :
          ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), x < 1 / 4))
  obtain ⟨L, hL, hlog⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  let H : ℝ := min F (min C (min U (min L 1))) / 2
  have hbase : 0 < min F (min C (min U (min L 1))) :=
    lt_min hF (lt_min hC (lt_min hU (lt_min hL (by norm_num))))
  have hH : 0 < H := div_pos hbase (by norm_num)
  have hHlt : H < min F (min C (min U (min L 1))) := by dsimp [H]; linarith
  have hHF : H < F := hHlt.trans_le (min_le_left _ _)
  have hrest := hHlt.trans_le (min_le_right _ _)
  have hHC : H < C := hrest.trans_le (min_le_left _ _)
  have hrestU := hrest.trans_le (min_le_right _ _)
  have hHU : H < U := hrestU.trans_le (min_le_left _ _)
  have hrestL := hrestU.trans_le (min_le_right _ _)
  have hHL : H < L := hrestL.trans_le (min_le_left _ _)
  have hH1 : H < 1 := hrestL.trans_le (min_le_right _ _)
  let M : ℝ → ℝ := fun h => (A.atScale h).minimum c
  have hgeom : ∀ h ∈ Ioc 0 H,
      c ∈ (A.atScale h).plateau (M h) ∧ IsCompact ((A.atScale h).plateau (M h)) ∧
      (A.atScale h).plateau (M h) ⊆
        openCoordinateBox (fun _ => h ^ (1 / 4 : ℝ)) (fun _ => (h ^ (1 / 4 : ℝ))⁻¹) := by
    intro h hh
    have hh1 := hh.2.trans_lt hH1
    obtain ⟨i₀, hi₀, hcK, hcompact, _, _⟩ := hcapc h hh.1 (hh.2.trans_lt hHC)
    have hslope : ∀ j, (A.atScale h).slope i₀ j = 0 := fun j => congrFun hi₀ j
    have hactive := ((A.atScale h).constant_active_iff_mem_plateau i₀ hslope c).mpr hcK
    have hM : M h = A.offset i₀ h := by
      change (A.atScale h).minimum c = _
      rw [((A.atScale h).active_iff_minimum_eq i₀ c).mp hactive,
        (A.atScale h).constant_value i₀ hslope c]
      rfl
    have hcbox := logarithmicExponent_norm_lt_mem_open_power_box hh.1 hh1 hc
      (hlog ⟨hh.1, hh.2.trans_lt hHL⟩)
    have hsmall : ∀ p ∈ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
        (A.atScale h).Active i₀ (exponentialPoint h p) → ‖p‖ < (1 / 4 : ℝ) := by
      intro p hp hi
      have hb := huniform h hh.1 (hh.2.trans_lt hHU) p hp i₀ hi
      rw [hi₀, sub_zero] at hb
      have he : zeroForcingTolerance η 0 ≤ (1 / 8 : ℝ) :=
        (zeroForcingTolerance_le η 0).trans (min_le_right _ _)
      exact (hb.trans_le he).trans (by norm_num)
    have hsub := A.zero_cap_plateau_subset_open_power_box hh.1 hh1
      (by norm_num) (by norm_num) i₀ hi₀ hactive hcbox hsmall
    rw [hM]
    exact ⟨hcK, hcompact, hsub⟩
  have hrelax : ∀ h : ℝ, ∃ δ : ℝ, 0 < δ ∧ (h ∈ Ioc 0 H →
      (A.atScale h).plateau (M h - δ) ⊆
        openCoordinateBox (fun _ => h ^ (1 / 4 : ℝ)) (fun _ => (h ^ (1 / 4 : ℝ))⁻¹)) := by
    intro h
    by_cases hh : h ∈ Ioc 0 H
    · obtain ⟨hcK, hcompact, hsub⟩ := hgeom h hh
      obtain ⟨δ, hδ, hδsub⟩ := (A.atScale h).exists_relaxed_plateau_subset_open
        ⟨c, hcK⟩ hcompact (isOpen_openCoordinateBox _ _) hsub
      exact ⟨δ, hδ, fun _ => hδsub⟩
    · exact ⟨1, by norm_num, fun hs => (hh hs).elim⟩
  choose δ hδ hδsub using hrelax
  let Q : ℝ → ℝ := fun h => M h - δ h
  have hbox : ∀ h ∈ Ioc 0 H, (A.atScale h).plateau (Q h) ⊆ powerBox h (1 / 4 : ℝ) :=
    fun h hh y hy => ⟨fun j => (hδsub h hh hy j).1.le, fun j => (hδsub h hh hy j).2.le⟩
  refine ⟨m, hm, ⟨{
    family := A
    threshold := H
    threshold_pos := hH
    threshold_lt_one := hH1
    level := M
    relaxed := Q
    reference := fun h hh => (hgeom h hh).1
    gap := fun h _ => sub_lt_self (M h) (hδ h)
    compact := fun h hh => (A.atScale h).plateau_isCompact_of_subset (Q h)
      isCompact_Icc (hbox h hh)
    box := hbox
    capture := ?_
    flux := ?_
  }⟩⟩
  · intro z hz
    obtain ⟨Z, hZ, _, hcapz⟩ := A.exists_small_scale_zero_cap η hseq hz
    let h : ℝ := min Z H / 2
    have hh : 0 < h := div_pos (lt_min hZ hH) (by norm_num)
    have hlt : h < min Z H := by dsimp [h]; linarith [lt_min hZ hH]
    have hhH : h ∈ Ioc 0 H := ⟨hh, (hlt.trans_le (min_le_right _ _)).le⟩
    obtain ⟨i, hi, hcK, _, _, _⟩ := hcapc h hh (hhH.2.trans_lt hHC)
    obtain ⟨j, hj, hzK, _, _, _⟩ := hcapz h hh (hlt.trans_le (min_le_left _ _))
    have hi' : ∀ k, (A.atScale h).slope i k = 0 := fun k => congrFun hi k
    have hj' : ∀ k, (A.atScale h).slope j k = 0 := fun k => congrFun hj k
    have hic := ((A.atScale h).constant_active_iff_mem_plateau i hi' c).mpr hcK
    have hjz := ((A.atScale h).constant_active_iff_mem_plateau j hj' z).mpr hzK
    have hiz := (A.atScale h).active_zero_transfer hi' hj' hic hjz
    have hM : M h = A.offset i h := by
      change (A.atScale h).minimum c = _
      rw [((A.atScale h).active_iff_minimum_eq i c).mp hic,
        (A.atScale h).constant_value i hi' c]
      rfl
    have hzM : z ∈ (A.atScale h).plateau (M h) := by
      rw [hM]
      exact ((A.atScale h).constant_active_iff_mem_plateau i hi' z).mp hiz
    exact ⟨h, hhH, fun i => (sub_le_self (M h) (hδ h).le).trans (hzM i)⟩
  · intro h hh y hy i hi hnonzero a ha
    have hypos : Positive y := fun j => hh.1.trans_le (hy.1 j)
    have hh1 := hh.2.trans_lt hH1
    have hpow := exponentialPoint_logarithmicExponent hh.1 hh1 hypos
    have hp := logarithmicExponent_mem_cube hh.1 hh1 hy
    have hb := hflux h hh.1 (hh.2.trans_lt hHF) (logarithmicExponent h y) hp i
      (hpow.symm ▸ hi) hnonzero a (fun e => ⟨ha.1 e, ha.2 e⟩)
    simpa only [hpow] using hb

end Endotactic
end

-- Source: Endotactic/GeneralPermanence.lean
section
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
end

-- Source: EndotacticPublication/Main.lean
section
/-!
# Compact-set permanence targets

These targets use the proof-library compact-set definitions.
CoordinateBounds proves equivalence with positive coordinate bounds;
FCPresentation proves the independently written FC targets.
The answer is outside every quantifier. Global positive existence and
uniqueness are included in the permanence definitions.
-/

namespace EndotacticPublication

/-- The natural-exponent Extended Permanence Conjecture of [CNP11, Section 4],
with the explicit locally finite piecewise differentiability convention.
For each admissible rate path and positive stoichiometric class, is there a
compact positive set absorbing every positive trajectory in that class?
The answer for the displayed model is positive. The rate path precedes the
compact set; the entry time may depend on the trajectory. -/
theorem extended_permanence :
    answer(True) ↔
      ∀ (d m : ℕ), 0 < d → ∀ N : Endotactic.Network d (Fin m),
        N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
          ∀ k : Fin m → ℝ → ℝ, Endotactic.AdmissibleRates k ℓ u →
            Endotactic.LocallyPiecewiseDifferentiableRates k →
              ∀ c : Endotactic.State d, Endotactic.Positive c →
                N.PermanentForRates k c := by
  exact ⟨fun _ => Endotactic.original_extended_permanence, fun _ => True.intro⟩

/-- A measurable-rate, common-coefficient-box strengthening of [CNP11].
For each finite endotactic network, positive coefficient box and positive
class, is there one compact positive set absorbing all positive trajectories
for every bounded measurable rate path in that box? The answer is positive.
The compact set precedes both the rate path and the initial state. -/
theorem measurable_extended_permanence :
    answer(True) ↔
      ∀ (d m : ℕ), 0 < d → ∀ N : Endotactic.Network d (Fin m),
        N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
          ∀ c : Endotactic.State d, Endotactic.Positive c →
            N.UniformPermanent ℓ u c (fun _ => True) := by
  exact ⟨fun _ => Endotactic.measurable_extended_permanence, fun _ => True.intro⟩

/-- The common-rate-box statement restricted to the displayed piecewise rates. -/
theorem uniform_piecewise_extended_permanence :
    Endotactic.ExtendedPermanenceConjecture :=
  Endotactic.extended_permanence

#print axioms extended_permanence
#print axioms measurable_extended_permanence
#print axioms uniform_piecewise_extended_permanence

end EndotacticPublication
end

-- Source: EndotacticPublication/CoordinateBounds.lean
section
/-! # Coordinate bounds and compact absorption -/

namespace Endotactic

open Set

variable {d : ℕ} {E : Type*} [Fintype E]

/-- Eventual positive coordinate bounds for one rate path. -/
def Network.BoundedPermanentForRates (N : Network d E) (k : E → ℝ → ℝ)
    (c : State d) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    (∀ x₀ ∈ N.positiveClass c, N.PositiveWellPosed k x₀) ∧
    ∀ x₀ ∈ N.positiveClass c, ∀ x : ℝ → State d,
      N.IsGlobalPositiveSolution k x₀ x →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
          ∀ i, ε ≤ x t i ∧ x t i ≤ ε⁻¹

/-- Common eventual coordinate bounds for all admissible rate paths. -/
def Network.UniformBoundedPermanent (N : Network d E) (ℓ u : ℝ) (c : State d) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    ∀ k : E → ℝ → ℝ, AdmissibleRates k ℓ u →
      (∀ x₀ ∈ N.positiveClass c, N.PositiveWellPosed k x₀) ∧
      ∀ x₀ ∈ N.positiveClass c, ∀ x : ℝ → State d,
        N.IsGlobalPositiveSolution k x₀ x →
          ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
            ∀ i, ε ≤ x t i ∧ x t i ≤ ε⁻¹

/-- A compact positive set has common positive coordinate bounds. -/
theorem compact_positive_coordinate_bounds (hd : 0 < d) {K : Set (State d)}
    (hne : K.Nonempty) (hK : IsCompact K) (hpos : ∀ x ∈ K, Positive x) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x ∈ K, ∀ i, ε ≤ x i ∧ x i ≤ ε⁻¹ := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  choose a ha hamin using fun i : Fin d =>
    hK.exists_isMinOn hne (continuous_apply i).continuousOn
  choose b hb hbmax using fun i : Fin d =>
    hK.exists_isMaxOn hne (continuous_apply i).continuousOn
  let δ : Fin d → ℝ := fun i => min (a i i) (min 1 (max (b i i) 1)⁻¹)
  have hδ : ∀ i, 0 < δ i := by
    intro i
    exact lt_min (hpos (a i) (ha i) i)
      (lt_min zero_lt_one (inv_pos.mpr (zero_lt_one.trans_le (le_max_right _ _))))
  let q : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
  have hq : 0 < q := (Finset.lt_inf'_iff _).mpr (fun i _ => hδ i)
  have hqi : ∀ i, q ≤ δ i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  let ε : ℝ := q / 2
  have hε : 0 < ε := half_pos hq
  have hεi : ∀ i, ε ≤ δ i := fun i => (half_le_self hq.le).trans (hqi i)
  have hε₁ : ε < 1 := by
    have := (hqi (⟨0, hd⟩ : Fin d)).trans
      ((min_le_right _ _).trans (min_le_left _ _))
    dsimp [ε]
    linarith
  refine ⟨ε, hε, hε₁, ?_⟩
  intro x hx i
  refine ⟨((hεi i).trans (min_le_left _ _)).trans (hamin i hx), ?_⟩
  have he : ε ≤ (max (b i i) 1)⁻¹ :=
    (hεi i).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hu : max (b i i) 1 ≤ ε⁻¹ := by
    simpa only [inv_inv] using inv_anti₀ hε he
  exact (hbmax i hx).trans ((le_max_left _ _).trans hu)

omit [Fintype E] in
/-- Coordinate bounds yield a nonempty compact set in a positive class. -/
theorem Network.coordinate_bounds_compact_class (N : Network d E) (hd : 0 < d)
    {c : State d} (hc : Positive c) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set (State d), K.Nonempty ∧ IsCompact K ∧ K ⊆ N.positiveClass c ∧
      ∀ x ∈ N.positiveClass c, (∀ i, ε ≤ x i ∧ x i ≤ ε⁻¹) → x ∈ K := by
  obtain ⟨η, hη, _, hcb⟩ := compact_positive_coordinate_bounds hd
    (singleton_nonempty c) isCompact_singleton (by simpa using hc)
  let δ : ℝ := min ε η
  have hδ : 0 < δ := lt_min hε hη
  let C : Set (State d) := {x | x - c ∈ N.stoichiometricSubspace}
  have hC : IsClosed C :=
    N.stoichiometricSubspace.closed_of_finiteDimensional.preimage
      (continuous_id.sub continuous_const)
  let K : Set (State d) := Icc (fun _ => δ) (fun _ => δ⁻¹) ∩ C
  have he : δ ≤ ε := min_le_left _ _
  have hη' : δ ≤ η := min_le_right _ _
  have huε : ε⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ he
  have huη : η⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ hη'
  refine ⟨K, ⟨c, ?_⟩, isCompact_Icc.inter_right hC, ?_, ?_⟩
  · refine ⟨⟨fun i => hη'.trans ((hcb c (mem_singleton c) i).1),
      fun i => ((hcb c (mem_singleton c) i).2).trans huη⟩, ?_⟩
    simp [C]
  · intro x hx
    exact ⟨fun i => hδ.trans_le (hx.1.1 i), hx.2⟩
  · intro x hx hb
    exact ⟨⟨fun i => he.trans (hb i).1, fun i => (hb i).2.trans huε⟩, hx.2⟩

/-- Coordinate-bound and compact-set permanence are equivalent. -/
theorem Network.boundedPermanentForRates_iff (N : Network d E) (hd : 0 < d)
    {k : E → ℝ → ℝ} {c : State d} (hc : Positive c) :
    N.BoundedPermanentForRates k c ↔ N.PermanentForRates k c := by
  constructor
  · rintro ⟨ε, hε, _, hwell, hb⟩
    obtain ⟨K, hne, hK, hclass, hbox⟩ := N.coordinate_bounds_compact_class hd hc hε
    refine ⟨K, hne, hK, hclass, hwell, ?_⟩
    intro x₀ h₀ x hx
    obtain ⟨T, hT, hstay⟩ := hb x₀ h₀ x hx
    exact ⟨T, hT, fun t ht =>
      hbox (x t) (hx.mem_positiveClass h₀ (hT.trans ht)) (hstay t ht)⟩
  · rintro ⟨K, hne, hK, hclass, hwell, hstay⟩
    obtain ⟨ε, hε, hε₁, hbox⟩ := compact_positive_coordinate_bounds hd hne hK
      (fun x hx => (hclass hx).1)
    refine ⟨ε, hε, hε₁, hwell, ?_⟩
    intro x₀ h₀ x hx
    obtain ⟨T, hT, ht⟩ := hstay x₀ h₀ x hx
    exact ⟨T, hT, fun t h => hbox (x t) (ht t h)⟩

/-- Common coordinate bounds and a common compact absorbing set are equivalent. -/
theorem Network.uniformBoundedPermanent_iff (N : Network d E) (hd : 0 < d)
    {ℓ u : ℝ} {c : State d} (hc : Positive c) :
    N.UniformBoundedPermanent ℓ u c ↔ N.UniformPermanent ℓ u c (fun _ => True) := by
  constructor
  · rintro ⟨ε, hε, _, hb⟩
    obtain ⟨K, hne, hK, hclass, hbox⟩ := N.coordinate_bounds_compact_class hd hc hε
    refine ⟨K, hne, hK, hclass, ?_⟩
    intro k hk _
    refine ⟨(hb k hk).1, ?_⟩
    intro x₀ h₀ x hx
    obtain ⟨T, hT, hstay⟩ := (hb k hk).2 x₀ h₀ x hx
    exact ⟨T, hT, fun t ht =>
      hbox (x t) (hx.mem_positiveClass h₀ (hT.trans ht)) (hstay t ht)⟩
  · rintro ⟨K, hne, hK, hclass, hstay⟩
    obtain ⟨ε, hε, hε₁, hbox⟩ := compact_positive_coordinate_bounds hd hne hK
      (fun x hx => (hclass hx).1)
    refine ⟨ε, hε, hε₁, ?_⟩
    intro k hk
    refine ⟨(hstay k hk True.intro).1, ?_⟩
    intro x₀ h₀ x hx
    obtain ⟨T, hT, ht⟩ := (hstay k hk True.intro).2 x₀ h₀ x hx
    exact ⟨T, hT, fun t h => hbox (x t) (ht t h)⟩

end Endotactic
end

-- Source: EndotacticPublication/FCPresentation.lean
section
/-!
# Complete proofs for the FC coordinate-bound presentation

The presentation definitions and target types come from the independently
written FC draft. Network conversion and compact/coordinate-bound equivalences
adapt the existing complete proofs. No proof-library interface is imposed on
the draft. Generated by lean/scripts/make_fc_proof.py.
-/

namespace EndotacticFC

/-- A directed reaction network. -/
structure Network (d m : ℕ) where
  /-- The source complex of each reaction. -/
  source : Fin m → Fin d → ℕ
  /-- The target complex of each reaction. -/
  target : Fin m → Fin d → ℕ

/-- The real reaction vector: target minus source. -/
def Network.vector {d m : ℕ} (N : Network d m) (e : Fin m) : Fin d → ℝ :=
  fun i => (N.target e i : ℝ) - (N.source e i : ℝ)

/-- Each negative projected reaction has a positive projected reaction
at a strictly lower source level. -/
def Network.IsEndotactic {d m : ℕ} (N : Network d m) : Prop :=
  ∀ (r : Fin d → ℝ) (e : Fin m), dotProduct r (N.vector e) < 0 →
    ∃ f : Fin m, 0 < dotProduct r (N.vector f) ∧
      dotProduct r (fun i => (N.source f i : ℝ)) < dotProduct r (fun i => (N.source e i : ℝ))

/-- All concentrations are strictly positive. -/
def Positive {d : ℕ} (x : Fin d → ℝ) : Prop := ∀ i, 0 < x i

/-- The positive affine stoichiometric class through `c`. -/
def Network.positiveClass {d m : ℕ} (N : Network d m)
    (c : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | Positive x ∧ x - c ∈ Submodule.span ℝ (Set.range N.vector)}

/-- The mass-action vector field. -/
def Network.rhs {d m : ℕ} (N : Network d m)
    (k : Fin m → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  ∑ e, (k e * ∏ i, x i ^ N.source e i) • N.vector e

open MeasureTheory Set

variable {d m : ℕ}

/-- Measurable rates in `[ℓ, u]` for nonnegative time. -/
def AdmissibleRates (k : Fin m → ℝ → ℝ) (ℓ u : ℝ) : Prop :=
  (∀ e, Measurable (k e)) ∧ ∀ e t, 0 ≤ t → ℓ ≤ k e t ∧ k e t ≤ u

/-- Rates differentiable off a finite set on each bounded positive time interval. -/
def LocallyPiecewiseDifferentiableRates (k : Fin m → ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ cuts : Finset ℝ,
    ∀ e t, t ∈ Ioo 0 T → t ∉ cuts → DifferentiableAt ℝ (k e) t

/-- A global positive integral solution on nonnegative time. -/
def Network.IsGlobalPositiveSolution (N : Network d m) (k : Fin m → ℝ → ℝ)
    (x₀ : Fin d → ℝ) (x : ℝ → Fin d → ℝ) : Prop :=
  (ContinuousOn x (Ici 0) ∧ x 0 = x₀ ∧
    (∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun t => N.rhs (fun e => k e t) (x t))
      volume 0 T) ∧
    ∀ t : ℝ, 0 ≤ t →
      x t = x₀ + ∫ s in (0 : ℝ)..t, N.rhs (fun e => k e s) (x s)) ∧
    ∀ t : ℝ, 0 ≤ t → Positive (x t)

/-- A unique global positive solution on nonnegative time. -/
def Network.PositiveWellPosed (N : Network d m) (k : Fin m → ℝ → ℝ)
    (x₀ : Fin d → ℝ) : Prop :=
  ∃ x : ℝ → Fin d → ℝ, N.IsGlobalPositiveSolution k x₀ x ∧
    ∀ y : ℝ → Fin d → ℝ, N.IsGlobalPositiveSolution k x₀ y →
      ∀ t : ℝ, 0 ≤ t → y t = x t

/-- Common eventual positive coordinate bounds for all admissible rate paths. -/
def Network.UniformPermanent (N : Network d m) (ℓ u : ℝ) (c : Fin d → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    ∀ k : Fin m → ℝ → ℝ, AdmissibleRates k ℓ u →
      (∀ x₀ ∈ N.positiveClass c, N.PositiveWellPosed k x₀) ∧
      ∀ x₀ ∈ N.positiveClass c, ∀ x : ℝ → Fin d → ℝ,
        N.IsGlobalPositiveSolution k x₀ x →
          ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
            ∀ i, ε ≤ x t i ∧ x t i ≤ ε⁻¹

/-- Eventual positive coordinate bounds for one fixed rate path. -/
def Network.PermanentForRates (N : Network d m) (k : Fin m → ℝ → ℝ) (c : Fin d → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    (∀ x₀ ∈ N.positiveClass c, N.PositiveWellPosed k x₀) ∧
    ∀ x₀ ∈ N.positiveClass c, ∀ x : ℝ → Fin d → ℝ,
      N.IsGlobalPositiveSolution k x₀ x →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
          ∀ i, ε ≤ x t i ∧ x t i ≤ ε⁻¹


/-- The same reactions in the proof-library representation. -/
def toProofNetwork {d m : ℕ} (N : Network d m) : Endotactic.Network d (Fin m) :=
  ⟨N.source, N.target⟩

/-- A proof-library network with finite reaction indices. -/
def fromProofNetwork {d m : ℕ} (N : Endotactic.Network d (Fin m)) : Network d m :=
  ⟨N.source, N.target⟩

theorem toProof_fromProof {d m : ℕ} (N : Endotactic.Network d (Fin m)) :
    toProofNetwork (fromProofNetwork N) = N := by
  cases N
  rfl

theorem fromProof_toProof {d m : ℕ} (N : Network d m) :
    fromProofNetwork (toProofNetwork N) = N := by
  cases N
  rfl

theorem Network.isEndotactic_iff {d m : ℕ} (N : Network d m) :
    N.IsEndotactic ↔ (toProofNetwork N).IsEndotactic := by
  rfl

theorem Network.permanentForRates_iff_compact {d m : ℕ} (N : Network d m)
    (hd : 0 < d) {k : Fin m → ℝ → ℝ} {c : Fin d → ℝ} (hc : Positive c) :
    N.PermanentForRates k c ↔ (toProofNetwork N).PermanentForRates k c := by
  change (toProofNetwork N).BoundedPermanentForRates k c ↔ _
  exact (toProofNetwork N).boundedPermanentForRates_iff hd hc

theorem Network.uniformPermanent_iff_compact {d m : ℕ} (N : Network d m)
    (hd : 0 < d) {ℓ u : ℝ} {c : Fin d → ℝ} (hc : Positive c) :
    N.UniformPermanent ℓ u c ↔ (toProofNetwork N).UniformPermanent ℓ u c (fun _ => True) := by
  change (toProofNetwork N).UniformBoundedPermanent ℓ u c ↔ _
  exact (toProofNetwork N).uniformBoundedPermanent_iff hd hc

/-- Permanence for endotactic κ-variable mass-action systems [CNP11, Section 4].
The answer is yes [Ki26]. -/
theorem extended_permanence :
    answer(True) ↔
      ∀ (d m : ℕ), 0 < d → ∀ N : Network d m,
        N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
          ∀ k : Fin m → ℝ → ℝ, AdmissibleRates k ℓ u →
            LocallyPiecewiseDifferentiableRates k →
              ∀ c : Fin d → ℝ, Positive c →
                N.PermanentForRates k c := by
  constructor
  · intro _ d m hd N hN ℓ u hℓ hlu k hk hr c hc
    apply (N.permanentForRates_iff_compact hd hc).mpr
    exact (EndotacticPublication.extended_permanence.mp True.intro)
      d m hd (toProofNetwork N) (N.isEndotactic_iff.mp hN) ℓ u hℓ hlu k hk hr c hc
  · intro _
    exact True.intro

/-- Common-box permanence for bounded measurable rates.
The answer is yes [Ki26]. -/
theorem measurable_extended_permanence :
    answer(True) ↔
      ∀ (d m : ℕ), 0 < d → ∀ N : Network d m,
        N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
          ∀ c : Fin d → ℝ, Positive c →
            N.UniformPermanent ℓ u c := by
  constructor
  · intro _ d m hd N hN ℓ u hℓ hlu c hc
    apply (N.uniformPermanent_iff_compact hd hc).mpr
    exact (EndotacticPublication.measurable_extended_permanence.mp True.intro)
      d m hd (toProofNetwork N) (N.isEndotactic_iff.mp hN) ℓ u hℓ hlu c hc
  · intro _
    exact True.intro

end EndotacticFC

#print axioms EndotacticFC.toProof_fromProof

#print axioms EndotacticFC.fromProof_toProof

#print axioms EndotacticFC.Network.isEndotactic_iff

#print axioms EndotacticFC.Network.permanentForRates_iff_compact

#print axioms EndotacticFC.Network.uniformPermanent_iff_compact

#print axioms EndotacticFC.extended_permanence

#print axioms EndotacticFC.measurable_extended_permanence
end

-- Source: Endotactic/DirectionalWallCounterexample.lean
section
/-!
# Compact nonconserved directions need not have a common ray threshold

The reversible network `A ⇄ 2A, 0 ⇄ B` has positive flux eventually on every
fixed nonconserved exponent ray. Nevertheless, for coefficients `(1,1,1,3)`,
directions `(1,1/n)` and scales `h=2^(-n)` have negative flux for every `n ≥ 3`.
All these directions lie in the compact segment `(1,t), 0 ≤ t ≤ 1`.
This refutes automatic uniformization of the fixed-direction lemma, not
permanence, nor the candidate affine approximation argument.
-/

namespace Endotactic.DirectionalWall

open Filter Topology

def network : Network 2 (Fin 4) where
  source := ![![1, 0], ![2, 0], ![0, 0], ![0, 1]]
  target := ![![2, 0], ![1, 0], ![0, 1], ![0, 0]]

theorem network_endotactic : network.IsEndotactic := by
  intro r e he
  fin_cases e
  · refine ⟨1, ?_, ?_⟩ <;>
      simp [network, Network.projection, Network.vector, Network.sourceLevel,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith
  · refine ⟨0, ?_, ?_⟩ <;>
      simp [network, Network.projection, Network.vector, Network.sourceLevel,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith
  · refine ⟨3, ?_, ?_⟩ <;>
      simp [network, Network.projection, Network.vector, Network.sourceLevel,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith
  · refine ⟨2, ?_, ?_⟩ <;>
      simp [network, Network.projection, Network.vector, Network.sourceLevel,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith

def directions : Set (State 2) :=
  (fun t : ℝ => ![1, t]) '' Set.Icc 0 1

theorem directions_compact : IsCompact directions := by
  apply isCompact_Icc.image
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun _ : ℝ => (1 : ℝ))
    exact continuous_const
  · change Continuous (fun t : ℝ => t)
    exact continuous_id

theorem directions_nonconserved (r : State 2) (hr : r ∈ directions) :
    ∃ e : Fin 4, network.projection r e ≠ 0 := by
  obtain ⟨t, _, rfl⟩ := hr
  refine ⟨0, ?_⟩
  norm_num [network, Network.projection, Network.vector, realComplex, dot,
    Fin.sum_univ_succ]

noncomputable def direction (n : ℕ) : State 2 := ![1, (n : ℝ)⁻¹]

theorem direction_mem {n : ℕ} (hn : 1 ≤ n) : direction n ∈ directions := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨(n : ℝ)⁻¹, ⟨inv_nonneg.mpr (by positivity), ?_⟩, rfl⟩
  exact inv_le_one_of_one_le₀ hnR

def rates : Fin 4 → ℝ := ![1, 1, 1, 3]

theorem rates_mem_box : ∀ e : Fin 4, 1 ≤ rates e ∧ rates e ≤ 3 := by
  intro e
  fin_cases e <;> norm_num [rates]

theorem rhs_formula (x : State 2) :
    network.rhs rates x = ![x 0 - (x 0) ^ 2, 1 - 3 * x 1] := by
  ext i
  fin_cases i <;>
    simp [network, Network.rhs, Network.vector, realComplex, monomial, rates,
      Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring

theorem exponentialPoint_at_direction {n : ℕ} (hn : 0 < n) :
    exponentialPoint ((1 / 2 : ℝ) ^ n) (direction n) =
      ![(1 / 2 : ℝ) ^ n, 1 / 2] := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  ext i
  fin_cases i
  · simp [exponentialPoint, direction]
  · change (((1 / 2 : ℝ) ^ n) ^ (n : ℝ)⁻¹) = 1 / 2
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      mul_inv_cancel₀ hnR, Real.rpow_one]

theorem twice_nat_lt_two_pow {n : ℕ} (hn : 3 ≤ n) : 2 * n < 2 ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show 3 + (m + 1) = (3 + m) + 1 by omega, pow_succ]
    nlinarith only [ih]

theorem negative_flux_at_direction {n : ℕ} (hn : 3 ≤ n) :
    dot (direction n)
      (network.rhs rates (exponentialPoint ((1 / 2 : ℝ) ^ n) (direction n))) < 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (2 : ℝ) * n < 2 ^ n := by exact_mod_cast twice_nat_lt_two_pow hn
  have hh : (0 : ℝ) < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hh2 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hsmall : (1 / 2 : ℝ) ^ n < (n : ℝ)⁻¹ / 2 := by
    have hmul := mul_lt_mul_of_pos_left hp hh
    rw [hh2] at hmul
    have hinv : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnR.ne'
    nlinarith only [hmul, hinv, hnR]
  rw [exponentialPoint_at_direction (by omega)]
  rw [rhs_formula]
  norm_num [dot, direction, Fin.sum_univ_succ]
  nlinarith only [hsmall, sq_nonneg ((1 / 2 : ℝ) ^ n)]

theorem scale_tendsto_zero :
    Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Pointwise fixed-ray dominance cannot be compactified without additional
geometric control near projection-zero walls. -/
theorem no_uniform_ray_threshold :
    ¬ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ r ∈ directions, ∀ k : Fin 4 → ℝ,
        (∀ e, 1 ≤ k e ∧ k e ≤ 3) →
          0 < dot r (network.rhs k (exponentialPoint h r)) := by
  rintro ⟨h₀, hh₀, hflux⟩
  have hevent := scale_tendsto_zero.eventually (eventually_lt_nhds hh₀)
  obtain ⟨n, hn, hsmall⟩ := (hevent.and (eventually_ge_atTop 3)).exists
  have hpos := hflux ((1 / 2 : ℝ) ^ n) (pow_pos (by norm_num) _)
    hn (direction n) (direction_mem (by omega)) rates rates_mem_box
  exact (not_lt_of_ge (negative_flux_at_direction hsmall).le) hpos

theorem no_uniform_directional_certificates :
    ¬ ∃ H B : ℝ, 0 < H ∧ ∀ r ∈ directions,
      Nonempty (network.DirectionalCertificate r r H B) := by
  rintro ⟨H, B, hH, hC⟩
  obtain ⟨h₀, hh₀, _, hflux⟩ := exists_uniform_directional_flux_threshold
    network (ℓ := 1) (u := 3) (B := B) (by norm_num) (by norm_num) hH
  apply no_uniform_ray_threshold
  refine ⟨h₀, hh₀, ?_⟩
  intro h hh hsmall r hr k hk
  obtain ⟨C⟩ := hC r hr
  exact hflux h hh hsmall r r C k hk

/-- Every finite sample passes eventual positivity, even though the whole
compact direction segment has no uniform threshold. -/
theorem finite_samples_eventually_positive (s : Finset (State 2))
    (hs : ∀ r ∈ s, r ∈ directions) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      ∀ r ∈ s, ∀ k : Fin 4 → ℝ, (∀ e, 1 ≤ k e ∧ k e ≤ 3) →
        0 < dot r (network.rhs k (exponentialPoint h r)) := by
  classical
  by_cases hne : s.Nonempty
  · let : Nonempty s := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    obtain ⟨ε, hε, h₀, hh₀, hh₀1, hflux⟩ := finite_slopes_tolerant_eventual_flux
      network network_endotactic (fun i : s => (i : State 2))
      (fun i => directions_nonconserved i (hs i i.property))
      (ℓ := 1) (u := 3) (by norm_num) (by norm_num)
    refine ⟨h₀, hh₀, hh₀1, ?_⟩
    intro h hh hsmall r hr k hk
    exact hflux h hh hsmall ⟨r, hr⟩ r
      (fun _ => by simpa using (hε ⟨r, hr⟩).le) k hk
  · refine ⟨1, by norm_num, le_rfl, ?_⟩
    intro h hh hsmall r hr
    exact (hne ⟨r, hr⟩).elim

end Endotactic.DirectionalWall
end

-- Source: Endotactic/AffineDualBounds.lean
section
/-!
# Finite dual certificates for affine coordinate bounds

Nonnegative combinations of plateau inequalities that reconstruct a coordinate
or its negative certify lower and upper coordinate bounds. A rational LP solver
may discover these weights externally; Lean checks the identities and bounds
for every state. Neither solver correctness nor termination is assumed.

Such a certificate supplies compactness and positivity to the face-certificate
global solution API. This module does not claim that every endotactic network
has a suitable affine family or face certificate.
-/

namespace Endotactic

open Set

variable {d m : ℕ}

theorem AffineFamily.weighted_value_eq (A : AffineFamily d m) (w : Fin m → ℝ)
    (x : State d) :
    (∑ i, w i * A.value i x) = dot (fun j => ∑ i, w i * A.slope i j) x +
      ∑ i, w i * A.offset i := by
  have hdot : (∑ i, w i * dot (A.slope i) x) =
      dot (fun j => ∑ i, w i * A.slope i j) x := by
    unfold dot
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [AffineFamily.value, mul_add, Finset.sum_add_distrib]
  rw [hdot]

theorem AffineFamily.weighted_plateau_bound (A : AffineFamily d m) {M : ℝ}
    (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) {x : State d} (hx : x ∈ A.plateau M) :
    M * (∑ i, w i) ≤ ∑ i, w i * A.value i x := by
  calc
    M * (∑ i, w i) = ∑ i, w i * M := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => mul_comm M (w i))
    _ ≤ ∑ i, w i * A.value i x :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hw i)

theorem dot_coordinate_mask (j : Fin d) (a : ℝ) (x : State d) :
    dot (fun k => if k = j then a else 0) x = a * x j := by
  classical
  simp [dot]

/-- A finite, checkable dual witness for coordinate bounds at one plateau level. -/
structure AffineFamily.BoxCertificate (A : AffineFamily d m) (M : ℝ)
    (lo hi : State d) where
  lowerWeight : Fin d → Fin m → ℝ
  upperWeight : Fin d → Fin m → ℝ
  lower_nonneg : ∀ j i, 0 ≤ lowerWeight j i
  upper_nonneg : ∀ j i, 0 ≤ upperWeight j i
  lower_coordinate : ∀ j k, (∑ i, lowerWeight j i * A.slope i k) =
    if k = j then 1 else 0
  upper_coordinate : ∀ j k, (∑ i, upperWeight j i * A.slope i k) =
    if k = j then -1 else 0
  lower_bound : ∀ j, lo j ≤ M * (∑ i, lowerWeight j i) -
    ∑ i, lowerWeight j i * A.offset i
  upper_bound : ∀ j, (∑ i, upperWeight j i * A.offset i) -
    M * (∑ i, upperWeight j i) ≤ hi j

theorem AffineFamily.BoxCertificate.plateau_subset_box (A : AffineFamily d m)
    {M : ℝ} {lo hi : State d} (C : A.BoxCertificate M lo hi) :
    A.plateau M ⊆ Icc lo hi := by
  intro x hx
  constructor
  · intro j
    have hb := A.weighted_plateau_bound (C.lowerWeight j) (C.lower_nonneg j) hx
    rw [A.weighted_value_eq] at hb
    have heq : (fun k => ∑ i, C.lowerWeight j i * A.slope i k) =
        (fun k => if k = j then 1 else 0) := funext (C.lower_coordinate j)
    rw [heq, dot_coordinate_mask, one_mul] at hb
    linarith [C.lower_bound j]
  · intro j
    have hb := A.weighted_plateau_bound (C.upperWeight j) (C.upper_nonneg j) hx
    rw [A.weighted_value_eq] at hb
    have heq : (fun k => ∑ i, C.upperWeight j i * A.slope i k) =
        (fun k => if k = j then -1 else 0) := funext (C.upper_coordinate j)
    rw [heq, dot_coordinate_mask, neg_one_mul] at hb
    linarith [C.upper_bound j]

theorem AffineFamily.BoxCertificate.isCompact (A : AffineFamily d m)
    {M : ℝ} {lo hi : State d} (C : A.BoxCertificate M lo hi) :
    IsCompact (A.plateau M) :=
  A.plateau_isCompact_of_subset M isCompact_Icc (C.plateau_subset_box A)

theorem AffineFamily.BoxCertificate.positive (A : AffineFamily d m)
    {M : ℝ} {lo hi : State d} (C : A.BoxCertificate M lo hi) (hlo : Positive lo) :
    A.plateau M ⊆ {x | Positive x} :=
  fun _ hx j => (hlo j).trans_le ((C.plateau_subset_box A hx).1 j)

variable {E : Type*} [Fintype E] [Nonempty (Fin m)]

theorem Network.exists_global_positive_of_affine_certificates (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} {lo hi : State d}
    (C : A.BoxCertificate M lo hi) (hlo : Positive lo)
    (hfaces : N.AffineFaceCertificate A ℓ u M) {z : State d} (hz : z ∈ A.plateau M) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧ ∀ t, 0 ≤ t → x t ∈ A.plateau M :=
  N.exists_global_positive_of_compact_affine_face_certificate hk A (C.isCompact A)
    (C.positive A hlo) hfaces hz

theorem Network.positiveWellPosed_of_affine_certificates (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} {lo hi : State d}
    (C : A.BoxCertificate M lo hi) (hlo : Positive lo)
    (hfaces : N.AffineFaceCertificate A ℓ u M) {z : State d} (hz : z ∈ A.plateau M) :
    N.PositiveWellPosed k z :=
  N.positiveWellPosed_of_compact_affine_face_certificate hk A (C.isCompact A)
    (C.positive A hlo) hfaces hz

end Endotactic
end

-- Source: Endotactic/ClassDualBounds.lean
section
/-!
# Coordinate dual certificates modulo conserved linear observables

Within a stoichiometric class, a conserved linear observable has the value at
the class representative. A nonnegative combination of plateau slopes may
therefore reconstruct a coordinate up to a conserved direction. This proves
relative coordinate bounds even when all plateau slopes point into a cone
and the ambient plateau is unbounded.

Conservation is checked by the finite reaction-projection equations. Candidate
weights and conserved directions can be discovered externally; the full
coordinate containment, compactness, positivity and global trapping below
are verified by Lean under the explicit face certificate.
-/

namespace Endotactic

open Set

variable {d m : ℕ} {E : Type*}

theorem dot_add_left (r s x : State d) : dot (r + s) x = dot r x + dot s x := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem Network.dot_eq_in_stoichiometricClass (N : Network d E) (r : State d)
    {x c : State d} (hx : x ∈ N.stoichiometricClass c)
    (hzero : ∀ e, N.projection r e = 0) : dot r x = dot r c :=
  dot_eq_of_zero_projections N r hx hzero

structure Network.ClassBoxCertificate (N : Network d E) (A : AffineFamily d m)
    (M : ℝ) (c lo hi : State d) where
  lowerWeight : Fin d → Fin m → ℝ
  upperWeight : Fin d → Fin m → ℝ
  lowerConserved : Fin d → State d
  upperConserved : Fin d → State d
  lower_nonneg : ∀ j i, 0 ≤ lowerWeight j i
  upper_nonneg : ∀ j i, 0 ≤ upperWeight j i
  lower_zero : ∀ j e, N.projection (lowerConserved j) e = 0
  upper_zero : ∀ j e, N.projection (upperConserved j) e = 0
  lower_coordinate : ∀ j k, (∑ i, lowerWeight j i * A.slope i k) =
    (if k = j then 1 else 0) + lowerConserved j k
  upper_coordinate : ∀ j k, (∑ i, upperWeight j i * A.slope i k) =
    (if k = j then -1 else 0) + upperConserved j k
  lower_bound : ∀ j, lo j ≤ M * (∑ i, lowerWeight j i) -
    (∑ i, lowerWeight j i * A.offset i) - dot (lowerConserved j) c
  upper_bound : ∀ j, (∑ i, upperWeight j i * A.offset i) +
    dot (upperConserved j) c - M * (∑ i, upperWeight j i) ≤ hi j

theorem Network.ClassBoxCertificate.class_plateau_subset_box (N : Network d E)
    (A : AffineFamily d m) {M : ℝ} {c lo hi : State d}
    (C : N.ClassBoxCertificate A M c lo hi) :
    A.plateau M ∩ N.stoichiometricClass c ⊆ Icc lo hi := by
  rintro x ⟨hx, hxC⟩
  constructor
  · intro j
    have hb := A.weighted_plateau_bound (C.lowerWeight j) (C.lower_nonneg j) hx
    rw [A.weighted_value_eq] at hb
    have heq : (fun k => ∑ i, C.lowerWeight j i * A.slope i k) =
        (fun k => if k = j then 1 else 0) + C.lowerConserved j :=
      funext (C.lower_coordinate j)
    rw [heq, dot_add_left, dot_coordinate_mask, one_mul,
      N.dot_eq_in_stoichiometricClass _ hxC (C.lower_zero j)] at hb
    linarith [C.lower_bound j]
  · intro j
    have hb := A.weighted_plateau_bound (C.upperWeight j) (C.upper_nonneg j) hx
    rw [A.weighted_value_eq] at hb
    have heq : (fun k => ∑ i, C.upperWeight j i * A.slope i k) =
        (fun k => if k = j then -1 else 0) + C.upperConserved j :=
      funext (C.upper_coordinate j)
    rw [heq, dot_add_left, dot_coordinate_mask, neg_one_mul,
      N.dot_eq_in_stoichiometricClass _ hxC (C.upper_zero j)] at hb
    linarith [C.upper_bound j]

theorem Network.ClassBoxCertificate.isCompact (N : Network d E)
    (A : AffineFamily d m) {M : ℝ} {c lo hi : State d}
    (C : N.ClassBoxCertificate A M c lo hi) :
    IsCompact (A.plateau M ∩ N.stoichiometricClass c) :=
  isCompact_Icc.of_isClosed_subset
    ((A.plateau_isClosed M).inter (N.stoichiometricClass_isClosed c))
    (C.class_plateau_subset_box N A)

theorem Network.ClassBoxCertificate.positive (N : Network d E)
    (A : AffineFamily d m) {M : ℝ} {c lo hi : State d}
    (C : N.ClassBoxCertificate A M c lo hi) (hlo : Positive lo) :
    A.plateau M ∩ N.stoichiometricClass c ⊆ {x | Positive x} :=
  fun _ hx j => (hlo j).trans_le ((C.class_plateau_subset_box N A hx).1 j)

variable [Fintype E] [Nonempty (Fin m)]

theorem Network.exists_global_positive_of_class_affine_certificates (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} {c lo hi : State d}
    (C : N.ClassBoxCertificate A M c lo hi) (hlo : Positive lo)
    (hfaces : N.ClassAffineFaceCertificate A ℓ u M c)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    ∃ x, N.IsGlobalPositiveSolution k z x ∧
      ∀ t, 0 ≤ t → x t ∈ A.plateau M ∩ N.stoichiometricClass c :=
  N.exists_global_positive_of_class_affine_face_certificate hk A c (C.isCompact N A)
    (C.positive N A hlo) hfaces hz

theorem Network.positiveWellPosed_of_class_affine_certificates (N : Network d E)
    {k : E → ℝ → ℝ} {ℓ u : ℝ} (hk : AdmissibleRates k ℓ u)
    (A : AffineFamily d m) {M : ℝ} {c lo hi : State d}
    (C : N.ClassBoxCertificate A M c lo hi) (hlo : Positive lo)
    (hfaces : N.ClassAffineFaceCertificate A ℓ u M c)
    {z : State d} (hz : z ∈ A.plateau M ∩ N.stoichiometricClass c) :
    N.PositiveWellPosed k z :=
  N.positiveWellPosed_of_class_affine_face_certificate hk A c (C.isCompact N A)
    (C.positive N A hlo) hfaces hz

end Endotactic
end

-- Source: Endotactic/ConversionPermanence.lean
section
/-!
# Complete measurable-rate permanence of the conservative conversion A ⇄ B

The full plateau `x ≥ α, y ≥ α` is unbounded. Its intersection with the
conserved class `x+y=s` is a positive compact segment. Nonnegative dual weights
plus the conserved normal `(1,1)` certify its upper bounds. Class-restricted
strict faces then give positive global existence for every positive initial
point. The known common target `x,y ≥ s/4` absorbs every positive trajectory
for all measurable rates in `[1,2]`, with active-branch margin `s/4`.

This exercises genuinely class-relative trapping; no full ambient compact
plateau and no explicit solution of the measurable linear equation are used.
-/

namespace Endotactic.Conversion

open Set

def conversion : Network 2 (Fin 2) where
  source := ![![1, 0], ![0, 1]]
  target := ![![0, 1], ![1, 0]]

theorem isEndotactic : conversion.IsEndotactic := by
  intro r e he
  fin_cases e
  · refine ⟨1, ?_, ?_⟩ <;>
      simp [conversion, Network.projection, Network.sourceLevel, Network.vector,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith
  · refine ⟨0, ?_, ?_⟩ <;>
      simp [conversion, Network.projection, Network.sourceLevel, Network.vector,
        realComplex, dot, Fin.sum_univ_succ] at * <;> linarith

theorem total_projection_zero (e : Fin 2) : conversion.projection ![1, 1] e = 0 := by
  fin_cases e <;> norm_num [conversion, Network.projection, Network.vector,
    realComplex, dot, Fin.sum_univ_succ]

theorem class_iff_total {y c : State 2} :
    y ∈ conversion.stoichiometricClass c ↔ y 0 + y 1 = c 0 + c 1 := by
  constructor
  · intro hy
    have hh := conversion.dot_eq_in_stoichiometricClass ![1, 1] hy total_projection_zero
    simpa [dot, Fin.sum_univ_succ] using hh
  · intro hs
    change y - c ∈ conversion.stoichiometricSubspace
    have heq : y - c = (y 1 - c 1) • conversion.vector 0 := by
      ext i
      fin_cases i <;> simp [conversion, Network.vector, realComplex]
      linarith
    rw [heq]
    exact conversion.stoichiometricSubspace.smul_mem _ (Submodule.subset_span ⟨0, rfl⟩)

theorem rhs_at (a : Fin 2 → ℝ) (y : State 2) :
    conversion.rhs a y 0 = -a 0 * y 0 + a 1 * y 1 ∧
      conversion.rhs a y 1 = a 0 * y 0 - a 1 * y 1 := by
  constructor <;> simp [conversion, Network.rhs, monomial, Network.vector,
    realComplex, Fin.sum_univ_succ]
  ring

noncomputable def family (α : ℝ) : AffineFamily 2 2 where
  slope := ![![1, 0], ![0, 1]]
  offset := ![-α, -α]

theorem family_value (α : ℝ) (i : Fin 2) (y : State 2) :
    (family α).value i y = ![y 0 - α, y 1 - α] i := by
  fin_cases i <;> simp [family, AffineFamily.value, dot, Fin.sum_univ_succ] <;> ring

noncomputable def familyBoxCertificate (α : ℝ) (c : State 2) :
    conversion.ClassBoxCertificate (family α) 0 c
      (![α, α] : State 2) ![c 0 + c 1 - α, c 0 + c 1 - α] where
  lowerWeight := ![![1, 0], ![0, 1]]
  upperWeight := ![![0, 1], ![1, 0]]
  lowerConserved := fun _ => 0
  upperConserved := fun _ => ![1, 1]
  lower_nonneg := by intro j i; fin_cases j <;> fin_cases i <;> norm_num
  upper_nonneg := by intro j i; fin_cases j <;> fin_cases i <;> norm_num
  lower_zero := by intro j e; simp [Network.projection, dot]
  upper_zero := fun _ => total_projection_zero
  lower_coordinate := by
    intro j k
    fin_cases j <;> fin_cases k <;> norm_num [family, Fin.sum_univ_succ]
  upper_coordinate := by
    intro j k
    fin_cases j <;> fin_cases k <;> norm_num [family, Fin.sum_univ_succ]
  lower_bound := by
    intro j
    fin_cases j <;> simp [family, dot, Fin.sum_univ_succ]
  upper_bound := by
    intro j
    fin_cases j <;> simp [family, dot, Fin.sum_univ_succ, sub_eq_add_neg, add_comm]

theorem family_class_box (α : ℝ) (c : State 2) :
    (family α).plateau 0 ∩ conversion.stoichiometricClass c ⊆
      Icc (![α, α] : State 2) ![c 0 + c 1 - α, c 0 + c 1 - α] :=
  (familyBoxCertificate α c).class_plateau_subset_box conversion (family α)

theorem family_class_compact (α : ℝ) (c : State 2) :
    IsCompact ((family α).plateau 0 ∩ conversion.stoichiometricClass c) :=
  (familyBoxCertificate α c).isCompact conversion (family α)

theorem family_class_positive {α : ℝ} (hα : 0 < α) (c : State 2) :
    (family α).plateau 0 ∩ conversion.stoichiometricClass c ⊆ {y | Positive y} :=
  (familyBoxCertificate α c).positive conversion (family α) (by
    intro i; fin_cases i <;> exact hα)

theorem family_face_certificate {α : ℝ} (c : State 2)
    (hα : 0 < α) (hα4 : 4 * α ≤ c 0 + c 1) :
    conversion.ClassAffineFaceCertificate (family α) 1 2 0 c := by
  intro i
  right
  intro a ha y hy he
  have hs := class_iff_total.mp hy.2
  fin_cases i
  · have hx : y 0 = α := by
      have hh : y 0 - α = 0 := by simpa [family_value] using he
      linarith
    have hy0 : 0 ≤ y 1 := by linarith
    have hu := mul_le_mul_of_nonneg_right (ha.2 0) hα.le
    have hl := mul_le_mul_of_nonneg_right (ha.1 1) hy0
    change 0 < dot ((family α).slope 0) (conversion.rhs a y)
    simp [family, dot, Fin.sum_univ_succ]
    rw [(rhs_at a y).1, hx]
    nlinarith
  · have hy' : y 1 = α := by
      have hh : y 1 - α = 0 := by simpa [family_value] using he
      linarith
    have hx0 : 0 ≤ y 0 := by linarith
    have hu := mul_le_mul_of_nonneg_right (ha.2 1) hα.le
    have hl := mul_le_mul_of_nonneg_right (ha.1 0) hx0
    change 0 < dot ((family α).slope 1) (conversion.rhs a y)
    simp [family, dot, Fin.sum_univ_succ]
    rw [(rhs_at a y).2, hy']
    nlinarith

theorem exists_global_positive {k : Fin 2 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 2} (hz : Positive z) :
    ∃ x, conversion.IsGlobalPositiveSolution k z x := by
  let α : ℝ := min (min (z 0) (z 1)) ((z 0 + z 1) / 4)
  have hα : 0 < α := lt_min (lt_min (hz 0) (hz 1)) (by linarith [hz 0, hz 1])
  have hα0 : α ≤ z 0 := (min_le_left _ _).trans (min_le_left _ _)
  have hα1 : α ≤ z 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hα4 : 4 * α ≤ z 0 + z 1 := by linarith [min_le_right (min (z 0) (z 1)) ((z 0 + z 1) / 4)]
  have hzA : z ∈ (family α).plateau 0 ∩ conversion.stoichiometricClass z := by
    constructor
    · intro i; fin_cases i <;> simp [family_value] <;> linarith
    · exact class_iff_total.mpr rfl
  obtain ⟨x, hx, _⟩ := conversion.exists_global_positive_of_class_affine_certificates hk
    (family α) (familyBoxCertificate α z)
    (by intro i; fin_cases i <;> exact hα) (family_face_certificate z hα hα4) hzA
  exact ⟨x, hx⟩

theorem positiveWellPosed {k : Fin 2 → ℝ → ℝ}
    (hk : AdmissibleRates k 1 2) {z : State 2} (hz : Positive z) :
    conversion.PositiveWellPosed k z :=
  conversion.positiveWellPosed_of_exists hk (exists_global_positive hk hz)

noncomputable def absorbingFamily (s : ℝ) : AffineFamily 2 3 where
  slope := ![![1, 0], ![0, 1], ![0, 0]]
  offset := ![-s / 4, -s / 4, 0]

theorem absorbingFamily_value (s : ℝ) (i : Fin 3) (y : State 2) :
    (absorbingFamily s).value i y = ![y 0 - s / 4, y 1 - s / 4, 0] i := by
  fin_cases i <;> simp [absorbingFamily, AffineFamily.value, dot, Fin.sum_univ_succ] <;> ring

theorem absorbingFamily_plateau (s : ℝ) :
    (absorbingFamily s).plateau 0 = (family (s / 4)).plateau 0 := by
  ext y
  constructor
  · intro hy i
    fin_cases i
    · simpa [family_value, absorbingFamily_value] using hy 0
    · simpa [family_value, absorbingFamily_value] using hy 1
  · intro hy i
    fin_cases i
    · simpa [family_value, absorbingFamily_value] using hy 0
    · simpa [family_value, absorbingFamily_value] using hy 1
    · simp [absorbingFamily_value]

theorem absorbingFamily_cap (s : ℝ) (y : State 2) : (absorbingFamily s).minimum y ≤ 0 := by
  have hh := finiteMinimum_le (fun i => (absorbingFamily s).value i y) 2
  simpa [AffineFamily.minimum, absorbingFamily_value] using hh

theorem absorbingFamily_flux_margin (s : ℝ) (a : Fin 2 → ℝ)
    (ha : a ∈ Icc (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ))) (y : State 2)
    (hy : Positive y) (htotal : y 0 + y 1 = s)
    (hbelow : (absorbingFamily s).minimum y < 0) (i : Fin 3)
    (hai : (absorbingFamily s).Active i y) :
    s / 4 ≤ dot ((absorbingFamily s).slope i) (conversion.rhs a y) := by
  have heq := ((absorbingFamily s).active_iff_minimum_eq i y).mp hai
  fin_cases i
  · have hx : y 0 < s / 4 := by
      have hh : (absorbingFamily s).minimum y = y 0 - s / 4 := by
        simpa [absorbingFamily_value] using heq
      linarith
    have hu := mul_le_mul_of_nonneg_right (ha.2 0) (hy 0).le
    have hl := mul_le_mul_of_nonneg_right (ha.1 1) (hy 1).le
    simp [absorbingFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a y).1]
    nlinarith
  · have hy' : y 1 < s / 4 := by
      have hh : (absorbingFamily s).minimum y = y 1 - s / 4 := by
        simpa [absorbingFamily_value] using heq
      linarith
    have hu := mul_le_mul_of_nonneg_right (ha.2 1) (hy 1).le
    have hl := mul_le_mul_of_nonneg_right (ha.1 0) (hy 0).le
    simp [absorbingFamily, dot, Fin.sum_univ_succ]
    rw [(rhs_at a y).2]
    nlinarith
  · have hh : (absorbingFamily s).minimum y = 0 := by
      simpa [absorbingFamily_value] using heq
    linarith

theorem uniformPermanent (c : State 2) (hs : 0 < c 0 + c 1) :
    conversion.UniformPermanent 1 2 c (fun _ => True) := by
  let s : ℝ := c 0 + c 1
  have hs' : 0 < s := hs
  have hpos : (absorbingFamily s).plateau 0 ∩ conversion.stoichiometricClass c ⊆
      {y | Positive y} := by
    rw [absorbingFamily_plateau]
    exact family_class_positive (by linarith) c
  have heq : (absorbingFamily s).plateau 0 ∩ conversion.positiveClass c =
      (absorbingFamily s).plateau 0 ∩ conversion.stoichiometricClass c := by
    ext y
    constructor
    · rintro ⟨hy, hp, hc⟩
      exact ⟨hy, hc⟩
    · intro hy
      exact ⟨hy.1, hpos hy, hy.2⟩
  have hne : ((absorbingFamily s).plateau 0 ∩ conversion.positiveClass c).Nonempty := by
    rw [heq, absorbingFamily_plateau]
    refine ⟨![s / 2, s / 2], ?_, ?_⟩
    · intro i; fin_cases i <;> simp [family_value] <;> linarith
    · apply class_iff_total.mpr
      simp [s]
  have hcompact : IsCompact ((absorbingFamily s).plateau 0 ∩ conversion.positiveClass c) := by
    rw [heq, absorbingFamily_plateau]
    exact family_class_compact _ _
  apply conversion.uniformPermanent_of_affine_plateau (absorbingFamily s) 1 2 0 c
    (fun _ => True) hne hcompact (fun y _ => absorbingFamily_cap s y)
  · intro k hk _ z hz
    exact positiveWellPosed hk hz.1
  · intro k hk _ z hz x hx
    refine ⟨s / 4, by linarith, ?_⟩
    intro t ht hb i hi
    have hclass := hx.mem_positiveClass hz ht
    have htotal : x t 0 + x t 1 = s := class_iff_total.mp hclass.2
    exact absorbingFamily_flux_margin s _
      ⟨fun e => (hk.2 e t ht).1, fun e => (hk.2 e t ht).2⟩ _ (hx.2 t ht) htotal hb i hi

end Endotactic.Conversion
end

-- Source: Endotactic/GeneralPermanenceExamples.lean
section
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
end

#print axioms EndotacticFC.extended_permanence
#print axioms EndotacticFC.measurable_extended_permanence
