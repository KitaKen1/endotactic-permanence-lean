# Endotactic permanence in Lean 4

The finite natural-exponent formulation of the Extended Permanence Conjecture
([Craciun–Nazarov–Pantea (2011), Section 4](https://arxiv.org/abs/1010.3050v2)) is:

> **Conjecture.**
> Every finite endotactic mass-action network, with locally piecewise
> differentiable rates bounded in a fixed positive coefficient box, is
> permanent on each positive stoichiometric class.

This repository presents a **Lean 4 proof** of this formulation.

Contributions:

1. **FC-style formalization** of the conjecture ([statement](FClikelean/EndotacticPermanence.lean)).
2. **Lean 4 proof** of permanence ([proof](lean/EndotacticPublication/FCPresentation.lean)).

SubContribution:

1. **A stronger theorem** for bounded measurable rates with a common absorbing set
   ([appendix](#appendix-relationship-between-the-original-conjecture-and-the-strengthening)).

<!-- PUBLICATION-LINKS:START -->
**Try it in Lean4Web:** [open the complete proof in one file](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fendotactic-permanence-lean%2Fmain%2Flean4web%2FEndotacticPermanenceLean4Web.lean) (Lean **v4.35.0-rc4**).
<!-- PUBLICATION-LINKS:END -->

## Formal Conjectures targets

[EndotacticPermanence.lean](FClikelean/EndotacticPermanence.lean) states the
**main Extended Permanence target** in the namespace `Endotactic`:

~~~lean
@[category research solved, AMS 34 92]
theorem extended_permanence :
    answer(True) ↔
      ∀ (d m : ℕ), 0 < d → ∀ N : Endotactic.Network d m,
        N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
          ∀ k : Fin m → ℝ → ℝ, Endotactic.AdmissibleRates k ℓ u →
            Endotactic.LocallyPiecewiseDifferentiableRates k →
              ∀ c : Fin d → ℝ, Endotactic.Positive c →
                N.PermanentForRates k c := by
  sorry
~~~

The same file states the **measurable-rate, common-box theorem** listed under
SubContribution:

~~~lean
@[category research solved, AMS 34 92]
theorem measurable_extended_permanence :
    answer(True) ↔
      ∀ (d m : ℕ), 0 < d → ∀ N : Endotactic.Network d m,
        N.IsEndotactic → ∀ (ℓ u : ℝ), 0 < ℓ → ℓ ≤ u →
          ∀ c : Fin d → ℝ, Endotactic.Positive c →
            N.UniformPermanent ℓ u c := by
  sorry
~~~

Both targets place `answer(True)` outside all quantifiers. Their `by sorry`
bodies are FC statement placeholders; [FCPresentation.lean](lean/EndotacticPublication/FCPresentation.lean)
proves the same coordinate-bound targets without holes. The strengthening is explained
in the [appendix](#appendix-relationship-between-the-original-conjecture-and-the-strengthening).

## Mathematical explanation (AI generated)

The proof first establishes the stronger measurable-rate theorem in the
[appendix](#appendix-relationship-between-the-original-conjecture-and-the-strengthening).
Restricting to locally piecewise differentiable rates then gives the main
conjecture. We sketch this argument below; the links identify the corresponding
Lean arguments.

**Setup and goal.** Write $v_e=y'_e-y_e$ for the reaction vectors and
$x^{y_e}=\prod_{j=1}^d x_j^{(y_e)_j}$ for the source monomials. Set

~~~math
F_a(x)=\sum_e a_e x^{y_e}v_e,\qquad
\dot x(t)=F_{k(t)}(x(t)),\qquad k(t)\in[\ell,u]^E,
\quad 0<\ell\le u.
~~~

Solutions are understood in the integral sense, so the differential equation
holds almost everywhere. Let $S=\operatorname{span}\{v_e:e\in E\}$ and fix
$c\in\mathbb R_{>0}^d$. Since $F_a(x)\in S$, solutions starting in $c+S$
remain in this affine space. We prove global positive existence and uniqueness
and construct a compact set $K\subset(c+S)\cap\mathbb R_{>0}^d$ that eventually
contains every positive trajectory in the class. The set must be chosen before
the rate path and the initial state; the entry time may depend on both.

**1. Endotacticity gives a positive projected flux.** Fix a direction
$r\notin S^\perp$. Among reactions with $r\cdot v_e\ne0$, choose $e_*$
minimizing $r\cdot y_e$. Endotacticity implies $r\cdot v_{e_*}>0$:
a negative projection would require a positive reaction at a strictly lower
source level. For the same reason, every negatively projected reaction has
$r\cdot(y_e-y_{e_*})>0$.

These finitely many strict gaps persist when the exponent vector is perturbed
from $r$ to a sufficiently close $p$. Thus there are
$\varepsilon(r),\gamma_r>0$ such that, for $0<h<1$ and
$\|p-r\|_\infty<\varepsilon(r)$, the point $x=h^p=(h^{p_1},\ldots,h^{p_d})$
satisfies

~~~math
\frac{x^{y_e}}{x^{y_{e_*}}}
 =h^{p\cdot(y_e-y_{e_*})}\le h^{\gamma_r}
 \quad\text{whenever }r\cdot v_e<0,
~~~

and consequently

~~~math
r\cdot F_a(x)\ge x^{y_{e_*}}
\left(\ell\,r\cdot v_{e_*}
 -u h^{\gamma_r}\sum_{r\cdot v_e<0}|r\cdot v_e|\right)>0
~~~

for all sufficiently small $h$, uniformly over $a\in[\ell,u]^E$.
Directions in $S^\perp$ instead have identically zero projected flux.
See [FluxBound.lean](lean/Endotactic/FluxBound.lean) and
[FiniteSlopeDominance.lean](lean/Endotactic/FiniteSlopeDominance.lean).

**2. Turn directional estimates into finitely many affine barriers.**
The main geometric lemma constructs fixed slopes $r_1,\ldots,r_m\in[-1,1]^d$
and scale-dependent offsets $b_i(h)$. Define

~~~math
L_{i,h}(x)=r_i\cdot x+b_i(h),\qquad
\Phi_h(x)=\min_{1\le i\le m}L_{i,h}(x).
~~~

A branch is *active* at $x$ when $L_{i,h}(x)=\Phi_h(x)$.
For any prescribed pointwise positive tolerance $\varepsilon$, the family can
be chosen so that, for all sufficiently small $h$,

~~~math
p\in[-1,1]^d,\quad L_{i,h}(h^p)=\Phi_h(h^p)
\quad\Longrightarrow\quad
\|p-r_i\|_\infty<\varepsilon(r_i).
~~~

This holds for every minimizing branch, including ties. The affine functions
are functions of the concentration $x$; the logarithmic coordinates $p$ locate
where their slopes give the flux estimate from Step 1.

The lemma is proved by induction on dimension. At a fixed minimum coordinate
$t=\min_j p_j$, lower-dimensional families are lifted by putting slope $t$
in the remaining coordinates; comparisons with competing branches control
those remaining coordinates. The resulting estimates extend to a neighborhood
of $t$. A finite interval cover of the possible minimum levels, with ordered
overlaps and suitable offset shifts, combines these local families.
The construction allows discontinuous tolerances with no positive uniform
lower bound. See
[MinimumBandSelection.lean](lean/Endotactic/MinimumBandSelection.lean) and
[AffineApproximationExistence.lean](lean/Endotactic/AffineApproximationExistence.lean).

Choose the tolerance small enough for Step 1, and also require
$\varepsilon(0)\le1/8$ and
$\varepsilon(r)\le\|r\|_\infty/2$ for $r\ne0$.
Since there are only finitely many slopes, one small-scale threshold works
for all of them. Throughout $[h,h^{-1}]^d$, every active branch then has
positive projected flux unless its slope belongs to $S^\perp$.
See [ActivityFluxBridge.lean](lean/Endotactic/ActivityFluxBridge.lean).

**3. Construct compact invariant sets that capture every positive point.**
For any fixed $z>0$, its exponent vector
$p_h(z)=(\log z_j/\log h)_j$ tends to $0$ as $h\downarrow0$.
The tolerance condition and finiteness of the slopes force every branch active
at $z$ to have slope zero once $h$ is sufficiently small.
A zero-slope branch is constant, so whenever it is active, $\Phi_h$ attains
its global maximum. In particular, for small $h$, put

~~~math
M_h=\Phi_h(c)=\max_{x\in\mathbb R^d}\Phi_h(x),\qquad
P_h=\{x:\Phi_h(x)=M_h\}.
~~~

The set $P_h$ is a closed convex polyhedron containing $c$.
For small $h$, the point $c$ lies inside $(h^{1/4},h^{-1/4})^d$.
So does all of $P_h$: otherwise a segment from $c$ to a point of $P_h$
outside this box would meet its boundary. At that boundary point,
$\|p_h(x)\|_\infty=1/4$, while the active zero-slope branch requires
$\|p_h(x)\|_\infty<\varepsilon(0)\le1/8$, a contradiction.

On the compact boundary of this box, the continuous function $\Phi_h$ has
maximum strictly below $M_h$. Choose $Q_h$ between that maximum and $M_h$.
Convexity again excludes any superlevel point outside the box, giving

~~~math
Q_h=M_h-\delta_h\quad(\delta_h>0),\qquad
B_h=\{x:\Phi_h(x)\ge Q_h\}
\subset(h^{1/4},h^{-1/4})^d.
~~~

Thus $B_h$ is compact and strictly positive. On each face, the corresponding
affine branch is active, so its derivative along the vector field is either
strictly positive or identically zero by conservation. Hence $B_h$ is forward
invariant for every admissible rate path. Every fixed $z>0$ belongs to $P_h$,
and hence to $B_h$, for all sufficiently small $h$.
Local existence and uniqueness for the measurable-in-time, locally
Lipschitz-in-state vector field, together with this compact confinement,
give global positive solutions.
See [NarrowZeroCap.lean](lean/Endotactic/NarrowZeroCap.lean) and
[ScaleTrapConstruction.lean](lean/Endotactic/ScaleTrapConstruction.lean).

**4. Pass from an initial trap to a common scale.** Fix $0<H<1$ so that
the flux, box and invariance properties hold for $0<h\le H$. Suppose a
trajectory in $c+S$ eventually stays in $B_h$ for some such $h$, and set
$g=\min\{\sqrt h,H\}$. Since
$g\le h^{1/4}$, we have

~~~math
B_h\subset[h^{1/4},h^{-1/4}]^d\subset[g,g^{-1}]^d.
~~~

The flux estimates for $\Phi_g$ therefore apply throughout the old trap.
Moreover, at a point $x\in c+S$ with $\Phi_g(x)<M_g$, no active slope can
belong to $S^\perp$: such a branch is constant on $c+S$ and has value at least
$M_g$ at $c$, contradicting activity at $x$.

On the compact set
$B_h\cap(c+S)\cap\{\Phi_g\le Q_g\}$, all active projected fluxes are
therefore strictly positive. Continuity, the compact coefficient box and
finiteness of the branches give a uniform lower bound $\eta>0$.
Along the trajectory, the finite minimum of affine observables is absolutely
continuous. Thus, after entry into $B_h$, the capped function

~~~math
\psi(t)=\min\{\Phi_g(x(t)),Q_g\}
\quad\text{satisfies}\quad
\psi'(t)\ge\eta\ \text{a.e. on }\{t:\psi(t)<Q_g\}.
~~~

It reaches $Q_g$ in finite time and stays there, proving eventual residence
in $B_g$. The strict gap $Q_g<M_g$ supplies the positive margin needed for
finite entry. This argument uses box containment and does not require the
sets $B_h$ to be nested.
See [LateCompactAbsorption.lean](lean/Endotactic/LateCompactAbsorption.lean) and
[ScaleTrapPermanence.lean](lean/Endotactic/ScaleTrapPermanence.lean).

**5. Finish the permanence argument.** Given any positive initial state in
$c+S$, Step 3 supplies an initial scale $h_0\le H$. Iterate

~~~math
h_{n+1}=\min\{\sqrt{h_n},H\},\qquad
h_n=\min\{h_0^{\,2^{-n}},H\}.
~~~

Since $h_0^{2^{-n}}\to1$ and $H<1$, the sequence reaches $H$ after finitely
many steps. Repeated application of Step 4 gives eventual residence in
$K=B_H\cap(c+S)$. This set is nonempty, compact and contained in the positive
class. It depends only on the network, coefficient bounds and chosen class
representative. The initial scale and the successive entry times may depend
on the trajectory, but $K$ does not. This proves the common-box measurable-rate
statement; restricting the rates gives the displayed piecewise-rate statement.
See [GeneralPermanence.lean](lean/Endotactic/GeneralPermanence.lean).

The FC presentation expresses compact absorption as common eventual bounds
`ε ≤ x t i ∧ x t i ≤ ε⁻¹`, with `0 < ε < 1`.
[CoordinateBounds.lean](lean/EndotacticPublication/CoordinateBounds.lean) proves
both directions: a compact positive set has uniform coordinate bounds, and
a coordinate box intersected with the closed affine class is compact.

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [FClikelean/](FClikelean/) | v4.33.1 | Self-contained FC-style statements, definitions and docstrings |
| [lean/](lean/) | v4.33.1 | Complete proof library and publication targets |
| [lean4web/](lean4web/) | v4.35.0-rc4 | Complete Mathlib-only proof in one file |

The modular entry point is
[EndotacticPublication.lean](lean/EndotacticPublication.lean).
The single-file edition includes 83 modules and 9,323 lines, generated by
[make_lean4web.py](lean/scripts/make_lean4web.py). Its
[source map](lean4web/source-map.json) records the original hashes and line spans.
The generator scopes each source module separately and adapts five renamed
conditional lemmas for Lean 4.35.

## Verification

Latest local audit: **PASS** — both proof builds and 754 project theorems checked.
The complete proofs have no holes and use only `propext`, `Classical.choice`
and `Quot.sound`. The FC-style draft has two intentional statement stubs.

The audit checks both FC targets using the pinned Formal Conjectures utility.
It compares the compiled presentation definitions and target types, checks
network conversion, and verifies equivalence with compact absorption in Lean. The FC draft is written independently of the
proof-library interface.

To reproduce the audit:

~~~bash
cd lean
lake exe cache get
python3 scripts/build_audit.py
~~~

Details: [audit results](lean/evidence/build_results.json) and
[build log](lean/evidence/build.log).

## References

- [Ki26] K. Kitamura, *Endotactic permanence* (2026),
  [Lean proof in this repository](lean/EndotacticPublication/FCPresentation.lean).
- [CNP11] G. Craciun, F. Nazarov and C. Pantea,
  [Persistence and permanence of mass-action and power-law dynamical systems](https://arxiv.org/abs/1010.3050v2),
  Definitions 2.6, 2.9–2.10 and Section 4.
- [GMS13] M. Gopalkrishnan, E. Miller and A. Shiu,
  [A projection argument for differential inclusions](https://arxiv.org/abs/1208.0874),
  Conjecture 6.5, as related broader-scope work.
- [TauCeti](https://github.com/TauCetiProject/TauCeti): autonomous ODE, AC and
  polyhedron API references; no package dependency was introduced.
- [LeanPool](https://github.com/LeanPool/lean-pool): attributed interval-clamp
  and continuous-path adaptations for the local Volterra construction.
  [Third-party notices](THIRD_PARTY_NOTICES.txt) and Apache notices are preserved.
- [Prove2Me](https://github.com/prove2me/prove2me_workspace/blob/main/references/prove.md)
  and [LeanEval](https://github.com/leanprover/lean-eval): exact-target and
  transitive-dependency verification references. Their services were not run.
- [PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) and
  [leanblueprint](https://github.com/PatrickMassot/leanblueprint): large-proof
  organization and dependency-documentation references. Official Blueprint
  rendering was not run for this package.
- [Formal Conjectures contribution guide](https://github.com/google-deepmind/formal-conjectures/blob/89294ea02bd7cd678d59984add52cb4baef3dbf4/CONTRIBUTING.md)
  at the utility pin.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra and GPT-6.1 sol.

## Appendix: relationship between the original conjecture and the strengthening

### Natural language relationship between the original conjecture and the strengthening

| Statement | Natural-language claim |
|---|---|
| Original conjecture | Each bounded measurable, locally piecewise differentiable rate path has a compact positive set in the class absorbing all positive trajectories. The set may depend on the path. |
| Strengthening | One compact positive set in the class absorbs all positive trajectories for every bounded measurable rate path in the coefficient box. |

Both statements concern finite natural-exponent endotactic networks in positive
dimension, with a fixed positive coefficient box and positive class. They include
positive global existence and uniqueness; entry times may depend on the trajectory.

**The strengthening implies the original conjecture:** restrict the rate paths
to locally piecewise differentiable ones and reuse the common compact set.

### Lean language relationship between the original conjecture and the strengthening

| Statement | Lean proposition |
|---|---|
| Original conjecture | `Endotactic.OriginalExtendedPermanenceConjecture` |
| Strengthening | `Endotactic.MeasurableExtendedPermanenceConjecture` |

The implication composes two lemmas from
[Permanence.lean](lean/Endotactic/Permanence.lean):

~~~lean
example (h : Endotactic.MeasurableExtendedPermanenceConjecture) :
    Endotactic.OriginalExtendedPermanenceConjecture :=
  Endotactic.uniform_extended_conjecture_implies_original
    (Endotactic.measurable_conjecture_implies_extended h)
~~~

[FCPresentation.lean](lean/EndotacticPublication/FCPresentation.lean) proves both
coordinate-bound targets. [CoordinateBounds.lean](lean/EndotacticPublication/CoordinateBounds.lean)
proves their equivalence with the compact-set formulations.

## Appendix: timeline

| Year | Who | Stage | Problem or result |
|---|---|---|---|
| 2010–2011 | [Craciun–Nazarov–Pantea](https://arxiv.org/abs/1010.3050v2) | Preprint and conjecture formulation | Introduces endotactic networks, proves two-species permanence, and states the Extended Permanence Conjecture in Section 4. |
| 2026 | **This repository (Kenta Kitamura)** | **Local Lean 4 proof** | Proves the displayed finite natural-exponent conjecture and its measurable-rate, common-box strengthening. |
