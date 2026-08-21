# Domain traces: Lean formalization of Sections 5.1–5.2

This Lean 4 project formalizes the domain construction and the smooth-boundary-trace reduction in the supplied text. It targets Lean `v4.33.0` and mathlib `v4.33.0`.

The project contains no `sorry`, `admit`, or custom `axiom` declarations.

## Build

From this directory:

```bash
lake build
```

The first build downloads the pinned mathlib revision.

## Files

- `DomainTraces/FlatBump.lean` develops
  \(b_a(t)=\operatorname{sgn}(t)e^{-a/t^2}\), including strict monotonicity, range bounds, `C∞` regularity, and vanishing of every iterated derivative at zero.
- `DomainTraces/DomainConstruction.lean` formalizes Section 5.1.
- `DomainTraces/SmoothBoundaryTraces.lean` formalizes Section 5.2 and states explicit interfaces for results imported from earlier sections of the paper and for trace theory not yet packaged in mathlib.
- `DomainTraces.lean` is the root import.

The barred coordinate space is an arbitrary real normed space `E`. For the paper's literal \(\mathbb R^n\), instantiate

```lean
E := EuclideanSpace ℝ (Fin (n - 1))
```

and regard `E × ℝ` as `(x̄,y)`. The separate theorem `norm_euclideanCylindricalGradient` uses mathlib's canonical Euclidean `ℓ²` norm in every dimension.

## Correspondence with the text

| Text | Principal Lean declarations | Status |
|---|---|---|
| signed flat function (0.56) | `flatBump`, `flatBump.contDiff`, `flatBump.strictMono`, `flatBump.iteratedDeriv_zero` | proved |
| `s`, `Λ`, and `Ω` (0.49.1) | `s`, `lam`, `paperLambda`, `paperOmega` | defined |
| graph description (0.49), (0.67) | `paperOmega_membership` | proved exactly |
| openness, boundedness, connectedness | `paperOmega_isOpen`, `paperOmega_isBounded`, `paperOmega_isPathConnected` | proved; connectedness is strengthened to star-convexity about `(0,-r/2)` |
| smooth boundary | `paper_regular_defining_function` | proves `Λ ∈ C∞`, `frontier Ω = {Λ=0}`, and `fderiv Λ z ≠ 0` on the zero level |
| projection bound (0.59) | `paper_projection_closure_subset_cube` | proved |
| zero-height slices (0.65)–(0.66) | `paperOmega_slice_zero`, `paperOmega_frontier_slice_zero` | proved |
| cylindrical gradient (0.72) | `norm_cylindricalGradient`, `norm_euclideanCylindricalGradient` | proved, including the literal Euclidean-norm version |
| exponent and factorization (0.53) | `alpha`, `signedRpow`, `PlanarInput.representation_5_9` | definitions; the representation is an input from Sections 3–4 |
| upper-graph identities (0.54) | `paperYPlus_mul_add_r_of_s_le_one`, `paperYPlus_add_r_pos` | proved |
| flat factor `b_p` | `boundaryBump`, `boundaryBump_contDiff`, `boundaryBump_vanishes_to_all_orders` | proved |
| signed boundary power (0.57) | `paper_hasBoundaryPowerIdentity` | proved, including the contact case `s=0` |
| boundary formula (0.58) | `paper_equation_5_12`, `PlanarInput.lifted_boundary_formula_of_s_lt_one` | proved from the planar representation |
| Hölder lift | `HolderBoundOn`, `PlanarInput.liftedValue_holder` | proved |
| weak-tail lift (0.75) | `WeakTailBoundOn`, `CylindricalTailComparison`, `PlanarInput.liftedGradient_weakTail` | proved from the explicit finite-fiber/Fubini comparison |
| smooth extension and zero trace (0.70) | `HasSmoothTraceExtension`, `TraceInterface` | explicit interface; see below |

## Explicit dependency boundary

Section 5.2 depends on results not contained in the supplied sections:

1. The two-dimensional minimizer, its kernel, weak gradient, representation formula, Hölder estimate, and planar weak-tail estimate come from Sections 3–4. They are collected without hidden axioms in the `PlanarInput` structure.
2. The dimensional weak-tail argument needs the finite measure of passive-coordinate fibers. `CylindricalTailComparison` states precisely that geometric/Fubini estimate, and `liftedGradient_weakTail` proves the claimed weak-tail bound from it.
3. Current mathlib has no general first-order `W₀¹,¹(Ω)` trace API matching (0.70), nor the needed packaged smooth extension theorem for a boundary hypersurface. `TraceInterface` therefore records the smooth extension, boundary agreement, and the chosen future zero-trace predicate explicitly.

Thus the elementary geometry, calculus, flatness, equations (0.54), (0.57), and (0.58), Hölder transport, and weak-tail transport are machine-checked. The earlier minimizer and the final general Sobolev trace theorem remain named hypotheses rather than being disguised as proved facts.

Mathlib also does not currently expose the paper's regular-set theorem as a one-line embedded-hypersurface constructor. `paper_regular_defining_function` proves its full hypotheses: smooth defining function, exact frontier, and nonzero Fréchet derivative on the level set.

## Source correction

At `y = -r/2`, the text says that `Λ=0` implies `s(x̄)^2=1`. The equation and strict monotonicity actually imply the stronger and necessary statement `s(x̄)=1`. This is formalized as `paper_s_eq_one_at_lower_equator`; it yields `‖x̄‖=√2 r` and the exceptional radial derivative `8`.

