# GMT reuse review for the Poincare project

Reviewed 2026-09-22 at
[`qinz1yang/gmt@f2bc42e99a9446b9b60462e8c8f93bebfede6982`](https://github.com/qinz1yang/gmt/tree/f2bc42e99a9446b9b60462e8c8f93bebfede6982).
This review inspected source declarations, selected proof bodies, repository
scope and dependency locks. It did not compile GMT or audit its transitive
axioms, add it to OpenGA's dependencies, copy its mathematics, or publish tasks.

## Assessment

GMT is a strong candidate for the Euclidean measure and varifold infrastructure
needed by the Colding-Minicozzi route. In particular, first variation and
stationarity no longer need to be treated as having no available upstream
implementation in the sources checked for this project.

GMT and OpenGA both pin Lean `v4.33.1` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. This removes an immediate toolchain
migration obstacle; it does not prove combined imports or interfaces compatible.

GMT deliberately keeps its Euclidean core independent of DifferentialGeometry.
Its AGENTS.md places Riemannian compatibility downstream. That fits an OpenGA
interoperability module connecting GMT with the existing geometric definitions.

## Available source interfaces and their limits

All paths below are relative to the pinned GMT checkout.

| Interface | Source declarations inspected | Poincare use and boundary |
| --- | --- | --- |
| General varifolds | `Varifold` in `GMT/Varifold/Defs.lean`; restriction and weight in `Basic.lean` | Locally finite measures on position/plane pairs. No rectifiability is built into the type. |
| First variation | `Varifold.firstVariation`, `firstVariation_apply`, `IsStationaryOn` in `FirstVariation.lean` | First variation is a continuous linear functional on compactly supported C1 test fields; stationarity is its vanishing. This is not defined by assuming monotonicity. |
| Stationary monotonicity | `Varifold.IsStationaryOn.monotonicity`, `massRatio_monotoneOn`, `tendsto_densityRatio` in `Monotonicity.lean` | Euclidean stationary varifolds on an open set, with the relevant closed ball contained in that set. This does not give the curved-ambient or nonstationary theorem automatically. |
| Area formula | `Area.area_formula`, `area_formula_of_contDiff` in `GMT/Area/Formula.lean` | Multiplicity-weighted Hausdorff area for Lipschitz/C1 Euclidean maps, including noninjective maps. Useful for identifying parametrized area with image measure. |
| Coarea and submanifolds | `Area.coarea_formula`, `coarea_formula_weighted` in `GMT/Area/Coarea.lean`; `IsContDiffSubmanifold` in `Submanifold.lean` | Euclidean C1 submanifold tangential calculus and coarea. A Riemannian manifold bridge is still needed. |
| Approximation | `IsWhitneyOneJetOn.exists_contDiff` and Lipschitz approximation in `GMT/Analysis/Whitney.lean` | Potential supporting analysis; not the CM harmonic replacement or bubble compactness theorem. |

The README expressly leaves the rectifiable-varifold representation bridge,
locally bounded first variation and nonstationary monotonicity unfinished.
It also does not claim completed Allard regularity, currents, or the full
rectifiability/BV program. Do not equate the intended scope with completed APIs.

## Concrete representation differences

| Object | OpenGA | GMT | Required bridge |
| --- | --- | --- | --- |
| Grassmannian | A dimension-k submodule, with metric induced by its orthogonal projection | A self-adjoint idempotent continuous linear operator with trace k | An isometric equivalence preserving the represented subspace and projection |
| Varifold | A measure on `E × OpenGA.Grassmannian E k` with `Measure.Regular` | A measure on `E × Grassmannian E k` finite on compact sets | Transport through the position-preserving product homeomorphism; verify measure regularity in the reverse direction |
| Area Jacobian | `OpenGA.Varifold.surfaceJacobian`, an NNReal norm determinant | `Area.jacobian`, a real norm determinant; `jacobianWithin` for set-domain maps | Coercion and derivative-domain identities, keeping the original domains |
| Base measure | Lebesgue volume on the two-dimensional parameter space | Normalized Hausdorff measure `μHE[2]` | An explicit equality of source measures and preserved multiplicity |

Do not replace either definition with an unproved coercion or silently identify
the Euclidean inner product with an arbitrary time-dependent Riemannian metric.

## Revised first batch

Together with T1 and T3 from [the main plan](CROWDSOURCING_PLAN.md), prioritize
the following three bounded integration tasks. Proposed home:
`OpenGALib/Interoperability/GMT/`, after a pinned dependency is introduced and
reviewed. These names and paths are proposals, not files already implemented.

### G1 — Grassmannian isometric equivalence

- **Input:** `OpenGA.Grassmannian.range_projection`, its `isometry_projection`,
  and GMT's `Grassmannian.ofSubmodule`, `subspace`, `finrank_subspace`,
  `projection_eq_starProjection`.
- **Output:** an isometric equivalence between both representations for every
  finite-dimensional real inner product space and every natural dimension k.
- **Acceptance:** prove both inverse laws, equality of ambient projections,
  and the induced measurable equivalence. Include the possible empty case
  `k > finrank E`; do not silently require a chosen plane.
- **Impact:** permits transporting existing OpenGA parametrized varifolds into
  the upstream first-variation API without rebuilding the foundation.

### G2 — Transport varifolds and preserve weight and mass

- **Dependency:** G1.
- **Output:** map an OpenGA varifold through `(x, P) ↦ (x, G1 P)` to a GMT
  varifold. Prove equality of weight measures and total mass and preservation
  of zero, addition and nonnegative scaling.
- **Acceptance:** use pushforward of the existing measure and prove finiteness
  on compact sets. For a bidirectional equivalence, establish the needed
  regularity theorem rather than adding regularity as an unexplained input.
  Transport compactly supported test integrals with the correct pullback.
- **Impact:** first variation and stationary monotonicity can be applied to
  converted objects once stationarity has been established geometrically.
  Stationarity is not automatic for a parametrized surface.

### G3 — Area formula for existing parametrized surfaces

- **Input:** `OpenGA.Varifold.ofParametrization`, `surfaceJacobian`,
  `mass_ofParametrization`, GMT's `Area.area_formula_of_contDiff` and the
  equality of two-dimensional normalized Hausdorff measure with volume.
- **First output:** for a C1 map from Euclidean 2-space, a measurable parameter
  domain, the existing measurable tangent lift and finite-area assumption,
  identify varifold mass with the integral of image multiplicity against
  normalized two-dimensional Hausdorff measure.
- **Acceptance:** preserve the full original domain and multiplicity; prove
  the Jacobian coercion identity and source-measure normalization. An injective
  chart is a specialization, not a reason to discard the noninjective case.
- **Next output:** extend from total mass to weight measures on measurable
  spatial sets. G2 then transports the result to GMT varifolds.
- **Boundary:** this task does not automatically construct the measurable
  tangent lift, handle arbitrary Sobolev maps, or glue manifold charts.

Suggested order is `T1 || G1 || G3 || T3`, then G2 after G1. This describes
independent contributor tasks; no agents or external assignments were launched.

## What this does not close

The CM route still needs C0-intersect-W1,2 mapping spaces and sweepouts,
positive width for a nontrivial class, harmonic replacement, bubbling and
good-sweepout estimates uniform over almost-maximal slices. It also needs the
Riemannian/branched-sphere area variation bridge, surgery width control and the
actual Ricci-flow existence and topology-extraction arguments. GMT's Euclidean
stationary monotonicity does not prove these statements by itself.

The statement error documented in the main plan is unaffected by GMT: adding
geometric-measure-theory lemmas cannot make every arbitrary abstract topology
evolution satisfy a finite-extinction estimate.

## Integration checks still required

- Pin the exact GMT commit; reproduce selected-module builds and audit the
  actual declarations used. Source inspection alone is not kernel verification.
- Check combined imports with OpenGA and DifferentialGeometry before changing
  public types. Prefer small interoperability lemmas over mass replacement.
- Preserve source authorship and applicable licensing. At this commit no
  LICENSE/COPYING file or explicit license grant was found in the inspected
  repository files; clarify upstream reuse terms before redistributing source.
- Keep the Prove2Me export dependency closure explicit: a local Lake dependency
  does not automatically make GMT modules available in the platform environment.
