# Bishop–Gromov — upstream interface contract (CH21-faithful)

**Branch:** `feat/bg-upstream-interface-spec` (off `feat/bishop-gromov-jacobi`)
**Source of truth:** `references/arXiv-2404.09792v2/CH21.tex` (Bishop–Gromov Volume Comparison)

## Current state (verified)

- `OpenGALib/Comparison/BishopGromov/` is **0 real code `sorry`** on this branch.
- `bishopGromov_volume_comparison` (VolumeComparison.lean:92) is proved **0-sorry
  modulo the `BishopGromovVolumeData` interface** (VolumeComparison.lean:57).
- The Jacobi/Riccati **spine is already 0-sorry**: `ratio_antitone_of_riccati_subsolution`
  (JacobiRatioMonotone.lean:47), `JacobiDeterminant`, `RatioMonotone`, `RiccatiComparison`,
  `MatrixRiccati`, `VolumeMonotone` (the monotone-average lemma = CH21 lem 6–42).
- The interface is **not yet discharged** (no constructor). "Missing upstream" =
  build exactly what discharging it requires — **no more** (do not build off-path
  machinery: CH21 uses ZERO `second variation` / `index form` / `Morse` / `spray` /
  `geodesic flow` — those are out of scope, see NON-GOALS).

## The contract: discharge `BishopGromovVolumeData g K p`

Two substantive fields. Each is fed by CH21's cited facts. **State each interface
point at exactly the strength CH21 uses — not a stronger/global version.**

### Field `ratio_antitone` — `A(t)/s_K(t)^{n-1}` non-increasing  (CH21:174–244)
The per-direction Jacobi-determinant monotonicity, then sphere-integrated.
The spine (`ratio_antitone_of_riccati_subsolution`) already delivers the pointwise
result; it consumes these cited facts:

| # | CH21 line | Interface point (state this strength) | Cite / Level-2 source |
|---|-----------|----------------------------------------|------------------------|
| 3 | 168 | `S(t) ∼ (1/t)·id` as `t→0⁺` (shape-operator base asymptotic) | standard; do Carmo / Lee Ch.10 |
| 4 | 174 | shortest geodesic ⟹ **no conjugate point on `[0,cut(v))`** | CH5:20 ("always satisfied"); std proof = index form (DO NOT build) |
| 5 | 174 | ⟹ `J_1..J_{n-1}` linearly independent on `[0,cut(v))` (⟺ `d exp_p` invertible) | **Lee19 Prop 10.20** (Jacobi fields; NO Morse) |
| 6 | 216 | scalar Riccati comparison `a ≤ ā = ct_K` | likely already `RiccatiComparison.lean` / CH20 |

### Field `vol_eq` — `vol_g B(p,R) = ∫₀ᴿ A(t) dt`  (CH21:254–263)
The geodesic-polar volume formula. Needs:

| # | CH21 line | Interface point | Cite / Level-2 source |
|---|-----------|------------------|------------------------|
| 7 | 254 | `exp_p : C_p → M\cut(p)` is a diffeomorphism | standard (Lee Ch.10 Cut Points) |
| 8 | 256 | **`\begin{fact}` `cut(p)` has measure 0** (notes flag it as a *fact*) | std; Level-2 = cut-time regularity + rectifiable null set |
| 9 | 263 | polar volume formula `vol(B) = ∫_{Sⁿ⁻¹}∫₀^{min(r,cut)} j` | built from #7 + #8 + area formula |
| 1 | 58 | `d exp_p|_0 = id` ⟹ `lim_{r→0} f = 1` (absolute-comparison corollary) | standard |
| 2 | 100 | zero-initial Jacobi field = `d exp` variation; `d exp(J̄_i)=J_i` | Lee19 Thm 10.1 / Prop 10.4 |

## The real criterion: involved-math gets built (hard or not); wrong things never

The test is **"does CH21's proof actually involve this math?"** — NOT "is it hard?".
Difficulty is never a reason to skip genuinely-involved upstream. The only thing to
forbid is building **wrong** things.

- **Level 1 (now):** every interface point above is *cited* by CH21, so the
  conditional theorem needs only the (true) statements. Index-form / geodesic-flow /
  Hopf–Rinow machinery is **encapsulated inside** those cited facts — not needed to
  state Level 1.
- **Level 2 (the real goal — build the upstream):** discharging the interface DOES
  involve real math, and we **do build it, however hard**:
  - fact #4 (shortest ⟹ no conjugate) — its genuine proof is the **index form /
    second variation**. Build it. (CH21 itself only cites it; building it is honest
    Level-2 work, not off-path.)
  - facts #1/#2 (`exp` smooth, `d exp` variation) — genuine proof is smooth ODE
    dependence (the geodesic flow). Build it.
  - fact #8 (cut(p) measure 0) — genuine proof = cut-time regularity + rectifiable
    null set. Build it.

**What "wrong things" means (this is what the snapshot `openga-bg-buildable-*`
actually did wrong — not that it tried hard math):**

- ❌ **false statements**: `metricUnitPolar` missing the angular density factor.
- ❌ **wrong object**: cut-locus nullity stated on the wrong (legacy tangent) object.
- ❌ **over-general / too strong**: `ConjugateJacobiSingular` "too global for what the
  before-cut route really needs"; the "arbitrary-competitor" Hopf–Rinow N1 (false; the
  narrower `C^1` version suffices).

So: index-form and geodesic-flow are **legitimate Level-2 targets** when discharging
#4 and #1/#2 — build them **at the right strength, as the right object, true**. The
snapshot's sin was wrong/over-general statements, not hardness.

## Discipline

1. Write each interface point above as an **axiom-clean Lean hypothesis / structure
   field**, stated at CH21's exact strength, annotated with its CH21 line + Lee cite.
   The interface = the precise, minimal-sufficient spec of the upstream.
2. **Build the upstream (Level 2), hard or not** — discharge each field by proving the
   genuinely-involved math.
3. Guard against **wrong**, not against hard: each discharge must be the **correct
   object, true statement, and no stronger than the spec needs**. Re-check fidelity to
   the interface (and to CH21) before proving (the snapshot shipped 3 false statements
   by skipping this).
