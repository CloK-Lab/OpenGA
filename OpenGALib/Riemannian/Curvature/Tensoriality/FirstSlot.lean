import OpenGALib.Riemannian.Curvature.Tensoriality.ZSlot

/-! # Tensoriality of the Riemann curvature tensor — first slot (X/Y) -/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle VectorField
open scoped ContDiff Manifold Bundle Riemannian Topology

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianSetup I M]
  (g : RiemannianMetric I M)

include g

/-! ## First-slot tensoriality

The X-slot of `riemannCurvature g` admits clean scalar Leibniz: the boundary
terms cancel symmetrically between the inner-section Leibniz and the
Lie-bracket Leibniz, leaving no curvature correction.

External reference: `riemannSec_smul_left` and `riemannSec_add_left` in
`differential-geometry/.../Curvature.lean`. -/

/-- **Math.** **First-slot scalar Leibniz** for `riemannCurvature g`:
$$R(f \cdot X, Y) Z(x) = f(x) \cdot R(X, Y) Z(x).$$
Clean cancellation: the cross-derivative residual from the inner `covDeriv g`
Leibniz pairs against the Lie-bracket smul-Leibniz with opposite sign.

In contrast to `riemannCurvature_smul_third_scalar_field`, the X-slot
identity requires no chart-interior hypothesis. -/
theorem riemannCurvature_smul_first_scalar_field
    [IsManifold I 2 M]
    (f : M → ℝ) (X Y Z : SmoothVectorField I M) (x : M)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    riemannCurvature g (f • X.toFun) Y.toFun Z.toFun x
      = f x • riemannCurvature g X.toFun Y.toFun Z.toFun x := by
  classical
  have hf_at : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
    (hf x).mdifferentiableAt (by simp)
  -- Directional derivative `Yf(x)`.
  set Yf_x : ℝ := (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x (Y.toFun x)) with hYf_def
  -- T1: covDeriv g (f • X) (∇_Y Z) x = f x • covDeriv g X (∇_Y Z) x via direction continuous linear map.
  have hT1 : covDeriv g (f • X.toFun) (fun y => covDeriv g Y.toFun Z.toFun y) x
      = f x • covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x := by
    show ((leviCivitaConnection (I := I) (M := M) g).toFun (fun y => covDeriv g Y.toFun Z.toFun y) x)
          ((f • X.toFun) x)
       = f x • ((leviCivitaConnection (I := I) (M := M) g).toFun (fun y => covDeriv g Y.toFun Z.toFun y) x)
                (X.toFun x)
    rw [show (f • X.toFun) x = f x • X.toFun x from rfl, map_smul]
  -- T2: inner section `covDeriv g (f • X) Z = f • (covDeriv g X Z)` pointwise.
  have h_inner :
      (fun y => covDeriv g (f • X.toFun) Z.toFun y)
        = f • (fun y => covDeriv g X.toFun Z.toFun y) := by
    funext y
    show ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y) ((f • X.toFun) y)
       = f y • ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y) (X.toFun y)
    rw [show (f • X.toFun) y = f y • X.toFun y from rfl, map_smul]
  -- T2: covDeriv g Y (f • cov X Z) x = f x • cov Y (cov X Z) x + Yf_x • cov X Z x.
  have hT2 :
      covDeriv g Y.toFun (fun y => covDeriv g (f • X.toFun) Z.toFun y) x
        = f x • covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x
          + Yf_x • covDeriv g X.toFun Z.toFun x := by
    rw [h_inner]
    exact covDeriv_smul_scalar_field g Y.toFun f
      (fun y => covDeriv g X.toFun Z.toFun y) x hf_at
      (covDeriv_smoothVF_smoothAt g X Z x)
  -- Lie-bracket smul: `[f • X, Y] x = -Yf_x • X x + f x • [X, Y] x`.
  have h_br : VectorField.mlieBracket I (f • X.toFun) Y.toFun x
      = -Yf_x • X.toFun x + f x • VectorField.mlieBracket I X.toFun Y.toFun x := by
    have h := VectorField.mlieBracket_smul_left (I := I) (V := X.toFun)
      (W := Y.toFun) (x := x) hf_at (X.smoothAt x)
    -- `fromTangentSpace (f x) v = v` definitionally on the scalar tangent space.
    show VectorField.mlieBracket I (f • X.toFun) Y.toFun x
      = -(show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x (Y.toFun x)) • X.toFun x
        + f x • VectorField.mlieBracket I X.toFun Y.toFun x
    convert h using 2
  -- T3: covDeriv g [f • X, Y] Z x = -Yf_x • cov X Z x + f x • cov [X, Y] Z x via continuous linear map.
  have hT3 :
      covDeriv g (VectorField.mlieBracket I (f • X.toFun) Y.toFun) Z.toFun x
        = -Yf_x • covDeriv g X.toFun Z.toFun x
          + f x • covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x := by
    show ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x)
          (VectorField.mlieBracket I (f • X.toFun) Y.toFun x)
       = -Yf_x • ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x) (X.toFun x)
         + f x • ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x)
                  (VectorField.mlieBracket I X.toFun Y.toFun x)
    rw [h_br, map_add, map_smul, map_smul]
  -- Assemble: 3 terms cancel the `Yf_x` boundary contribution symmetrically.
  rw [riemannCurvature_commutator_form, hT1, hT2, hT3, riemannCurvature_commutator_form]
  rw [smul_sub, smul_sub]
  -- The `Yf_x • cov X Z x` boundary terms cancel: `-Yf_x • c - (-Yf_x) • c = 0`.
  -- Canonicalize the double-negative via `neg_smul`/`neg_neg` so `abel` sees the cancellation.
  simp only [neg_smul]
  abel

/-- **Math.** **First-slot additivity** for `riemannCurvature g`: $R(X + X', Y) Z = R(X, Y) Z + R(X', Y) Z$. -/
theorem riemannCurvature_add_first
    (X X' Y Z : SmoothVectorField I M) (x : M) :
    riemannCurvature g (X + X').toFun Y.toFun Z.toFun x
      = riemannCurvature g X.toFun Y.toFun Z.toFun x
        + riemannCurvature g X'.toFun Y.toFun Z.toFun x := by
  classical
  -- Pi-add unfolds.
  have h_pi_add : (X + X').toFun = X.toFun + X'.toFun := by funext y; rfl
  -- T1: cov (X + X') (∇_Y Z) x = cov X (∇_Y Z) x + cov X' (∇_Y Z) x via direction continuous linear map add.
  have hT1 : covDeriv g (X + X').toFun (fun y => covDeriv g Y.toFun Z.toFun y) x
      = covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x
        + covDeriv g X'.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x := by
    show ((leviCivitaConnection (I := I) (M := M) g).toFun (fun y => covDeriv g Y.toFun Z.toFun y) x)
          ((X + X').toFun x)
       = ((leviCivitaConnection (I := I) (M := M) g).toFun (fun y => covDeriv g Y.toFun Z.toFun y) x) (X.toFun x)
       + ((leviCivitaConnection (I := I) (M := M) g).toFun (fun y => covDeriv g Y.toFun Z.toFun y) x) (X'.toFun x)
    rw [show (X + X').toFun x = X.toFun x + X'.toFun x from rfl, map_add]
  -- Inner section: cov (X + X') Z = cov X Z + cov X' Z via direction continuous linear map add.
  have h_inner :
      (fun y => covDeriv g (X + X').toFun Z.toFun y)
        = (fun y => covDeriv g X.toFun Z.toFun y) + (fun y => covDeriv g X'.toFun Z.toFun y) := by
    funext y
    show ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y) ((X + X').toFun y)
       = ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y) (X.toFun y)
       + ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y) (X'.toFun y)
    rw [show (X + X').toFun y = X.toFun y + X'.toFun y from rfl, map_add]
  -- T2: outer cov_add.
  have hT2 :
      covDeriv g Y.toFun (fun y => covDeriv g (X + X').toFun Z.toFun y) x
        = covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x
          + covDeriv g Y.toFun (fun y => covDeriv g X'.toFun Z.toFun y) x := by
    rw [h_inner]
    exact covDeriv_add_field g Y.toFun
      (fun y => covDeriv g X.toFun Z.toFun y)
      (fun y => covDeriv g X'.toFun Z.toFun y) x
      (covDeriv_smoothVF_smoothAt g X Z x)
      (covDeriv_smoothVF_smoothAt g X' Z x)
  -- Lie-bracket additivity: [X + X', Y] x = [X, Y] x + [X', Y] x.
  have h_br : VectorField.mlieBracket I (X + X').toFun Y.toFun x
      = VectorField.mlieBracket I X.toFun Y.toFun x
        + VectorField.mlieBracket I X'.toFun Y.toFun x := by
    rw [h_pi_add]
    exact VectorField.mlieBracket_add_left (I := I) (V := X.toFun) (V₁ := X'.toFun)
      (W := Y.toFun) (x := x) (X.smoothAt x) (X'.smoothAt x)
  -- T3: cov [X+X', Y] Z x = cov [X, Y] Z x + cov [X', Y] Z x via continuous linear map add.
  have hT3 :
      covDeriv g (VectorField.mlieBracket I (X + X').toFun Y.toFun) Z.toFun x
        = covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x
          + covDeriv g (VectorField.mlieBracket I X'.toFun Y.toFun) Z.toFun x := by
    show ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x)
          (VectorField.mlieBracket I (X + X').toFun Y.toFun x)
       = ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x)
          (VectorField.mlieBracket I X.toFun Y.toFun x)
       + ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x)
          (VectorField.mlieBracket I X'.toFun Y.toFun x)
    rw [h_br, map_add]
  rw [riemannCurvature_commutator_form, hT1, hT2, hT3, riemannCurvature_commutator_form, riemannCurvature_commutator_form]
  abel

/-- **Math.** **X-slot locality of `riemannCurvature g`**: if `X =ᶠ[𝓝 x] X'`, then
`R(X, Y) Z(x) = R(X', Y) Z(x)`. Compared to Z-slot locality, the X-slot
proof is short — terms T1 and T3 depend on `X` only pointwise at `x`
(since the direction enters as `(lc.toFun ... x)(X x)`), and T2 reduces
via inner-section locality plus `covDeriv_congr_eventuallyEq_field`. -/
theorem riemannCurvature_eq_of_X_eventuallyEq
    (X X' Y Z : SmoothVectorField I M) (x : M)
    (hXX' : ∀ᶠ y in 𝓝 x, X.toFun y = X'.toFun y) :
    riemannCurvature g X.toFun Y.toFun Z.toFun x
      = riemannCurvature g X'.toFun Y.toFun Z.toFun x := by
  classical
  have hXx : X.toFun x = X'.toFun x := hXX'.self_of_nhds
  -- T1: direction continuous linear map application — only `X x` matters.
  have hT1 : covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x
      = covDeriv g X'.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x := by
    show ((leviCivitaConnection (I := I) (M := M) g).toFun (fun y => covDeriv g Y.toFun Z.toFun y) x)
          (X.toFun x)
       = ((leviCivitaConnection (I := I) (M := M) g).toFun (fun y => covDeriv g Y.toFun Z.toFun y) x)
          (X'.toFun x)
    rw [hXx]
  -- T2: inner section locality + outer covDeriv g field-locality.
  --   `covDeriv g X Z =ᶠ covDeriv g X' Z` near x via X-pointwise direction continuous linear map.
  have h_inner_ev : ∀ᶠ y in 𝓝 x,
      (fun y => covDeriv g X.toFun Z.toFun y) y = (fun y => covDeriv g X'.toFun Z.toFun y) y := by
    filter_upwards [hXX'] with y hy
    show ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y) (X.toFun y)
       = ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y) (X'.toFun y)
    rw [hy]
  have hT2 : covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x
      = covDeriv g Y.toFun (fun y => covDeriv g X'.toFun Z.toFun y) x :=
    covDeriv_congr_eventuallyEq_field g Y.toFun
      (fun y => covDeriv g X.toFun Z.toFun y)
      (fun y => covDeriv g X'.toFun Z.toFun y) x
      (covDeriv_smoothVF_smoothAt g X Z x)
      (covDeriv_smoothVF_smoothAt g X' Z x) h_inner_ev
  -- T3: `[X, Y] x = [X', Y] x` from pointwise X equality + Lie-bracket eventuallyEq.
  have h_br_x : VectorField.mlieBracket I X.toFun Y.toFun x
      = VectorField.mlieBracket I X'.toFun Y.toFun x :=
    Filter.EventuallyEq.mlieBracket_vectorField_eq (I := I)
      hXX' (Filter.EventuallyEq.refl _ Y.toFun)
  have hT3 : covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x
      = covDeriv g (VectorField.mlieBracket I X'.toFun Y.toFun) Z.toFun x := by
    show ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x)
          (VectorField.mlieBracket I X.toFun Y.toFun x)
       = ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x)
          (VectorField.mlieBracket I X'.toFun Y.toFun x)
    rw [h_br_x]
  rw [riemannCurvature_commutator_form, riemannCurvature_commutator_form, hT1, hT2, hT3]

/-! ## X-slot vanishing

If `X x = 0`, then `R(X, Y) Z(x) = 0`. Same chart-frame + bump decomposition
as Z-slot vanishing, applied to the X-slot via Z-slot locality
(`riemannCurvature_eq_of_X_eventuallyEq`) and the X-slot scalar Leibniz +
additivity.

The structure is parallel to `riemannCurvature_eq_zero_of_Z_eq_zero_field`,
but the per-summand Leibniz uses `riemannCurvature_smul_first_scalar_field`
(no `h_interior` required) and `riemannCurvature_add_first`. -/

/-- **Math.** **X-slot vanishing**: $X(x) = 0 \Rightarrow R(X, Y) Z(x) = 0$ for smooth
global sections `X, Y, Z`. -/
theorem riemannCurvature_eq_zero_of_X_eq_zero_field
    [IsManifold I 2 M] [T2Space M]
    (X Y Z : SmoothVectorField I M) (x : M)
    (hXx : X.toFun x = 0) :
    riemannCurvature g X.toFun Y.toFun Z.toFun x = 0 := by
  classical
  let e := trivializationAt E (TangentSpace I) x
  have he_mem : x ∈ e.baseSet := mem_baseSet_trivializationAt E _ x
  let basisF : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  obtain ⟨χ, -, hχsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (e.open_baseSet.mem_nhds he_mem)
  -- Bumped frame sections.
  have hs'_smooth : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => (⟨b, χ b • e.localFrame basisF i b⟩ : TangentBundle I M)) := by
    intro i
    have hχ_on : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (χ : M → ℝ) e.baseSet :=
      χ.contMDiff.contMDiffOn
    have hlf := e.contMDiffOn_localFrame_baseSet (I := I) (n := ∞) (b := basisF) i
    exact hχ_on.smul_section_of_tsupport e.open_baseSet hχsupp hlf
  let s' : Fin (Module.finrank ℝ E) → SmoothVectorField I M := fun i =>
    { toFun := fun b => χ b • e.localFrame basisF i b
      smooth := hs'_smooth i }
  -- Coefficient functions `c i` smooth + vanishing at x (since `X x = 0`).
  let c : Fin (Module.finrank ℝ E) → M → ℝ := fun i b =>
    χ b • e.localFrame_coeff I basisF i b (X.toFun b)
  have hc_smooth : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (c i) := by
    intro i b
    by_cases hb : b ∈ tsupport (χ : M → ℝ)
    · have hb_base : b ∈ e.baseSet := hχsupp hb
      have hχ_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (χ : M → ℝ) b := χ.contMDiff.contMDiffAt
      have hcoeff_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          ((LinearMap.piApply (e.localFrame_coeff I basisF i)) X.toFun) b :=
        contMDiffAt_localFrame_coeff basisF hb_base (X.smooth b) i
      exact hχ_at.smul hcoeff_at
    · have hχ_zero : ∀ᶠ y in nhds b, (χ : M → ℝ) y = 0 := by
        apply Filter.Eventually.mono
          ((isClosed_tsupport (χ : M → ℝ)).isOpen_compl.mem_nhds hb)
        intro y hy
        exact (notMem_tsupport_iff_eventuallyEq.mp hy).self_of_nhds
      apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hχ_zero] with y hy
      show χ y • e.localFrame_coeff I basisF i y (X.toFun y) = 0
      rw [hy, zero_smul]
  have hc_zero : ∀ i, c i x = 0 := by
    intro i
    show χ x • e.localFrame_coeff I basisF i x (X.toFun x) = 0
    rw [hXx, map_zero, smul_zero]
  -- `X =ᶠ ∑ g_i • s'_i` near x.
  have hX_eq_sum : ∀ᶠ b in 𝓝 x,
      X.toFun b = ∑ i, c i b • (s' i).toFun b := by
    filter_upwards [χ.eventuallyEq_one, e.open_baseSet.mem_nhds he_mem]
      with b hχb hb_base
    show X.toFun b
      = ∑ i, (χ b • e.localFrame_coeff I basisF i b (X.toFun b))
          • (χ b • e.localFrame basisF i b)
    have hχ1 : (χ : M → ℝ) b = 1 := hχb
    simp only [hχ1, one_smul]
    exact e.eq_sum_localFrame_coeff_smul (b := basisF) hb_base
  have hXsum_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, ∑ i, c i b • (s' i).toFun b⟩ : TangentBundle I M)) := by
    refine ContMDiff.sum_section (s := Finset.univ) ?_
    intro i _
    exact (hc_smooth i).smul_section (hs'_smooth i)
  let Xsum : SmoothVectorField I M :=
    { toFun := fun b => ∑ i, c i b • (s' i).toFun b
      smooth := hXsum_smooth }
  rw [riemannCurvature_eq_of_X_eventuallyEq g X Xsum Y Z x hX_eq_sum]
  show riemannCurvature g (fun b => ∑ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
                  c i b • (s' i).toFun b) Y.toFun Z.toFun x = 0
  suffices h : ∀ (T : Finset (Fin (Module.finrank ℝ E))),
      riemannCurvature g (fun b => ∑ i ∈ T, c i b • (s' i).toFun b)
        Y.toFun Z.toFun x
      = ∑ i ∈ T, c i x • riemannCurvature g (s' i).toFun Y.toFun Z.toFun x by
    rw [h Finset.univ]
    apply Finset.sum_eq_zero
    intro i _
    rw [hc_zero i, zero_smul]
  intro T
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    -- Goal: `R(fun _ : M => 0) Y.toFun Z.toFun x = 0`.
    rw [riemannCurvature_commutator_form]
    -- The zero-section identification (Pi-zero).
    have h_zero_pi :
        (fun _ : M => (0 : TangentSpace I _)) = (0 : VectorFieldSection I M) := rfl
    -- T1: outer cov at direction `0` = `0` (map_zero of continuous linear map in direction).
    have hT1 : covDeriv g (fun _ : M => (0 : TangentSpace I _))
                (fun y => covDeriv g Y.toFun Z.toFun y) x = 0 := by
      show ((leviCivitaConnection (I := I) (M := M) g).toFun (fun y => covDeriv g Y.toFun Z.toFun y) x)
            ((fun _ : M => (0 : TangentSpace I _)) x) = 0
      show ((leviCivitaConnection (I := I) (M := M) g).toFun _ x) (0 : TangentSpace I x) = 0
      exact map_zero _
    -- Inner section `cov (fun _ => 0) Z` is the zero section.
    have h_inner :
        (fun y => covDeriv g (fun _ : M => (0 : TangentSpace I _)) Z.toFun y)
          = (fun _ : M => (0 : TangentSpace I _)) := by
      funext y
      show ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y) (0 : TangentSpace I y) = 0
      exact map_zero _
    -- T2: outer cov of the zero section = 0 (via `IsCovariantDerivativeOn.zero`).
    have hT2 : covDeriv g Y.toFun
                (fun y => covDeriv g (fun _ : M => (0 : TangentSpace I _)) Z.toFun y) x = 0 := by
      rw [h_inner]
      show ((leviCivitaConnection (I := I) (M := M) g).toFun (fun _ : M => (0 : TangentSpace I _)) x) (Y.toFun x) = 0
      rw [h_zero_pi]
      rw [(leviCivitaConnection (I := I) (M := M) g).isCovariantDerivativeOnUniv.zero (x := x)]; rfl
    -- T3: `[fun _ => 0, Y] = 0` section, then `cov 0 Z x = 0`.
    have h_br : VectorField.mlieBracket I (fun _ : M => (0 : TangentSpace I _)) Y.toFun
        = (fun _ : M => (0 : TangentSpace I _)) := by
      rw [h_zero_pi]
      exact VectorField.mlieBracket_zero_left
    have hT3 : covDeriv g (VectorField.mlieBracket I
                  (fun _ : M => (0 : TangentSpace I _)) Y.toFun) Z.toFun x = 0 := by
      rw [h_br]
      show ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x) (0 : TangentSpace I x) = 0
      exact map_zero _
    rw [hT1, hT2, hT3]; abel
  | insert j s hjs IH =>
    have hsplit : (fun b : M => ∑ i ∈ insert j s, c i b • (s' i).toFun b)
        = ((c j • (s' j).toFun : Π b, TangentSpace I b)
           + (fun b : M => ∑ i ∈ s, c i b • (s' i).toFun b)) := by
      funext b
      change ∑ i ∈ insert j s, c i b • (s' i).toFun b
        = c j b • (s' j).toFun b + ∑ i ∈ s, c i b • (s' i).toFun b
      rw [Finset.sum_insert hjs]
    rw [hsplit]
    have hgj_smooth_section : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => (⟨b, c j b • (s' j).toFun b⟩ : TangentBundle I M)) :=
      (hc_smooth j).smul_section (hs'_smooth j)
    have hrest_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => (⟨b, ∑ i ∈ s, c i b • (s' i).toFun b⟩ : TangentBundle I M)) := by
      refine ContMDiff.sum_section (s := s) ?_
      intro i _
      exact (hc_smooth i).smul_section (hs'_smooth i)
    let gjs : SmoothVectorField I M :=
      { toFun := fun b => c j b • (s' j).toFun b, smooth := hgj_smooth_section }
    let rest : SmoothVectorField I M :=
      { toFun := fun b => ∑ i ∈ s, c i b • (s' i).toFun b, smooth := hrest_smooth }
    show riemannCurvature g (gjs.toFun + rest.toFun) Y.toFun Z.toFun x
      = ∑ i ∈ insert j s, c i x • riemannCurvature g (s' i).toFun Y.toFun Z.toFun x
    have h_add :
        riemannCurvature g (gjs.toFun + rest.toFun) Y.toFun Z.toFun x
        = riemannCurvature g gjs.toFun Y.toFun Z.toFun x
          + riemannCurvature g rest.toFun Y.toFun Z.toFun x := by
      have := riemannCurvature_add_first g gjs rest Y Z x
      simpa using this
    have h_smul :
        riemannCurvature g gjs.toFun Y.toFun Z.toFun x
        = c j x • riemannCurvature g (s' j).toFun Y.toFun Z.toFun x := by
      show riemannCurvature g (c j • (s' j).toFun) Y.toFun Z.toFun x
        = c j x • riemannCurvature g (s' j).toFun Y.toFun Z.toFun x
      exact riemannCurvature_smul_first_scalar_field
        g (c j) (s' j) Y Z x (hc_smooth j)
    rw [h_add, h_smul, IH, Finset.sum_insert hjs]

/-- **Math.** **X-slot pointwise dependence**: `X x = X' x ⇒ R(X, Y) Z(x) = R(X', Y) Z(x)`. -/
theorem riemannCurvature_eq_of_X_eq_at
    [IsManifold I 2 M] [T2Space M]
    (X X' Y Z : SmoothVectorField I M) (x : M)
    (hXX' : X.toFun x = X'.toFun x) :
    riemannCurvature g X.toFun Y.toFun Z.toFun x
      = riemannCurvature g X'.toFun Y.toFun Z.toFun x := by
  let τ : SmoothVectorField I M := X - X'
  have hτ_zero : τ.toFun x = 0 := by
    show X.toFun x - X'.toFun x = 0
    rw [hXX']; abel
  have hτ_vanish : riemannCurvature g τ.toFun Y.toFun Z.toFun x = 0 :=
    riemannCurvature_eq_zero_of_X_eq_zero_field g τ Y Z x hτ_zero
  have h_pi : (X' + τ).toFun = X.toFun := by
    funext y
    show X'.toFun y + (X.toFun y - X'.toFun y) = X.toFun y
    abel
  have h_add := riemannCurvature_add_first g X' τ Y Z x
  rw [h_pi] at h_add
  rw [h_add, hτ_vanish, add_zero]

/-- **Math.** **Y-slot pointwise dependence**: `Y x = Y' x ⇒ R(X, Y) Z(x) = R(X, Y') Z(x)`.
Reduces to X-slot pointwise dependence via antisymmetry of the first pair. -/
theorem riemannCurvature_eq_of_Y_eq_at
    [IsManifold I 2 M] [T2Space M]
    (X Y Y' Z : SmoothVectorField I M) (x : M)
    (hYY' : Y.toFun x = Y'.toFun x) :
    riemannCurvature g X.toFun Y.toFun Z.toFun x
      = riemannCurvature g X.toFun Y'.toFun Z.toFun x := by
  -- R(X, Y) Z x = -R(Y, X) Z x = -R(Y', X) Z x = R(X, Y') Z x.
  rw [riemannCurvature_antisymm g X.toFun Y.toFun Z.toFun x,
      riemannCurvature_eq_of_X_eq_at g Y Y' X Z x hYY',
      ← riemannCurvature_antisymm g X.toFun Y'.toFun Z.toFun x]

/-- **Math.** **Pointwise well-definedness of `riemannCurvature g` on smooth global sections**:
given two triples `(X, Y, Z)` and `(X', Y', Z')` of smooth global sections
agreeing pointwise at `x`, the values of `riemannCurvature g` at `x` coincide.

Chained through the X-, Y-, and Z-slot `eq_at` lemmas. Used to define
`riemannCurvature g` as a continuous trilinear form `riemannOp x` on
`T_xM × T_xM × T_xM → T_xM` (downstream bundling). -/
theorem riemannCurvature_eq_of_pointwise_eq
    [IsManifold I 2 M] [T2Space M]
    (X X' Y Y' Z Z' : SmoothVectorField I M) (x : M)
    (hX_eq : X.toFun x = X'.toFun x)
    (hY_eq : Y.toFun x = Y'.toFun x)
    (hZ_eq : Z.toFun x = Z'.toFun x) :
    riemannCurvature g X.toFun Y.toFun Z.toFun x
      = riemannCurvature g X'.toFun Y'.toFun Z'.toFun x := by
  rw [riemannCurvature_eq_of_X_eq_at g X X' Y Z x hX_eq,
      riemannCurvature_eq_of_Y_eq_at g X' Y Y' Z x hY_eq,
      riemannCurvature_eq_of_Z_eq_at g X' Y' Z Z' x hZ_eq]

end Riemannian
