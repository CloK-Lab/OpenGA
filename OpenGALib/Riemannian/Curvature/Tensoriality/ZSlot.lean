import OpenGALib.Riemannian.Curvature.RiemannSymmetries
import OpenGALib.Riemannian.Operators.Gradient
import OpenGALib.Riemannian.Util.Metric.MetricInnerSmoothness
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Defs
import OpenGALib.Riemannian.Metric.Util.RiemannianSetup

/-! # Tensoriality of the Riemann curvature tensor — Z-slot -/

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

theorem mfderiv_apply_smoothVF_contMDiff
    (f : M → ℝ) (V : SmoothVectorField I M)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun y => (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f y (V.toFun y))) := by
  -- Identify with `y ↦ g.metricInner y (manifoldGradient f y) (V y)` via grad duality.
  -- Then smoothness follows from manifoldGradient smoothness + V smoothness +
  -- bilinearity of the metric (encoded in `HasMetric` smoothness).
  have h_eq : (fun y => (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f y (V.toFun y)))
      = (fun y => g.metricInner y (manifoldGradient (I := I) g f y) (V.toFun y)) := by
    funext y
    exact (manifoldGradient_inner_eq (I := I) g f y (V.toFun y)).symm
  rw [h_eq]
  exact fun y => g.metricInner_contMDiffAt
    (n := ∞) (manifoldGradient_smooth_of_smooth (I := I) g f hf y) (V.smooth y)

/-- **Math.** **3rd-slot (Z-slot) C∞-linearity of `riemannCurvature g`**:
$$R(X, Y)(f \cdot Z)(x) = f(x) \cdot R(X, Y)\,Z(x).$$

External reference: `riemannSec_smul_third` in
`differential-geometry/.../Curvature.lean:521`. -/
theorem riemannCurvature_smul_third_scalar_field
    [IsManifold I 2 M]
    (f : M → ℝ) (X Y Z : SmoothVectorField I M) (x : M)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    riemannCurvature g X.toFun Y.toFun (f • Z.toFun) x
      = f x • riemannCurvature g X.toFun Y.toFun Z.toFun x := by
  classical
  -- `[I.Boundaryless]` makes `range I = univ`, so the chart-interior hypothesis
  -- is automatic and can be discharged internally.
  have h_interior : extChartAt I x x ∈ closure (interior (Set.range I)) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ, interior_univ, closure_univ]
    exact Set.mem_univ _
  have hf_at : ∀ y, MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    fun y => (hf y).mdifferentiableAt (by simp)
  have hf_C2_at : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x :=
    (hf x).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  have hX1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) x :=
    (X.smooth x).of_le (by
      show ((1 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hY1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) x :=
    (Y.smooth x).of_le (by
      show ((1 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  -- Directional-derivative scalar functions.
  set Yf : M → ℝ :=
    fun y => (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f y (Y.toFun y)) with hYf_def
  set Xf : M → ℝ :=
    fun y => (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f y (X.toFun y)) with hXf_def
  -- Smoothness of Yf, Xf as C∞ scalar functions.
  have hYf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ Yf :=
    mfderiv_apply_smoothVF_contMDiff (I := I) g f Y hf
  have hXf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ Xf :=
    mfderiv_apply_smoothVF_contMDiff (I := I) g f X hf
  have hYf_at : MDifferentiableAt I 𝓘(ℝ, ℝ) Yf x :=
    (hYf_smooth x).mdifferentiableAt (by simp)
  have hXf_at : MDifferentiableAt I 𝓘(ℝ, ℝ) Xf x :=
    (hXf_smooth x).mdifferentiableAt (by simp)
  -- ∇_V (f Z) section identity at every y (V ∈ {X, Y}).
  -- We state as Π-pointwise functions (not lambda-form) to match `covDeriv g` shape.
  have h_inner_Y :
      covDeriv g Y.toFun (f • Z.toFun)
        = (fun y : M => f y • covDeriv g Y.toFun Z.toFun y + Yf y • Z.toFun y) := by
    funext y
    exact covDeriv_smul_scalar_field g Y.toFun f Z.toFun y (hf_at y) (Z.smoothAt y)
  have h_inner_X :
      covDeriv g X.toFun (f • Z.toFun)
        = (fun y : M => f y • covDeriv g X.toFun Z.toFun y + Xf y • Z.toFun y) := by
    funext y
    exact covDeriv_smul_scalar_field g X.toFun f Z.toFun y (hf_at y) (Z.smoothAt y)
  -- Riemann curvature unfold via def.
  rw [riemannCurvature_commutator_form, riemannCurvature_commutator_form, h_inner_Y, h_inner_X]
  -- Pointwise sums need to be split into Π-add form for `covDeriv_add_field`.
  -- The two summands as separate Π-sections.
  set g1Y : VectorFieldSection I M :=
    fun y => f y • covDeriv g Y.toFun Z.toFun y with hg1Y_def
  set g2Y : VectorFieldSection I M :=
    fun y => Yf y • Z.toFun y with hg2Y_def
  set g1X : VectorFieldSection I M :=
    fun y => f y • covDeriv g X.toFun Z.toFun y with hg1X_def
  set g2X : VectorFieldSection I M :=
    fun y => Xf y • Z.toFun y with hg2X_def
  -- Convert `fun y => g1Y y + g2Y y` to Π-add `g1Y + g2Y` definitionally.
  have h_pi_addY : (fun y : M => g1Y y + g2Y y) = g1Y + g2Y := rfl
  have h_pi_addX : (fun y : M => g1X y + g2X y) = g1X + g2X := rfl
  rw [h_pi_addY, h_pi_addX]
  -- Smoothness witnesses for the summands at x.
  have h_dY_Z_smooth : TangentSmoothAt (fun y => covDeriv g Y.toFun Z.toFun y) x :=
    covDeriv_smoothVF_smoothAt g Y Z x
  have h_dX_Z_smooth : TangentSmoothAt (fun y => covDeriv g X.toFun Z.toFun y) x :=
    covDeriv_smoothVF_smoothAt g X Z x
  have hg1Y_smooth : TangentSmoothAt g1Y x :=
    (hf_at x).smul_section h_dY_Z_smooth
  have hg2Y_smooth : TangentSmoothAt g2Y x :=
    hYf_at.smul_section (Z.smoothAt x)
  have hg1X_smooth : TangentSmoothAt g1X x :=
    (hf_at x).smul_section h_dX_Z_smooth
  have hg2X_smooth : TangentSmoothAt g2X x :=
    hXf_at.smul_section (Z.smoothAt x)
  -- Apply outer additivity (covDeriv_add_field).
  rw [covDeriv_add_field g X.toFun g1Y g2Y x hg1Y_smooth hg2Y_smooth,
      covDeriv_add_field g Y.toFun g1X g2X x hg1X_smooth hg2X_smooth]
  -- Apply Leibniz to each summand at x.
  -- g1Y = f • (∇_Y Z), g2Y = Yf • Z, g1X = f • (∇_X Z), g2X = Xf • Z.
  -- ∇_X (f • ∇_Y Z) x = f x • ∇_X (∇_Y Z) x + (Xf x) • (∇_Y Z) x.
  have hT1_g1Y : covDeriv g X.toFun g1Y x
      = f x • covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x (X.toFun x))
            • covDeriv g Y.toFun Z.toFun x :=
    covDeriv_smul_scalar_field g X.toFun f
      (fun y => covDeriv g Y.toFun Z.toFun y) x (hf_at x) h_dY_Z_smooth
  have hT1_g2Y : covDeriv g X.toFun g2Y x
      = Yf x • covDeriv g X.toFun Z.toFun x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) Yf x (X.toFun x)) • Z.toFun x :=
    covDeriv_smul_scalar_field g X.toFun Yf Z.toFun x hYf_at (Z.smoothAt x)
  have hT2_g1X : covDeriv g Y.toFun g1X x
      = f x • covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x (Y.toFun x))
            • covDeriv g X.toFun Z.toFun x :=
    covDeriv_smul_scalar_field g Y.toFun f
      (fun y => covDeriv g X.toFun Z.toFun y) x (hf_at x) h_dX_Z_smooth
  have hT2_g2X : covDeriv g Y.toFun g2X x
      = Xf x • covDeriv g Y.toFun Z.toFun x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) Xf x (Y.toFun x)) • Z.toFun x :=
    covDeriv_smul_scalar_field g Y.toFun Xf Z.toFun x hXf_at (Z.smoothAt x)
  -- Third term: ∇_{[X,Y]} (f Z) x = f x • ∇_{[X,Y]} Z x + (mfderiv f x ([X,Y] x)) • Z x.
  have hT3 : covDeriv g (mlieBracket I X.toFun Y.toFun) (f • Z.toFun) x
      = f x • covDeriv g (mlieBracket I X.toFun Y.toFun) Z.toFun x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x
            (mlieBracket I X.toFun Y.toFun x)) • Z.toFun x :=
    covDeriv_smul_scalar_field g (mlieBracket I X.toFun Y.toFun) f Z.toFun x
      (hf_at x) (Z.smoothAt x)
  rw [hT1_g1Y, hT1_g2Y, hT2_g1X, hT2_g2X, hT3]
  -- Apply Hessian-Lie identity: X(Yf) x - Y(Xf) x = mfderiv f x ([X,Y] x).
  have h_HL : (show ℝ from mfderiv I 𝓘(ℝ, ℝ) Yf x (X.toFun x))
              - (show ℝ from mfderiv I 𝓘(ℝ, ℝ) Xf x (Y.toFun x))
            = (show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x
                (mlieBracket I X.toFun Y.toFun x)) :=
    mfderiv_iterate_sub_eq_mlieBracket_apply
      f X.toFun Y.toFun x h_interior hf_C2_at hX1 hY1
  -- Rewrite the `mfderiv f x ([X,Y] x) • Z x` term using h_HL to make
  -- the `(Yf' x - Xf' x) • Z x` cancellation explicit.
  rw [← h_HL, sub_smul]
  -- Identify `Xf x = mfderiv f x (X x)` and `Yf x = mfderiv f x (Y x)` definitionally
  -- (both sides reduce by `set ... with` unfolding).
  show f x • covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x
      + Xf x • covDeriv g Y.toFun Z.toFun x
      + (Yf x • covDeriv g X.toFun Z.toFun x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) Yf x (X.toFun x)) • Z.toFun x)
    - (f x • covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x
      + Yf x • covDeriv g X.toFun Z.toFun x
      + (Xf x • covDeriv g Y.toFun Z.toFun x
        + (show ℝ from mfderiv I 𝓘(ℝ, ℝ) Xf x (Y.toFun x)) • Z.toFun x))
    - (f x • covDeriv g (mlieBracket I X.toFun Y.toFun) Z.toFun x
      + ((show ℝ from mfderiv I 𝓘(ℝ, ℝ) Yf x (X.toFun x)) • Z.toFun x
        - (show ℝ from mfderiv I 𝓘(ℝ, ℝ) Xf x (Y.toFun x)) • Z.toFun x))
    = f x • (covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x
        - covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x
        - covDeriv g (mlieBracket I X.toFun Y.toFun) Z.toFun x)
  -- Pure AddCommGroup arithmetic — cross-cancellation + f x • distributes.
  rw [smul_sub, smul_sub]
  abel

/-! ## Z-slot locality

`riemannCurvature g` is local in the Z-slot: if `Z =ᶠ[𝓝 x] Z'`, then
`R(X, Y) Z(x) = R(X, Y) Z'(x)`. Each of the three terms in `riemannCurvature_commutator_form`
satisfies a covariant-derivative locality identity in `Z`:

* `covDeriv g X (covDeriv g Y Z) x` and `covDeriv g Y (covDeriv g X Z) x` use the
  fact that the inner section `covDeriv g U Z` is locally constant in `Z`
  (apply `covDeriv_congr_eventuallyEq_field` at every nearby `b`), then
  evaluate the outer `covDeriv g` via the same field-locality lemma.
* `covDeriv g [X, Y] Z x` reduces directly. -/

/-- **Math.** **Z-slot locality of `riemannCurvature g`**: if `Z =ᶠ[𝓝 x] Z'`, then
`R(X, Y) Z(x) = R(X, Y) Z'(x)`. External reference: `riemannSec_eq_of_Z_eventuallyEq`
(`differential-geometry/.../CurvatureBundling.lean:227`). -/
theorem riemannCurvature_eq_of_Z_eventuallyEq
    (X Y Z Z' : SmoothVectorField I M) (x : M)
    (hZZ' : ∀ᶠ y in 𝓝 x, Z.toFun y = Z'.toFun y) :
    riemannCurvature g X.toFun Y.toFun Z.toFun x
      = riemannCurvature g X.toFun Y.toFun Z'.toFun x := by
  classical
  -- Convert eventual equality to an open nbhd `V'` on which `Z = Z'`.
  rw [Filter.eventually_iff_exists_mem] at hZZ'
  obtain ⟨U, hU, hZeqZ'⟩ := hZZ'
  obtain ⟨V', hV'U, hV'_open, hpV'⟩ := mem_nhds_iff.mp hU
  -- `Z =ᶠ[𝓝 b] Z'` for any `b ∈ V'` (V' open, V' ⊆ U).
  have hZZ'_at : ∀ b ∈ V', ∀ᶠ b' in 𝓝 b, Z.toFun b' = Z'.toFun b' := by
    intro b hbV'
    exact Filter.eventually_of_mem (hV'_open.mem_nhds hbV')
      (fun b' hb'V' => hZeqZ' b' (hV'U hb'V'))
  -- Inner section pointwise equality on `V'` (Y- and X-flavored).
  have h_inner_Y_pt : ∀ b ∈ V',
      (fun y => covDeriv g Y.toFun Z.toFun y) b
        = (fun y => covDeriv g Y.toFun Z'.toFun y) b := by
    intro b hbV'
    exact covDeriv_congr_eventuallyEq_field g Y.toFun Z.toFun Z'.toFun b
      (Z.smoothAt b) (Z'.smoothAt b) (hZZ'_at b hbV')
  have h_inner_X_pt : ∀ b ∈ V',
      (fun y => covDeriv g X.toFun Z.toFun y) b
        = (fun y => covDeriv g X.toFun Z'.toFun y) b := by
    intro b hbV'
    exact covDeriv_congr_eventuallyEq_field g X.toFun Z.toFun Z'.toFun b
      (Z.smoothAt b) (Z'.smoothAt b) (hZZ'_at b hbV')
  -- Lift to eventual equality on a nbhd of `x`.
  have h_inner_Y_ev : ∀ᶠ b in 𝓝 x,
      (fun y => covDeriv g Y.toFun Z.toFun y) b
        = (fun y => covDeriv g Y.toFun Z'.toFun y) b :=
    Filter.eventually_of_mem (hV'_open.mem_nhds hpV') h_inner_Y_pt
  have h_inner_X_ev : ∀ᶠ b in 𝓝 x,
      (fun y => covDeriv g X.toFun Z.toFun y) b
        = (fun y => covDeriv g X.toFun Z'.toFun y) b :=
    Filter.eventually_of_mem (hV'_open.mem_nhds hpV') h_inner_X_pt
  -- T1: outer `covDeriv g X ·` field-locality, with `covDeriv_smoothVF_smoothAt`
  -- discharging the inner-section smoothness witnesses.
  have hT1 : covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x
      = covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z'.toFun y) x :=
    covDeriv_congr_eventuallyEq_field g X.toFun
      (fun y => covDeriv g Y.toFun Z.toFun y)
      (fun y => covDeriv g Y.toFun Z'.toFun y) x
      (covDeriv_smoothVF_smoothAt g Y Z x)
      (covDeriv_smoothVF_smoothAt g Y Z' x) h_inner_Y_ev
  -- T2: outer `covDeriv g Y ·` field-locality.
  have hT2 : covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x
      = covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z'.toFun y) x :=
    covDeriv_congr_eventuallyEq_field g Y.toFun
      (fun y => covDeriv g X.toFun Z.toFun y)
      (fun y => covDeriv g X.toFun Z'.toFun y) x
      (covDeriv_smoothVF_smoothAt g X Z x)
      (covDeriv_smoothVF_smoothAt g X Z' x) h_inner_X_ev
  -- T3: `covDeriv g [X, Y] Z x = covDeriv g [X, Y] Z' x` direct.
  have hZZ'_x : ∀ᶠ y in 𝓝 x, Z.toFun y = Z'.toFun y :=
    Filter.eventually_of_mem (hV'_open.mem_nhds hpV')
      (fun b hbV' => hZeqZ' b (hV'U hbV'))
  have hT3 : covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x
      = covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z'.toFun x :=
    covDeriv_congr_eventuallyEq_field g
      (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun Z'.toFun x
      (Z.smoothAt x) (Z'.smoothAt x) hZZ'_x
  -- Combine via `riemannCurvature_commutator_form`.
  rw [riemannCurvature_commutator_form, riemannCurvature_commutator_form, hT1, hT2, hT3]

/-! ## Z-slot vanishing

If `Z x = 0` for a smooth global section `Z`, then `R(X, Y) Z(x) = 0`.

Decomposition strategy: pick a local trivialization `e` of `TM` at `x`, the
induced local frame `e.localFrame basisF`, and a smooth bump function `χ`
with `tsupport χ ⊆ e.baseSet`. Write `Z` near `x` as a finite sum
`∑ gᵢ • s'ᵢ` of products of smooth scalar functions `gᵢ` vanishing at `x`
(because `Z x = 0`) with smooth global frame extensions `s'ᵢ`. Apply
Z-slot scalar multiplication (`riemannCurvature_smul_third_scalar_field`)
and additivity (`riemannCurvature_add_third`) inductively to each summand.

External reference: `riemannSec_eq_zero_of_Z_eq_zero`
(`differential-geometry/.../CurvatureBundling.lean:436`). -/

/-- **Math.** **Z-slot vanishing**: $Z(x) = 0 \Rightarrow R(X, Y) Z(x) = 0$ for smooth
global sections `X, Y, Z`. -/
theorem riemannCurvature_eq_zero_of_Z_eq_zero_field
    [IsManifold I 2 M] [T2Space M]
    (X Y Z : SmoothVectorField I M) (x : M)
    (hZx : Z.toFun x = 0) :
    riemannCurvature g X.toFun Y.toFun Z.toFun x = 0 := by
  classical
  -- Trivialization at `x`, basis of model fibre, induced local frame.
  let e := trivializationAt E (TangentSpace I) x
  have he_mem : x ∈ e.baseSet := mem_baseSet_trivializationAt E _ x
  let basisF : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  -- Bump function `χ` at `x` with `tsupport χ ⊆ e.baseSet`.
  obtain ⟨χ, -, hχsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (e.open_baseSet.mem_nhds he_mem)
  -- Smoothness of `b ↦ χ b • e.localFrame basisF i b` as a global section.
  have hs'_smooth : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => (⟨b, χ b • e.localFrame basisF i b⟩ : TangentBundle I M)) := by
    intro i
    have hχ_on : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (χ : M → ℝ) e.baseSet :=
      χ.contMDiff.contMDiffOn
    have hlf := e.contMDiffOn_localFrame_baseSet (I := I) (n := ∞) (b := basisF) i
    exact hχ_on.smul_section_of_tsupport e.open_baseSet hχsupp hlf
  -- Bundled `s' i : SmoothVectorField I M`.
  let s' : Fin (Module.finrank ℝ E) → SmoothVectorField I M := fun i =>
    { toFun := fun b => χ b • e.localFrame basisF i b
      smooth := hs'_smooth i }
  -- Smoothness of the scalar coefficient `c i b = χ b • coeff i b (Z b)`.
  let c : Fin (Module.finrank ℝ E) → M → ℝ := fun i b =>
    χ b • e.localFrame_coeff I basisF i b (Z.toFun b)
  have hc_smooth : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (c i) := by
    intro i b
    by_cases hb : b ∈ tsupport (χ : M → ℝ)
    · have hb_base : b ∈ e.baseSet := hχsupp hb
      have hχ_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (χ : M → ℝ) b :=
        χ.contMDiff.contMDiffAt
      have hcoeff_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
          ((LinearMap.piApply (e.localFrame_coeff I basisF i)) Z.toFun) b :=
        contMDiffAt_localFrame_coeff basisF hb_base (Z.smooth b) i
      exact hχ_at.smul hcoeff_at
    · -- Outside `tsupport χ`, `χ = 0` near `b`, so `c i = 0` near `b`.
      have hχ_zero : ∀ᶠ y in nhds b, (χ : M → ℝ) y = 0 := by
        apply Filter.Eventually.mono
          ((isClosed_tsupport (χ : M → ℝ)).isOpen_compl.mem_nhds hb)
        intro y hy
        exact (notMem_tsupport_iff_eventuallyEq.mp hy).self_of_nhds
      apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hχ_zero] with y hy
      show χ y • e.localFrame_coeff I basisF i y (Z.toFun y) = 0
      rw [hy, zero_smul]
  -- `c i x = 0` from `Z x = 0` and linearity of `localFrame_coeff`.
  have hc_zero : ∀ i, c i x = 0 := by
    intro i
    show χ x • e.localFrame_coeff I basisF i x (Z.toFun x) = 0
    rw [hZx, map_zero, smul_zero]
  -- `Z =ᶠ ∑ g_i • s'_i` near `x`: on a nbhd where `χ = 1` and `b ∈ e.baseSet`,
  -- the sum reduces to `eq_sum_localFrame_coeff_smul`.
  have hZ_eq_sum : ∀ᶠ b in 𝓝 x,
      Z.toFun b = ∑ i, c i b • (s' i).toFun b := by
    filter_upwards [χ.eventuallyEq_one, e.open_baseSet.mem_nhds he_mem]
      with b hχb hb_base
    show Z.toFun b
      = ∑ i, (χ b • e.localFrame_coeff I basisF i b (Z.toFun b))
          • (χ b • e.localFrame basisF i b)
    have hχ1 : (χ : M → ℝ) b = 1 := hχb
    simp only [hχ1, one_smul]
    exact e.eq_sum_localFrame_coeff_smul (b := basisF) hb_base
  -- Wrap the finite sum as a `SmoothVectorField`.
  have hZsum_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, ∑ i, c i b • (s' i).toFun b⟩ : TangentBundle I M)) := by
    refine ContMDiff.sum_section (s := Finset.univ) ?_
    intro i _
    exact (hc_smooth i).smul_section (hs'_smooth i)
  let Zsum : SmoothVectorField I M :=
    { toFun := fun b => ∑ i, c i b • (s' i).toFun b
      smooth := hZsum_smooth }
  -- Z-slot locality reduces to the sum form.
  rw [riemannCurvature_eq_of_Z_eventuallyEq g X Y Z Zsum x hZ_eq_sum]
  -- Induct on the Finset, splitting summands and applying Z-slot Leibniz + additivity.
  show riemannCurvature g X.toFun Y.toFun
        (fun b => ∑ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
                  c i b • (s' i).toFun b) x = 0
  -- The generalized induction statement.
  suffices h : ∀ (T : Finset (Fin (Module.finrank ℝ E))),
      riemannCurvature g X.toFun Y.toFun
        (fun b => ∑ i ∈ T, c i b • (s' i).toFun b) x
      = ∑ i ∈ T, c i x • riemannCurvature g X.toFun Y.toFun (s' i).toFun x by
    rw [h Finset.univ]
    apply Finset.sum_eq_zero
    intro i _
    rw [hc_zero i, zero_smul]
  intro T
  induction T using Finset.induction_on with
  | empty =>
    -- Goal: R(X, Y) (fun _ => 0) x = 0.
    simp only [Finset.sum_empty]
    -- Identify `fun _ : M => (0 : TangentSpace I _)` with the zero global section.
    show riemannCurvature g X.toFun Y.toFun (fun _ : M => (0 : TangentSpace I _)) x = 0
    -- Each `covDeriv g U (fun _ => 0)` is the zero section pointwise.
    have h_zero_outer : ∀ U V : VectorFieldSection I M,
        covDeriv g U (fun y : M =>
          covDeriv g V (fun _ : M => (0 : TangentSpace I _)) y) x = 0 := by
      intro U V
      -- Inner section is the zero section.
      have h_inner : (fun y : M =>
            covDeriv g V (fun _ : M => (0 : TangentSpace I _)) y)
          = (fun _ : M => (0 : TangentSpace I _)) := by
        funext y
        show ((leviCivitaConnection (I := I) (M := M) g).toFun (fun _ : M => (0 : TangentSpace I _)) y) (V y) = 0
        have h0 : (leviCivitaConnection (I := I) (M := M) g).toFun (fun _ : M => (0 : TangentSpace I _)) y = 0 :=
          (leviCivitaConnection (I := I) (M := M) g).isCovariantDerivativeOnUniv.zero (x := y)
        rw [h0]; rfl
      rw [h_inner]
      show ((leviCivitaConnection (I := I) (M := M) g).toFun (fun _ : M => (0 : TangentSpace I _)) x) (U x) = 0
      have h0 : (leviCivitaConnection (I := I) (M := M) g).toFun (fun _ : M => (0 : TangentSpace I _)) x = 0 :=
        (leviCivitaConnection (I := I) (M := M) g).isCovariantDerivativeOnUniv.zero (x := x)
      rw [h0]; rfl
    have h_zero_third :
        covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun)
          (fun _ : M => (0 : TangentSpace I _)) x = 0 := by
      show ((leviCivitaConnection (I := I) (M := M) g).toFun (fun _ : M => (0 : TangentSpace I _)) x)
        (VectorField.mlieBracket I X.toFun Y.toFun x) = 0
      have h0 : (leviCivitaConnection (I := I) (M := M) g).toFun (fun _ : M => (0 : TangentSpace I _)) x = 0 :=
        (leviCivitaConnection (I := I) (M := M) g).isCovariantDerivativeOnUniv.zero (x := x)
      rw [h0]; rfl
    rw [riemannCurvature_commutator_form, h_zero_outer X.toFun Y.toFun,
        h_zero_outer Y.toFun X.toFun, h_zero_third]
    abel
  | insert j s hjs IH =>
    -- Split `∑_{insert j s} = c j • s'_j + ∑_s` via `Finset.sum_insert`.
    have hsplit : (fun b : M => ∑ i ∈ insert j s, c i b • (s' i).toFun b)
        = ((c j • (s' j).toFun : Π b, TangentSpace I b)
           + (fun b : M => ∑ i ∈ s, c i b • (s' i).toFun b)) := by
      funext b
      change ∑ i ∈ insert j s, c i b • (s' i).toFun b
        = c j b • (s' j).toFun b + ∑ i ∈ s, c i b • (s' i).toFun b
      rw [Finset.sum_insert hjs]
    rw [hsplit]
    -- Wrap the head summand and the tail as `SmoothVectorField`.
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
    show riemannCurvature g X.toFun Y.toFun (gjs.toFun + rest.toFun) x
      = ∑ i ∈ insert j s, c i x • riemannCurvature g X.toFun Y.toFun (s' i).toFun x
    -- Z-slot additivity on the sum head + tail.
    have h_add :
        riemannCurvature g X.toFun Y.toFun (gjs.toFun + rest.toFun) x
        = riemannCurvature g X.toFun Y.toFun gjs.toFun x
          + riemannCurvature g X.toFun Y.toFun rest.toFun x := by
      have := riemannCurvature_add_third g X Y gjs rest x
      simpa using this
    -- Z-slot scalar Leibniz on the head: R(X, Y) (c j • s' j) x = c j x • R(X, Y) (s' j) x.
    have h_smul :
        riemannCurvature g X.toFun Y.toFun gjs.toFun x
        = c j x • riemannCurvature g X.toFun Y.toFun (s' j).toFun x := by
      show riemannCurvature g X.toFun Y.toFun (c j • (s' j).toFun) x
        = c j x • riemannCurvature g X.toFun Y.toFun (s' j).toFun x
      exact riemannCurvature_smul_third_scalar_field
        g (c j) X Y (s' j) x (hc_smooth j)
    rw [h_add, h_smul, IH, Finset.sum_insert hjs]

/-! ## Z-slot pointwise dependence

`riemannCurvature g` at `x` depends only on `Z(x)` (modulo smoothness of `Z`):
if `Z x = Z' x`, then `R(X, Y) Z(x) = R(X, Y) Z'(x)`. Derived from
Z-slot vanishing on `τ := Z - Z'` combined with Z-slot additivity. -/

/-- **Math.** **Z-slot pointwise dependence**: `Z x = Z' x ⇒ R(X, Y) Z(x) = R(X, Y) Z'(x)`. -/
theorem riemannCurvature_eq_of_Z_eq_at
    [IsManifold I 2 M] [T2Space M]
    (X Y Z Z' : SmoothVectorField I M) (x : M)
    (hZZ' : Z.toFun x = Z'.toFun x) :
    riemannCurvature g X.toFun Y.toFun Z.toFun x
      = riemannCurvature g X.toFun Y.toFun Z'.toFun x := by
  -- `τ := Z - Z'` is smooth with `τ x = 0`.
  let τ : SmoothVectorField I M := Z - Z'
  have hτ_zero : τ.toFun x = 0 := by
    show Z.toFun x - Z'.toFun x = 0
    rw [hZZ']; abel
  have hτ_vanish : riemannCurvature g X.toFun Y.toFun τ.toFun x = 0 :=
    riemannCurvature_eq_zero_of_Z_eq_zero_field g X Y τ x hτ_zero
  -- `Z = Z' + τ` pointwise; transfer to `(Z' + τ).toFun = Z.toFun` via the
  -- SmoothVectorField `Add` instance (defn-equality `(Z' + τ).toFun y = Z'.toFun y + τ.toFun y`).
  have h_pi : (Z' + τ).toFun = Z.toFun := by
    funext y
    show Z'.toFun y + (Z.toFun y - Z'.toFun y) = Z.toFun y
    abel
  -- Apply Z-slot additivity on `Z' + τ` and rewrite `(Z' + τ).toFun` to `Z.toFun`.
  have h_add := riemannCurvature_add_third g X Y Z' τ x
  rw [h_pi] at h_add
  rw [h_add, hτ_vanish, add_zero]

end Riemannian
