import OpenGALib.Riemannian.Connection.LeviCivita
import OpenGALib.Riemannian.Connection.LeviCivita
import OpenGALib.Riemannian.TangentBundle.TangentSmooth
import OpenGALib.Riemannian.Operators.HessianLie
import OpenGALib.Riemannian.Util.Metric.MetricInnerSmoothness
-- `Riem(X, Y) Z` notation is now defined inline in `Connection.lean`
-- alongside `riemannCurvature`; it transitively reaches us via the
-- `import OpenGALib.Riemannian.Connection.LeviCivita` above.
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import OpenGALib.Riemannian.Util.CovDeriv.CovDerivBridges
import OpenGALib.Riemannian.Metric.Util.RiemannianSetup

/-!
# Riemann curvature, Ricci, and scalar curvature

For $(M, g)$ with Levi-Civita connection $\nabla$:

* **Riemann curvature**:
  $R(X, Y) Z := \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z.$
* **Ricci curvature**: trace of $z \mapsto R(z, X) Y$ on $T_xM$,
  $\mathrm{Ric}(X, Y)(x) := \mathrm{tr}\bigl(z \mapsto R(z, X) Y(x)\bigr).$
* **Scalar curvature**: metric trace of the Ricci tensor,
  $\mathrm{scal}(x) := \mathrm{tr}_g \mathrm{Ric}(x).$

`riemannCurvature` itself lives in `Riemannian.Connection` as connection
data, not metric data. This file collects the antisymmetry corollary
and the metric-dependent Ricci / scalar-curvature constructions.

Reference: do Carmo 1992 §4.
-/

open Bundle VectorField
open scoped ContDiff Manifold Riemannian InnerProductSpace

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianSetup I M]

/-- **Eng.** Constant smooth vector field at a tangent vector. Hides
`SmoothVectorField.const (I := I) (M := M) V` boilerplate inside this file. -/
local notation "cF[" V "]" => SmoothVectorField.const (I := I) (M := M) V

/-! ## Math API -/

/-- **Math.** $R(X, Y) Z = -R(Y, X) Z$.

Reference: do Carmo §4 Proposition 2.5 (i). -/
theorem riemannCurvature_antisymm
    (g : RiemannianMetric I M)
    (X Y Z : VectorFieldSection I M) (x : M) :
    riemannCurvature g X Y Z x = -riemannCurvature g Y X Z x := by
  simp only [riem_simp]
  rw [covDeriv_mlieBracket_swap_apply]
  abel

/-- **Math.** The endomorphism $z \mapsto R(z, X) Y(x)$ on $T_xM$ (with $z$ extended to
the constant section). Trace of this is the Ricci tensor at $x$. -/
noncomputable def curvatureEndo
    [IsManifold I 2 M]
    (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun z :=
    riemannCurvature g (fun _ => z) X Y x
  map_add' z₁ z₂ := by
    show riemannCurvature g (fun _ => z₁ + z₂) X.toFun Y.toFun x
       = riemannCurvature g (fun _ => z₁) X.toFun Y.toFun x
        + riemannCurvature g (fun _ => z₂) X.toFun Y.toFun x
    -- Unfold riemannCurvature g into 3 covDeriv g terms.
    show covDeriv g (fun _ => z₁ + z₂) (fun y => covDeriv g X.toFun Y.toFun y) x
          - covDeriv g X.toFun (fun y => covDeriv g (fun _ => z₁ + z₂) Y.toFun y) x
          - covDeriv g (fun y => mlieBracket I (fun _ => z₁ + z₂) X.toFun y) Y.toFun x
        = (covDeriv g (fun _ => z₁) (fun y => covDeriv g X.toFun Y.toFun y) x
            - covDeriv g X.toFun (fun y => covDeriv g (fun _ => z₁) Y.toFun y) x
            - covDeriv g (fun y => mlieBracket I (fun _ => z₁) X.toFun y) Y.toFun x)
        + (covDeriv g (fun _ => z₂) (fun y => covDeriv g X.toFun Y.toFun y) x
            - covDeriv g X.toFun (fun y => covDeriv g (fun _ => z₂) Y.toFun y) x
            - covDeriv g (fun y => mlieBracket I (fun _ => z₂) X.toFun y) Y.toFun x)
    -- Π-equality for adding constant sections.
    have h_const_add : ((fun _ : M => z₁ + z₂) : (y : M) → TangentSpace I y)
        = (fun _ => z₁) + (fun _ => z₂) := by funext y; rfl
    -- Term 1: covDeriv g (fun _ => z) F x = lev.toFun F x z is continuous linear map-linear in z.
    have hT1 : covDeriv g (fun _ : M => z₁ + z₂) (fun y => covDeriv g X.toFun Y.toFun y) x
        = covDeriv g (fun _ => z₁) (fun y => covDeriv g X.toFun Y.toFun y) x
        + covDeriv g (fun _ => z₂) (fun y => covDeriv g X.toFun Y.toFun y) x := by
      show ((leviCivitaConnection g).toFun (fun y => covDeriv g X.toFun Y.toFun y) x) (z₁ + z₂)
          = ((leviCivitaConnection g).toFun (fun y => covDeriv g X.toFun Y.toFun y) x) z₁
          + ((leviCivitaConnection g).toFun (fun y => covDeriv g X.toFun Y.toFun y) x) z₂
      exact map_add _ _ _
    -- Term 2: inner field `fun y => covDeriv g (fun _ => z) Y y = lev.toFun Y y z`.
    -- continuous linear map-linear in z, so the inner field is the pointwise sum.
    have h_inner_add : (fun y => covDeriv g (fun _ : M => z₁ + z₂) Y.toFun y)
        = (fun y => covDeriv g (fun _ => z₁) Y.toFun y)
          + (fun y => covDeriv g (fun _ => z₂) Y.toFun y) := by
      funext y
      show ((leviCivitaConnection g).toFun Y.toFun y) (z₁ + z₂)
          = ((leviCivitaConnection g).toFun Y.toFun y) z₁
          + ((leviCivitaConnection g).toFun Y.toFun y) z₂
      exact map_add _ _ _
    -- Smoothness of each summand: `(fun y => covDeriv g (fun _ => z) Y y) =
    -- (fun y => lev.toFun Y y z)` is smooth via `leviCivitaConnection`'s
    -- isCovariantDerivativeOnUniv applied at the constant section.
    have h_const_z₁_smooth : ∀ y, TangentSmoothAt
        (fun _ : M => z₁) y :=
      fun y => (cF[z₁]).smoothAt y
    have h_const_z₂_smooth : ∀ y, TangentSmoothAt
        (fun _ : M => z₂) y :=
      fun y => (cF[z₂]).smoothAt y
    have hY_smooth := Y.smoothAt
    have hT2 : covDeriv g X.toFun (fun y => covDeriv g (fun _ : M => z₁ + z₂) Y.toFun y) x
        = covDeriv g X.toFun (fun y => covDeriv g (fun _ => z₁) Y.toFun y) x
        + covDeriv g X.toFun (fun y => covDeriv g (fun _ => z₂) Y.toFun y) x := by
      rw [h_inner_add]
      apply covDeriv_add_field
      · exact covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) z₁ Y x
      · exact covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) z₂ Y x
    -- Term 3: mlieBracket linearity in left argument.
    have h_lieBr_add : (fun y => mlieBracket I (fun _ : M => z₁ + z₂) X.toFun y)
        = (fun y => mlieBracket I (fun _ => z₁) X.toFun y)
          + (fun y => mlieBracket I (fun _ => z₂) X.toFun y) := by
      funext y
      rw [show ((fun _ : M => z₁ + z₂) : (y : M) → TangentSpace I y)
          = (fun _ => z₁) + (fun _ => z₂) from h_const_add]
      exact VectorField.mlieBracket_add_left (h_const_z₁_smooth y) (h_const_z₂_smooth y)
    -- Smoothness of (fun y => mlieBracket I (fun _ => z) X.toFun y) at x.
    -- This requires C^2 manifold for derivatives of mlieBracket; we assert
    -- via a separate framework lemma that we might not have. For now use
    -- a placeholder via Mathlib + framework's fallback.
    have hT3 : covDeriv g (fun y => mlieBracket I (fun _ : M => z₁ + z₂) X.toFun y) Y.toFun x
        = covDeriv g (fun y => mlieBracket I (fun _ => z₁) X.toFun y) Y.toFun x
        + covDeriv g (fun y => mlieBracket I (fun _ => z₂) X.toFun y) Y.toFun x := by
      rw [h_lieBr_add]
      -- For the OUTER covDeriv g, the field A vs A+B issue: covDeriv g is
      -- linear in the FIRST (direction) argument via continuous linear map, since
      -- covDeriv g F G x = lev.toFun G x (F x), and `(F + G) x = F x + G x`.
      show ((leviCivitaConnection g).toFun Y.toFun x)
          ((fun y => mlieBracket I (fun _ => z₁) X.toFun y) x
            + (fun y => mlieBracket I (fun _ => z₂) X.toFun y) x)
        = ((leviCivitaConnection g).toFun Y.toFun x)
            ((fun y => mlieBracket I (fun _ => z₁) X.toFun y) x)
          + ((leviCivitaConnection g).toFun Y.toFun x)
            ((fun y => mlieBracket I (fun _ => z₂) X.toFun y) x)
      exact map_add _ _ _
    rw [hT1, hT2, hT3]
    abel
  map_smul' c z := by
    show riemannCurvature g (fun _ => c • z) X.toFun Y.toFun x
       = c • riemannCurvature g (fun _ => z) X.toFun Y.toFun x
    show covDeriv g (fun _ => c • z) (fun y => covDeriv g X.toFun Y.toFun y) x
          - covDeriv g X.toFun (fun y => covDeriv g (fun _ => c • z) Y.toFun y) x
          - covDeriv g (fun y => mlieBracket I (fun _ => c • z) X.toFun y) Y.toFun x
        = c • (covDeriv g (fun _ => z) (fun y => covDeriv g X.toFun Y.toFun y) x
            - covDeriv g X.toFun (fun y => covDeriv g (fun _ => z) Y.toFun y) x
            - covDeriv g (fun y => mlieBracket I (fun _ => z) X.toFun y) Y.toFun x)
    have h_const_smul : ((fun _ : M => c • z) : (y : M) → TangentSpace I y)
        = c • (fun _ => z) := by funext y; rfl
    have h_const_z_smooth : ∀ y, TangentSmoothAt (fun _ : M => z) y :=
      fun y => (cF[z]).smoothAt y
    have hY_smooth := Y.smoothAt
    -- Term 1: continuous linear map map_smul.
    have hT1 : covDeriv g (fun _ : M => c • z) (fun y => covDeriv g X.toFun Y.toFun y) x
        = c • covDeriv g (fun _ => z) (fun y => covDeriv g X.toFun Y.toFun y) x := by
      show ((leviCivitaConnection g).toFun (fun y => covDeriv g X.toFun Y.toFun y) x) (c • z)
          = c • ((leviCivitaConnection g).toFun (fun y => covDeriv g X.toFun Y.toFun y) x) z
      exact ContinuousLinearMap.map_smul _ _ _
    -- Term 2.
    have h_inner_smul : (fun y => covDeriv g (fun _ : M => c • z) Y.toFun y)
        = c • (fun y => covDeriv g (fun _ => z) Y.toFun y) := by
      funext y
      show ((leviCivitaConnection g).toFun Y.toFun y) (c • z)
          = c • ((leviCivitaConnection g).toFun Y.toFun y) z
      exact ContinuousLinearMap.map_smul _ _ _
    have hT2 : covDeriv g X.toFun (fun y => covDeriv g (fun _ : M => c • z) Y.toFun y) x
        = c • covDeriv g X.toFun (fun y => covDeriv g (fun _ => z) Y.toFun y) x := by
      rw [h_inner_smul]
      apply covDeriv_smul_const_field
      exact covDeriv_const_smoothVF_smoothAt g (I := I) (M := M) z Y x
    -- Term 3.
    have h_lieBr_smul : (fun y => mlieBracket I (fun _ : M => c • z) X.toFun y)
        = c • (fun y => mlieBracket I (fun _ => z) X.toFun y) := by
      funext y
      rw [show ((fun _ : M => c • z) : (y : M) → TangentSpace I y)
          = c • (fun _ => z) from h_const_smul]
      exact VectorField.mlieBracket_const_smul_left (h_const_z_smooth y)
    have hT3 : covDeriv g (fun y => mlieBracket I (fun _ : M => c • z) X.toFun y) Y.toFun x
        = c • covDeriv g (fun y => mlieBracket I (fun _ => z) X.toFun y) Y.toFun x := by
      rw [h_lieBr_smul]
      show ((leviCivitaConnection g).toFun Y.toFun x)
          ((c • fun y => mlieBracket I (fun _ : M => z) X.toFun y) x)
        = c • ((leviCivitaConnection g).toFun Y.toFun x)
            ((fun y => mlieBracket I (fun _ : M => z) X.toFun y) x)
      show ((leviCivitaConnection g).toFun Y.toFun x)
          (c • mlieBracket I (fun _ => z) X.toFun x)
        = c • ((leviCivitaConnection g).toFun Y.toFun x)
            (mlieBracket I (fun _ => z) X.toFun x)
      exact ContinuousLinearMap.map_smul _ _ _
    rw [hT1, hT2, hT3]
    -- Goal: c • A - c • B - c • C = c • (A - B - C)
    rw [smul_sub, smul_sub]

/-- **Math.** The **Ricci curvature** $\mathrm{Ric}(X, Y) \in \mathbb{R}$ at $x$:
$$\mathrm{Ric}(X, Y)(x) := \mathrm{tr}(\mathrm{curvatureEndo}\,X\,Y\,x).$$

Reference: do Carmo §4 ex. 1. -/
noncomputable def ricci
    (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (x : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) (curvatureEndo g X Y x)

/-! ## Special metric predicates: flat manifold

These predicates describe properties of the ambient Riemannian metric
(via `[hm : HasMetric I M]` in scope); they do not take the metric as an
explicit argument because the underlying notations (`Riem`, `Ric_g`)
already consume the metric through the typeclass. -/

/-- **Math.** A Riemannian metric `g` is **flat** if its Riemann
curvature tensor vanishes pointwise. -/
def IsFlat (g : RiemannianMetric I M) : Prop :=
  ∀ (X Y Z : VectorFieldSection I M) (x : M), riemannCurvature g X Y Z x = 0

end Riemannian
