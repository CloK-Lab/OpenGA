import OpenGALib.Riemannian.Curvature.RiemannCurvature
import OpenGALib.Riemannian.Metric.Util.RiemannianSetup

/-! # Sectional curvature -/

open Bundle VectorField
open scoped ContDiff Manifold Riemannian InnerProductSpace

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianSetup I M]

/-- **Math.** Sectional curvature `K_g(X,Y)(x) = g(R(X,Y)Y, X) / |X∧Y|²`
(junk value `0` at linearly dependent inputs). -/
noncomputable def sectionalCurvature
    (g : RiemannianMetric I M)
    (X Y : VectorFieldSection I M) (x : M) : ℝ :=
  g.metricInner x (riemannCurvature g X Y Y x) (X x) /
    (g.metricInner x (X x) (X x) * g.metricInner x (Y x) (Y x)
      - g.metricInner x (X x) (Y x) ^ 2)

/-- **Math.** Tangent-vector form `K_g(v,w)` via constant-section lifts. -/
noncomputable def sectionalCurvatureAt
    (g : RiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) : ℝ :=
  sectionalCurvature g (SmoothVectorField.const (I := I) (M := M) (v : E))
    (SmoothVectorField.const (I := I) (M := M) (w : E)) x

/-- **Math.** Symmetry `K_g(X,Y) = K_g(Y,X)`. -/
theorem sectionalCurvature_symmetric
    (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (x : M) :
    sectionalCurvature g X Y x = sectionalCurvature g Y X x := by
  unfold sectionalCurvature
  congr 1
  · exact riemannCurvature_pair_symm g X Y Y X x
  · rw [g.metricInner_comm x (X x) (Y x)]; ring

end Riemannian
