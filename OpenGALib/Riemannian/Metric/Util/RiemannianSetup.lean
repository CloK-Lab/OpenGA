import OpenGALib.Riemannian.Metric.RiemannianMetric
import OpenGALib.Riemannian.TangentBundle.Util.SmoothManifoldSetup

/-! # Bundled Riemannian-manifold setup -/

open scoped Manifold ContDiff

namespace Riemannian

/-- **Eng.** Bundles the Riemannian structure (inner product on the model, metric
on `M`, plus the boundaryless/Hausdorff/non-degenerate-dimension hypotheses) on
top of `SmoothManifoldSetup`, so downstream files write one `[RiemannianSetup I M]`
instead of a dozen `[...]`s. -/
class RiemannianSetup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    extends SmoothManifoldSetup I M where
  [innerProductSpace : InnerProductSpace ℝ E]
  [neZero : NeZero (Module.finrank ℝ E)]
  [boundaryless : I.Boundaryless]
  [t2Space : T2Space M]
  [hasMetric : HasMetric I M]

attribute [reducible] RiemannianSetup.innerProductSpace RiemannianSetup.hasMetric
attribute [instance] RiemannianSetup.innerProductSpace RiemannianSetup.neZero
  RiemannianSetup.boundaryless RiemannianSetup.t2Space RiemannianSetup.hasMetric

/-! ## Downstream usage: one assumption, the whole stack recovered for free -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianSetup I M]

-- both the smooth-manifold layer and the Riemannian layer are synthesizable:
example : CompleteSpace E := inferInstance
example : FiniteDimensional ℝ E := inferInstance
example : IsLocallyConstantChartedSpace H M := inferInstance
example : InnerProductSpace ℝ E := inferInstance
example : I.Boundaryless := inferInstance
example : T2Space M := inferInstance
example : HasMetric I M := inferInstance
noncomputable example : RiemannianMetric I M := HasMetric.metric

end Riemannian
