import OpenGALib.Riemannian.Metric.RiemannianMetric
import OpenGALib.Riemannian.TangentBundle.LocallyConstant

/-! # Bundled Riemannian-manifold setup -/

open scoped Manifold ContDiff

namespace Riemannian

/-- **Eng.** Bundles all the "extra" structure a Riemannian manifold needs on top
of the bare `E / H / I / M` skeleton, so downstream files write one
`[RiemannianSetup I M]` instead of eight `[...]`s. -/
class RiemannianSetup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  [innerProductSpace : InnerProductSpace ℝ E]
  [completeSpace : CompleteSpace E]
  [finiteDimensional : FiniteDimensional ℝ E]
  [neZero : NeZero (Module.finrank ℝ E)]
  [boundaryless : I.Boundaryless]
  [t2Space : T2Space M]
  [locallyConstant : IsLocallyConstantChartedSpace H M]
  [hasMetric : HasMetric I M]

attribute [reducible] RiemannianSetup.innerProductSpace RiemannianSetup.hasMetric
attribute [instance] RiemannianSetup.innerProductSpace RiemannianSetup.completeSpace
  RiemannianSetup.finiteDimensional RiemannianSetup.neZero RiemannianSetup.boundaryless
  RiemannianSetup.t2Space RiemannianSetup.locallyConstant RiemannianSetup.hasMetric

/-! ## Downstream usage: one assumption, all eight recovered for free -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianSetup I M]

-- all eight are now synthesizable from the single `[RiemannianSetup I M]`:
example : InnerProductSpace ℝ E := inferInstance
example : CompleteSpace E := inferInstance
example : FiniteDimensional ℝ E := inferInstance
example : I.Boundaryless := inferInstance
example : T2Space M := inferInstance
example : IsLocallyConstantChartedSpace H M := inferInstance
example : HasMetric I M := inferInstance

-- and so a `RiemannianMetric` is available with the slim variable block:
noncomputable example : RiemannianMetric I M := HasMetric.metric

end Riemannian
