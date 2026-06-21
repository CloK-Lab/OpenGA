import OpenGALib.Riemannian.TangentBundle.LocallyConstant

/-! # Bundled smooth-manifold setup (metric-free) -/

open scoped Manifold ContDiff

namespace Riemannian

/-- **Eng.** Bundles the metric-free "smooth manifold over a complete
finite-dimensional model" structure (`CompleteSpace`/`FiniteDimensional` on the
model `E`, `IsLocallyConstantChartedSpace` on `M`) behind a single
`[SmoothManifoldSetup I M]`. The Riemannian layer extends this. -/
class SmoothManifoldSetup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  [completeSpace : CompleteSpace E]
  [finiteDimensional : FiniteDimensional ℝ E]
  [locallyConstant : IsLocallyConstantChartedSpace H M]

attribute [instance] SmoothManifoldSetup.completeSpace
  SmoothManifoldSetup.finiteDimensional SmoothManifoldSetup.locallyConstant

end Riemannian
