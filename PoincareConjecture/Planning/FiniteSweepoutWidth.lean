import OpenGALib.Riemannian.Surface.Width

/-!
# Finite sweepout width

The two theorems below are unfinished proof tasks with explicit `sorry` holes.
This file treats the smooth auxiliary case. The CM mapping space and its
finite-width target are developed separately in `CMSweepout.lean` beside it.
The metrics are fixed. The width is the existing smooth-slice homotopy width;
no identification with Colding--Minicozzi Sobolev width is asserted.
-/

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry DifferentialGeometry.Integral.Measure

namespace OpenGA.MilestoneSpecification

variable {N : Type*} [TopologicalSpace N] [ChartedSpace Surface.Model N]
  [IsManifold 𝓘(ℝ, Surface.Model) ∞ N] [T2Space N] [CompactSpace N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

/-- Continuity of the actual vertical differential as a map of total spaces.
The parameter is a sweepout parameter, not Ricci-flow time. -/
def HasContinuousVerticalDifferential
    (W : RicciFlow.SmoothSweepout (N := N) (I := I) (M := M)) : Prop :=
  Continuous (fun p : Icc (0 : ℝ) 1 × TangentBundle 𝓘(ℝ, Surface.Model) N =>
    (TotalSpace.mk' E (W.map p.1 p.2.proj)
      (mfderiv 𝓘(ℝ, Surface.Model) I (W.map p.1) p.2.proj p.2.snd) :
        TangentBundle I M))

/-- First task: integrability and finiteness follow from smoothness and
compactness; they are not hypotheses. Degenerate maps are allowed. -/
theorem smoothMap_finiteEnergy
    (q : SmoothRiemannianMetric 𝓘(ℝ, Surface.Model) N)
    (g : SmoothRiemannianMetric I M)
    (f : N → M) (hf : ContMDiff 𝓘(ℝ, Surface.Model) I ∞ f) :
    Continuous (Surface.dirichletDensity q g f) ∧
    Integrable (Surface.dirichletDensity q g f)
      (riemannianVolumeMeasure 𝓘(ℝ, Surface.Model) N q) ∧
    Surface.dirichletEnergy q g f < ⊤ := by
  sorry

/-- Full milestone for a given regular family, using the existing geometric
energy and width definitions. The proof remains to be completed. -/
theorem finiteSweepout_width
    (q : SmoothRiemannianMetric 𝓘(ℝ, Surface.Model) N)
    (g : SmoothRiemannianMetric I M)
    (W : RicciFlow.SmoothSweepout (N := N) (I := I) (M := M))
    (hW : HasContinuousVerticalDifferential W) :
    Continuous (fun p : Icc (0 : ℝ) 1 × N =>
      Surface.dirichletDensity q g (W.map p.1) p.2) ∧
    (∀ u, Integrable (Surface.dirichletDensity q g (W.map u))
      (riemannianVolumeMeasure 𝓘(ℝ, Surface.Model) N q)) ∧
    (∀ u, Surface.dirichletEnergy q g (W.map u) < ⊤) ∧
    Continuous (fun u => (Surface.dirichletEnergy q g (W.map u)).toReal) ∧
    (∃ u : Icc (0 : ℝ) 1,
      W.maxEnergy q g = Surface.dirichletEnergy q g (W.map u)) ∧
    W.maxEnergy q g < ⊤ ∧
    W.homotopyWidth q g ≤ W.maxEnergy q g ∧
    W.homotopyWidth q g < ⊤ := by
  sorry

end OpenGA.MilestoneSpecification
