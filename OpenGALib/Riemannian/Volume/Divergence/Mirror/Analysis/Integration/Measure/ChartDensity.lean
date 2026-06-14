import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import OpenGALib.Riemannian.Volume.Divergence.Mirror.Geometry.Metric.ChartGram

/-!
# Chart-local volume density from a Riemannian metric

Given a smooth `ContMDiffRiemannianMetric` `g` on the tangent bundle of a manifold `M`
and a base point `x₀ : M`, we construct a chart-local positive smooth density on the
domain of the base chart at `x₀`, and the associated chart-local Borel measure on `M`.

## Overview

Inside the open set `triv.baseSet = (chartAt H x₀).source`, we build a pointwise basis of
the tangent bundle by transporting a fixed algebraic basis of the model space `E` through
the tangent-bundle trivialization centred at `x₀`. The Gram matrix of this basis under
`g` is symmetric positive-definite, so its determinant is strictly positive and its
square root gives a positive smooth density on the chart domain.

The chart-local measure is obtained by weighting a chosen reference measure on the model
space `E` by the pullback of this density through the extended chart, and then pushing
forward to `M`.

## Main definitions

* `chartBasisVec g x₀ i` : the tangent-bundle section over `triv.baseSet` whose value
  at `x` is the image of the `i`-th model-space basis vector under the inverse of the
  tangent trivialization centred at `x₀`.
* `chartGramMatrix g x₀ x` : the Gram matrix at `x` of the family `chartBasisVec g x₀ •`
  under the inner product `g.inner x`.
* `chartDensity g x₀ x` : the positive density `√(det (chartGramMatrix g x₀ x))`.
* `chartLocalMeasure g x₀` : the chart-local measure on `M` obtained by pushing
  forward the weighted canonical additive Haar measure on the model space `E`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The chart-local density at `x` is `√(det (Gram matrix at x))`. -/
def chartDensity (g : SmoothRiemannianMetric I M) (x₀ : M) : M → ℝ :=
  fun x => Real.sqrt (chartGramMatrix g x₀ x).det

/-- The chart-local density is strictly positive on the trivialization base set. -/
lemma chartDensity_pos
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    0 < chartDensity g x₀ x :=
  Real.sqrt_pos.mpr (chartGramMatrix_det_pos (I := I) g x₀ hx)
lemma chartDensity_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity g x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  intro x hx
  have hdet := chartGramMatrix_det_contMDiffOn (I := I) g x₀ x hx
  have hpos_ne : (chartGramMatrix (I := I) g x₀ x).det ≠ 0 :=
    ne_of_gt (chartGramMatrix_det_pos (I := I) g x₀ hx)
  have hsqrt : ContDiffAt ℝ ∞ Real.sqrt
      (chartGramMatrix (I := I) g x₀ x).det :=
    Real.contDiffAt_sqrt hpos_ne
  have := hsqrt.comp_contMDiffWithinAt (f :=
      fun y : M => (chartGramMatrix (I := I) g x₀ y).det) hdet
  exact this

/-- The canonical additive Haar measure on the model space `E`, obtained from the
basis `chartModelBasis E`. Serves as the reference measure on the chart target.

This basis is the image of the standard `EuclideanSpace.basisFun` under the inverse
of the canonical `toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin n)`. With this choice,
the pushforward of `modelHaar` along `toEuclidean` is the standard Lebesgue volume on
`EuclideanSpace ℝ (Fin n)`; see `map_toEuclidean_modelHaar_eq_volume` below. -/
noncomputable def modelHaar : MeasureTheory.Measure E := (chartModelBasis E).addHaar

/-- The canonical Haar measure on `E` is an additive Haar measure. This
instance is derived from `Module.Basis.addHaar`. -/
instance modelHaar_isAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure (modelHaar (E := E)) := by
  unfold modelHaar
  infer_instance

/-- The pushforward of `modelHaar` along `toEuclidean` is the canonical Lebesgue
volume on `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`.

This is the defining property of the chosen basis: by construction
`chartModelBasis = (EuclideanSpace.basisFun).map toEuclidean.symm`, so by
`Module.Basis.map_addHaar` we have
`map toEuclidean modelHaar = (EuclideanSpace.basisFun).addHaar = volume`. -/
theorem map_toEuclidean_modelHaar_eq_volume :
    MeasureTheory.Measure.map (toEuclidean (E := E)) (modelHaar (E := E)) =
      (MeasureTheory.volume :
        MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have h₁ :
      MeasureTheory.Measure.map (toEuclidean (E := E))
          (modelHaar (E := E)) =
        ((chartModelBasis E).map
            (toEuclidean (E := E)).toLinearEquiv).addHaar := by
    unfold modelHaar
    exact Module.Basis.map_addHaar (chartModelBasis E)
      (toEuclidean (E := E))
  rw [h₁]
  have hcancel :
      (chartModelBasis E).map (toEuclidean (E := E)).toLinearEquiv
        = (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis := by
    refine Module.Basis.eq_of_apply_eq ?_
    intro i
    have hb_i : (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis i
        = EuclideanSpace.single i (1 : ℝ) := by
      simp [OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply (𝕜 := ℝ) (ι := Fin (Module.finrank ℝ E))]
    rw [Module.Basis.map_apply, chartModelBasis_apply, hb_i]
    simp
  rw [hcancel]
  exact (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).addHaar_eq_volume

/-- Chart-local measure on `M` built from the chart-local density and the extended
chart at `x₀`, using the canonical additive Haar measure on the model space `E`.

The measure is constructed in three steps: restrict the canonical Haar measure on `E` to
the target of the extended chart; weight it by the pullback of the chart-local density
through the extended chart's inverse; push forward the result to `M` along the extended
chart's inverse. -/
def chartLocalMeasure
    (g : SmoothRiemannianMetric I M) (x₀ : M) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.map (extChartAt I x₀).symm
    (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
      (fun y : E =>
        ENNReal.ofReal
          (chartDensity g x₀ ((extChartAt I x₀).symm y))))

/-- The chart-local measure is (by definition) the pushforward along `(extChartAt I x₀).symm`
of the density-weighted restriction of the canonical Haar measure on `E` to the chart
target. -/
lemma chartLocalMeasure_def
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    chartLocalMeasure (I := I) g x₀ =
      MeasureTheory.Measure.map (extChartAt I x₀).symm
        (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
          (fun y : E =>
            ENNReal.ofReal
              (chartDensity g x₀ ((extChartAt I x₀).symm y)))) := rfl

end Measure
end Integral
end DifferentialGeometry
