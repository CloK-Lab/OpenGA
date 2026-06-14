import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Chart model basis

The canonical basis of a finite-dimensional real inner-product model space `E`,
transported from the Euclidean standard basis through `toEuclidean`. It is the
fixed model-space frame used to read off chart-coordinate components in the
divergence-theorem construction.

Lifted from `external/differential-geometry` (`Geometry/Metric/ChartGram`) as the
first leaf of the divergence-theorem port; see `docs/DIVERGENCE_THEOREM_PORT.md`.
Bridging to OpenGALib's existing chart-frame API is deferred (port first,
optimize later).

Provenance: differential-geometry Geometry/Metric/ChartGram.lean.
-/

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Math.** The canonical basis of the model space `E`: the Euclidean standard
basis pulled back through the isometry `toEuclidean : E ≃L EuclideanSpace ℝ (Fin n)`.
Marked `irreducible` so downstream proofs use `chartModelBasis_apply` rather than
unfolding the `Module.Basis.map`. -/
@[irreducible] noncomputable def chartModelBasis (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.map
    (toEuclidean (E := E)).symm.toLinearEquiv

/-- **Math.** The `i`-th model-basis vector is `toEuclidean⁻¹` of the `i`-th
Euclidean coordinate vector. -/
@[simp] lemma chartModelBasis_apply (i : Fin (Module.finrank ℝ E)) :
    chartModelBasis E i =
      (toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ)) := by
  classical
  with_unfolding_all
  change (toEuclidean (E := E)).symm.toLinearEquiv
        ((EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis i) =
      (toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ))
  simp [OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply (𝕜 := ℝ) (ι := Fin (Module.finrank ℝ E))]

end Riemannian
