import OpenGALib.Riemannian.Curvature.RiemannCurvature
import OpenGALib.Riemannian.Curvature.RiemannSymmetries
import OpenGALib.Riemannian.Curvature.Tensoriality
import OpenGALib.Riemannian.Curvature.SectionalCurvature
import OpenGALib.Riemannian.Curvature.RicciTensorBundle
import OpenGALib.Riemannian.Curvature.Killing

/-!
# Curvature (aggregator)

Single stable entry point for the Riemannian curvature layer. Downstream that
wants "all of curvature" imports `OpenGALib.Riemannian.Curvature`; the internal
file layout (core tensor, symmetries, tensoriality, sectional, Ricci, Killing)
can then be reorganized freely without breaking consumers.

Layer dependency DAG (acyclic):
  RiemannCurvature (core: tensor, antisymm, Ricci, IsFlat)
    └─ RiemannSymmetries (pair symmetry, Bianchi, ricci_symm)
         ├─ Tensoriality (Z-slot + first-slot pointwise dependence)
         ├─ SectionalCurvature
         └─ Killing
  RicciTensorBundle (Ricci bundle constructions)
-/
