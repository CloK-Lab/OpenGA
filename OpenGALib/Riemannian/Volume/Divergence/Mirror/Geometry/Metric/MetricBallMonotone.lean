import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import OpenGALib.Riemannian.Volume.Divergence.Mirror.Geometry.Metric.Basic

set_option autoImplicit false

/-!
# Smooth Riemannian Metric Alias

This file contains the alias for smooth Riemannian metrics.
It is not a realized object; realized metric families import this definition.
-/

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]

theorem ball_subset_of_le
    {X : Type*} [PseudoMetricSpace X] {x : X} {r R : Real}
    (hr : r ≤ R) :
    Metric.ball x r ⊆ Metric.ball x R := by
  intro y hy
  rw [Metric.mem_ball] at hy ⊢
  exact lt_of_lt_of_le hy hr

/-- Closed metric balls are monotone in the radius. -/
theorem cball_subset_of_le
    {X : Type*} [PseudoMetricSpace X] {x : X} {r R : Real}
    (hr : r ≤ R) :
    Metric.closedBall x r ⊆ Metric.closedBall x R := by
  intro y hy
  rw [Metric.mem_closedBall] at hy ⊢
  exact le_trans hy hr

end DifferentialGeometry
