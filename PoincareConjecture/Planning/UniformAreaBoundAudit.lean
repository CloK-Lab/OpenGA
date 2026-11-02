import OpenGALib.Topology.ExtinctionEndgame
import OpenGALib.Analysis.Width.SurgeryAreaEvolution

/-!
# Audit of the arbitrary-evolution area-bound target

On 2026-09-22, platform theorem
`4e7712f8-c457-4100-9d0e-91210ea81c7a` quantified over every
`SurgeryTopologyEvolution M`. The local record permits a constant evolution.
Such an evolution cannot have uniform area-evolution data: the existing
comparison theorem would force its nonempty slice to disappear.

This is a statement audit, not a disproof of geometric Ricci-flow extinction.
No platform theorem stubs are imported.
-/

namespace OpenGA.StatementAudit

universe u

def constantEvolution (M : ClosedThreeManifold.{u}) : SurgeryTopologyEvolution M where
  components := fun _ => [M]
  initial := rfl
  initial_interval := ⟨1, by norm_num, fun _ _ => rfl⟩
  history := fun _ _ => .refl [M]

/-- **Math.** Abstract topological evolutions exist without any Ricci-flow
construction or simply-connected hypothesis. -/
theorem nonempty_abstract_evolution (M : ClosedThreeManifold.{u}) :
    Nonempty (SurgeryTopologyEvolution M) := ⟨constantEvolution M⟩

theorem constantEvolution_not_finiteExtinction (M : ClosedThreeManifold.{u}) :
    ¬ (constantEvolution M).FiniteExtinction := by
  rintro ⟨T, _, h⟩
  have hempty := h T le_rfl
  simp [constantEvolution] at hempty

theorem constantEvolution_no_uniform_area_bound (M : ClosedThreeManifold.{u}) :
    ¬ (∃ W : ℝ, 0 ≤ W ∧ ∀ T : ℝ,
      0 < T → (constantEvolution M).components T ≠ [] →
        Nonempty (SurgeryAreaEvolutionData W T)) := by
  rintro ⟨W, _, h⟩
  apply constantEvolution_not_finiteExtinction M
  apply (constantEvolution M).finiteExtinction_of_width_control (W := W)
  intro T hT hne
  obtain ⟨D⟩ := h T hT hne
  exact nonempty_widthComparisonTrace_of_surgeryComparisonProcess D.toMeasured.toProcess

/-- **Math.** The added simply-connected hypothesis does not repair universal
quantification over the abstract evolution record. -/
theorem not_every_evolution_has_uniform_area_bound
    (M : ClosedThreeManifold.{u}) [SimplyConnectedSpace M] :
    ¬ (∀ E : SurgeryTopologyEvolution M,
      ∃ W : ℝ, 0 ≤ W ∧ ∀ T : ℝ,
        0 < T → E.components T ≠ [] → Nonempty (SurgeryAreaEvolutionData W T)) := by
  intro h
  exact constantEvolution_no_uniform_area_bound M (h (constantEvolution M))

#print axioms constantEvolution_no_uniform_area_bound
#print axioms not_every_evolution_has_uniform_area_bound
#print axioms nonempty_abstract_evolution

end OpenGA.StatementAudit
