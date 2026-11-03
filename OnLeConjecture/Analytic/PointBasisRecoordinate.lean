/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProximityTopOrderChain
public import OnLeConjecture.Analytic.RightLeftRelation
import Mathlib.Tactic

/-!
# Coordinate changes on a recorded analytic point basis

Each center is changed by an analytic equivalence preserving the second
coordinate. An identity of actual pointed map germs specifies how the
new chart and its parent coordinate change reproduce the old chart.
The new analytic point basis has unchanged predecessors, generations,
and exact multiplicities. The top-chain application constructs all the
required map identities from the finite triangular straightening maps.
-/

public section

namespace OnLeConjecture.Analytic.AnalyticPointBasis

open OnLeConjecture.Analytic.Germ

variable {N : ℕ} (c : AnalyticPointBasis N)

/-- Analytic coordinate changes and commuting chart maps transport all
strict-transform identities, not just the germs on a selected chain. -/
@[expose] noncomputable def recoordinate
    (E lift : Fin N → PointedEquivGerm 2) (center : Fin N → ℂ)
    (hy : ∀ q, (E q).forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1)
    (hchart : ∀ q, q ≠ c.root →
      (lift q).forward.comp (pointBlowupChartGerm (center q)) =
        (pointBlowupChartGerm (c.chartCenter q)).comp (E q).forward) :
    AnalyticPointBasis N where
  root := c.root
  predecessor := c.predecessor
  predecessor_root := c.predecessor_root
  generation := c.generation
  generation_decreases := c.generation_decreases
  germ := fun q ↦ (E q).forward.pullbackRingHom (c.germ q)
  multiplicity := c.multiplicity
  multiplicity_pos := c.multiplicity_pos
  germ_mem := fun q ↦ ((E q).pullback_mem_maximalIdeal_pow_iff _).mpr (c.germ_mem q)
  germ_not_mem_succ := fun q ↦
    ((E q).pullback_mem_maximalIdeal_pow_iff _).not.mpr (c.germ_not_mem_succ q)
  sourceCoordinates := fun q ↦ (E (c.predecessor q)).symm.comp
    ((c.sourceCoordinates q).comp (lift q))
  chartCenter := center
  transform_identity := by
    intro q hq
    change (pointBlowupChartGerm (center q)).pullbackRingHom
      (((E (c.predecessor q)).inverse.comp
        ((c.sourceCoordinates q).forward.comp (lift q).forward)).pullbackRingHom
          ((E (c.predecessor q)).forward.pullbackRingHom (c.germ (c.predecessor q)))) = _
    simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
    have hinverse : (E (c.predecessor q)).inverse.pullbackRingHom
        ((E (c.predecessor q)).forward.pullbackRingHom (c.germ (c.predecessor q))) =
          c.germ (c.predecessor q) :=
      (E (c.predecessor q)).pullbackRingEquiv.symm_apply_apply _
    rw [hinverse, ← RingHom.comp_apply, ← PointedMapGerm.pullbackRingHom_comp,
      hchart q hq, PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
      c.transform_identity q hq, map_mul, map_pow, hy]

/-- The compensated source coordinates cancel the coordinate change at
the parent, leaving the specified lift of the old parent expression. -/
theorem recoordinate_source_parent_apply
    (E lift : Fin N → PointedEquivGerm 2) (center : Fin N → ℂ)
    (hy : ∀ q, (E q).forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1)
    (hchart : ∀ q, q ≠ c.root →
      (lift q).forward.comp (pointBlowupChartGerm (center q)) =
        (pointBlowupChartGerm (c.chartCenter q)).comp (E q).forward)
    (q : Fin N) :
    ((c.recoordinate E lift center hy hchart).sourceCoordinates q).forward.pullbackRingHom
      ((c.recoordinate E lift center hy hchart).germ (c.predecessor q)) =
    (lift q).forward.pullbackRingHom
      ((c.sourceCoordinates q).forward.pullbackRingHom (c.germ (c.predecessor q))) := by
  change (((E (c.predecessor q)).inverse.comp
    ((c.sourceCoordinates q).forward.comp (lift q).forward)).pullbackRingHom
      ((E (c.predecessor q)).forward.pullbackRingHom (c.germ (c.predecessor q)))) = _
  simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
  congr 2
  exact (E (c.predecessor q)).pullbackRingEquiv.symm_apply_apply _

end OnLeConjecture.Analytic.AnalyticPointBasis
