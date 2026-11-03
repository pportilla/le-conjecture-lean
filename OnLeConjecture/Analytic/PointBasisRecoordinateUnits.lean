/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GeneralSourceBlowupLift
public import OnLeConjecture.Analytic.PointBasisRecoordinate

/-!
# Point-basis transport with exceptional-coordinate units

General blowup lifts multiply the exceptional equation by an analytic
unit. These units must be accumulated along the recorded predecessor
relation. The recursion below constructs the factors, proves that they
are units, and transports every exact strict-transform identity and
multiplicity. The commuting chart identities are the local analytic
data supplied by the general blowup-lift construction.
-/

public section

namespace OnLeConjecture.Analytic.AnalyticPointBasis

open OnLeConjecture.Analytic.Germ

variable {N : ℕ} (c : AnalyticPointBasis N)

/-- The compensated coordinates at a predecessor. -/
@[expose] noncomputable def unitTransportSource
    (E lift : Fin N → PointedEquivGerm 2) (q : Fin N) : PointedEquivGerm 2 :=
  (E (c.predecessor q)).symm.comp ((c.sourceCoordinates q).comp (lift q))

/-- The accumulated analytic unit is constructed recursively from the
unit at the parent and the exceptional-coordinate unit of the child. -/
@[expose] noncomputable def transportUnit
    (c : AnalyticPointBasis N)
    (E lift : Fin N → PointedEquivGerm 2) (center : Fin N → ℂ)
    (U : Fin N → Germ 2) (q : Fin N) : Germ 2 :=
  if _hq : q = c.root then 1 else
    (pointBlowupChartGerm (center q)).pullbackRingHom
      ((c.unitTransportSource E lift q).forward.pullbackRingHom
        (transportUnit c E lift center U (c.predecessor q))) *
      U q ^ c.multiplicity (c.predecessor q)
termination_by c.generation q
decreasing_by exact c.generation_decreases q _hq

theorem transportUnit_isUnit
    (c : AnalyticPointBasis N)
    (E lift : Fin N → PointedEquivGerm 2) (center : Fin N → ℂ)
    (U : Fin N → Germ 2) (hU : ∀ q, q ≠ c.root → IsUnit (U q)) (q : Fin N) :
    IsUnit (c.transportUnit E lift center U q) := by
  rw [transportUnit]
  split_ifs with hq
  · exact isUnit_one
  · exact (((transportUnit_isUnit c E lift center U hU (c.predecessor q)).map _).map _).mul
      ((hU q hq).pow _)
termination_by c.generation q
decreasing_by exact c.generation_decreases q hq

theorem unitTransportSource_parent_apply
    (E lift : Fin N → PointedEquivGerm 2) (q : Fin N) :
    (c.unitTransportSource E lift q).forward.pullbackRingHom
      ((E (c.predecessor q)).forward.pullbackRingHom (c.germ (c.predecessor q))) =
    (lift q).forward.pullbackRingHom
      ((c.sourceCoordinates q).forward.pullbackRingHom (c.germ (c.predecessor q))) := by
  change (((E (c.predecessor q)).inverse.comp
    ((c.sourceCoordinates q).forward.comp (lift q).forward)).pullbackRingHom
      ((E (c.predecessor q)).forward.pullbackRingHom (c.germ (c.predecessor q)))) = _
  simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
  congr 2
  exact (E (c.predecessor q)).pullbackRingEquiv.symm_apply_apply _

/-- A whole recorded analytic point basis with accumulated unit factors.
The coordinate change at the root is unrestricted. -/
@[expose] noncomputable def recoordinateWithUnits
    (E lift : Fin N → PointedEquivGerm 2) (center : Fin N → ℂ)
    (U : Fin N → Germ 2) (hU : ∀ q, q ≠ c.root → IsUnit (U q))
    (hy : ∀ q, q ≠ c.root →
      (E q).forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U q)
    (hchart : ∀ q, q ≠ c.root →
      (lift q).forward.comp (pointBlowupChartGerm (center q)) =
        (pointBlowupChartGerm (c.chartCenter q)).comp (E q).forward) :
    AnalyticPointBasis N where
  root := c.root
  predecessor := c.predecessor
  predecessor_root := c.predecessor_root
  generation := c.generation
  generation_decreases := c.generation_decreases
  multiplicity := c.multiplicity
  multiplicity_pos := c.multiplicity_pos
  germ := fun q ↦ c.transportUnit E lift center U q * (E q).forward.pullbackRingHom (c.germ q)
  germ_mem := by
    intro q
    apply (Ideal.unit_mul_mem_iff_mem _ (c.transportUnit_isUnit E lift center U hU q)).mpr
    exact ((E q).pullback_mem_maximalIdeal_pow_iff _).mpr (c.germ_mem q)
  germ_not_mem_succ := by
    intro q h
    apply c.germ_not_mem_succ q
    apply ((E q).pullback_mem_maximalIdeal_pow_iff _).mp
    exact (Ideal.unit_mul_mem_iff_mem _ (c.transportUnit_isUnit E lift center U hU q)).mp h
  sourceCoordinates := c.unitTransportSource E lift
  chartCenter := center
  transform_identity := by
    intro q hq
    have hbase :
        (pointBlowupChartGerm (center q)).pullbackRingHom
          ((c.unitTransportSource E lift q).forward.pullbackRingHom
            ((E (c.predecessor q)).forward.pullbackRingHom (c.germ (c.predecessor q)))) =
        coordinate (1 : Fin 2) ^ c.multiplicity (c.predecessor q) *
          (U q ^ c.multiplicity (c.predecessor q) * (E q).forward.pullbackRingHom (c.germ q)) := by
      rw [c.unitTransportSource_parent_apply]
      have h := congrArg (fun B : PointedMapGerm 2 2 ↦ B.pullbackRingHom
        ((c.sourceCoordinates q).forward.pullbackRingHom (c.germ (c.predecessor q)))) (hchart q hq)
      simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply] at h
      rw [h, c.transform_identity q hq, map_mul, map_pow, hy q hq, mul_pow, mul_assoc]
    change (pointBlowupChartGerm (center q)).pullbackRingHom
      ((c.unitTransportSource E lift q).forward.pullbackRingHom
        (c.transportUnit E lift center U (c.predecessor q) *
          (E (c.predecessor q)).forward.pullbackRingHom (c.germ (c.predecessor q)))) = _
    rw [map_mul, map_mul, hbase]
    conv_rhs => rw [transportUnit, dif_neg hq]
    ring

/-- The root unit is one, so the prescribed source equivalence is
realized exactly at the root, not merely up to a unit. -/
theorem recoordinateWithUnits_root_germ
    (E lift : Fin N → PointedEquivGerm 2) (center : Fin N → ℂ)
    (U : Fin N → Germ 2) (hU : ∀ q, q ≠ c.root → IsUnit (U q))
    (hy : ∀ q, q ≠ c.root →
      (E q).forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U q)
    (hchart : ∀ q, q ≠ c.root →
      (lift q).forward.comp (pointBlowupChartGerm (center q)) =
        (pointBlowupChartGerm (c.chartCenter q)).comp (E q).forward) :
    (c.recoordinateWithUnits E lift center U hU hy hchart).germ c.root =
      (E c.root).forward.pullbackRingHom (c.germ c.root) := by
  change c.transportUnit E lift center U c.root * _ = _
  rw [transportUnit, dif_pos rfl, one_mul]

/-- The proximity certificate is retained with its matched roots,
generations, predecessors, and exact multiplicities. -/
@[expose] noncomputable def recoordinateWithUnitsProximity
    (d : AnalyticProximityData c)
    (E lift : Fin N → PointedEquivGerm 2) (center : Fin N → ℂ)
    (U : Fin N → Germ 2) (hU : ∀ q, q ≠ c.root → IsUnit (U q))
    (hy : ∀ q, q ≠ c.root →
      (E q).forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * U q)
    (hchart : ∀ q, q ≠ c.root →
      (lift q).forward.comp (pointBlowupChartGerm (center q)) =
        (pointBlowupChartGerm (c.chartCenter q)).comp (E q).forward) :
    AnalyticProximityData (c.recoordinateWithUnits E lift center U hU hy hchart) where
  proximity := d.proximity
  root_eq := d.root_eq
  multiplicity_eq := d.multiplicity_eq
  predecessor_mem := d.predecessor_mem
  generation_decreases := d.generation_decreases
  nested_parents := d.nested_parents

end OnLeConjecture.Analytic.AnalyticPointBasis
