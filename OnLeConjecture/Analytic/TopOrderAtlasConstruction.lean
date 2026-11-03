/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SupportedFiniteBlowupLift
public import OnLeConjecture.Analytic.PointBasisRecoordinateUnits

/-!
# Constructing transverse coordinates along the top-order centers

An arbitrary transverse root coordinate change is lifted recursively at
every supported child of a top-order point. The finite-tangent condition
is derived from regularity. Beyond those children the original charts are
retained, with the compensating parent coordinate change. This constructs
the analytic atlas identities needed on the whole top-order part without
assuming that the original atlas was adapted to the chosen smooth axis.

Separation of different recorded children is a distinct geometric condition.
It is not inferred from the predecessor relation or multiplicities.
-/

public section

namespace OnLeConjecture.Analytic.AnalyticPointBasis

open OnLeConjecture.Analytic.Germ

variable {N : ℕ} (c : AnalyticPointBasis N)

/-- Local coordinates, including regularity exactly at top-order points. -/
structure RegularAtlasCoordinate (q : Fin N) where
  equivalence : PointedEquivGerm 2
  exceptionalUnit : Germ 2
  center : ℂ
  isUnit : IsUnit exceptionalUnit
  second_coordinate : q ≠ c.root →
    equivalence.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1 * exceptionalUnit
  regular : c.multiplicity q = c.multiplicity c.root →
    IsRegularInFirstCoordinateOfOrder (equivalence.forward.pullbackRingHom (c.germ q))
      (c.multiplicity q)

theorem exists_regularAtlasChild
    (q : Fin N) (hq : q ≠ c.root)
    (htop : c.multiplicity (c.predecessor q) = c.multiplicity c.root)
    (parent : c.RegularAtlasCoordinate (c.predecessor q)) :
    ∃ A : c.RegularAtlasCoordinate q,
      ((c.sourceCoordinates q).symm.comp parent.equivalence).forward.comp
        (pointBlowupChartGerm A.center) =
          (pointBlowupChartGerm (c.chartCenter q)).comp A.equivalence.forward := by
  let e := (c.sourceCoordinates q).symm.comp parent.equivalence
  let f := (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (c.predecessor q))
  have heval : e.forward.pullbackRingHom f =
      parent.equivalence.forward.pullbackRingHom (c.germ (c.predecessor q)) := by
    change ((c.sourceCoordinates q).inverse.comp parent.equivalence.forward).pullbackRingHom
      ((c.sourceCoordinates q).forward.pullbackRingHom (c.germ (c.predecessor q))) = _
    rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
    congr 1
    exact (c.sourceCoordinates q).pullbackRingEquiv.symm_apply_apply _
  have hf : f ∈ maximalIdeal 2 ^ c.multiplicity (c.predecessor q) :=
    (c.sourceCoordinates q).forward.pullback_mem_maximalIdeal_pow (c.germ_mem _)
  have hnext : f ∉ maximalIdeal 2 ^ (c.multiplicity (c.predecessor q) + 1) :=
    ((c.sourceCoordinates q).pullback_mem_maximalIdeal_pow_iff _).not.mpr (c.germ_not_mem_succ _)
  have hreg : IsRegularInFirstCoordinateOfOrder (e.forward.pullbackRingHom f)
      (c.multiplicity (c.predecessor q)) := by
    rw [heval]
    exact parent.regular htop
  have hg : c.germ q ∈ maximalIdeal 2 := by
    simpa only [pow_one] using
      Ideal.pow_le_pow_right (c.multiplicity_pos q) (c.germ_mem q)
  obtain ⟨ζ, E, U, hU, hEy, hcomm, _hnew⟩ := exists_finite_chart_lift_of_regular_pullback
    e (c.chartCenter q) (c.multiplicity (c.predecessor q)) f (c.germ q) hf hreg
    (c.transform_identity q hq) hg
  refine ⟨⟨E, U, ζ, hU, fun _ ↦ hEy, ?_⟩, hcomm⟩
  intro hqtop
  have horder : c.multiplicity q = c.multiplicity (c.predecessor q) := hqtop.trans htop.symm
  rw [horder]
  exact regular_child_of_finite_chart_lift e E (c.chartCenter q) ζ
    (c.multiplicity (c.predecessor q)) f (c.germ q) U hf hnext
    (horder ▸ c.germ_mem q) hU hEy hcomm (c.transform_identity q hq)

@[expose] noncomputable def regularAtlasChild
    (q : Fin N) (hq : q ≠ c.root)
    (htop : c.multiplicity (c.predecessor q) = c.multiplicity c.root)
    (parent : c.RegularAtlasCoordinate (c.predecessor q)) : c.RegularAtlasCoordinate q :=
  Classical.choose (c.exists_regularAtlasChild q hq htop parent)

theorem regularAtlasChild_chart
    (q : Fin N) (hq : q ≠ c.root)
    (htop : c.multiplicity (c.predecessor q) = c.multiplicity c.root)
    (parent : c.RegularAtlasCoordinate (c.predecessor q)) :
    ((c.sourceCoordinates q).symm.comp parent.equivalence).forward.comp
      (pointBlowupChartGerm (c.regularAtlasChild q hq htop parent).center) =
        (pointBlowupChartGerm (c.chartCenter q)).comp
          (c.regularAtlasChild q hq htop parent).equivalence.forward :=
  Classical.choose_spec (c.exists_regularAtlasChild q hq htop parent)

/-- Recursive analytic coordinates constructed from the original exact
strict-transform identities and the chosen transverse root coordinates. -/
@[expose] noncomputable def regularAtlasCoordinates
    (c : AnalyticPointBasis N) (e : PointedEquivGerm 2)
    (hregular : IsRegularInFirstCoordinateOfOrder
      (e.forward.pullbackRingHom (c.germ c.root)) (c.multiplicity c.root))
    (q : Fin N) : c.RegularAtlasCoordinate q :=
  if hq : q = c.root then
    { equivalence := e
      exceptionalUnit := 1
      center := c.chartCenter q
      isUnit := isUnit_one
      second_coordinate := fun hne ↦ (hne hq).elim
      regular := fun _ ↦ by simpa only [hq] using hregular }
  else if htop : c.multiplicity (c.predecessor q) = c.multiplicity c.root then
    c.regularAtlasChild q hq htop
      (regularAtlasCoordinates c e hregular (c.predecessor q))
  else
    { equivalence := PointedEquivGerm.identity 2
      exceptionalUnit := 1
      center := c.chartCenter q
      isUnit := isUnit_one
      second_coordinate := fun _ ↦ by
        rw [PointedEquivGerm.identity_forward, PointedMapGerm.pullbackRingHom_identity]
        simp only [RingHom.id_apply, mul_one]
      regular := fun hqtop ↦ (htop (c.predecessor_top_order hqtop ⟨hq, rfl⟩)).elim }
termination_by c.generation q
decreasing_by exact c.generation_decreases q hq

/-- The parent expression used to lift an old edge. Only children of
top-order points need new lifts. -/
@[expose] noncomputable def regularAtlasLift
    (e : PointedEquivGerm 2)
    (hregular : IsRegularInFirstCoordinateOfOrder
      (e.forward.pullbackRingHom (c.germ c.root)) (c.multiplicity c.root))
    (q : Fin N) : PointedEquivGerm 2 :=
  if c.multiplicity (c.predecessor q) = c.multiplicity c.root then
    (c.sourceCoordinates q).symm.comp
      (c.regularAtlasCoordinates e hregular (c.predecessor q)).equivalence
  else PointedEquivGerm.identity 2

theorem regularAtlasCoordinates_chart
    (e : PointedEquivGerm 2)
    (hregular : IsRegularInFirstCoordinateOfOrder
      (e.forward.pullbackRingHom (c.germ c.root)) (c.multiplicity c.root))
    (q : Fin N) (hq : q ≠ c.root) :
    (c.regularAtlasLift e hregular q).forward.comp
      (pointBlowupChartGerm (c.regularAtlasCoordinates e hregular q).center) =
        (pointBlowupChartGerm (c.chartCenter q)).comp
          (c.regularAtlasCoordinates e hregular q).equivalence.forward := by
  rw [regularAtlasLift]
  by_cases htop : c.multiplicity (c.predecessor q) = c.multiplicity c.root
  · have hstate : c.regularAtlasCoordinates e hregular q =
        c.regularAtlasChild q hq htop (c.regularAtlasCoordinates e hregular (c.predecessor q)) := by
      rw [regularAtlasCoordinates, dif_neg hq, dif_pos htop]
    rw [if_pos htop, hstate]
    exact c.regularAtlasChild_chart q hq htop _
  · rw [if_neg htop, regularAtlasCoordinates, dif_neg hq, dif_neg htop]
    simp only [PointedEquivGerm.identity_forward, PointedMapGerm.identity_comp,
      PointedMapGerm.comp_identity]

/-- The whole point basis in the constructed transverse coordinates. -/
@[expose] noncomputable def regularAtlas
    (e : PointedEquivGerm 2)
    (hregular : IsRegularInFirstCoordinateOfOrder
      (e.forward.pullbackRingHom (c.germ c.root)) (c.multiplicity c.root)) : AnalyticPointBasis N :=
  c.recoordinateWithUnits
    (fun q ↦ (c.regularAtlasCoordinates e hregular q).equivalence)
    (c.regularAtlasLift e hregular)
    (fun q ↦ (c.regularAtlasCoordinates e hregular q).center)
    (fun q ↦ (c.regularAtlasCoordinates e hregular q).exceptionalUnit)
    (fun q _ ↦ (c.regularAtlasCoordinates e hregular q).isUnit)
    (fun q hq ↦ (c.regularAtlasCoordinates e hregular q).second_coordinate hq)
    (c.regularAtlasCoordinates_chart e hregular)

theorem regularAtlas_root_germ
    (e : PointedEquivGerm 2)
    (hregular : IsRegularInFirstCoordinateOfOrder
      (e.forward.pullbackRingHom (c.germ c.root)) (c.multiplicity c.root)) :
    (c.regularAtlas e hregular).germ c.root = e.forward.pullbackRingHom (c.germ c.root) := by
  rw [regularAtlas, recoordinateWithUnits_root_germ, regularAtlasCoordinates, dif_pos rfl]

/-- Each transported equation is its coordinate pullback multiplied by
the recursively accumulated analytic unit. -/
theorem exists_regularAtlas_germ_unit
    (e : PointedEquivGerm 2)
    (hregular : IsRegularInFirstCoordinateOfOrder
      (e.forward.pullbackRingHom (c.germ c.root)) (c.multiplicity c.root)) (q : Fin N) :
    ∃ K : Germ 2, IsUnit K ∧ (c.regularAtlas e hregular).germ q =
      K * (c.regularAtlasCoordinates e hregular q).equivalence.forward.pullbackRingHom
        (c.germ q) := by
  refine ⟨_, c.transportUnit_isUnit _ _ _ _
    (fun q _ ↦ (c.regularAtlasCoordinates e hregular q).isUnit) q, rfl⟩

theorem regularAtlas_source_identity_of_parent_top
    (e : PointedEquivGerm 2)
    (hregular : IsRegularInFirstCoordinateOfOrder
      (e.forward.pullbackRingHom (c.germ c.root)) (c.multiplicity c.root))
    (q : Fin N) (htop : c.multiplicity (c.predecessor q) = c.multiplicity c.root) :
    ((c.regularAtlas e hregular).sourceCoordinates q).forward = PointedMapGerm.identity 2 := by
  change (c.regularAtlasCoordinates e hregular (c.predecessor q)).equivalence.inverse.comp
    ((c.sourceCoordinates q).forward.comp (c.regularAtlasLift e hregular q).forward) = _
  rw [regularAtlasLift, if_pos htop]
  change (c.regularAtlasCoordinates e hregular (c.predecessor q)).equivalence.inverse.comp
    ((c.sourceCoordinates q).forward.comp ((c.sourceCoordinates q).inverse.comp
      (c.regularAtlasCoordinates e hregular (c.predecessor q)).equivalence.forward)) = _
  rw [← PointedMapGerm.comp_assoc (c.sourceCoordinates q).forward,
    (c.sourceCoordinates q).forward_inverse, PointedMapGerm.identity_comp]
  exact (c.regularAtlasCoordinates e hregular (c.predecessor q)).equivalence.inverse_forward

/-- The recursive construction yields literal commuting parent-chart
maps at every child of a top-order point. -/
theorem regularAtlas_parent_chart
    (e : PointedEquivGerm 2)
    (hregular : IsRegularInFirstCoordinateOfOrder
      (e.forward.pullbackRingHom (c.germ c.root)) (c.multiplicity c.root))
    (q : Fin N) (hq : q ≠ c.root)
    (htop : c.multiplicity (c.predecessor q) = c.multiplicity c.root) :
    (c.regularAtlasCoordinates e hregular (c.predecessor q)).equivalence.forward.comp
      (pointBlowupChartGerm (c.regularAtlasCoordinates e hregular q).center) =
        (c.sourceCoordinates q).forward.comp
          ((pointBlowupChartGerm (c.chartCenter q)).comp
            (c.regularAtlasCoordinates e hregular q).equivalence.forward) := by
  have h := c.regularAtlasCoordinates_chart e hregular q hq
  rw [regularAtlasLift, if_pos htop] at h
  have hcomp := congrArg (fun B : PointedMapGerm 2 2 ↦ (c.sourceCoordinates q).forward.comp B) h
  change (c.sourceCoordinates q).forward.comp
    (((c.sourceCoordinates q).inverse.comp
      (c.regularAtlasCoordinates e hregular (c.predecessor q)).equivalence.forward).comp
        (pointBlowupChartGerm (c.regularAtlasCoordinates e hregular q).center)) = _ at hcomp
  rw [← PointedMapGerm.comp_assoc, ← PointedMapGerm.comp_assoc,
    (c.sourceCoordinates q).forward_inverse, PointedMapGerm.identity_comp] at hcomp
  exact hcomp

/-- The proximity data stay matched to the unchanged centers,
predecessors, generations, and exact multiplicities. -/
@[expose] noncomputable def regularAtlasProximity
    (d : AnalyticProximityData c) (e : PointedEquivGerm 2)
    (hregular : IsRegularInFirstCoordinateOfOrder
      (e.forward.pullbackRingHom (c.germ c.root)) (c.multiplicity c.root)) :
    AnalyticProximityData (c.regularAtlas e hregular) where
  proximity := d.proximity
  root_eq := d.root_eq
  multiplicity_eq := d.multiplicity_eq
  predecessor_mem := d.predecessor_mem
  generation_decreases := d.generation_decreases
  nested_parents := d.nested_parents

end OnLeConjecture.Analytic.AnalyticPointBasis
