/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeierstrassPreparation
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Tactic.FinCases
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Linear coordinates for plane analytic germs

A nonzero vector in the source plane can be chosen as the first vector of an
invertible linear coordinate change. Consequently every nonzero plane
analytic germ becomes regular in the first coordinate after a linear source
change.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- A matrix whose first column is `v` and whose second column is chosen so
that it is invertible whenever `v` is nonzero. -/
@[expose]
noncomputable def planeFirstColumnMatrix (v : Source 2) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  if v 0 = 0 then
    !![v 0, 1; v 1, 0]
  else
    !![v 0, 0; v 1, 1]

/-- The continuous linear map represented by `planeFirstColumnMatrix`. -/
@[expose]
noncomputable def planeFirstColumnMap (v : Source 2) :
    Source 2 →L[ℂ] Source 2 :=
  (Matrix.toLin' (planeFirstColumnMatrix v)).toContinuousLinearMap

theorem planeFirstColumnMap_firstCoordinateVector (v : Source 2) :
    planeFirstColumnMap v (firstCoordinateVector 1) = v := by
  by_cases hv0 : v 0 = 0
  all_goals
    ext i
    fin_cases i <;>
      simp [planeFirstColumnMap, planeFirstColumnMatrix,
        Matrix.toLin'_apply, firstCoordinateVector, hv0]

theorem planeFirstColumnMap_det_ne_zero {v : Source 2} (hv : v ≠ 0) :
    (planeFirstColumnMap v).det ≠ 0 := by
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro hv1
      apply hv
      ext i
      fin_cases i
      · exact hv0
      · exact hv1
    exact (by simp [planeFirstColumnMap, planeFirstColumnMatrix, hv0,
      LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
      Matrix.det_fin_two, hv1])
  · exact (by simp [planeFirstColumnMap, planeFirstColumnMatrix, hv0,
      LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
      Matrix.det_fin_two])

/-- The linear equivalence whose first column is `v`. -/
@[expose]
noncomputable def planeFirstColumnEquiv (v : Source 2) (hv : v ≠ 0) :
    Source 2 ≃L[ℂ] Source 2 :=
  (planeFirstColumnMap v).toContinuousLinearEquivOfDetNeZero
    (planeFirstColumnMap_det_ne_zero hv)

@[simp]
theorem planeFirstColumnEquiv_apply (v : Source 2) (hv : v ≠ 0)
    (z : Source 2) :
    planeFirstColumnEquiv v hv z = planeFirstColumnMap v z := by
  exact ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply _ _ _

@[simp]
theorem planeFirstColumnEquiv_firstCoordinateVector
    (v : Source 2) (hv : v ≠ 0) :
    planeFirstColumnEquiv v hv (firstCoordinateVector 1) = v := by
  rw [planeFirstColumnEquiv_apply,
    planeFirstColumnMap_firstCoordinateVector]

/-- A continuous linear equivalence determines a pointed analytic
equivalence germ. -/
@[expose]
noncomputable def pointedEquivGermOfContinuousLinearEquiv {n : ℕ}
    (e : Source n ≃L[ℂ] Source n) : PointedEquivGerm n where
  forward := PointedMapGerm.ofFunction e (e.analyticAt 0) (map_zero e)
  inverse := PointedMapGerm.ofFunction e.symm (e.symm.analyticAt 0)
    (map_zero e.symm)
  forward_inverse := by
    rw [PointedMapGerm.comp_ofFunction]
    apply Subtype.ext
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z ↦ e.apply_symm_apply z
  inverse_forward := by
    rw [PointedMapGerm.comp_ofFunction]
    apply Subtype.ext
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z ↦ e.symm_apply_apply z

/-- The pointed analytic linear coordinate change whose first source vector
is `v`. -/
@[expose]
noncomputable def planeFirstColumnPointedEquiv
    (v : Source 2) (hv : v ≠ 0) : PointedEquivGerm 2 :=
  pointedEquivGermOfContinuousLinearEquiv (planeFirstColumnEquiv v hv)

theorem planeFirstColumnPointedEquiv_forward_comp_line
    (v : Source 2) (hv : v ≠ 0) :
    (planeFirstColumnPointedEquiv v hv).forward.comp
        (lineGerm (firstCoordinateVector 1)) =
      lineGerm v := by
  simp only [planeFirstColumnPointedEquiv,
    pointedEquivGermOfContinuousLinearEquiv, lineGerm]
  rw [PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    ext i
    change
      (planeFirstColumnEquiv v hv
        (z 0 • firstCoordinateVector 1)) i = (z 0 • v) i
    rw [map_smul, planeFirstColumnEquiv_firstCoordinateVector]

/-- Restriction to the zero vector is the constant germ given by evaluation
at the origin. -/
theorem lineRestriction_zero (f : Germ 2) :
    lineRestriction (0 : Source 2) f =
      constRingHom 1 (valueRingHom 2 f) := by
  rcases f with ⟨f, hf⟩
  induction f using Filter.Germ.inductionOn with
  | _ f =>
      rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hf
      change lineRestriction (0 : Source 2) (ofFunction f hf) =
        constRingHom 1 (valueRingHom 2 (ofFunction f hf))
      rw [lineRestriction_ofFunction, valueRingHom_ofFunction]
      apply Subtype.ext
      rw [Germ.coe_ofFunction, Germ.coe_constRingHom]
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z ↦ by
        simp [lineMap_apply]

/-- Pulling back along the linear coordinate change and then restricting to
the first coordinate axis equals restriction to the chosen line. -/
theorem lineRestriction_planeFirstColumn_pullback
    (v : Source 2) (hv : v ≠ 0) (f : Germ 2) :
    lineRestriction (firstCoordinateVector 1)
        ((planeFirstColumnPointedEquiv v hv).forward.pullbackRingHom f) =
      lineRestriction v f := by
  change (lineGerm (firstCoordinateVector 1)).pullbackRingHom
      ((planeFirstColumnPointedEquiv v hv).forward.pullbackRingHom f) =
    (lineGerm v).pullbackRingHom f
  change ((lineGerm (firstCoordinateVector 1)).pullbackRingHom.comp
      (planeFirstColumnPointedEquiv v hv).forward.pullbackRingHom) f =
    (lineGerm v).pullbackRingHom f
  rw [← PointedMapGerm.pullbackRingHom_comp,
    planeFirstColumnPointedEquiv_forward_comp_line]

/-- Every nonzero plane analytic germ is regular in the first coordinate
after an invertible linear source change. -/
theorem exists_linear_equiv_regularInFirstCoordinate
    {f : Germ 2} (hf : f ≠ 0) :
    ∃ e : PointedEquivGerm 2, ∃ d : ℕ,
      IsRegularInFirstCoordinateOfOrder
        (e.forward.pullbackRingHom f) d := by
  by_cases hfUnit : IsUnit f
  · let e : PointedEquivGerm 2 :=
      pointedEquivGermOfContinuousLinearEquiv
        (ContinuousLinearEquiv.refl ℂ (Source 2))
    refine ⟨e, 0, ?_⟩
    rw [IsRegularInFirstCoordinateOfOrder]
    change vanishingOrder
      (lineRestriction (firstCoordinateVector 1)
        (e.forward.pullbackRingHom f)) = (0 : ℕ∞)
    rw [vanishingOrder_eq_zero_iff_isUnit]
    exact (hfUnit.map e.forward.pullbackRingHom).map
      (lineRestriction (firstCoordinateVector 1))
  have hfValue : valueRingHom 2 f = 0 := by
    by_contra hfValue
    exact hfUnit (isUnit_of_valueRingHom_ne_zero hfValue)
  obtain ⟨v, hvline⟩ := exists_lineRestriction_ne_zero hf
  have hv : v ≠ 0 := by
    intro hv
    subst v
    apply hvline
    rw [lineRestriction_zero, hfValue]
    exact map_zero (constRingHom 1)
  let e : PointedEquivGerm 2 := planeFirstColumnPointedEquiv v hv
  obtain ⟨d, u, hu, hfactor⟩ :=
    exists_eq_coordinate_pow_mul_unit hvline
  have horder : vanishingOrder (lineRestriction v f) = d :=
    vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hfactor
  refine ⟨e, d, ?_⟩
  rw [IsRegularInFirstCoordinateOfOrder]
  change vanishingOrder
      (lineRestriction (firstCoordinateVector 1)
        (e.forward.pullbackRingHom f)) = (d : ℕ∞)
  rw [lineRestriction_planeFirstColumn_pullback]
  exact horder

end Germ

end OnLeConjecture.Analytic
