/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.AnalyticBranchPullback
public import OnLeConjecture.PlaneCurve.SmoothBranch

/-!
# Intersection with the branches of an even quadratic curve

For a square root `epsilon` of `-1`, the factors of
`x² + y²ᵃ` are `x - epsilon yᵃ` and `x + epsilon yᵃ`. This file
constructs the triangular analytic coordinate changes that straighten these
factors and identifies their intersection multiplicities with the orders on
the two explicit parametrizations.
-/

public section

namespace OnLeConjecture.DTwo

open Filter
open OnLeConjecture.Analytic
open OnLeConjecture.PlaneCurve

namespace Germ

private theorem intersectionMultiplicity_eq_of_eq
    {g g' h h' : Germ 2}
    (hg : g = g') (hh : h = h')
    (hfinite : HasFiniteIntersection g h)
    (hfinite' : HasFiniteIntersection g' h') :
    intersectionMultiplicity g h hfinite =
      intersectionMultiplicity g' h' hfinite' := by
  subst g'
  subst h'
  rfl

/-- Finite intersection with a product implies finite intersection with its
left factor. -/
theorem hasFiniteIntersection_left_of_mul
    (g h u : Germ 2) (hfinite : HasFiniteIntersection (g * h) u) :
    HasFiniteIntersection g u := by
  rw [hasFiniteIntersection_iff_exists_maximalIdeal_pow_le] at hfinite ⊢
  rcases hfinite with ⟨N, hN⟩
  refine ⟨N, hN.trans ?_⟩
  rw [pairIdeal_eq_span, pairIdeal_eq_span, Ideal.span_le]
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl
  · exact (pairIdeal g u).mul_mem_right h
      (Ideal.subset_span (Set.mem_insert _ _))
  · exact Ideal.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- Finite intersection with a product implies finite intersection with its
right factor. -/
theorem hasFiniteIntersection_right_of_mul
    (g h u : Germ 2) (hfinite : HasFiniteIntersection (g * h) u) :
    HasFiniteIntersection h u := by
  rw [mul_comm] at hfinite
  exact hasFiniteIntersection_left_of_mul h g u hfinite

/-- The triangular map `(x,y) ↦ (x + epsilon yᵃ,y)`. -/
@[expose]
noncomputable def evenBranchShiftMap
    (a : ℕ) (epsilon : ℂ) (z : Source 2) : Source 2 :=
  fun i ↦ Fin.cases (z 0 + epsilon * z 1 ^ a) (fun j ↦ z j.succ) i

/-- The inverse triangular map `(x,y) ↦ (x - epsilon yᵃ,y)`. -/
@[expose]
noncomputable def evenBranchShiftInverseMap
    (a : ℕ) (epsilon : ℂ) (z : Source 2) : Source 2 :=
  fun i ↦ Fin.cases (z 0 - epsilon * z 1 ^ a) (fun j ↦ z j.succ) i

@[simp]
theorem evenBranchShiftMap_apply_zero
    (a : ℕ) (epsilon : ℂ) (z : Source 2) :
    evenBranchShiftMap a epsilon z 0 = z 0 + epsilon * z 1 ^ a := by
  simp [evenBranchShiftMap]

@[simp]
theorem evenBranchShiftMap_apply_one
    (a : ℕ) (epsilon : ℂ) (z : Source 2) :
    evenBranchShiftMap a epsilon z 1 = z 1 := by
  rfl

@[simp]
theorem evenBranchShiftInverseMap_apply_zero
    (a : ℕ) (epsilon : ℂ) (z : Source 2) :
    evenBranchShiftInverseMap a epsilon z 0 =
      z 0 - epsilon * z 1 ^ a := by
  simp [evenBranchShiftInverseMap]

@[simp]
theorem evenBranchShiftInverseMap_apply_one
    (a : ℕ) (epsilon : ℂ) (z : Source 2) :
    evenBranchShiftInverseMap a epsilon z 1 = z 1 := by
  rfl

theorem evenBranchShiftMap_analyticAt (a : ℕ) (epsilon : ℂ) :
    AnalyticAt ℂ (evenBranchShiftMap a epsilon) 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact
      ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).analyticAt 0).add
        (analyticAt_const.mul
          (((ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0).pow a))
  · exact
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0

theorem evenBranchShiftInverseMap_analyticAt (a : ℕ) (epsilon : ℂ) :
    AnalyticAt ℂ (evenBranchShiftInverseMap a epsilon) 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact
      ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).analyticAt 0).sub
        (analyticAt_const.mul
          (((ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0).pow a))
  · exact
      (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0

@[simp]
theorem evenBranchShiftMap_zero {a : ℕ} (ha : 1 ≤ a) (epsilon : ℂ) :
    evenBranchShiftMap a epsilon (0 : Source 2) = 0 := by
  ext i
  fin_cases i <;> simp [zero_pow (by omega : a ≠ 0)]

@[simp]
theorem evenBranchShiftInverseMap_zero
    {a : ℕ} (ha : 1 ≤ a) (epsilon : ℂ) :
    evenBranchShiftInverseMap a epsilon (0 : Source 2) = 0 := by
  ext i
  fin_cases i <;> simp [zero_pow (by omega : a ≠ 0)]

@[simp]
theorem evenBranchShiftMap_inverse
    (a : ℕ) (epsilon : ℂ) (z : Source 2) :
    evenBranchShiftMap a epsilon (evenBranchShiftInverseMap a epsilon z) = z := by
  ext i
  fin_cases i <;> simp

@[simp]
theorem evenBranchShiftInverseMap_shift
    (a : ℕ) (epsilon : ℂ) (z : Source 2) :
    evenBranchShiftInverseMap a epsilon (evenBranchShiftMap a epsilon z) = z := by
  ext i
  fin_cases i <;> simp

/-- The triangular map as a pointed analytic germ. -/
@[expose]
noncomputable def evenBranchShiftGerm
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ) : PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction (evenBranchShiftMap a epsilon)
    (evenBranchShiftMap_analyticAt a epsilon)
    (evenBranchShiftMap_zero ha epsilon)

/-- The inverse triangular map as a pointed analytic germ. -/
@[expose]
noncomputable def evenBranchShiftInverseGerm
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ) : PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction (evenBranchShiftInverseMap a epsilon)
    (evenBranchShiftInverseMap_analyticAt a epsilon)
    (evenBranchShiftInverseMap_zero ha epsilon)

@[simp]
theorem evenBranchShiftGerm_comp_inverse
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ) :
    (evenBranchShiftGerm a ha epsilon).comp
        (evenBranchShiftInverseGerm a ha epsilon) =
      PointedMapGerm.identity 2 := by
  rw [evenBranchShiftGerm, evenBranchShiftInverseGerm,
    PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦
    evenBranchShiftMap_inverse a epsilon z

@[simp]
theorem evenBranchShiftInverseGerm_comp
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ) :
    (evenBranchShiftInverseGerm a ha epsilon).comp
        (evenBranchShiftGerm a ha epsilon) =
      PointedMapGerm.identity 2 := by
  rw [evenBranchShiftGerm, evenBranchShiftInverseGerm,
    PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦
    evenBranchShiftInverseMap_shift a epsilon z

/-- The triangular source coordinate change that straightens
`x - epsilon yᵃ`. -/
@[expose]
noncomputable def evenBranchShiftEquiv
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ) : PointedEquivGerm 2 where
  forward := evenBranchShiftGerm a ha epsilon
  inverse := evenBranchShiftInverseGerm a ha epsilon
  forward_inverse := evenBranchShiftGerm_comp_inverse a ha epsilon
  inverse_forward := evenBranchShiftInverseGerm_comp a ha epsilon

/-- The equation `x - epsilon yᵃ` of the parametrized branch. -/
@[expose]
noncomputable def evenBranchFactor (a : ℕ) (epsilon : ℂ) : Germ 2 :=
  Germ.coordinate (0 : Fin 2) -
    Germ.constRingHom 2 epsilon * Germ.coordinate (1 : Fin 2) ^ a

@[simp]
theorem evenBranchShiftEquiv_pullback_factor
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ) :
    (evenBranchShiftEquiv a ha epsilon).pullbackAlgEquiv
        (evenBranchFactor a epsilon) =
      Germ.coordinate (0 : Fin 2) := by
  rw [evenBranchFactor, map_sub, map_mul, map_pow]
  rw [PointedEquivGerm.pullbackAlgEquiv_apply,
    PointedEquivGerm.pullbackRingEquiv_apply]
  change
    (evenBranchShiftGerm a ha epsilon).pullbackRingHom
        (Germ.coordinate (0 : Fin 2)) -
      (evenBranchShiftGerm a ha epsilon).pullbackRingHom
          (Germ.constRingHom 2 epsilon) *
        (evenBranchShiftGerm a ha epsilon).pullbackRingHom
            (Germ.coordinate (1 : Fin 2)) ^ a = _
  rw [PointedMapGerm.pullback_coordinate,
    PointedMapGerm.pullback_coordinate,
    PointedMapGerm.pullback_constRingHom]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    change (z 0 + epsilon * z 1 ^ a) - epsilon * z 1 ^ a = z 0
    ring

/-- Restriction after the triangular coordinate change is pullback along
`t ↦ (epsilon tᵃ,t)`. -/
theorem hyperplaneRestriction_evenBranchShiftEquiv_pullback
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ) (u : Germ 2) :
    Germ.hyperplaneRestriction 1
        ((evenBranchShiftEquiv a ha epsilon).pullbackAlgEquiv u) =
      (evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom u := by
  have hcomp : (evenBranchShiftGerm a ha epsilon).comp
      (Germ.hyperplaneInclusionGerm 1) =
      evenQuadraticBranchMapGerm a ha epsilon := by
    rw [evenBranchShiftGerm, Germ.hyperplaneInclusionGerm,
      evenQuadraticBranchMapGerm, PointedMapGerm.comp_ofFunction]
    apply Subtype.ext
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z ↦ by
      ext i
      fin_cases i
      · change 0 + epsilon *
            (Germ.hyperplaneInclusion 1 z (1 : Fin 2)) ^ a =
          epsilon * z 0 ^ a
        rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide,
          Germ.hyperplaneInclusion_apply_succ]
        ring
      · change Germ.hyperplaneInclusion 1 z (1 : Fin 2) = z 0
        rw [show (1 : Fin 2) = (0 : Fin 1).succ by decide,
          Germ.hyperplaneInclusion_apply_succ]
  calc
    Germ.hyperplaneRestriction 1
        ((evenBranchShiftEquiv a ha epsilon).pullbackAlgEquiv u) =
        ((evenBranchShiftGerm a ha epsilon).comp
          (Germ.hyperplaneInclusionGerm 1)).pullbackRingHom u := by
      exact (DFunLike.congr_fun
        (PointedMapGerm.pullbackRingHom_comp
          (evenBranchShiftGerm a ha epsilon)
          (Germ.hyperplaneInclusionGerm 1)) u).symm
    _ = (evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom u := by
      rw [hcomp]

/-- A nonzero restriction to an even branch gives finite intersection with
its defining factor. -/
theorem hasFiniteIntersection_evenBranchFactor_of_pullback_ne_zero
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ) (u : Germ 2)
    (hne : (evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom u ≠ 0) :
    HasFiniteIntersection (evenBranchFactor a epsilon) u := by
  have hrestriction : Germ.hyperplaneRestriction 1
      ((evenBranchShiftEquiv a ha epsilon).pullbackAlgEquiv u) ≠ 0 := by
    rw [hyperplaneRestriction_evenBranchShiftEquiv_pullback]
    exact hne
  have hpull :=
    hasFiniteIntersection_coordinate_of_restriction_ne_zero
      ((evenBranchShiftEquiv a ha epsilon).pullbackAlgEquiv u) hrestriction
  have hback := hpull.pullback (evenBranchShiftEquiv a ha epsilon).symm
  have hesymm : (evenBranchShiftEquiv a ha epsilon).symm.pullbackAlgEquiv =
      (evenBranchShiftEquiv a ha epsilon).pullbackAlgEquiv.symm := by
    ext q
    rfl
  have hfactorBack : (evenBranchShiftEquiv a ha epsilon).symm.pullbackAlgEquiv
      (Germ.coordinate (0 : Fin 2)) = evenBranchFactor a epsilon := by
    rw [hesymm, ← evenBranchShiftEquiv_pullback_factor a ha epsilon]
    exact (evenBranchShiftEquiv a ha epsilon).pullbackAlgEquiv.symm_apply_apply
      (evenBranchFactor a epsilon)
  have huBack : (evenBranchShiftEquiv a ha epsilon).symm.pullbackAlgEquiv
      ((evenBranchShiftEquiv a ha epsilon).pullbackAlgEquiv u) = u := by
    rw [hesymm]
    exact (evenBranchShiftEquiv a ha epsilon).pullbackAlgEquiv.symm_apply_apply u
  convert hback using 1
  · exact hfactorBack.symm
  · exact huBack.symm

/-- Finite intersection with a branch factor forces its explicit branch
restriction to be nonzero. -/
theorem evenQuadraticBranchMapGerm_pullback_ne_zero_of_hasFiniteIntersection
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ) (u : Germ 2)
    (hfinite : HasFiniteIntersection (evenBranchFactor a epsilon) u) :
    (evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom u ≠ 0 := by
  let e := evenBranchShiftEquiv a ha epsilon
  have hpull := hfinite.pullback e
  have hcoordinate : HasFiniteIntersection (Germ.coordinate (0 : Fin 2))
      (e.pullbackAlgEquiv u) := by
    convert hpull using 1
    exact (evenBranchShiftEquiv_pullback_factor a ha epsilon).symm
  have hrestriction :=
    restriction_ne_zero_of_hasFiniteIntersection_coordinate
      (e.pullbackAlgEquiv u) hcoordinate
  rw [hyperplaneRestriction_evenBranchShiftEquiv_pullback] at hrestriction
  exact hrestriction

/-- Intersection with `x - epsilon yᵃ` is the vanishing order along
`t ↦ (epsilon tᵃ,t)`. -/
theorem intersectionMultiplicity_evenBranchFactor_eq_order
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ) (u : Germ 2)
    (hne : (evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom u ≠ 0) :
    intersectionMultiplicity (evenBranchFactor a epsilon) u
        (hasFiniteIntersection_evenBranchFactor_of_pullback_ne_zero
          a ha epsilon u hne) =
      (Germ.vanishingOrder
        ((evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom u)).toNat := by
  let e := evenBranchShiftEquiv a ha epsilon
  have hrestriction : Germ.hyperplaneRestriction 1
      (e.pullbackAlgEquiv u) ≠ 0 := by
    rw [hyperplaneRestriction_evenBranchShiftEquiv_pullback]
    exact hne
  have hfinite :=
    hasFiniteIntersection_evenBranchFactor_of_pullback_ne_zero
      a ha epsilon u hne
  calc
    intersectionMultiplicity (evenBranchFactor a epsilon) u hfinite =
        intersectionMultiplicity (e.pullbackAlgEquiv
            (evenBranchFactor a epsilon)) (e.pullbackAlgEquiv u)
          (hfinite.pullback e) :=
      intersectionMultiplicity_pullback e hfinite
    _ = (Germ.vanishingOrder
          (Germ.hyperplaneRestriction 1 (e.pullbackAlgEquiv u))).toNat :=
      by
        have hcoordinate :=
          intersectionMultiplicity_coordinate_eq_restrictionOrder
            (e.pullbackAlgEquiv u) hrestriction
        exact (intersectionMultiplicity_eq_of_eq
          (evenBranchShiftEquiv_pullback_factor a ha epsilon) rfl
          (hfinite.pullback e)
          (hasFiniteIntersection_coordinate_of_restriction_ne_zero
            (e.pullbackAlgEquiv u) hrestriction)).trans hcoordinate
    _ = (Germ.vanishingOrder
          ((evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom u)).toNat := by
      rw [hyperplaneRestriction_evenBranchShiftEquiv_pullback]

/-- The product of the two branch factors is `x² + y²ᵃ`. -/
theorem evenBranchFactor_mul_negative
    (a : ℕ) (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1) :
    evenBranchFactor a epsilon * evenBranchFactor a (-epsilon) =
      Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.coordinate (1 : Fin 2) ^ (2 * a) := by
  have hconstant : Germ.constRingHom 2 epsilon ^ 2 = -1 := by
    rw [← map_pow, hepsilon, map_neg, map_one]
  rw [evenBranchFactor, evenBranchFactor]
  simp only [map_neg]
  rw [pow_mul]
  ring_nf
  rw [hconstant]
  ring

/-- Finite intersection with `x²+y²ᵃ` makes both branch restrictions
nonzero. -/
theorem evenQuadraticBranchMapGerm_pullbacks_ne_zero
    (a : ℕ) (ha : 1 ≤ a) (epsilon : ℂ)
    (hepsilon : epsilon ^ 2 = -1) (u : Germ 2)
    (hfinite : HasFiniteIntersection
      (Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.coordinate (1 : Fin 2) ^ (2 * a)) u) :
    (evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom u ≠ 0 ∧
      (evenQuadraticBranchMapGerm a ha (-epsilon)).pullbackRingHom u ≠ 0 := by
  have hproduct : HasFiniteIntersection
      (evenBranchFactor a epsilon * evenBranchFactor a (-epsilon)) u := by
    rw [evenBranchFactor_mul_negative a epsilon hepsilon]
    exact hfinite
  constructor
  · exact evenQuadraticBranchMapGerm_pullback_ne_zero_of_hasFiniteIntersection
      a ha epsilon u (hasFiniteIntersection_left_of_mul
        (evenBranchFactor a epsilon) (evenBranchFactor a (-epsilon)) u hproduct)
  · exact evenQuadraticBranchMapGerm_pullback_ne_zero_of_hasFiniteIntersection
      a ha (-epsilon) u (hasFiniteIntersection_right_of_mul
        (evenBranchFactor a epsilon) (evenBranchFactor a (-epsilon)) u hproduct)

end Germ

end OnLeConjecture.DTwo
