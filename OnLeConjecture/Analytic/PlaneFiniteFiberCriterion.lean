/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CoordinatePowerResultant
public import OnLeConjecture.Analytic.RegularMonicRelation
public import OnLeConjecture.Analytic.NestedMonicTargetFinite
public import OnLeConjecture.Analytic.IsolatedFiberFiniteness
public import OnLeConjecture.Analytic.CoordinatePermutation
public import OnLeConjecture.Analytic.PairRepresentative

/-!
# The finite fibre criterion for a plane source

Finite complex dimension of the coordinate quotient places a power of the
source maximal ideal in the coordinate ideal. A nonzero component becomes
regular after a linear source change. Preparation gives a first monic
relation, and resultant elimination gives a second one. The two relations
make the analytic germ ring finite over the image ring.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped BigOperators Topology

namespace PointedMapGerm

/-- A finite coordinate fibre and a regular component imply finiteness at
the origin for a displayed analytic representative. -/
theorem isFiniteAtOrigin_of_finiteCoordinateFiber_regularComponent_ofFunction
    {m d : ℕ}
    (F : Source 2 → Source m) (hF : AnalyticAt ℂ F 0)
    (hFZero : F 0 = 0) (targetIndex : Fin m)
    (hfinite : Module.Finite ℂ
      (Germ 2 ⧸
        (PointedMapGerm.ofFunction F hF hFZero).1.coordinateIdeal))
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder
      ((PointedMapGerm.ofFunction F hF hFZero).1.component targetIndex)
      (d + 1)) :
    (PointedMapGerm.ofFunction F hF hFZero).IsFiniteAtOrigin := by
  let f : PointedMapGerm 2 m :=
    PointedMapGerm.ofFunction F hF hFZero
  obtain ⟨N, hN⟩ :=
    (Germ.quotient_moduleFinite_iff_exists_maximalIdeal_pow_le
      f.1.coordinateIdeal).mp hfinite
  have hcoordinatePowN : Germ.coordinate (1 : Fin 2) ^ N ∈
      f.1.coordinateIdeal :=
    hN (Ideal.pow_mem_pow
      (Germ.coordinate_mem_maximalIdeal (1 : Fin 2)) N)
  have hcoordinatePowSucc : Germ.coordinate (1 : Fin 2) ^ (N + 1) ∈
      f.1.coordinateIdeal := by
    rw [pow_succ]
    exact f.1.coordinateIdeal.mul_mem_right
      (Germ.coordinate (1 : Fin 2)) hcoordinatePowN
  have hcoordinatePowSpan : Germ.coordinate (1 : Fin 2) ^ (N + 1) ∈
      Ideal.span (Set.range f.1.component) := by
    have hcoordinateIdeal : f.1.coordinateIdeal =
        Ideal.span (Set.range f.1.component) := by
      apply le_antisymm
      · rw [MapGerm.coordinateIdeal_le]
        intro j
        exact Ideal.subset_span (Set.mem_range_self j)
      · rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        exact f.1.component_mem_coordinateIdeal j
    rwa [← hcoordinateIdeal]
  rw [Ideal.mem_span_range_iff_exists_fun] at hcoordinatePowSpan
  obtain ⟨multiplier, hmultiplier⟩ := hcoordinatePowSpan
  have hpower : Germ.coordinate (1 : Fin 2) ^ (N + 1) =
      ∑ j : Fin m, f.1.component j * multiplier j := by
    calc
      Germ.coordinate (1 : Fin 2) ^ (N + 1) =
          ∑ j : Fin m, multiplier j * f.1.component j :=
        hmultiplier.symm
      _ = ∑ j : Fin m, f.1.component j * multiplier j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact mul_comm _ _
  obtain ⟨G, hG, hcomponentG, A, hA, hAZero, hfirstG⟩ :=
    Germ.exists_analytic_monicRelation_at_regularGermValue hregular
  have hFCoordinate : AnalyticAt ℂ (fun z ↦ F z targetIndex) 0 := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (AnalyticAt.comp (x := (0 : Source 2))
        ((ContinuousLinearMap.proj (R := ℂ) targetIndex).analyticAt
          (F 0)) hF)
  have hcomponentF : f.1.component targetIndex = Germ.ofFunction
      (fun z ↦ F z targetIndex) hFCoordinate := by
    rw [show f = PointedMapGerm.ofFunction F hF hFZero by rfl]
    apply Subtype.ext
    exact MapGerm.component_ofFunction F hF targetIndex
  have hGEqualsCoordinate : G =ᶠ[nhds 0]
      (fun z ↦ F z targetIndex) := by
    apply Filter.Germ.coe_eq.mp
    calc
      (G : FunctionGerm 2) =
          ((Germ.ofFunction G hG : Germ 2) : FunctionGerm 2) := rfl
      _ = ((f.1.component targetIndex : Germ 2) : FunctionGerm 2) :=
        congrArg (fun q : Germ 2 ↦ (q : FunctionGerm 2))
          hcomponentG.symm
      _ = ((Germ.ofFunction (fun z ↦ F z targetIndex)
          hFCoordinate : Germ 2) : FunctionGerm 2) :=
        congrArg (fun q : Germ 2 ↦ (q : FunctionGerm 2)) hcomponentF
      _ = ((fun z ↦ F z targetIndex) : FunctionGerm 2) := rfl
  have hfirst : ∀ᶠ z : Source 2 in nhds 0,
      Germ.generalDivisionPolynomialValue (z 0)
        (A (z 1, F z targetIndex)) = 0 := by
    filter_upwards [hfirstG, hGEqualsCoordinate] with z hz hcoordinate
    simpa only [hcoordinate] using hz
  obtain ⟨B, hB, hBZero, hsecond⟩ :=
    Germ.exists_secondMonicRelation_of_coordinatePowerRelation
      F hF hFZero targetIndex A hA hAZero hfirst multiplier (by
        simpa only [f] using hpower)
  exact PointedMapGerm.isFiniteAtOrigin_of_nestedMonicTarget_relations
    F hF hFZero targetIndex d (N * (d + 1) + d)
      A B hA hAZero hB hBZero hfirst hsecond

/-- A finite coordinate fibre and a regular component imply finiteness at
the origin. -/
theorem isFiniteAtOrigin_of_finiteCoordinateFiber_regularComponent
    {m d : ℕ} (f : PointedMapGerm 2 m) (targetIndex : Fin m)
    (hfinite : f.HasFiniteCoordinateFiber)
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder
      (f.1.component targetIndex) (d + 1)) :
    f.IsFiniteAtOrigin := by
  obtain ⟨F, hF, hFZero, rfl⟩ := f.exists_ofFunction
  exact
    PointedMapGerm.isFiniteAtOrigin_of_finiteCoordinateFiber_regularComponent_ofFunction
      F hF hFZero targetIndex hfinite hregular

/-- Finite complex dimension of the coordinate quotient implies analytic
module finiteness for every map germ with plane source. -/
theorem finiteFiberCriterionAtOrigin_two (m : ℕ) :
    PointedMapGerm.FiniteFiberCriterionAtOrigin 2 m := by
  intro f hfinite
  obtain ⟨N, hN⟩ :=
    (Germ.quotient_moduleFinite_iff_exists_maximalIdeal_pow_le
      f.1.coordinateIdeal).mp hfinite
  have hcoordinatePowN : Germ.coordinate (0 : Fin 2) ^ N ∈
      f.1.coordinateIdeal :=
    hN (Ideal.pow_mem_pow
      (Germ.coordinate_mem_maximalIdeal (0 : Fin 2)) N)
  have hcoordinatePowSucc : Germ.coordinate (0 : Fin 2) ^ (N + 1) ∈
      f.1.coordinateIdeal := by
    rw [pow_succ]
    exact f.1.coordinateIdeal.mul_mem_right
      (Germ.coordinate (0 : Fin 2)) hcoordinatePowN
  have hcoordinatePowNe :
      Germ.coordinate (0 : Fin 2) ^ (N + 1) ≠ 0 :=
    pow_ne_zero _ (Germ.coordinate_ne_zero (0 : Fin 2))
  have hcomponent : ∃ targetIndex : Fin m,
      f.1.component targetIndex ≠ 0 := by
    by_contra hnone
    have hall : ∀ targetIndex : Fin m,
        f.1.component targetIndex = 0 := by
      intro targetIndex
      by_contra hne
      exact hnone ⟨targetIndex, hne⟩
    have hcoordinatePowSpan : Germ.coordinate (0 : Fin 2) ^ (N + 1) ∈
        Ideal.span (Set.range f.1.component) := by
      have hcoordinateIdeal : f.1.coordinateIdeal =
          Ideal.span (Set.range f.1.component) := by
        apply le_antisymm
        · rw [MapGerm.coordinateIdeal_le]
          intro j
          exact Ideal.subset_span (Set.mem_range_self j)
        · rw [Ideal.span_le]
          rintro _ ⟨j, rfl⟩
          exact f.1.component_mem_coordinateIdeal j
      rwa [← hcoordinateIdeal]
    rw [Ideal.mem_span_range_iff_exists_fun] at hcoordinatePowSpan
    obtain ⟨coefficient, hcoefficient⟩ := hcoordinatePowSpan
    apply hcoordinatePowNe
    rw [← hcoefficient]
    simp only [hall, mul_zero, Finset.sum_const_zero]
  obtain ⟨targetIndex, hcomponentNe⟩ := hcomponent
  obtain ⟨source, order, hregular⟩ :=
    Germ.exists_linear_equiv_regularInFirstCoordinate hcomponentNe
  let transformed : PointedMapGerm 2 m := f.comp source.forward
  have htransformedComponent : transformed.1.component targetIndex =
      source.forward.pullbackRingHom (f.1.component targetIndex) := by
    exact f.component_comp_general source.forward targetIndex
  have htransformedRegular : Germ.IsRegularInFirstCoordinateOfOrder
      (transformed.1.component targetIndex) order := by
    rw [htransformedComponent]
    exact hregular
  have horderPositive : 0 < order := by
    by_contra hnotPositive
    have horderZero : order = 0 := Nat.eq_zero_of_not_pos hnotPositive
    subst order
    have hunit : IsUnit (transformed.1.component targetIndex) := by
      simpa using
        Germ.isUnit_firstCoordinateTailIterate_of_regular
          htransformedRegular
    have hmaximal : transformed.1.component targetIndex ∈
        Germ.maximalIdeal 2 :=
      transformed.coordinateIdeal_le_maximalIdeal
        (transformed.1.component_mem_coordinateIdeal targetIndex)
    rw [Germ.mem_maximalIdeal_iff] at hmaximal
    exact (Germ.isUnit_iff_valueRingHom_ne_zero.mp hunit) hmaximal
  obtain ⟨d, horder⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt horderPositive)
  subst order
  have hmap := f.map_coordinateIdeal_pullbackRingEquiv source
  have htransformedFinite : transformed.HasFiniteCoordinateFiber :=
    (Germ.quotient_moduleFinite_iff_of_map_eq
      f.1.coordinateIdeal transformed.1.coordinateIdeal
      source.pullbackAlgEquiv hmap).mp hfinite
  have hfiniteTransformed : transformed.IsFiniteAtOrigin :=
    PointedMapGerm.isFiniteAtOrigin_of_finiteCoordinateFiber_regularComponent
      transformed targetIndex htransformedFinite htransformedRegular
  exact (PointedMapGerm.isFiniteAtOrigin_sourceEquiv_comp_iff
    f source).mp hfiniteTransformed

/-- The finite fibre criterion needed for maps from `ℂ²` to `ℂ³`. -/
theorem finiteFiberCriterionAtOrigin_two_three :
    PointedMapGerm.FiniteFiberCriterionAtOrigin 2 3 :=
  PointedMapGerm.finiteFiberCriterionAtOrigin_two 3

end PointedMapGerm

end OnLeConjecture.Analytic
