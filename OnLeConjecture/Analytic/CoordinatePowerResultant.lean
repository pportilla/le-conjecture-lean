/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MvPolynomialFinitePreparation
public import OnLeConjecture.Analytic.ParametricResultant

/-!
# Elimination from a coordinate power relation

A monic relation in the first source coordinate permits analytic division
of the coefficients in a coordinate ideal relation. The resultant of the
divided relation and the monic polynomial has a regular constant
coefficient. Finite parameter preparation then produces a monic relation
in the second source coordinate whose coefficients depend on the target.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Polynomial
open scoped BigOperators Topology

namespace Germ

/-- A monic polynomial with an arbitrary commutative coefficient ring and
the lower coefficients indexed in increasing order. -/
@[expose] noncomputable def parameterMonicPolynomial
    {R : Type*} [CommRing R] (d : ℕ) (a : Fin (d + 1) → R) : R[X] :=
  Polynomial.monomial (d + 1) 1 +
    ∑ i : Fin (d + 1), Polynomial.monomial i.1 (a i)

theorem parameterMonicPolynomial_coeff_degree
    {R : Type*} [CommRing R] (d : ℕ) (a : Fin (d + 1) → R) :
    (Germ.parameterMonicPolynomial d a).coeff (d + 1) = 1 := by
  simp only [Germ.parameterMonicPolynomial, Polynomial.coeff_add]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, if_true]
  have hsum : (∑ i : Fin (d + 1),
      if i.1 = d + 1 then a i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (by omega)]
  rw [hsum, add_zero]

theorem parameterMonicPolynomial_coeff_of_degree_lt
    {R : Type*} [CommRing R] (d : ℕ) (a : Fin (d + 1) → R)
    (k : ℕ) (hk : d + 1 < k) :
    (Germ.parameterMonicPolynomial d a).coeff k = 0 := by
  simp only [Germ.parameterMonicPolynomial, Polynomial.coeff_add]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [if_neg (by omega : d + 1 ≠ k), zero_add]
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg (by omega)]

theorem parameterMonicPolynomial_natDegree
    {R : Type*} [CommRing R] [Nontrivial R]
    (d : ℕ) (a : Fin (d + 1) → R) :
    (Germ.parameterMonicPolynomial d a).natDegree = d + 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    exact Germ.parameterMonicPolynomial_coeff_of_degree_lt d a k hk
  · rw [Germ.parameterMonicPolynomial_coeff_degree]
    exact one_ne_zero

theorem parameterMonicPolynomial_monic
    {R : Type*} [CommRing R] [Nontrivial R]
    (d : ℕ) (a : Fin (d + 1) → R) :
    (Germ.parameterMonicPolynomial d a).Monic := by
  change (Germ.parameterMonicPolynomial d a).coeff
      (Germ.parameterMonicPolynomial d a).natDegree = 1
  rw [Germ.parameterMonicPolynomial_natDegree,
    Germ.parameterMonicPolynomial_coeff_degree]

/-- A polynomial assembled from `d + 1` coefficients has degree at most
`d`. -/
theorem natDegree_fin_sum_monomial_le
    {R : Type*} [CommRing R] (d : ℕ)
    (a : Fin (d + 1) → R) :
    (∑ i : Fin (d + 1), Polynomial.monomial i.1 (a i)).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_monomial_le (a i)).trans (by omega)

/-- A coordinate power relation and a monic relation in the first source
coordinate produce a monic relation in the second source coordinate. -/
theorem exists_secondMonicRelation_of_coordinatePowerRelation
    {m d N : ℕ}
    (F : Source 2 → Source m) (hF : AnalyticAt ℂ F 0)
    (hFZero : F 0 = 0) (targetIndex : Fin m)
    (A : ℂ × ℂ → Germ.GeneralCoefficientSpace d)
    (hA : AnalyticAt ℂ A (0, 0)) (hAZero : A (0, 0) = 0)
    (hfirst : ∀ᶠ z : Source 2 in nhds 0,
      Germ.generalDivisionPolynomialValue (z 0)
        (A (z 1, F z targetIndex)) = 0)
    (multiplier : Fin m → Germ 2)
    (hpower : Germ.coordinate (1 : Fin 2) ^ (N + 1) =
      ∑ j : Fin m,
        (PointedMapGerm.ofFunction F hF hFZero).1.component j *
          multiplier j) :
    ∃ B : Source m →
        Germ.GeneralCoefficientSpace (N * (d + 1) + d),
      AnalyticAt ℂ B 0 ∧
      B 0 = 0 ∧
      ∀ᶠ z : Source 2 in nhds 0,
        Germ.generalDivisionPolynomialValue (z 1) (B (F z)) = 0 := by
  choose H hH hmultiplier using fun j : Fin m ↦
    Germ.exists_analyticRepresentative_allOrders (multiplier j)
  let p : Fin m → FormalMultilinearSeries ℂ (Source 2) ℂ :=
    fun j ↦ (hH j).choose
  have hp (j : Fin m) : HasFPowerSeriesAt (H j) (p j) 0 :=
    (hH j).choose_spec
  choose quotient remainder hquotient hremainder hdivision using
    fun j : Fin m ↦
      Germ.exists_analytic_generalDivision_withTwoParameters
        (p j) d (hp j).radius_pos A hA hAZero
  have hcoordinateZero : AnalyticAt ℂ
      (fun z : Source 2 ↦ z 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ)
      (0 : Fin 2)).analyticAt 0
  have hcoordinateOne : AnalyticAt ℂ
      (fun z : Source 2 ↦ z 1) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ)
      (1 : Fin 2)).analyticAt 0
  have hFCoordinate (j : Fin m) :
      AnalyticAt ℂ (fun z ↦ F z j) 0 := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (AnalyticAt.comp (x := (0 : Source 2))
        ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt (F 0)) hF)
  let pairCoordinates : Source 2 → ℂ × ℂ := fun w ↦ (w 0, w 1)
  have hpairCoordinates : AnalyticAt ℂ pairCoordinates 0 :=
    hcoordinateZero.prod hcoordinateOne
  have hpairCoordinatesZero : pairCoordinates 0 = (0, 0) := rfl
  let coefficientFunction : Fin (d + 1) → Source 2 → ℂ :=
    fun i w ↦ A (pairCoordinates w) i
  have hcoefficientFunction (i : Fin (d + 1)) :
      AnalyticAt ℂ (coefficientFunction i) 0 := by
    have hAcomp : AnalyticAt ℂ (fun w ↦ A (pairCoordinates w)) 0 := by
      simpa only [Function.comp_def, hpairCoordinatesZero] using
        (AnalyticAt.comp (x := (0 : Source 2)) hA hpairCoordinates)
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (AnalyticAt.comp (x := (0 : Source 2))
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt (A (0, 0)))
        hAcomp)
  let coefficient : Fin (d + 1) → Germ 2 := fun i ↦
    Germ.ofFunction (coefficientFunction i) (hcoefficientFunction i)
  let W : Polynomial (Germ 2) :=
    Germ.parameterMonicPolynomial d coefficient
  have hWMonic : W.Monic :=
    Germ.parameterMonicPolynomial_monic d coefficient
  have hWDegree : W.natDegree = d + 1 :=
    Germ.parameterMonicPolynomial_natDegree d coefficient
  let remainderFunction : Fin m → Fin (d + 1) → Source 2 → ℂ :=
    fun j k w ↦ remainder j (pairCoordinates w) k
  have hremainderFunction (j : Fin m) (k : Fin (d + 1)) :
      AnalyticAt ℂ (remainderFunction j k) 0 := by
    have hcomp : AnalyticAt ℂ
        (fun w ↦ remainder j (pairCoordinates w)) 0 := by
      simpa only [Function.comp_def, hpairCoordinatesZero] using
        (AnalyticAt.comp (x := (0 : Source 2))
          (hremainder j) hpairCoordinates)
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (AnalyticAt.comp (x := (0 : Source 2))
        ((ContinuousLinearMap.proj (R := ℂ) k).analyticAt
          (remainder j (0, 0))) hcomp)
  let remainderCoefficient : Fin m → Fin (d + 1) → Germ 2 :=
    fun j k ↦ Germ.ofFunction (remainderFunction j k)
      (hremainderFunction j k)
  let q : Fin m → Polynomial (Germ 2) := fun j ↦
    ∑ k : Fin (d + 1),
      Polynomial.monomial k.1 (remainderCoefficient j k)
  have hqDegree (j : Fin m) : (q j).natDegree ≤ d := by
    exact Germ.natDegree_fin_sum_monomial_le d
      (remainderCoefficient j)
  let baseFunction : Source 2 → Source 2 := fun z ↦
    Germ.planePoint (z 1) (F z targetIndex)
  have hbaseFunction : AnalyticAt ℂ baseFunction 0 := by
    have hpair : AnalyticAt ℂ
        (fun z ↦ (z 1, F z targetIndex)) 0 :=
      hcoordinateOne.prod (hFCoordinate targetIndex)
    simpa only [Function.comp_def,
      Germ.generalPlanePointContinuousLinearMap_apply] using
      (AnalyticAt.comp (x := (0 : Source 2))
        (Germ.generalPlanePointContinuousLinearMap.analyticAt
          ((0 : Source 2) 1, F 0 targetIndex)) hpair)
  have hbaseFunctionZero : baseFunction 0 = 0 := by
    simp [baseFunction, hFZero, Germ.planePoint]
  let baseMap : PointedMapGerm 2 2 :=
    PointedMapGerm.ofFunction baseFunction hbaseFunction hbaseFunctionZero
  let sourceMap : PointedMapGerm 2 m :=
    PointedMapGerm.ofFunction F hF hFZero
  let ψ : Germ 2 →+* Germ 2 := baseMap.pullbackRingHom
  let sourceX : Germ 2 := Germ.coordinate (0 : Fin 2)
  have hHsum (j : Fin m) :
      H j =ᶠ[nhds 0] (p j).sum := by
    have hsum : HasFPowerSeriesAt (p j).sum (p j) 0 :=
      ((p j).hasFPowerSeriesOnBall (hp j).radius_pos).hasFPowerSeriesAt
    filter_upwards [(hp j).eventually_hasSum_sub,
      hsum.eventually_hasSum_sub] with z hzH hzsum
    simpa only [sub_zero] using hzH.unique hzsum
  have hsourceCoefficientFunction (i : Fin (d + 1)) :
      AnalyticAt ℂ (fun z : Source 2 ↦
        A (z 1, F z targetIndex) i) 0 := by
    have hinputZero : ((fun z : Source 2 ↦
        (z 1, F z targetIndex)) 0) = (0, 0) := by
      simp [hFZero]
    have hinput : AnalyticAt ℂ
        (fun z : Source 2 ↦ (z 1, F z targetIndex)) 0 :=
      hcoordinateOne.prod (hFCoordinate targetIndex)
    have hcomp : AnalyticAt ℂ
        (fun z : Source 2 ↦ A (z 1, F z targetIndex)) 0 := by
      have hAAt : AnalyticAt ℂ A
          ((fun z : Source 2 ↦ (z 1, F z targetIndex)) 0) := by
        simpa only [hinputZero] using hA
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (x := (0 : Source 2)) hAAt hinput)
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (AnalyticAt.comp (x := (0 : Source 2))
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt
          (A ((fun z : Source 2 ↦ (z 1, F z targetIndex)) 0)))
        hcomp)
  have hcoefficientPullback (i : Fin (d + 1)) :
      ψ (coefficient i) = Germ.ofFunction
        (fun z : Source 2 ↦ A (z 1, F z targetIndex) i)
        (hsourceCoefficientFunction i) := by
    rw [show ψ = baseMap.pullbackRingHom by rfl]
    rw [show coefficient i = Germ.ofFunction
        (coefficientFunction i) (hcoefficientFunction i) by rfl]
    rw [show baseMap = PointedMapGerm.ofFunction baseFunction
        hbaseFunction hbaseFunctionZero by rfl]
    rw [PointedMapGerm.pullbackRingHom_apply,
      Germ.compPointed_ofFunction]
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    apply Filter.Eventually.of_forall
    intro z
    simp [baseFunction, coefficientFunction, pairCoordinates,
      Germ.planePoint]
  have hsourceRemainderFunction (j : Fin m) (k : Fin (d + 1)) :
      AnalyticAt ℂ (fun z : Source 2 ↦
        remainder j (z 1, F z targetIndex) k) 0 := by
    have hinputZero : ((fun z : Source 2 ↦
        (z 1, F z targetIndex)) 0) = (0, 0) := by
      simp [hFZero]
    have hinput : AnalyticAt ℂ
        (fun z : Source 2 ↦ (z 1, F z targetIndex)) 0 :=
      hcoordinateOne.prod (hFCoordinate targetIndex)
    have hcomp : AnalyticAt ℂ
        (fun z : Source 2 ↦ remainder j (z 1, F z targetIndex)) 0 := by
      have hremainderAt : AnalyticAt ℂ (remainder j)
          ((fun z : Source 2 ↦ (z 1, F z targetIndex)) 0) := by
        simpa only [hinputZero] using hremainder j
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (x := (0 : Source 2))
          hremainderAt hinput)
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (AnalyticAt.comp (x := (0 : Source 2))
        ((ContinuousLinearMap.proj (R := ℂ) k).analyticAt
          (remainder j
            ((fun z : Source 2 ↦ (z 1, F z targetIndex)) 0))) hcomp)
  have hremainderPullback (j : Fin m) (k : Fin (d + 1)) :
      ψ (remainderCoefficient j k) = Germ.ofFunction
        (fun z : Source 2 ↦ remainder j
          (z 1, F z targetIndex) k)
        (hsourceRemainderFunction j k) := by
    rw [show ψ = baseMap.pullbackRingHom by rfl]
    rw [show remainderCoefficient j k = Germ.ofFunction
        (remainderFunction j k) (hremainderFunction j k) by rfl]
    rw [show baseMap = PointedMapGerm.ofFunction baseFunction
        hbaseFunction hbaseFunctionZero by rfl]
    rw [PointedMapGerm.pullbackRingHom_apply,
      Germ.compPointed_ofFunction]
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    apply Filter.Eventually.of_forall
    intro z
    simp [baseFunction, remainderFunction, pairCoordinates,
      Germ.planePoint]
  let divisionSubstitution : Source 2 → ℂ × (ℂ × ℂ) := fun z ↦
    (z 0, (z 1, F z targetIndex))
  have hdivisionSubstitution : AnalyticAt ℂ divisionSubstitution 0 :=
    hcoordinateZero.prod
      (hcoordinateOne.prod (hFCoordinate targetIndex))
  have hdivisionSubstitutionZero : divisionSubstitution 0 = (0, 0) := by
    simp [divisionSubstitution, hFZero]
  have hdivisionPulled (j : Fin m) :
      ∀ᶠ z : Source 2 in nhds 0,
        (p j).sum (Germ.planePoint (z 0) (z 1)) =
          Germ.generalDivisionPolynomialValue (z 0)
              (A (z 1, F z targetIndex)) *
                quotient j (divisionSubstitution z) +
            ∑ k : Fin (d + 1), (z 0) ^ k.1 *
              remainder j (z 1, F z targetIndex) k := by
    have hpull := hdivisionSubstitution.continuousAt.eventually (by
      simpa only [hdivisionSubstitutionZero] using hdivision j)
    filter_upwards [hpull] with z hz
    simpa only [divisionSubstitution] using hz
  have hmultiplierRemainder (j : Fin m) :
      ∀ᶠ z : Source 2 in nhds 0,
        H j z = ∑ k : Fin (d + 1),
          (z 0) ^ k.1 * remainder j (z 1, F z targetIndex) k := by
    filter_upwards [hHsum j, hdivisionPulled j, hfirst] with
      z hHvalue hdiv hzero
    have hplane : Germ.planePoint (z 0) (z 1) = z := by
      ext i
      fin_cases i <;> simp [Germ.planePoint]
    rw [hplane] at hdiv
    rw [hHvalue, hdiv, hzero, zero_mul, zero_add]
  have hqEvaluation (j : Fin m) :
      multiplier j = Polynomial.eval sourceX ((q j).map ψ) := by
    rw [hmultiplier j, Polynomial.eval_map]
    rw [show q j = ∑ k : Fin (d + 1),
      Polynomial.monomial k.1 (remainderCoefficient j k) by rfl]
    rw [Polynomial.eval₂_finsetSum]
    simp only [Polynomial.eval₂_monomial]
    simp_rw [hremainderPullback]
    apply Subtype.ext
    calc
      ((Germ.ofFunction (H j) (hH j) : Germ 2) : FunctionGerm 2) =
          (H j : FunctionGerm 2) := rfl
      _ = (((fun z : Source 2 ↦ ∑ k : Fin (d + 1),
            remainder j (z 1, F z targetIndex) k * z 0 ^ k.1) :
              Source 2 → ℂ) : FunctionGerm 2) := by
        apply Filter.Germ.coe_eq.mpr
        filter_upwards [hmultiplierRemainder j] with z hz
        simpa only [mul_comm] using hz
      _ = ((((∑ k : Fin (d + 1), fun z : Source 2 ↦
            remainder j (z 1, F z targetIndex) k * z 0 ^ k.1) :
              Source 2 → ℂ)) : FunctionGerm 2) := by
        congr 1
        funext z
        simp only [Finset.sum_apply]
      _ = ∑ k : Fin (d + 1),
          (((fun z : Source 2 ↦
            remainder j (z 1, F z targetIndex) k * z 0 ^ k.1) :
              Source 2 → ℂ) : FunctionGerm 2) := by
        simpa only using Germ.coe_sum (nhds (0 : Source 2)) ℂ
          (fun k : Fin (d + 1) ↦ fun z : Source 2 ↦
            remainder j (z 1, F z targetIndex) k * z 0 ^ k.1)
          Finset.univ
      _ = ∑ k : Fin (d + 1),
          ((Germ.ofFunction
              (fun z : Source 2 ↦ remainder j
                (z 1, F z targetIndex) k)
              (hsourceRemainderFunction j k) * sourceX ^ k.1 : Germ 2) :
            FunctionGerm 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        calc
          (((fun z : Source 2 ↦
            remainder j (z 1, F z targetIndex) k * z 0 ^ k.1) :
              Source 2 → ℂ) : FunctionGerm 2) =
              ((fun z : Source 2 ↦ remainder j
                (z 1, F z targetIndex) k) : FunctionGerm 2) *
                ((fun z : Source 2 ↦ z 0 ^ k.1) :
                  FunctionGerm 2) := Filter.Germ.coe_mul _ _
          _ = ((Germ.ofFunction
                (fun z : Source 2 ↦ remainder j
                  (z 1, F z targetIndex) k)
                (hsourceRemainderFunction j k) : Germ 2) :
                  FunctionGerm 2) *
                ((sourceX ^ k.1 : Germ 2) : FunctionGerm 2) := by
              congr 1
          _ = ((Germ.ofFunction
                (fun z : Source 2 ↦ remainder j
                  (z 1, F z targetIndex) k)
                (hsourceRemainderFunction j k) * sourceX ^ k.1 : Germ 2) :
                  FunctionGerm 2) := by
              symm
              exact (analyticGermSubring 2).subtype.map_mul _ _
      _ = ((∑ k : Fin (d + 1),
          Germ.ofFunction
            (fun z : Source 2 ↦ remainder j
              (z 1, F z targetIndex) k)
            (hsourceRemainderFunction j k) * sourceX ^ k.1 : Germ 2) :
            FunctionGerm 2) := by
        symm
        exact map_sum (analyticGermSubring 2).subtype
          (fun k : Fin (d + 1) ↦
            Germ.ofFunction
              (fun z : Source 2 ↦ remainder j
                (z 1, F z targetIndex) k)
              (hsourceRemainderFunction j k) * sourceX ^ k.1)
          Finset.univ
  have hsourceXPow (n : ℕ) :
      ((sourceX ^ n : Germ 2) : FunctionGerm 2) =
        (((fun z : Source 2 ↦ z 0 ^ n) : Source 2 → ℂ) :
          FunctionGerm 2) := by
    rfl
  have hWEvaluation : Polynomial.eval₂ ψ sourceX W = 0 := by
    rw [show W = Germ.parameterMonicPolynomial d coefficient by rfl]
    rw [Germ.parameterMonicPolynomial, Polynomial.eval₂_add,
      Polynomial.eval₂_monomial, Polynomial.eval₂_finsetSum]
    simp only [map_one, one_mul]
    simp only [Polynomial.eval₂_monomial]
    simp_rw [hcoefficientPullback]
    apply Subtype.ext
    calc
      ((sourceX ^ (d + 1) +
          ∑ i : Fin (d + 1), Germ.ofFunction
            (fun z : Source 2 ↦ A (z 1, F z targetIndex) i)
            (hsourceCoefficientFunction i) * sourceX ^ i.1 : Germ 2) :
            FunctionGerm 2) =
          ((sourceX ^ (d + 1) : Germ 2) : FunctionGerm 2) +
            ((∑ i : Fin (d + 1), Germ.ofFunction
              (fun z : Source 2 ↦ A (z 1, F z targetIndex) i)
              (hsourceCoefficientFunction i) * sourceX ^ i.1 : Germ 2) :
              FunctionGerm 2) :=
        (analyticGermSubring 2).subtype.map_add _ _
      _ = (((fun z : Source 2 ↦ z 0 ^ (d + 1)) :
            Source 2 → ℂ) : FunctionGerm 2) +
          ∑ i : Fin (d + 1),
            ((Germ.ofFunction
              (fun z : Source 2 ↦ A (z 1, F z targetIndex) i)
              (hsourceCoefficientFunction i) * sourceX ^ i.1 : Germ 2) :
              FunctionGerm 2) := by
        rw [hsourceXPow]
        exact congrArg
          (fun t : FunctionGerm 2 ↦
            (((fun z : Source 2 ↦ z 0 ^ (d + 1)) :
              Source 2 → ℂ) : FunctionGerm 2) + t)
          (map_sum (analyticGermSubring 2).subtype
            (fun i : Fin (d + 1) ↦ Germ.ofFunction
              (fun z : Source 2 ↦ A (z 1, F z targetIndex) i)
              (hsourceCoefficientFunction i) * sourceX ^ i.1)
            Finset.univ)
      _ = (((fun z : Source 2 ↦ z 0 ^ (d + 1)) :
            Source 2 → ℂ) : FunctionGerm 2) +
          ∑ i : Fin (d + 1),
            (((fun z : Source 2 ↦
              A (z 1, F z targetIndex) i * z 0 ^ i.1) :
                Source 2 → ℂ) : FunctionGerm 2) := by
        apply congrArg
        apply Finset.sum_congr rfl
        intro i hi
        calc
          ((Germ.ofFunction
              (fun z : Source 2 ↦ A (z 1, F z targetIndex) i)
              (hsourceCoefficientFunction i) * sourceX ^ i.1 : Germ 2) :
              FunctionGerm 2) =
            ((Germ.ofFunction
              (fun z : Source 2 ↦ A (z 1, F z targetIndex) i)
              (hsourceCoefficientFunction i) : Germ 2) : FunctionGerm 2) *
              ((sourceX ^ i.1 : Germ 2) : FunctionGerm 2) :=
            (analyticGermSubring 2).subtype.map_mul _ _
          _ = ((fun z : Source 2 ↦ A (z 1, F z targetIndex) i) :
              FunctionGerm 2) *
                (((fun z : Source 2 ↦ z 0 ^ i.1) :
                  Source 2 → ℂ) : FunctionGerm 2) := by
            rw [Germ.coe_ofFunction, hsourceXPow]
          _ = (((fun z : Source 2 ↦
              A (z 1, F z targetIndex) i * z 0 ^ i.1) :
                Source 2 → ℂ) : FunctionGerm 2) :=
            (Filter.Germ.coe_mul _ _).symm
      _ = (((fun z : Source 2 ↦ z 0 ^ (d + 1)) :
            Source 2 → ℂ) : FunctionGerm 2) +
          ((((∑ i : Fin (d + 1), fun z : Source 2 ↦
              A (z 1, F z targetIndex) i * z 0 ^ i.1) :
                Source 2 → ℂ)) : FunctionGerm 2) := by
        congr 1
        symm
        exact Germ.coe_sum (nhds (0 : Source 2)) ℂ
          (fun i : Fin (d + 1) ↦ fun z : Source 2 ↦
            A (z 1, F z targetIndex) i * z 0 ^ i.1) Finset.univ
      _ = (((fun z : Source 2 ↦ z 0 ^ (d + 1)) +
          (∑ i : Fin (d + 1), fun z : Source 2 ↦
            A (z 1, F z targetIndex) i * z 0 ^ i.1) :
              Source 2 → ℂ) : FunctionGerm 2) :=
        (Filter.Germ.coe_add _ _).symm
      _ = (((fun z : Source 2 ↦
          Germ.generalDivisionPolynomialValue (z 0)
            (A (z 1, F z targetIndex))) : Source 2 → ℂ) :
              FunctionGerm 2) := by
        congr 1
        funext z
        simp only [Pi.add_apply, Finset.sum_apply,
          Germ.generalDivisionPolynomialValue]
      _ = 0 := Filter.Germ.coe_eq.mpr hfirst
  have hWRoot : (W.map ψ).IsRoot sourceX := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map]
    exact hWEvaluation
  let r : Germ 2 := Germ.coordinate (0 : Fin 2) ^ (N + 1)
  have hbaseCoordinate :
      ψ (Germ.coordinate (0 : Fin 2)) =
        Germ.coordinate (1 : Fin 2) := by
    rw [show ψ = baseMap.pullbackRingHom by rfl,
      PointedMapGerm.pullback_coordinate]
    rw [show baseMap = PointedMapGerm.ofFunction baseFunction
      hbaseFunction hbaseFunctionZero by rfl]
    apply Subtype.ext
    calc
      (((PointedMapGerm.ofFunction baseFunction hbaseFunction
          hbaseFunctionZero).1.component (0 : Fin 2) : Germ 2) :
          FunctionGerm 2) =
        ((fun z : Source 2 ↦ baseFunction z 0) : FunctionGerm 2) :=
          MapGerm.component_ofFunction baseFunction hbaseFunction 0
      _ = ((Germ.coordinate (1 : Fin 2) : Germ 2) :
          FunctionGerm 2) := by
        apply Filter.Germ.coe_eq.mpr
        apply Filter.Eventually.of_forall
        intro z
        simp [baseFunction, Germ.planePoint]
  have hresultantRelation : ψ r =
      ∑ j : Fin m, sourceMap.1.component j *
        ((q j).map ψ).eval sourceX := by
    calc
      ψ r = Germ.coordinate (1 : Fin 2) ^ (N + 1) := by
        rw [show r = Germ.coordinate (0 : Fin 2) ^ (N + 1) by rfl,
          map_pow, hbaseCoordinate]
      _ = ∑ j : Fin m, sourceMap.1.component j * multiplier j := by
        simpa only [sourceMap] using hpower
      _ = ∑ j : Fin m, sourceMap.1.component j *
          ((q j).map ψ).eval sourceX := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hqEvaluation j]
  let resultant : MvPolynomial (Fin m) (Germ 2) :=
    PolynomialResultant.multivariableResultantEliminant W q r d
  have hresultantZero : MvPolynomial.eval₂ ψ
      (fun j ↦ sourceMap.1.component j) resultant = 0 := by
    exact PolynomialResultant.eval₂_multivariableResultantEliminant_eq_zero
      W q r d hWMonic hqDegree ψ
        (fun j ↦ sourceMap.1.component j) sourceX hWRoot
          hresultantRelation
  have hconstantCoefficient : resultant.coeff 0 = r ^ W.natDegree := by
    have hspecialization :=
      PolynomialResultant.eval₂_zero_multivariableResultantEliminant_eq_pow
        W q r d hWMonic (RingHom.id (Germ 2))
    simpa only [resultant, MvPolynomial.eval₂_zero'_apply,
      MvPolynomial.constantCoeff_eq, RingHom.id_apply] using
      hspecialization
  have hconstantPower : resultant.coeff 0 =
      Germ.coordinate (0 : Fin 2) ^ ((N + 1) * (d + 1)) := by
    rw [hconstantCoefficient, hWDegree]
    change (Germ.coordinate (0 : Fin 2) ^ (N + 1)) ^ (d + 1) = _
    rw [pow_mul]
  have hcoordinatePowerRegular : Germ.IsRegularInFirstCoordinateOfOrder
      (Germ.coordinate (0 : Fin 2) ^ ((N + 1) * (d + 1)))
      ((N + 1) * (d + 1)) := by
    rw [Germ.IsRegularInFirstCoordinateOfOrder]
    change Germ.vanishingOrder
      (Germ.lineRestrictionAlgHom (Germ.firstCoordinateVector 1)
        (Germ.coordinate (0 : Fin 2) ^ ((N + 1) * (d + 1)))) = _
    rw [map_pow, Germ.lineRestrictionAlgHom_apply,
      Germ.lineRestriction_firstCoordinate,
      Germ.vanishingOrder_coordinate_pow]
  have horder : N * (d + 1) + d + 1 = (N + 1) * (d + 1) := by
    ring
  have hresultantRegular : Germ.IsRegularInFirstCoordinateOfOrder
      (resultant.coeff 0) (N * (d + 1) + d + 1) := by
    rw [hconstantPower, horder]
    exact hcoordinatePowerRegular
  obtain ⟨b, hb, hbZero, hbrelation⟩ :=
    Germ.exists_analytic_monicRelation_of_mvPolynomialGermEvaluation
      resultant (N * (d + 1) + d) hresultantRegular
      (fun z : Source 2 ↦ z 1) (fun z ↦ F z targetIndex) F
      hcoordinateOne (hFCoordinate targetIndex) hF rfl (by simp [hFZero])
      hFZero baseMap sourceMap (by rfl) (by rfl) hresultantZero
  let targetDiagonal : Source m → ℂ × Source m := fun value ↦
    (value targetIndex, value)
  have htargetDiagonal : AnalyticAt ℂ targetDiagonal 0 := by
    exact ((ContinuousLinearMap.proj (R := ℂ) targetIndex).analyticAt 0).prod
      (analyticAt_id : AnalyticAt ℂ (fun value : Source m ↦ value) 0)
  have htargetDiagonalZero : targetDiagonal 0 = (0, 0) := rfl
  let B : Source m → Germ.GeneralCoefficientSpace
      (N * (d + 1) + d) := fun value ↦ b (targetDiagonal value)
  have hB : AnalyticAt ℂ B 0 := by
    have hbAt : AnalyticAt ℂ b (targetDiagonal 0) := by
      simpa only [htargetDiagonalZero] using hb
    simpa only [B, Function.comp_def] using
      (AnalyticAt.comp (x := (0 : Source m)) hbAt htargetDiagonal)
  have hBZero : B 0 = 0 := by
    simp only [B, htargetDiagonalZero, hbZero]
  refine ⟨B, hB, hBZero, ?_⟩
  simpa only [B, targetDiagonal] using hbrelation

end Germ

end OnLeConjecture.Analytic
