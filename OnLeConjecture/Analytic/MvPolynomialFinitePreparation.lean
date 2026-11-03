/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RegularFiniteParameterRelation
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Preparation of multivariable polynomial parameters

A multivariable polynomial over the plane analytic germ ring is a finite
parameter expansion in its target variables. If its constant coefficient is
regular in the first plane coordinate, eventual vanishing after analytic
substitution produces a monic relation.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped BigOperators Topology

namespace Germ

/-- A multivariable polynomial expansion with a regular constant coefficient
gives a monic relation after an analytic substitution on which it vanishes. -/
theorem exists_analytic_monicRelation_of_mvPolynomialExpansion
    {m : ℕ} (R : MvPolynomial (Fin m) (Germ 2))
    (coefficientRepresentative : (Fin m →₀ ℕ) → Source 2 → ℂ)
    (hRepresentative : ∀ exponent,
      AnalyticAt ℂ (coefficientRepresentative exponent) 0)
    (hCoefficient : ∀ exponent,
      R.coeff exponent = Germ.ofFunction
        (coefficientRepresentative exponent) (hRepresentative exponent))
    (d : ℕ)
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder
      (R.coeff 0) (d + 1))
    (x y : Source 2 → ℂ) (parameter : Source 2 → Source m)
    (hx : AnalyticAt ℂ x 0) (hy : AnalyticAt ℂ y 0)
    (hparameter : AnalyticAt ℂ parameter 0)
    (hxZero : x 0 = 0) (hyZero : y 0 = 0)
    (hparameterZero : parameter 0 = 0)
    (hvanish : ∀ᶠ z : Source 2 in nhds 0,
      ∑ exponent ∈ R.support,
        (∏ j : Fin m, parameter z j ^ exponent j) *
          coefficientRepresentative exponent
            (Germ.planePoint (x z) (y z)) = 0) :
    ∃ b : ℂ × Source m → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ b (0, 0) ∧
      b (0, 0) = 0 ∧
      ∀ᶠ z : Source 2 in nhds 0,
        Germ.generalDivisionPolynomialValue (x z)
          (b (y z, parameter z)) = 0 := by
  have hconstantNe : R.coeff 0 ≠ 0 := by
    intro hzero
    have hunit := Germ.isUnit_firstCoordinateTailIterate_of_regular hregular
    rw [hzero] at hunit
    simp at hunit
  have hzeroSupport : (0 : Fin m →₀ ℕ) ∈ R.support :=
    MvPolynomial.mem_support_iff.mpr hconstantNe
  let index := ↑R.support
  let distinguished : index := ⟨0, hzeroSupport⟩
  let F : index → Source 2 → ℂ := fun exponent ↦
    coefficientRepresentative exponent.1
  have hF (exponent : index) : AnalyticAt ℂ (F exponent) 0 :=
    hRepresentative exponent.1
  have hregularF : Germ.IsRegularInFirstCoordinateOfOrder
      (Germ.ofFunction (F distinguished) (hF distinguished)) (d + 1) := by
    change Germ.IsRegularInFirstCoordinateOfOrder
      (Germ.ofFunction (coefficientRepresentative 0)
        (hRepresentative 0)) (d + 1)
    rw [← hCoefficient 0]
    exact hregular
  let monomialCoefficient : Source m → index → ℂ :=
    fun value exponent ↦ ∏ j : Fin m, value j ^ exponent.1 j
  have hmonomialCoefficient : AnalyticAt ℂ monomialCoefficient 0 := by
    apply AnalyticAt.pi
    intro exponent
    have hterm (j : Fin m) : AnalyticAt ℂ
        (fun value : Source m ↦ value j ^ exponent.1 j) 0 := by
      exact ((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin m ↦ ℂ) j).analyticAt 0).pow _
    have hprod (s : Finset (Fin m)) : AnalyticAt ℂ
        (fun value : Source m ↦ ∏ j ∈ s, value j ^ exponent.1 j) 0 := by
      induction s using Finset.induction_on with
      | empty => simpa using
          (analyticAt_const : AnalyticAt ℂ
            (fun _ : Source m ↦ (1 : ℂ)) 0)
      | @insert j s hj hs =>
          simp only [Finset.prod_insert, hj, not_false_eq_true]
          exact (hterm j).mul hs
    exact hprod Finset.univ
  have hmonomialCoefficientZero (exponent : index) :
      monomialCoefficient 0 exponent =
        if exponent = distinguished then 1 else 0 := by
    by_cases hexponent : exponent = distinguished
    · subst exponent
      simp [monomialCoefficient, distinguished]
    · rw [if_neg hexponent]
      have hvalue : exponent.1 ≠ 0 := by
        intro hzero
        apply hexponent
        apply Subtype.ext
        exact hzero
      obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hvalue
      change ∏ k : Fin m, (0 : ℂ) ^ exponent.1 k = 0
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact zero_pow hj
  have hvanishSubtype : ∀ᶠ z : Source 2 in nhds 0,
      ∑ exponent : index,
        monomialCoefficient (parameter z) exponent *
          F exponent (Germ.planePoint (x z) (y z)) = 0 := by
    filter_upwards [hvanish] with z hz
    change ∑ exponent : ↑R.support,
      (∏ j : Fin m, parameter z j ^ exponent.1 j) *
        coefficientRepresentative exponent.1
          (Germ.planePoint (x z) (y z)) = 0
    calc
      ∑ exponent : ↑R.support,
          (∏ j : Fin m, parameter z j ^ exponent.1 j) *
            coefficientRepresentative exponent.1
              (Germ.planePoint (x z) (y z)) =
        ∑ exponent ∈ R.support,
          (∏ j : Fin m, parameter z j ^ exponent j) *
            coefficientRepresentative exponent
              (Germ.planePoint (x z) (y z)) := by
          symm
          exact Finset.sum_subtype R.support (fun _ ↦ Iff.rfl) _
      _ = 0 := hz
  exact Germ.exists_analytic_monicRelation_of_regularFiniteExpansion
    F hF d distinguished hregularF monomialCoefficient
      hmonomialCoefficient hmonomialCoefficientZero
      x y parameter hx hy hparameter hxZero hyZero hparameterZero
      hvanishSubtype

/-- A germ level multivariable polynomial identity gives a monic relation
after analytic representatives are substituted into its coefficients and
variables. -/
theorem exists_analytic_monicRelation_of_mvPolynomialGermEvaluation
    {m : ℕ} (R : MvPolynomial (Fin m) (Germ 2))
    (d : ℕ)
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder
      (R.coeff 0) (d + 1))
    (x y : Source 2 → ℂ) (parameter : Source 2 → Source m)
    (hx : AnalyticAt ℂ x 0) (hy : AnalyticAt ℂ y 0)
    (hparameter : AnalyticAt ℂ parameter 0)
    (hxZero : x 0 = 0) (hyZero : y 0 = 0)
    (hparameterZero : parameter 0 = 0)
    (planeMap : PointedMapGerm 2 2)
    (targetMap : PointedMapGerm 2 m)
    (hplaneMap : planeMap = PointedMapGerm.ofFunction
      (fun z ↦ Germ.planePoint (x z) (y z))
      (by
        have hpair : AnalyticAt ℂ (fun z ↦ (x z, y z)) 0 := hx.prod hy
        simpa only [Function.comp_def,
          Germ.generalPlanePointContinuousLinearMap_apply] using
          (AnalyticAt.comp (x := (0 : Source 2))
            (Germ.generalPlanePointContinuousLinearMap.analyticAt
              (x 0, y 0)) hpair))
      (by simp [hxZero, hyZero, Germ.planePoint]))
    (htargetMap : targetMap =
      PointedMapGerm.ofFunction parameter hparameter hparameterZero)
    (hzero : MvPolynomial.eval₂ planeMap.pullbackRingHom
      (fun j ↦ targetMap.1.component j) R = 0) :
    ∃ b : ℂ × Source m → Germ.GeneralCoefficientSpace d,
      AnalyticAt ℂ b (0, 0) ∧
      b (0, 0) = 0 ∧
      ∀ᶠ z : Source 2 in nhds 0,
        Germ.generalDivisionPolynomialValue (x z)
          (b (y z, parameter z)) = 0 := by
  choose coefficientRepresentative hRepresentative hCoefficient using
    fun exponent : Fin m →₀ ℕ ↦
      Germ.exists_analyticRepresentative_allOrders (R.coeff exponent)
  apply Germ.exists_analytic_monicRelation_of_mvPolynomialExpansion
    R coefficientRepresentative hRepresentative hCoefficient d hregular
      x y parameter hx hy hparameter hxZero hyZero hparameterZero
  have hcoefficientPullback (exponent : Fin m →₀ ℕ) :
      planeMap.pullbackRingHom (R.coeff exponent) =
        Germ.ofFunction
          (fun z ↦ coefficientRepresentative exponent
            (Germ.planePoint (x z) (y z)))
          (by
            have hpair : AnalyticAt ℂ (fun z ↦ (x z, y z)) 0 :=
              hx.prod hy
            have hplane : AnalyticAt ℂ
                (fun z ↦ Germ.planePoint (x z) (y z)) 0 := by
              simpa only [Function.comp_def,
                Germ.generalPlanePointContinuousLinearMap_apply] using
                (AnalyticAt.comp (x := (0 : Source 2))
                  (Germ.generalPlanePointContinuousLinearMap.analyticAt
                    (x 0, y 0)) hpair)
            have hcoefficientAt : AnalyticAt ℂ
                (coefficientRepresentative exponent)
                (Germ.planePoint (x 0) (y 0)) := by
              simpa [hxZero, hyZero, Germ.planePoint] using
                hRepresentative exponent
            exact AnalyticAt.comp (x := (0 : Source 2))
              hcoefficientAt hplane) := by
    rw [hplaneMap, hCoefficient exponent,
      PointedMapGerm.pullbackRingHom_apply,
      Germ.compPointed_ofFunction]
    apply Subtype.ext
    rfl
  have hparameterCoordinate (j : Fin m) :
      AnalyticAt ℂ (fun z ↦ parameter z j) 0 := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (AnalyticAt.comp (x := (0 : Source 2))
        ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt
          (parameter 0)) hparameter)
  have hparameterComponent (j : Fin m) :
      targetMap.1.component j = Germ.ofFunction
        (fun z ↦ parameter z j) (hparameterCoordinate j) := by
    rw [htargetMap]
    apply Subtype.ext
    exact MapGerm.component_ofFunction parameter hparameter j
  rw [MvPolynomial.eval₂_eq'] at hzero
  apply Filter.Germ.coe_eq.mp
  have hparameterPower (exponent : Fin m →₀ ℕ) (j : Fin m) :
      (((fun z : Source 2 ↦ parameter z j ^ exponent j) :
          Source 2 → ℂ) : FunctionGerm 2) =
        ((targetMap.1.component j ^ exponent j : Germ 2) :
          FunctionGerm 2) := by
    calc
      (((fun z : Source 2 ↦ parameter z j ^ exponent j) :
          Source 2 → ℂ) : FunctionGerm 2) =
          ((((fun z : Source 2 ↦ parameter z j) ^ exponent j) :
            Source 2 → ℂ) : FunctionGerm 2) := by
        congr 1
      _ =
          ((fun z : Source 2 ↦ parameter z j) : FunctionGerm 2) ^
            exponent j := Filter.Germ.coe_pow _ _
      _ = ((targetMap.1.component j : Germ 2) : FunctionGerm 2) ^
          exponent j := by
        congr 1
        calc
          ((fun z : Source 2 ↦ parameter z j) : FunctionGerm 2) =
              ((Germ.ofFunction (fun z ↦ parameter z j)
                (hparameterCoordinate j) : Germ 2) : FunctionGerm 2) := rfl
          _ = ((targetMap.1.component j : Germ 2) : FunctionGerm 2) := by
            rw [hparameterComponent]
      _ = ((targetMap.1.component j ^ exponent j : Germ 2) :
            FunctionGerm 2) := by
        symm
        exact (analyticGermSubring 2).subtype.map_pow
          (targetMap.1.component j) (exponent j)
  have hmonomial (exponent : Fin m →₀ ℕ) :
      (((fun z : Source 2 ↦
          ∏ j : Fin m, parameter z j ^ exponent j) :
          Source 2 → ℂ) : FunctionGerm 2) =
        ((∏ j : Fin m, targetMap.1.component j ^ exponent j : Germ 2) :
          FunctionGerm 2) := by
    calc
      (((fun z : Source 2 ↦
          ∏ j : Fin m, parameter z j ^ exponent j) :
          Source 2 → ℂ) : FunctionGerm 2) =
          (((∏ j : Fin m,
            (fun z : Source 2 ↦ parameter z j ^ exponent j)) :
              Source 2 → ℂ) : FunctionGerm 2) := by
        congr 1
        funext z
        simp only [Finset.prod_apply]
      _ =
          ∏ j : Fin m,
            (((fun z : Source 2 ↦ parameter z j ^ exponent j) :
              Source 2 → ℂ) : FunctionGerm 2) := by
        exact map_prod
          (Filter.Germ.coeRingHom (nhds (0 : Source 2)))
          (fun j : Fin m ↦
            (fun z : Source 2 ↦ parameter z j ^ exponent j)) Finset.univ
      _ = ∏ j : Fin m,
          ((targetMap.1.component j ^ exponent j : Germ 2) :
            FunctionGerm 2) := by
        apply Finset.prod_congr rfl
        intro j hj
        exact hparameterPower exponent j
      _ = ((∏ j : Fin m,
          targetMap.1.component j ^ exponent j : Germ 2) :
            FunctionGerm 2) := by
        symm
        exact map_prod (analyticGermSubring 2).subtype
          (fun j : Fin m ↦ targetMap.1.component j ^ exponent j)
          Finset.univ
  have hcoefficientFunction (exponent : Fin m →₀ ℕ) :
      ((coefficientRepresentative exponent ∘
          fun z ↦ Germ.planePoint (x z) (y z) : Source 2 → ℂ) :
          FunctionGerm 2) =
        ((planeMap.pullbackRingHom (R.coeff exponent) : Germ 2) :
          FunctionGerm 2) := by
    calc
      ((coefficientRepresentative exponent ∘
          fun z ↦ Germ.planePoint (x z) (y z) : Source 2 → ℂ) :
          FunctionGerm 2) =
          ((Germ.ofFunction
            (fun z ↦ coefficientRepresentative exponent
              (Germ.planePoint (x z) (y z)))
            (by
              have hpair : AnalyticAt ℂ (fun z ↦ (x z, y z)) 0 :=
                hx.prod hy
              have hplane : AnalyticAt ℂ
                  (fun z ↦ Germ.planePoint (x z) (y z)) 0 := by
                simpa only [Function.comp_def,
                  Germ.generalPlanePointContinuousLinearMap_apply] using
                  (AnalyticAt.comp (x := (0 : Source 2))
                    (Germ.generalPlanePointContinuousLinearMap.analyticAt
                      (x 0, y 0)) hpair)
              have hcoefficientAt : AnalyticAt ℂ
                  (coefficientRepresentative exponent)
                  (Germ.planePoint (x 0) (y 0)) := by
                simpa [hxZero, hyZero, Germ.planePoint] using
                  hRepresentative exponent
              exact AnalyticAt.comp (x := (0 : Source 2))
                hcoefficientAt hplane) : Germ 2) : FunctionGerm 2) := by
            rfl
      _ = ((planeMap.pullbackRingHom (R.coeff exponent) : Germ 2) :
            FunctionGerm 2) := by
          rw [hcoefficientPullback]
  calc
    (((fun z : Source 2 ↦
        ∑ exponent ∈ R.support,
          (∏ j : Fin m, parameter z j ^ exponent j) *
            coefficientRepresentative exponent
              (Germ.planePoint (x z) (y z))) : Source 2 → ℂ) :
          FunctionGerm 2) =
        ((((∑ exponent ∈ R.support,
          fun z : Source 2 ↦
            (∏ j : Fin m, parameter z j ^ exponent j) *
              coefficientRepresentative exponent
                (Germ.planePoint (x z) (y z))) :
            Source 2 → ℂ)) : FunctionGerm 2) := by
      congr 1
      funext z
      simp only [Finset.sum_apply]
    _ =
        ∑ exponent ∈ R.support,
          (((fun z : Source 2 ↦
            (∏ j : Fin m, parameter z j ^ exponent j) *
              coefficientRepresentative exponent
                (Germ.planePoint (x z) (y z))) : Source 2 → ℂ) :
            FunctionGerm 2) := by
      exact map_sum
        (Filter.Germ.coeAddHom (nhds (0 : Source 2)))
        (fun exponent : Fin m →₀ ℕ ↦
          fun z : Source 2 ↦
            (∏ j : Fin m, parameter z j ^ exponent j) *
              coefficientRepresentative exponent
                (Germ.planePoint (x z) (y z))) R.support
    _ = ∑ exponent ∈ R.support,
        (((∏ j : Fin m, targetMap.1.component j ^ exponent j) *
          planeMap.pullbackRingHom (R.coeff exponent) : Germ 2) :
          FunctionGerm 2) := by
      apply Finset.sum_congr rfl
      intro exponent hexponent
      calc
        (((fun z : Source 2 ↦
            (∏ j : Fin m, parameter z j ^ exponent j) *
              coefficientRepresentative exponent
                (Germ.planePoint (x z) (y z))) : Source 2 → ℂ) :
              FunctionGerm 2) =
            (((fun z : Source 2 ↦
              ∏ j : Fin m, parameter z j ^ exponent j) :
                Source 2 → ℂ) : FunctionGerm 2) *
              ((coefficientRepresentative exponent ∘
                fun z ↦ Germ.planePoint (x z) (y z) :
                  Source 2 → ℂ) : FunctionGerm 2) := by
            exact Filter.Germ.coe_mul _ _
        _ = ((∏ j : Fin m,
              targetMap.1.component j ^ exponent j : Germ 2) :
                FunctionGerm 2) *
              ((planeMap.pullbackRingHom (R.coeff exponent) : Germ 2) :
                FunctionGerm 2) := by
            rw [hmonomial exponent, hcoefficientFunction exponent]
        _ = (((∏ j : Fin m,
              targetMap.1.component j ^ exponent j) *
                planeMap.pullbackRingHom (R.coeff exponent) : Germ 2) :
                FunctionGerm 2) := by
            symm
            exact (analyticGermSubring 2).subtype.map_mul
              (∏ j : Fin m, targetMap.1.component j ^ exponent j)
              (planeMap.pullbackRingHom (R.coeff exponent))
    _ = ((∑ exponent ∈ R.support,
        (∏ j : Fin m, targetMap.1.component j ^ exponent j) *
          planeMap.pullbackRingHom (R.coeff exponent) : Germ 2) :
          FunctionGerm 2) := by
      symm
      exact map_sum (analyticGermSubring 2).subtype
        (fun exponent : Fin m →₀ ℕ ↦
          (∏ j : Fin m, targetMap.1.component j ^ exponent j) *
            planeMap.pullbackRingHom (R.coeff exponent)) R.support
    _ = ((0 : Germ 2) : FunctionGerm 2) := by
      apply congrArg (fun q : Germ 2 ↦ (q : FunctionGerm 2))
      simpa only [mul_comm] using hzero
    _ = 0 := rfl

end Germ

end OnLeConjecture.Analytic
