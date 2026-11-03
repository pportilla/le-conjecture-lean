/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ParametricGeneralDivision
public import OnLeConjecture.Analytic.ImageRing
public import OnLeConjecture.Analytic.PullbackEquivalence

/-!
# Finiteness of monic triangular analytic maps

A monic polynomial in the first source coordinate together with the second
source coordinate defines a finite analytic map germ. Division by the
polynomial after adjoining its value as an auxiliary parameter gives an
explicit finite set of module generators.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Metric
open scoped BigOperators Topology

namespace Germ

/-- Evaluation of a monic polynomial whose lower coefficients are analytic
functions of the second coordinate. -/
@[expose] noncomputable def monicTriangularPolynomialFunction
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ) (z : Source 2) : ℂ :=
  z 0 ^ (d + 1) + ∑ i : Fin (d + 1), A i (z 1) * z 0 ^ i.1

/-- The coefficient vector of the divisor obtained by adjoining the value
of the monic polynomial as a second parameter. -/
@[expose] noncomputable def monicTriangularParameterCoefficients
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ) (w : ℂ × ℂ) :
    Germ.GeneralCoefficientSpace d := fun i ↦
  A i w.1 - if i = 0 then w.2 else 0

theorem generalDivisionPolynomialValue_monicTriangularParameterCoefficients
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ) (x y t : ℂ) :
    Germ.generalDivisionPolynomialValue x
        (Germ.monicTriangularParameterCoefficients d A (y, t)) =
      Germ.monicTriangularPolynomialFunction d A
        ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm (x, y)) - t := by
  have hsum :
      ∑ i : Fin (d + 1),
          (A i y - if i = 0 then t else 0) * x ^ i.1 =
        (∑ i : Fin (d + 1), A i y * x ^ i.1) - t := by
    calc
      ∑ i : Fin (d + 1),
          (A i y - if i = 0 then t else 0) * x ^ i.1 =
          (∑ i : Fin (d + 1), A i y * x ^ i.1) -
            ∑ i : Fin (d + 1),
              (if i = 0 then t else 0) * x ^ i.1 := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [sub_mul]
      _ = (∑ i : Fin (d + 1), A i y * x ^ i.1) - t := by
        simp
  simp only [Germ.generalDivisionPolynomialValue,
    Germ.monicTriangularParameterCoefficients,
    Germ.monicTriangularPolynomialFunction,
    ContinuousLinearEquiv.finTwoArrow_symm_apply]
  rw [hsum]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Analyticity of the parameter dependent coefficient vector. -/
theorem analyticAt_monicTriangularParameterCoefficients
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ)
    (hA : ∀ i, AnalyticAt ℂ (A i) 0) :
    AnalyticAt ℂ
      (Germ.monicTriangularParameterCoefficients d A) (0, 0) := by
  apply AnalyticAt.pi
  intro i
  have hbase : AnalyticAt ℂ (fun w : ℂ × ℂ ↦ A i w.1) (0, 0) :=
    (hA i).comp (x := (0, 0)) analyticAt_fst
  by_cases hi : i = 0
  · subst i
    have hsub := hbase.sub analyticAt_snd
    change AnalyticAt ℂ (fun w : ℂ × ℂ ↦ A 0 w.1 - w.2)
      (0, 0)
    rw [show (fun w : ℂ × ℂ ↦ A 0 w.1 - w.2) =
      (fun w : ℂ × ℂ ↦ A 0 w.1) -
        (fun w : ℂ × ℂ ↦ w.2) by rfl]
    exact hsub
  · simpa only [Germ.monicTriangularParameterCoefficients, hi,
      ↓reduceIte, sub_zero] using hbase

@[simp]
theorem monicTriangularParameterCoefficients_zero
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ)
    (hAZero : ∀ i, A i 0 = 0) :
    Germ.monicTriangularParameterCoefficients d A (0, 0) = 0 := by
  funext i
  simp [Germ.monicTriangularParameterCoefficients, hAZero]

/-- The triangular map whose first component is the monic polynomial and
whose second component is the second source coordinate. -/
@[expose] noncomputable def monicTriangularFunction
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ) (z : Source 2) : Source 2 :=
  (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
    (Germ.monicTriangularPolynomialFunction d A z, z 1)

theorem analyticAt_monicTriangularPolynomialFunction
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ)
    (hA : ∀ i, AnalyticAt ℂ (A i) 0) :
    AnalyticAt ℂ (Germ.monicTriangularPolynomialFunction d A) 0 := by
  have hx : AnalyticAt ℂ (fun z : Source 2 ↦ z 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).analyticAt 0
  have hy : AnalyticAt ℂ (fun z : Source 2 ↦ z 1) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0
  apply (hx.pow (d + 1)).add
  have hterms : ∀ i : Fin (d + 1), AnalyticAt ℂ
      (fun z : Source 2 ↦ A i (z 1) * z 0 ^ i.1) 0 := by
    intro i
    have hAi : AnalyticAt ℂ (fun z : Source 2 ↦ A i (z 1)) 0 := by
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (x := (0 : Source 2)) (hA i) hy)
    exact hAi.mul (hx.pow i.1)
  have hsum := Finset.analyticAt_sum
    (f := fun (i : Fin (d + 1)) (z : Source 2) ↦
      A i (z 1) * z 0 ^ i.1) Finset.univ fun i _ ↦ hterms i
  rw [show (∑ i : Fin (d + 1), fun z : Source 2 ↦
      A i (z 1) * z 0 ^ i.1) =
        fun z : Source 2 ↦ ∑ i : Fin (d + 1),
          A i (z 1) * z 0 ^ i.1 by
    funext z
    simp only [Finset.sum_apply]] at hsum
  exact hsum

theorem analyticAt_monicTriangularFunction
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ)
    (hA : ∀ i, AnalyticAt ℂ (A i) 0) :
    AnalyticAt ℂ (Germ.monicTriangularFunction d A) 0 := by
  have hfirst := Germ.analyticAt_monicTriangularPolynomialFunction d A hA
  have hsecond : AnalyticAt ℂ (fun z : Source 2 ↦ z 1) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · simpa [Germ.monicTriangularFunction] using hfirst
  · simpa [Germ.monicTriangularFunction] using hsecond

@[simp]
theorem monicTriangularFunction_zero
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ)
    (hAZero : ∀ i, A i 0 = 0) :
    Germ.monicTriangularFunction d A 0 = 0 := by
  apply (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).injective
  simp [Germ.monicTriangularFunction,
    Germ.monicTriangularPolynomialFunction, hAZero]

/-- The pointed map germ associated with a monic triangular function. -/
@[expose] noncomputable def monicTriangularMap
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ)
    (hA : ∀ i, AnalyticAt ℂ (A i) 0)
    (hAZero : ∀ i, A i 0 = 0) : PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction (Germ.monicTriangularFunction d A)
    (Germ.analyticAt_monicTriangularFunction d A hA)
    (Germ.monicTriangularFunction_zero d A hAZero)

end Germ

namespace PointedMapGerm

/-- Two analytic map germs are equal when all scalar components are equal. -/
theorem _root_.OnLeConjecture.Analytic.MapGerm.ext_components
    {n m : ℕ} {f g : MapGerm n m}
    (h : ∀ i, f.component i = g.component i) : f = g := by
  rcases f with ⟨f, hf⟩
  rcases g with ⟨g, hg⟩
  induction f using Filter.Germ.inductionOn with
  | _ F =>
    induction g using Filter.Germ.inductionOn with
    | _ G =>
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      have hcoordinate : ∀ i : Fin m, ∀ᶠ z in nhds (0 : Source n),
          F z i = G z i := by
        intro i
        have hi := congrArg Subtype.val (h i)
        change Filter.Germ.map (fun z : Source m ↦ z i)
            (F : FunctionMapGerm n m) =
          Filter.Germ.map (fun z : Source m ↦ z i)
            (G : FunctionMapGerm n m) at hi
        rw [Filter.Germ.map_coe, Filter.Germ.map_coe] at hi
        exact Filter.Germ.coe_eq.mp hi
      have hall := Filter.eventually_all.mpr hcoordinate
      filter_upwards [hall] with z hz
      exact funext hz

/-- Two pointed analytic map germs are equal when all scalar components are
equal. -/
theorem ext_components {n m : ℕ} {f g : PointedMapGerm n m}
    (h : ∀ i, f.1.component i = g.1.component i) : f = g := by
  apply Subtype.ext
  exact MapGerm.ext_components h

/-- Composing a map germ on the target can only decrease its analytic image
ring. -/
theorem imageRing_comp_le {l n m : ℕ}
    (g : PointedMapGerm n m) (f : PointedMapGerm l n) :
    (g.comp f).ImageRing ≤ f.ImageRing := by
  rintro q ⟨r, hr⟩
  refine ⟨g.pullbackRingHom r, ?_⟩
  rw [PointedMapGerm.pullbackRingHom_comp] at hr
  exact hr

/-- Module finiteness over a smaller analytic image ring implies module
finiteness over a larger analytic image ring. -/
theorem isFiniteAtOrigin_of_imageRing_le {n m k : ℕ}
    (f : PointedMapGerm n m) (g : PointedMapGerm n k)
    (hgf : g.ImageRing ≤ f.ImageRing) (hg : g.IsFiniteAtOrigin) :
    f.IsFiniteAtOrigin := by
  let inclusion : g.ImageRing →+* f.ImageRing :=
    Subring.inclusion hgf
  let _ : Algebra g.ImageRing f.ImageRing := inclusion.toAlgebra
  let _ : IsScalarTower g.ImageRing f.ImageRing (Germ n) :=
    IsScalarTower.of_algebraMap_eq fun q ↦ by
      rfl
  let _ : Module.Finite g.ImageRing (Germ n) := hg
  exact Module.Finite.of_restrictScalars_finite
    g.ImageRing f.ImageRing (Germ n)

/-- Finiteness of a target projection implies finiteness of the original
map germ. -/
theorem isFiniteAtOrigin_of_comp {n m k : ℕ}
    (f : PointedMapGerm n m) (g : PointedMapGerm m k)
    (hfinite : (g.comp f).IsFiniteAtOrigin) : f.IsFiniteAtOrigin :=
  PointedMapGerm.isFiniteAtOrigin_of_imageRing_le f (g.comp f)
    (PointedMapGerm.imageRing_comp_le g f) hfinite

/-- Every plane germ is a linear combination of the first coordinate
monomials over the image ring of a monic triangular map. -/
theorem exists_monicTriangular_image_decomposition
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ)
    (hA : ∀ i, AnalyticAt ℂ (A i) 0)
    (hAZero : ∀ i, A i 0 = 0) (b : Germ 2) :
    let f := Germ.monicTriangularMap d A hA hAZero
    ∃ coefficient : Fin (d + 1) → f.ImageRing,
      b = ∑ i : Fin (d + 1),
        (coefficient i : Germ 2) * Germ.coordinate (0 : Fin 2) ^ i.1 := by
  let f := Germ.monicTriangularMap d A hA hAZero
  obtain ⟨B, hB, hb⟩ := Germ.exists_analyticRepresentative_allOrders b
  rcases hB with ⟨p, hp⟩
  let parameterCoefficients : ℂ × ℂ →
      Germ.GeneralCoefficientSpace d :=
    Germ.monicTriangularParameterCoefficients d A
  have hparameter : AnalyticAt ℂ parameterCoefficients (0, 0) :=
    Germ.analyticAt_monicTriangularParameterCoefficients d A hA
  have hparameterZero : parameterCoefficients (0, 0) = 0 :=
    Germ.monicTriangularParameterCoefficients_zero d A hAZero
  obtain ⟨Q, R, hQ, hR, hdivision⟩ :=
    Germ.exists_analytic_generalDivision_withTwoParameters
      p d hp.radius_pos parameterCoefficients hparameter hparameterZero
  let substitution : Source 2 → ℂ × (ℂ × ℂ) := fun z ↦
    (z 0, (z 1, Germ.monicTriangularPolynomialFunction d A z))
  have hfirst : AnalyticAt ℂ (fun z : Source 2 ↦ z 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (0 : Fin 2)).analyticAt 0
  have hsecond : AnalyticAt ℂ (fun z : Source 2 ↦ z 1) 0 :=
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 2 ↦ ℂ) (1 : Fin 2)).analyticAt 0
  have hpolynomial :=
    Germ.analyticAt_monicTriangularPolynomialFunction d A hA
  have hsubstitution : AnalyticAt ℂ substitution 0 :=
    hfirst.prod (hsecond.prod hpolynomial)
  have hsubstitutionZero : substitution 0 = (0, 0) := by
    simp [substitution, Germ.monicTriangularPolynomialFunction, hAZero]
  have hdivisionSubstituted : ∀ᶠ z : Source 2 in nhds 0,
      p.sum (Germ.planePoint (substitution z).1 (substitution z).2.1) =
        Germ.generalDivisionPolynomialValue (substitution z).1
            (parameterCoefficients (substitution z).2) *
              Q (substitution z) +
          ∑ i : Fin (d + 1), (substitution z).1 ^ i.1 *
            R (substitution z).2 i := by
    exact hsubstitution.continuousAt.eventually (by
      simpa only [hsubstitutionZero] using hdivision)
  have hpSum : HasFPowerSeriesAt p.sum p 0 :=
    (p.hasFPowerSeriesOnBall hp.radius_pos).hasFPowerSeriesAt
  have hBsum : B =ᶠ[nhds 0] p.sum := by
    filter_upwards [hp.eventually_hasSum_sub,
      hpSum.eventually_hasSum_sub] with z hzB hzSum
    simpa only [sub_zero] using hzB.unique hzSum
  let targetCoefficientFunction : Fin (d + 1) → Source 2 → ℂ :=
    fun i w ↦ R (w 1, w 0) i
  have htargetCoefficient : ∀ i, AnalyticAt ℂ
      (targetCoefficientFunction i) 0 := by
    intro i
    have hswap : AnalyticAt ℂ
        (fun w : Source 2 ↦ (w 1, w 0)) 0 := hsecond.prod hfirst
    have hRAt : AnalyticAt ℂ R
        (((0 : Source 2) 1, (0 : Source 2) 0)) := by
      simpa using hR
    have hRComp : AnalyticAt ℂ
        (fun w : Source 2 ↦ R (w 1, w 0)) 0 := by
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (x := (0 : Source 2)) hRAt hswap)
    have hcoordinate : AnalyticAt ℂ
        (fun w : Source 2 ↦ R (w 1, w 0) i) 0 := by
      simpa [Function.comp_def] using
        (AnalyticAt.comp (x := (0 : Source 2))
          ((ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin (d + 1) ↦ ℂ) i).analyticAt
              (R (((0 : Source 2) 1, (0 : Source 2) 0)))) hRComp)
    exact hcoordinate
  let targetCoefficient : Fin (d + 1) → Germ 2 := fun i ↦
    Germ.ofFunction (targetCoefficientFunction i) (htargetCoefficient i)
  let coefficient : Fin (d + 1) → f.ImageRing := fun i ↦
    f.pullbackToImageRing (targetCoefficient i)
  let sourceCoefficientFunction : Fin (d + 1) → Source 2 → ℂ :=
    fun i z ↦ R (z 1,
      Germ.monicTriangularPolynomialFunction d A z) i
  have hsourceParameter : AnalyticAt ℂ
      (fun z : Source 2 ↦
        (z 1, Germ.monicTriangularPolynomialFunction d A z)) 0 :=
    hsecond.prod hpolynomial
  have hsourceParameterZero :
      ((0 : Source 2) 1,
        Germ.monicTriangularPolynomialFunction d A (0 : Source 2)) =
      (0, 0) := by
    simp [Germ.monicTriangularPolynomialFunction, hAZero]
  have hsourceCoefficient : ∀ i, AnalyticAt ℂ
      (sourceCoefficientFunction i) 0 := by
    intro i
    have hRComp : AnalyticAt ℂ
        (fun z : Source 2 ↦ R
          (z 1, Germ.monicTriangularPolynomialFunction d A z)) 0 := by
      have hRAt : AnalyticAt ℂ R
          ((0 : Source 2) 1,
            Germ.monicTriangularPolynomialFunction d A (0 : Source 2)) := by
        rw [hsourceParameterZero]
        exact hR
      simpa only [Function.comp_def] using
        (AnalyticAt.comp (x := (0 : Source 2)) hRAt hsourceParameter)
    have hcoordinate : AnalyticAt ℂ
        (fun z : Source 2 ↦ R
          (z 1, Germ.monicTriangularPolynomialFunction d A z) i) 0 := by
      simpa [Function.comp_def] using
        (AnalyticAt.comp (x := (0 : Source 2))
          ((ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin (d + 1) ↦ ℂ) i).analyticAt
              (R ((0 : Source 2) 1,
                Germ.monicTriangularPolynomialFunction d A
                  (0 : Source 2)))) hRComp)
    exact hcoordinate
  let sourceCoefficient : Fin (d + 1) → Germ 2 := fun i ↦
    Germ.ofFunction (sourceCoefficientFunction i) (hsourceCoefficient i)
  have hpullbackCoefficient (i : Fin (d + 1)) :
      f.pullbackRingHom (targetCoefficient i) = sourceCoefficient i := by
    rw [show f = PointedMapGerm.ofFunction
        (Germ.monicTriangularFunction d A)
        (Germ.analyticAt_monicTriangularFunction d A hA)
        (Germ.monicTriangularFunction_zero d A hAZero) by rfl]
    rw [show targetCoefficient i = Germ.ofFunction
        (targetCoefficientFunction i) (htargetCoefficient i) by rfl]
    rw [PointedMapGerm.pullbackRingHom_apply,
      Germ.compPointed_ofFunction]
    rw [show sourceCoefficient i = Germ.ofFunction
        (sourceCoefficientFunction i) (hsourceCoefficient i) by rfl]
    apply Germ.ofFunction_eq_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro z
    simp only [Function.comp_apply, targetCoefficientFunction,
      sourceCoefficientFunction, Germ.monicTriangularFunction]
    have hzero :
        (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
          (Germ.monicTriangularPolynomialFunction d A z, z 1) 0 =
        Germ.monicTriangularPolynomialFunction d A z := by
      simp
    have hone :
        (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
          (Germ.monicTriangularPolynomialFunction d A z, z 1) 1 = z 1 := by
      simp
    rw [hzero, hone]
  have hcoefficient (i : Fin (d + 1)) :
      (coefficient i : Germ 2) = sourceCoefficient i := by
    change f.pullbackRingHom (targetCoefficient i) = sourceCoefficient i
    exact hpullbackCoefficient i
  refine ⟨coefficient, ?_⟩
  rw [hb]
  apply Subtype.ext
  let remainderFunction : Source 2 → ℂ := fun z ↦
    ∑ i : Fin (d + 1),
      sourceCoefficientFunction i z * z 0 ^ i.1
  have hBrem : (B : FunctionGerm 2) =
      (remainderFunction : FunctionGerm 2) := by
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hBsum, hdivisionSubstituted] with z hzB hzDivision
    rw [hzB]
    have hplane : Germ.planePoint (substitution z).1
        (substitution z).2.1 = z := by
      ext i
      fin_cases i <;> simp [Germ.planePoint, substitution]
    rw [hplane] at hzDivision
    have hdivisor : Germ.generalDivisionPolynomialValue
        (substitution z).1 (parameterCoefficients (substitution z).2) = 0 := by
      rw [Germ.generalDivisionPolynomialValue_monicTriangularParameterCoefficients]
      simp only [substitution]
      have hpoint :
          (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm (z 0, z 1) = z := by
        exact (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm_apply_apply z
      rw [hpoint, sub_self]
    rw [hdivisor, zero_mul, zero_add] at hzDivision
    rw [hzDivision]
    simp only [remainderFunction, sourceCoefficientFunction, substitution]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    ((Germ.ofFunction B hp.analyticAt : Germ 2) : FunctionGerm 2) =
        (B : FunctionGerm 2) := rfl
    _ = (remainderFunction : FunctionGerm 2) := hBrem
    _ = (((∑ i : Fin (d + 1),
        sourceCoefficientFunction i *
          fun z : Source 2 ↦ z 0 ^ i.1) : Source 2 → ℂ) :
            FunctionGerm 2) := by
      congr 1
      funext z
      simp only [remainderFunction, Finset.sum_apply, Pi.mul_apply]
    _ = ∑ i : Fin (d + 1),
        ((sourceCoefficientFunction i *
          fun z : Source 2 ↦ z 0 ^ i.1 : Source 2 → ℂ) :
            FunctionGerm 2) :=
      Germ.coe_sum (nhds (0 : Source 2)) ℂ
        (fun i : Fin (d + 1) ↦
          sourceCoefficientFunction i *
            fun z : Source 2 ↦ z 0 ^ i.1) Finset.univ
    _ = ∑ i : Fin (d + 1),
        ((sourceCoefficient i * Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
          FunctionGerm 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        ((sourceCoefficientFunction i *
            fun z : Source 2 ↦ z 0 ^ i.1 : Source 2 → ℂ) :
              FunctionGerm 2) =
            (sourceCoefficientFunction i : FunctionGerm 2) *
              ((fun z : Source 2 ↦ z 0 ^ i.1) : FunctionGerm 2) :=
          Filter.Germ.coe_mul _ _
        _ = ((sourceCoefficient i : Germ 2) : FunctionGerm 2) *
              ((Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
                FunctionGerm 2) := by
          rw [show sourceCoefficient i = Germ.ofFunction
              (sourceCoefficientFunction i) (hsourceCoefficient i) by rfl]
          rfl
        _ = ((sourceCoefficient i *
              Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
            FunctionGerm 2) := by
          exact ((analyticGermSubring 2).subtype.map_mul
            (sourceCoefficient i)
            (Germ.coordinate (0 : Fin 2) ^ i.1)).symm
    _ = ∑ i : Fin (d + 1),
        (((coefficient i : Germ 2) *
          Germ.coordinate (0 : Fin 2) ^ i.1 : Germ 2) :
            FunctionGerm 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoefficient]
    _ = ((∑ i : Fin (d + 1),
        (coefficient i : Germ 2) * Germ.coordinate (0 : Fin 2) ^ i.1 :
          Germ 2) : FunctionGerm 2) := by
      exact (map_sum (analyticGermSubring 2).subtype
        (fun i : Fin (d + 1) ↦
          (coefficient i : Germ 2) *
            Germ.coordinate (0 : Fin 2) ^ i.1) Finset.univ).symm

/-- A monic triangular pointed map germ is finite at the origin. -/
theorem monicTriangularMap_isFiniteAtOrigin
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ)
    (hA : ∀ i, AnalyticAt ℂ (A i) 0)
    (hAZero : ∀ i, A i 0 = 0) :
    (Germ.monicTriangularMap d A hA hAZero).IsFiniteAtOrigin := by
  let f := Germ.monicTriangularMap d A hA hAZero
  let v : Fin (d + 1) → Germ 2 := fun i ↦
    Germ.coordinate (0 : Fin 2) ^ i.1
  have hspan : Submodule.span f.ImageRing (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro b hb
    obtain ⟨coefficient, hdecomposition⟩ :=
      PointedMapGerm.exists_monicTriangular_image_decomposition
        d A hA hAZero b
    rw [hdecomposition]
    apply Submodule.sum_mem
    intro i hi
    have hvi : v i ∈ Submodule.span f.ImageRing (Set.range v) :=
      Submodule.subset_span (Set.mem_range_self i)
    have hsmul := Submodule.smul_mem
      (Submodule.span f.ImageRing (Set.range v)) (coefficient i) hvi
    rw [Algebra.smul_def, Algebra.algebraMap_ofSubring] at hsmul
    change f.ImageRing.subtype (coefficient i) * v i ∈
      Submodule.span f.ImageRing (Set.range v)
    exact hsmul
  refine ⟨?_⟩
  rw [← hspan]
  exact Submodule.fg_span (Set.finite_range v)

/-- The first component of the monic triangular map is its defining
polynomial function. -/
theorem monicTriangularMap_component_zero
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ)
    (hA : ∀ i, AnalyticAt ℂ (A i) 0)
    (hAZero : ∀ i, A i 0 = 0) :
    (Germ.monicTriangularMap d A hA hAZero).1.component 0 =
      Germ.ofFunction (Germ.monicTriangularPolynomialFunction d A)
        (Germ.analyticAt_monicTriangularPolynomialFunction d A hA) := by
  apply Subtype.ext
  change ((MapGerm.ofFunction (Germ.monicTriangularFunction d A)
      (Germ.analyticAt_monicTriangularFunction d A hA)).component 0).1 = _
  rw [MapGerm.component_ofFunction]
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro z
  simp [Germ.monicTriangularFunction]

/-- The second component of the monic triangular map is the second source
coordinate. -/
theorem monicTriangularMap_component_one
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ)
    (hA : ∀ i, AnalyticAt ℂ (A i) 0)
    (hAZero : ∀ i, A i 0 = 0) :
    (Germ.monicTriangularMap d A hA hAZero).1.component 1 =
      Germ.coordinate (1 : Fin 2) := by
  apply Subtype.ext
  change ((MapGerm.ofFunction (Germ.monicTriangularFunction d A)
      (Germ.analyticAt_monicTriangularFunction d A hA)).component 1).1 = _
  rw [MapGerm.component_ofFunction, Germ.coe_coordinate]
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro z
  simp [Germ.monicTriangularFunction]

/-- A pointed plane map with the two monic triangular components is finite
at the origin. -/
theorem isFiniteAtOrigin_of_components_eq_monicTriangular
    (f : PointedMapGerm 2 2)
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ)
    (hA : ∀ i, AnalyticAt ℂ (A i) 0)
    (hAZero : ∀ i, A i 0 = 0)
    (hzero : f.1.component 0 =
      Germ.ofFunction (Germ.monicTriangularPolynomialFunction d A)
        (Germ.analyticAt_monicTriangularPolynomialFunction d A hA))
    (hone : f.1.component 1 = Germ.coordinate (1 : Fin 2)) :
    f.IsFiniteAtOrigin := by
  have hf : f = Germ.monicTriangularMap d A hA hAZero := by
    apply PointedMapGerm.ext_components
    intro i
    fin_cases i
    · simpa using hzero.trans
        (PointedMapGerm.monicTriangularMap_component_zero
          d A hA hAZero).symm
    · simpa using hone.trans
        (PointedMapGerm.monicTriangularMap_component_one
          d A hA hAZero).symm
  rw [hf]
  exact PointedMapGerm.monicTriangularMap_isFiniteAtOrigin
    d A hA hAZero

/-- A map germ is finite when a two dimensional target projection has
monic triangular components. -/
theorem isFiniteAtOrigin_of_targetProjection_monicTriangular
    {m : ℕ} (f : PointedMapGerm 2 m) (g : PointedMapGerm m 2)
    (d : ℕ) (A : Fin (d + 1) → ℂ → ℂ)
    (hA : ∀ i, AnalyticAt ℂ (A i) 0)
    (hAZero : ∀ i, A i 0 = 0)
    (hzero : (g.comp f).1.component 0 =
      Germ.ofFunction (Germ.monicTriangularPolynomialFunction d A)
        (Germ.analyticAt_monicTriangularPolynomialFunction d A hA))
    (hone : (g.comp f).1.component 1 = Germ.coordinate (1 : Fin 2)) :
    f.IsFiniteAtOrigin := by
  apply PointedMapGerm.isFiniteAtOrigin_of_comp f g
  exact PointedMapGerm.isFiniteAtOrigin_of_components_eq_monicTriangular
    (g.comp f) d A hA hAZero hzero hone

end PointedMapGerm

end OnLeConjecture.Analytic
