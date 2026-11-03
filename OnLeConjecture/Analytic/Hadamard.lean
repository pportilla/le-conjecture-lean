/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Jet
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Hadamard factorization for complex analytic germs

This file proves a factorization of an analytic function through its argument
and identifies the ideal of germs with zero first jet with the square of the
maximal ideal.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

/-- An analytic function near the origin is its value at the origin plus the
value of an analytic family of linear maps on its argument. -/
theorem AnalyticAt.exists_eventuallyEq_add_apply {n : ℕ}
    {f : Source n → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ A : Source n → (Source n →L[ℂ] ℂ),
      AnalyticAt ℂ A 0 ∧ A 0 = fderiv ℂ f 0 ∧
        f =ᶠ[nhds 0] fun z ↦ f 0 + A z z := by
  rcases hf with ⟨p, hp⟩
  let A : Source n → (Source n →L[ℂ] ℂ) := p.shift.sum
  have hp_radius : 0 < p.radius := hp.radius_pos
  have hA_ball : HasFPowerSeriesOnBall A p.shift 0 p.shift.radius := by
    exact p.shift.hasFPowerSeriesOnBall (by simpa using hp_radius)
  have hA : HasFPowerSeriesAt A p.shift 0 :=
    hA_ball.hasFPowerSeriesAt
  have hp_recover : (p.shift).unshift (f 0) = p := by
    ext k v
    cases k with
    | zero =>
        simpa only [FormalMultilinearSeries.unshift,
          continuousMultilinearCurryFin0_symm_apply_apply] using
            (hp.coeff_zero v).symm
    | succ k =>
        simp only [FormalMultilinearSeries.unshift,
          FormalMultilinearSeries.shift]
        have h := LinearIsometryEquiv.symm_apply_apply
          (continuousMultilinearCurryRightEquiv' ℂ k (Source n) ℂ) (p (k + 1))
        exact congrArg (fun q ↦ q v) h
  have hfactor : HasFPowerSeriesAt
      (fun z : Source n ↦ f 0 + A z z) p 0 := by
    have h := hA_ball.unshift (z := f 0)
    rw [hp_recover] at h
    simpa using h.hasFPowerSeriesAt
  have hA_zero : A 0 = fderiv ℂ f 0 := by
    rw [hp.fderiv_eq]
    have hcoeff := hA.coeff_zero (fun i : Fin 0 ↦ nomatch i)
    rw [← hcoeff]
    apply ContinuousLinearMap.ext
    intro z
    simp [FormalMultilinearSeries.shift, Fin.snoc_zero,
      continuousMultilinearCurryFin1_apply,
      ContinuousMultilinearMap.curryRight_apply]
  refine ⟨A, hA.analyticAt, hA_zero, ?_⟩
  filter_upwards [hp.eventually_hasSum_sub,
    hfactor.eventually_hasSum_sub] with z hzf hzfactor
  exact hzf.unique hzfactor

namespace Germ

/-- An analytic germ with zero value and zero differential belongs to the
square of the maximal ideal. -/
theorem firstOrderIdeal_le_maximalIdeal_sq (n : ℕ) :
    Germ.firstOrderIdeal n ≤ Germ.maximalIdeal n ^ 2 := by
  intro g hg
  rw [Germ.mem_firstOrderIdeal_iff] at hg
  rcases g with ⟨g, hgan⟩
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hgan
      obtain ⟨hg0, hgd⟩ := hg
      have hf0 : f 0 = 0 := by
        change Filter.Germ.value (f : FunctionGerm n) = 0 at hg0
        simpa only [Filter.Germ.value_ofFun] using hg0
      have hdf : fderiv ℂ f 0 = 0 := by
        exact hgd
      rcases AnalyticAt.exists_eventuallyEq_add_apply hgan with
        ⟨A, hA, hA_zero, hfactor⟩
      let b : Module.Basis (Fin n) ℂ (Source n) := Pi.basisFun ℂ (Fin n)
      have hcoordinate (i : Fin n) :
          AnalyticAt ℂ (fun z : Source n ↦ z i) 0 :=
        (ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0
      let coordinate (i : Fin n) : Germ n :=
        Germ.ofFunction (fun z : Source n ↦ z i) (hcoordinate i)
      have hcoefficient (i : Fin n) :
          AnalyticAt ℂ (fun z : Source n ↦ A z (b i)) 0 := by
        exact ((ContinuousLinearMap.apply ℂ ℂ (b i)).analyticAt (A 0)).comp hA
      let coefficient (i : Fin n) : Germ n :=
        Germ.ofFunction (fun z : Source n ↦ A z (b i)) (hcoefficient i)
      have hcoefficient_mem (i : Fin n) :
          coefficient i ∈ Germ.maximalIdeal n := by
        rw [Germ.mem_maximalIdeal_iff]
        change A 0 (b i) = 0
        rw [hA_zero, hdf]
        rfl
      have hcoordinate_mem (i : Fin n) :
          coordinate i ∈ Germ.maximalIdeal n := by
        rw [Germ.mem_maximalIdeal_iff]
        change (0 : Source n) i = 0
        rfl
      have heq :
          (⟨(f : FunctionGerm n),
            (mem_analyticGermSubring.mpr
              ((isAnalyticGerm_ofFun f).mpr hgan))⟩ : Germ n) =
            ∑ i, coordinate i * coefficient i := by
        have hfun : (f : FunctionGerm n) =
            ((fun z : Source n ↦ ∑ i, z i * A z (b i)) : FunctionGerm n) := by
          apply Filter.Germ.coe_eq.mpr
          filter_upwards [hfactor] with z hz
          rw [hz, hf0, zero_add]
          calc
            A z z = A z (∑ i, z i • b i) := by
              congr 1
              simpa only [b, Pi.basisFun_repr] using (b.sum_repr z).symm
            _ = ∑ i, z i * A z (b i) := by
              simp only [map_sum, map_smul, smul_eq_mul]
        apply Subtype.ext
        calc
          ((⟨(f : FunctionGerm n),
            (mem_analyticGermSubring.mpr
              ((isAnalyticGerm_ofFun f).mpr hgan))⟩ : Germ n) :
              FunctionGerm n) = (f : FunctionGerm n) := rfl
          _ = ((fun z : Source n ↦ ∑ i, z i * A z (b i)) :
              FunctionGerm n) := hfun
          _ = ((∑ i, coordinate i * coefficient i : Germ n) :
              FunctionGerm n) := by
                have hsum (s : Finset (Fin n)) :
                    ((fun z : Source n ↦ ∑ i ∈ s,
                      z i * A z (b i)) : FunctionGerm n) =
                        ∑ i ∈ s,
                          ((fun z : Source n ↦ z i * A z (b i)) :
                            FunctionGerm n) := by
                  induction s using Finset.induction_on with
                  | empty =>
                      change (((fun _ : Source n ↦ (0 : ℂ)) :
                        FunctionGerm n)) = 0
                      exact Filter.Germ.coe_zero
                  | @insert i s his ih =>
                      simp only [Finset.sum_insert his]
                      rw [← ih]
                      exact Filter.Germ.coe_add
                        (fun z : Source n ↦ z i * A z (b i))
                        (fun z : Source n ↦ ∑ j ∈ s, z j * A z (b j))
                rw [hsum Finset.univ]
                calc
                  ∑ i, ((fun z : Source n ↦ z i * A z (b i)) :
                      FunctionGerm n) =
                      ∑ i, (((coordinate i * coefficient i : Germ n) :
                        FunctionGerm n)) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    have hpoint :
                        (fun z : Source n ↦ z i * A z (b i)) =
                          (fun z : Source n ↦ z i) *
                            (fun z : Source n ↦ A z (b i)) := by
                      funext z
                      rfl
                    rw [hpoint]
                    calc
                      (((fun z : Source n ↦ z i) *
                        (fun z : Source n ↦ A z (b i))) :
                          FunctionGerm n) =
                          ((fun z : Source n ↦ z i) : FunctionGerm n) *
                            ((fun z : Source n ↦ A z (b i)) :
                              FunctionGerm n) :=
                        Filter.Germ.coe_mul
                        (l := nhds (0 : Source n))
                        (fun z : Source n ↦ z i)
                        (fun z : Source n ↦ A z (b i))
                      _ = ((coordinate i : Germ n) : FunctionGerm n) *
                          ((coefficient i : Germ n) : FunctionGerm n) := by
                        simp only [coordinate, coefficient,
                          Germ.coe_ofFunction]
                      _ = (((coordinate i * coefficient i : Germ n) :
                          FunctionGerm n)) := by
                        exact ((analyticGermSubring n).subtype.map_mul
                          (coordinate i) (coefficient i)).symm
                  _ = ((∑ i, coordinate i * coefficient i : Germ n) :
                      FunctionGerm n) := by
                    exact (map_sum (analyticGermSubring n).subtype
                      (fun i ↦ coordinate i * coefficient i)
                      Finset.univ).symm
      rw [heq, pow_two]
      exact Submodule.sum_mem _ fun i _ ↦
        Ideal.mul_mem_mul (hcoordinate_mem i) (hcoefficient_mem i)

/-- The square of the maximal ideal is the ideal of analytic germs whose
value and differential vanish at the origin. -/
theorem firstOrderIdeal_eq_maximalIdeal_sq (n : ℕ) :
    Germ.firstOrderIdeal n = Germ.maximalIdeal n ^ 2 :=
  le_antisymm (firstOrderIdeal_le_maximalIdeal_sq n)
    (Germ.maximalIdeal_sq_le_firstOrderIdeal n)

end Germ

/-- A pointed analytic map germ has zero differential exactly when its
coordinate ideal is contained in the square of the source maximal ideal. -/
theorem PointedMapGerm.differential_eq_zero_iff_coordinateIdeal_le_sq
    {n m : ℕ} (f : PointedMapGerm n m) :
    f.differential = 0 ↔
      f.1.coordinateIdeal ≤ Germ.maximalIdeal n ^ 2 := by
  rw [PointedMapGerm.differential_eq_zero_iff_coordinateIdeal_le_firstOrderIdeal]
  rw [Germ.firstOrderIdeal_eq_maximalIdeal_sq]

end OnLeConjecture.Analytic
