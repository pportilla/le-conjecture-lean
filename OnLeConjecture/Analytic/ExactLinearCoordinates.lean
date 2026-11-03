/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LinearCoordinates
public import OnLeConjecture.Analytic.PolynomialJets

/-!
# Linear coordinates preserving the order of a plane germ

The first nonzero homogeneous jet of a plane analytic germ is nonzero on
some complex line. Choosing that line as the first coordinate axis makes the
germ regular in the first coordinate with order equal to its maximal ideal
order.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- A polynomial in the `d`th power of the variable ideal but not in its
next power has a nonzero homogeneous component of degree `d`. -/
theorem homogeneousComponent_ne_zero_of_mem_idealOfVars_pow_not_mem_succ
    {p : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hd : p ∈ MvPolynomial.idealOfVars (Fin 2) ℂ ^ d)
    (hnext : p ∉ MvPolynomial.idealOfVars (Fin 2) ℂ ^ (d + 1)) :
    MvPolynomial.homogeneousComponent d p ≠ 0 := by
  rw [MvPolynomial.mem_pow_idealOfVars_iff'] at hd hnext
  push Not at hnext
  obtain ⟨a, haDegree, haCoeff⟩ := hnext
  have hda : d ≤ a.degree := by
    by_contra h
    exact haCoeff (hd a (Nat.lt_of_not_ge h))
  have had : a.degree ≤ d := Nat.lt_succ_iff.mp haDegree
  have haEq : a.degree = d := Nat.le_antisymm had hda
  intro hzero
  have hcoeff := congrArg (MvPolynomial.coeff a) hzero
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos haEq,
    MvPolynomial.coeff_zero] at hcoeff
  exact haCoeff hcoeff

/-- A nonzero homogeneous polynomial of positive degree in two complex
variables is nonzero at some nonzero vector. -/
theorem exists_nonzero_direction_eval_ne_zero
    {p : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hp : p.IsHomogeneous d) (hpzero : p ≠ 0) (hd : 0 < d) :
    ∃ v : Source 2, v ≠ 0 ∧ MvPolynomial.eval v p ≠ 0 := by
  have hexists : ∃ v : Source 2, MvPolynomial.eval v p ≠ 0 := by
    by_contra h
    push Not at h
    exact hpzero (hp.eq_zero_of_forall_eval_eq_zero h)
  obtain ⟨v, hv⟩ := hexists
  refine ⟨v, ?_, hv⟩
  intro hvzero
  subst v
  have heval : MvPolynomial.eval (0 : Source 2) p = 0 := by
    rw [MvPolynomial.eval_zero]
    change MvPolynomial.coeff 0 p = 0
    by_contra hcoefficient
    have hdegree := hp hcoefficient
    simpa using (hd.ne' hdegree.symm)
  exact hv heval

/-- If a plane germ has maximal ideal order exactly `d`, an invertible
linear source change makes it regular of order `d` in the first coordinate. -/
theorem exists_linear_equiv_regularInFirstCoordinateOfOrder
    {f : Germ 2} {d : ℕ}
    (hfd : f ∈ Germ.maximalIdeal 2 ^ d)
    (hnext : f ∉ Germ.maximalIdeal 2 ^ (d + 1)) :
    ∃ e : PointedEquivGerm 2,
      IsRegularInFirstCoordinateOfOrder
        (e.forward.pullbackRingHom f) d := by
  by_cases hdzero : d = 0
  · subst d
    have hfValue : Germ.valueRingHom 2 f ≠ 0 := by
      simpa [Germ.mem_maximalIdeal_iff] using hnext
    have hfUnit : IsUnit f := Germ.isUnit_of_valueRingHom_ne_zero hfValue
    let e : PointedEquivGerm 2 :=
      pointedEquivGermOfContinuousLinearEquiv
        (ContinuousLinearEquiv.refl ℂ (Source 2))
    refine ⟨e, ?_⟩
    rw [IsRegularInFirstCoordinateOfOrder]
    change vanishingOrder
      (lineRestriction (firstCoordinateVector 1)
        (e.forward.pullbackRingHom f)) = (0 : ℕ∞)
    rw [vanishingOrder_eq_zero_iff_isUnit]
    exact (hfUnit.map e.forward.pullbackRingHom).map
      (lineRestriction (firstCoordinateVector 1))
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hdzero
    obtain ⟨p, hremainder⟩ :=
      Germ.exists_coordinatePolynomial_mod_maximalIdeal_pow
        2 (d + 1) f
    have hremainderD :
        f - Germ.coordinatePolynomialAlgHom 2 p ∈
          Germ.maximalIdeal 2 ^ d :=
      Ideal.pow_le_pow_right (Nat.le_succ d) hremainder
    have hpD : Germ.coordinatePolynomialAlgHom 2 p ∈
        Germ.maximalIdeal 2 ^ d := by
      have hsub := (Germ.maximalIdeal 2 ^ d).sub_mem hfd hremainderD
      simpa only [sub_sub_cancel] using hsub
    have hpNext : Germ.coordinatePolynomialAlgHom 2 p ∉
        Germ.maximalIdeal 2 ^ (d + 1) := by
      intro hp
      apply hnext
      have hadd := (Germ.maximalIdeal 2 ^ (d + 1)).add_mem
        hremainder hp
      simpa only [sub_add_cancel] using hadd
    have hpPolynomialD :
        p ∈ MvPolynomial.idealOfVars (Fin 2) ℂ ^ d :=
      Germ.mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mpr
        hpD
    have hpPolynomialNext :
        p ∉ MvPolynomial.idealOfVars (Fin 2) ℂ ^ (d + 1) := by
      intro hp
      exact hpNext
        (Germ.mem_idealOfVars_pow_iff_coordinatePolynomial_mem_maximalIdeal_pow.mp
          hp)
    let initial := MvPolynomial.homogeneousComponent d p
    have hinitialHomogeneous : initial.IsHomogeneous d :=
      MvPolynomial.homogeneousComponent_isHomogeneous d p
    have hinitialZero : initial ≠ 0 :=
      Germ.homogeneousComponent_ne_zero_of_mem_idealOfVars_pow_not_mem_succ
        hpPolynomialD hpPolynomialNext
    obtain ⟨v, hvzero, hveval⟩ :=
      Germ.exists_nonzero_direction_eval_ne_zero
        hinitialHomogeneous hinitialZero hdpos
    have hlineRemainder :
        Germ.lineRestriction v
            (f - Germ.coordinatePolynomialAlgHom 2 p) ∈
          Germ.maximalIdeal 1 ^ (d + 1) :=
      Germ.lineRestriction_mem_maximalIdeal_pow v hremainder
    have hlineRemainderCoeff :
        PowerSeries.coeff d
            (Germ.radialTaylorAlgHom 2
              (f - Germ.coordinatePolynomialAlgHom 2 p) v) = 0 := by
      change PowerSeries.coeff d
          (Germ.oneVariableTaylorSeries
            (Germ.lineRestriction v
              (f - Germ.coordinatePolynomialAlgHom 2 p))) = 0
      exact Germ.oneVariableTaylorSeries_coeff_eq_zero_of_mem_maximalIdeal_pow
        hlineRemainder (Nat.lt_succ_self d)
    have hlineCoeff :
        PowerSeries.coeff d (Germ.radialTaylorAlgHom 2 f v) =
          MvPolynomial.eval v initial := by
      rw [show f =
          (f - Germ.coordinatePolynomialAlgHom 2 p) +
            Germ.coordinatePolynomialAlgHom 2 p by
        exact (sub_add_cancel f
          (Germ.coordinatePolynomialAlgHom 2 p)).symm]
      rw [map_add, Pi.add_apply, map_add, hlineRemainderCoeff, zero_add]
      exact Germ.radialTaylor_coordinatePolynomial_coeff v p d
    have hlineD : Germ.lineRestriction v f ∈
        Germ.maximalIdeal 1 ^ d :=
      Germ.lineRestriction_mem_maximalIdeal_pow v hfd
    have hlineNext : Germ.lineRestriction v f ∉
        Germ.maximalIdeal 1 ^ (d + 1) := by
      intro hmem
      have hcoeff :=
        Germ.oneVariableTaylorSeries_coeff_eq_zero_of_mem_maximalIdeal_pow
          hmem (Nat.lt_succ_self d)
      change PowerSeries.coeff d
          (Germ.radialTaylorAlgHom 2 f v) = 0 at hcoeff
      rw [hlineCoeff] at hcoeff
      exact hveval hcoeff
    have hlineZero : Germ.lineRestriction v f ≠ 0 := by
      intro hzero
      apply hlineNext
      rw [hzero]
      exact (Germ.maximalIdeal 1 ^ (d + 1)).zero_mem
    obtain ⟨k, u, hu, hfactor⟩ :=
      Germ.exists_eq_coordinate_pow_mul_unit hlineZero
    have horder : Germ.vanishingOrder (Germ.lineRestriction v f) = k :=
      Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu hfactor
    have hdk : d ≤ k := by
      have horderLower :=
        Germ.mem_maximalIdeal_one_pow_iff.mp hlineD
      rw [horder] at horderLower
      exact_mod_cast horderLower
    have hkUpper : k < d + 1 := by
      by_contra hk
      apply hlineNext
      rw [Germ.mem_maximalIdeal_one_pow_iff, horder]
      exact_mod_cast Nat.le_of_not_gt hk
    have hkd : k = d := by omega
    let e : PointedEquivGerm 2 :=
      Germ.planeFirstColumnPointedEquiv v hvzero
    refine ⟨e, ?_⟩
    rw [Germ.IsRegularInFirstCoordinateOfOrder]
    change Germ.vanishingOrder
      (Germ.lineRestriction (firstCoordinateVector 1)
        (e.forward.pullbackRingHom f)) = (d : ℕ∞)
    rw [Germ.lineRestriction_planeFirstColumn_pullback]
    simpa [hkd] using horder

end Germ

end OnLeConjecture.Analytic
