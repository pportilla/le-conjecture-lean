/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OrderThreeNormalForm
public import OnLeConjecture.Analytic.CoordinateJetOrder

/-!
# Analytic reduction in order three

This file extracts the three cubic residue germs of an analytic plane germ.
For a germ regular of order three, the residue with exponent zero is regular
of order one and the other two residues vanish at the origin. Preparation in
order one then normalizes the leading residue.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped BigOperators NNReal ENNReal Topology

namespace Germ

/-- The mixed coefficient whose first coordinate degree equals the total
degree is evaluation on the first coordinate axis. -/
theorem mixedCoefficient_self
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (d : ℕ) :
    Germ.mixedCoefficient p d d =
      p d (fun _ : Fin d ↦ Germ.firstAxis) := by
  simp only [Germ.mixedCoefficient]
  rw [Finset.sum_eq_single (Finset.univ : Finset (Fin d))]
  · congr 1
    funext i
    simp [Germ.mixedArguments]
  · intro b hb hne
    rw [Finset.mem_powersetCard] at hb
    exfalso
    apply hne
    apply Finset.eq_univ_of_card
    simpa using hb.2
  · simp [Finset.mem_powersetCard]

/-- The coefficient on the first coordinate axis of an analytic power series
is the corresponding mixed coefficient. -/
theorem firstCoordinateAxisTaylorSeries_coeff_of_hasFPowerSeriesAt
    {F : Source 2 → ℂ}
    {p : FormalMultilinearSeries ℂ (Source 2) ℂ}
    (hp : HasFPowerSeriesAt F p 0) (d : ℕ) :
    PowerSeries.coeff d
        (Germ.firstCoordinateAxisTaylorSeries
          (Germ.ofFunction F hp.analyticAt)) =
      Germ.mixedCoefficient p d d := by
  have hv : Germ.firstCoordinateVector 1 = Germ.firstAxis := by
    ext i
    fin_cases i <;> simp [Germ.firstAxis, Germ.firstCoordinateVector]
  change PowerSeries.coeff d
      (Germ.radialTaylorAlgHom 2 (Germ.ofFunction F hp.analyticAt)
        (Germ.firstCoordinateVector 1)) = _
  rw [hv, Germ.radialTaylorAlgHom_coeff_ofFunction]
  rw [Germ.mixedCoefficient_self]
  let L : ℂ →L[ℂ] Source 2 :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight Germ.firstAxis
  have hpAtImage : HasFPowerSeriesAt F p (L (0 : ℂ)) := by
    simpa [L] using hp
  have hline := hpAtImage.compContinuousLinearMap
    (u := L) (x := (0 : ℂ))
  rcases hline with ⟨r, hr⟩
  have hfactorial := hr.factorial_smul (1 : ℂ) d
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hcomp : F ∘ (L : ℂ → Source 2) =
      fun z : ℂ ↦ F (z • Germ.firstAxis) := by rfl
  rw [hcomp] at hfactorial
  simp only [FormalMultilinearSeries.compContinuousLinearMap_apply]
    at hfactorial
  have hargs : ((L : ℂ → Source 2) ∘ fun _ : Fin d ↦ (1 : ℂ)) =
      fun _ : Fin d ↦ Germ.firstAxis := by
    funext i
    simp [L]
  rw [hargs] at hfactorial
  simp only [nsmul_eq_mul] at hfactorial
  rw [← hfactorial]
  field_simp [Nat.factorial_ne_zero]

/-- A diagonal mixed coefficient is the value of the corresponding analytic
Hadamard coefficient. -/
theorem mixedCoefficient_self_eq_value_firstCoordinateTaylorCoefficient
    {F : Source 2 → ℂ}
    {p : FormalMultilinearSeries ℂ (Source 2) ℂ}
    (hp : HasFPowerSeriesAt F p 0) (d : ℕ) :
    Germ.mixedCoefficient p d d =
      Germ.valueRingHom 1
        (Germ.firstCoordinateTaylorCoefficient d
          (Germ.ofFunction F hp.analyticAt)) := by
  rw [← Germ.firstCoordinateAxisTaylorSeries_coeff
    (Germ.ofFunction F hp.analyticAt)]
  exact (Germ.firstCoordinateAxisTaylorSeries_coeff_of_hasFPowerSeriesAt
    hp d).symm

/-- Evaluation of a cubic residue germ is the mixed coefficient at the
corresponding first coordinate degree. -/
theorem value_cubicResidueGerm
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ) (r : Fin 3)
    (hpos : 0 < (Germ.cubicResidueCompressedSeries p r).radius) :
    Germ.valueRingHom 2
        (Germ.ofFunction (Germ.cubicResidueCompressedSeries p r).sum
          ((Germ.cubicResidueCompressedSeries p r).hasFPowerSeriesOnBall
            hpos).analyticAt) =
      Germ.mixedCoefficient p r.1 r.1 := by
  rw [Germ.valueRingHom_ofFunction]
  let q := Germ.cubicResidueCompressedSeries p r
  have hq := q.hasFPowerSeriesOnBall hpos
  have hzero := hq.coeff_zero (fun _ : Fin 0 ↦ (0 : Source 2))
  change q.sum 0 = Germ.mixedCoefficient p r.1 r.1
  rw [← hzero]
  change q 0 (fun _ : Fin 0 ↦ Germ.planePoint 0 0) = _
  rw [Germ.cubicResidueCompressedSeries_apply_diagonal]
  simp

/-- The derivative of the exponent zero residue in its first coordinate is
the cubic mixed coefficient of the original series. -/
theorem differential_cubicResidueGerm_zero
    (p : FormalMultilinearSeries ℂ (Source 2) ℂ)
    (hpos : 0 < (Germ.cubicResidueCompressedSeries p 0).radius) :
    Germ.differential
        (Germ.ofFunction (Germ.cubicResidueCompressedSeries p 0).sum
          ((Germ.cubicResidueCompressedSeries p 0).hasFPowerSeriesOnBall
            hpos).analyticAt)
        (Germ.firstCoordinateVector 1) =
      Germ.mixedCoefficient p 3 3 := by
  let q := Germ.cubicResidueCompressedSeries p (0 : Fin 3)
  have hq := q.hasFPowerSeriesOnBall hpos
  rw [Germ.differential_ofFunction, hq.hasFPowerSeriesAt.fderiv_eq,
    continuousMultilinearCurryFin1_apply]
  change q 1 (fun _ : Fin 1 ↦ Germ.firstCoordinateVector 1) = _
  have hv : Germ.firstCoordinateVector 1 = Germ.planePoint 1 0 := by
    ext i
    fin_cases i <;> simp [Germ.firstCoordinateVector]
  rw [hv, Germ.cubicResidueCompressedSeries_apply_diagonal]
  rw [Fin.sum_univ_two]
  norm_num

/-- Exact regularity of order three gives a cubic residue decomposition in
which the exponent zero residue is regular of order one. -/
theorem exists_cubic_decomposition_of_regular_order_three
    {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f 3) :
    ∃ A B C : Germ 2,
      f = Germ.cubicSubstitutionAlgHom A +
          Germ.coordinate (0 : Fin 2) *
            Germ.cubicSubstitutionAlgHom B +
          Germ.coordinate (0 : Fin 2) ^ 2 *
            Germ.cubicSubstitutionAlgHom C ∧
        Germ.IsRegularInFirstCoordinateOfOrder A 1 ∧
        B ∈ Germ.maximalIdeal 2 ∧ C ∈ Germ.maximalIdeal 2 := by
  rcases f with ⟨f, hf⟩
  change IsAnalyticGerm f at hf
  induction f using Filter.Germ.inductionOn with
  | _ F =>
      rw [isAnalyticGerm_ofFun] at hf
      rcases hf with ⟨p, hp⟩
      let q : Fin 3 → FormalMultilinearSeries ℂ (Source 2) ℂ :=
        fun r ↦ Germ.cubicResidueCompressedSeries p r
      have hqRadius (r : Fin 3) : 0 < (q r).radius :=
        Germ.cubicResidueCompressedSeries_radius_pos p hp.radius_pos r
      have hqAnalytic (r : Fin 3) : AnalyticAt ℂ (q r).sum 0 :=
        ((q r).hasFPowerSeriesOnBall (hqRadius r)).analyticAt
      let D : Fin 3 → Germ 2 := fun r ↦
        Germ.ofFunction (q r).sum (hqAnalytic r)
      have hdecomposition :
          Germ.ofFunction F ⟨p, hp⟩ =
            ∑ r : Fin 3, Germ.coordinate (0 : Fin 2) ^ r.1 *
              Germ.cubicSubstitutionAlgHom (D r) := by
        obtain ⟨C, ρ, hC, hρ, hpBound⟩ :=
          p.le_mul_pow_of_radius_pos hp.radius_pos
        have hpSum : HasFPowerSeriesAt p.sum p 0 :=
          (p.hasFPowerSeriesOnBall hp.radius_pos).hasFPowerSeriesAt
        have hFSeries : F =ᶠ[nhds 0] p.sum := by
          filter_upwards [hp.eventually_hasSum_sub,
            hpSum.eventually_hasSum_sub] with z hzF hzSum
          simpa only [sub_zero] using hzF.unique hzSum
        have hxSmall :=
          Germ.eventually_geometric_coordinate_bound hρ (0 : Fin 2)
        have hySmall :=
          Germ.eventually_geometric_coordinate_bound hρ (1 : Fin 2)
        have hsubstitution (r : Fin 3) :
            Germ.cubicSubstitutionAlgHom (D r) =
              Germ.ofFunction ((q r).sum ∘ Germ.cubicMap)
                (by
                  have hqAt : AnalyticAt ℂ (q r).sum
                      (Germ.cubicMap 0) := by
                    simpa using hqAnalytic r
                  exact hqAt.comp Germ.cubicMap_analyticAt) := by
          change Germ.compPointed
              (Germ.ofFunction (q r).sum (hqAnalytic r))
                Germ.cubicMapGerm = _
          rw [Germ.cubicMapGerm, Germ.compPointed_ofFunction]
        simp_rw [hsubstitution]
        apply Subtype.ext
        apply Filter.Germ.coe_eq.mpr
        filter_upwards [hxSmall, hySmall, hFSeries] with z hx hy hzF
        change F z = ∑ r : Fin 3,
          z 0 ^ r.1 * (q r).sum (Germ.cubicMap z)
        rw [hzF]
        have hcubicMap : Germ.cubicMap z =
            Germ.planePoint (z 0 ^ 3) (z 1) := by
          ext i
          fin_cases i <;> simp
        rw [hcubicMap]
        rw [← Germ.planePoint_coordinates z]
        simpa only [q, Germ.planePoint_apply_zero,
          Germ.planePoint_apply_one] using
            Germ.sum_eq_sum_cubicResidueCompressedSeries
              p hC hρ hpBound hx hy
      have hcoefficients :=
        Germ.isRegularInFirstCoordinateOfOrder_iff.mp hregular
      have hmixed (d : ℕ) : Germ.mixedCoefficient p d d =
          Germ.valueRingHom 1
            (Germ.firstCoordinateTaylorCoefficient d
              (Germ.ofFunction F ⟨p, hp⟩)) :=
        Germ.mixedCoefficient_self_eq_value_firstCoordinateTaylorCoefficient
          hp d
      have hDValue (r : Fin 3) : Germ.valueRingHom 2 (D r) =
          Germ.mixedCoefficient p r.1 r.1 := by
        exact Germ.value_cubicResidueGerm p r (hqRadius r)
      have hDZero : Germ.valueRingHom 2 (D 0) = 0 := by
        rw [hDValue, hmixed]
        exact hcoefficients.2 0 (by omega)
      have hDOne : Germ.valueRingHom 2 (D 1) = 0 := by
        rw [hDValue, hmixed]
        exact hcoefficients.2 1 (by omega)
      have hDTwo : Germ.valueRingHom 2 (D 2) = 0 := by
        rw [hDValue, hmixed]
        exact hcoefficients.2 2 (by omega)
      have hDDerivative : Germ.differential (D 0)
          (Germ.firstCoordinateVector 1) ≠ 0 := by
        rw [show Germ.differential (D 0)
            (Germ.firstCoordinateVector 1) =
          Germ.mixedCoefficient p 3 3 by
            exact Germ.differential_cubicResidueGerm_zero p (hqRadius 0)]
        rw [hmixed]
        exact hcoefficients.1
      have hDRegular : Germ.IsRegularInFirstCoordinateOfOrder (D 0) 1 := by
        apply Germ.isRegularInFirstCoordinateOfOrder_iff_derivativeIterates.mpr
        constructor
        · change Germ.valueRingHom 2
              (Germ.partialDerivative (0 : Fin 2) (D 0)) ≠ 0
          rw [Germ.valueRingHom_partialDerivative]
          simpa [Germ.firstCoordinateVector,
            Germ.coordinateVector] using hDDerivative
        · intro k hk
          have hkZero : k = 0 := by omega
          subst k
          simpa using hDZero
      have hDOneMaximal : D 1 ∈ Germ.maximalIdeal 2 :=
        Germ.mem_maximalIdeal_iff.mpr hDOne
      have hDTwoMaximal : D 2 ∈ Germ.maximalIdeal 2 :=
        Germ.mem_maximalIdeal_iff.mpr hDTwo
      refine ⟨D 0, D 1, D 2, ?_, hDRegular,
        hDOneMaximal, hDTwoMaximal⟩
      have hsame : (⟨↑F, hf⟩ : Germ 2) =
          Germ.ofFunction F ⟨p, hp⟩ := Subtype.ext rfl
      rw [hsame, hdecomposition, Fin.sum_univ_three]
      norm_num

/-- A germ regular of order three is a unit times a normalized cubic residue
expression. Every coefficient below `x³` vanishes at the origin. -/
theorem exists_normalizedCubicResidueForm_of_regular_order_three
    {f : Germ 2}
    (hregular : Germ.IsRegularInFirstCoordinateOfOrder f 3) :
    ∃ h : Germ 1, ∃ B C U : Germ 2,
      h ∈ Germ.maximalIdeal 1 ∧
        B ∈ Germ.maximalIdeal 2 ∧ C ∈ Germ.maximalIdeal 2 ∧
        IsUnit U ∧
        f = (Germ.coordinate (0 : Fin 2) ^ 3 +
              Germ.hyperplaneExtension 1 h +
              Germ.coordinate (0 : Fin 2) *
                Germ.cubicSubstitutionAlgHom B +
              Germ.coordinate (0 : Fin 2) ^ 2 *
                Germ.cubicSubstitutionAlgHom C) *
            Germ.cubicSubstitutionAlgHom U := by
  obtain ⟨A, B₀, C₀, hdecomposition, hARegular,
      hB₀Maximal, hC₀Maximal⟩ :=
    Germ.exists_cubic_decomposition_of_regular_order_three hregular
  obtain ⟨p, U, hpMonic, hpDegree, hpMaximal, hUUnit, hA⟩ :=
    Germ.hasAnalyticWeierstrassFactorizationOfOrder_one hARegular
  have hpForm : p = Polynomial.X + Polynomial.C (p.coeff 0) :=
    hpMonic.eq_X_add_C hpDegree
  let h : Germ 1 := p.coeff 0
  have hh : h ∈ Germ.maximalIdeal 1 :=
    hpMaximal 0 (by omega)
  have hAEvaluation :
      Germ.firstCoordinatePolynomialEvaluation p =
        Germ.coordinate (0 : Fin 2) +
          Germ.hyperplaneExtension 1 h := by
    rw [Germ.firstCoordinatePolynomialEvaluation, hpForm]
    simp [h]
  have hANormal : A =
      (Germ.coordinate (0 : Fin 2) +
        Germ.hyperplaneExtension 1 h) * U := by
    rw [hA, hAEvaluation]
  let Uinv : Germ 2 := (↑(hUUnit.unit⁻¹) : Germ 2)
  have hUinv : U * Uinv = 1 := by
    calc
      U * Uinv = (↑hUUnit.unit : Germ 2) *
          (↑(hUUnit.unit⁻¹) : Germ 2) := by
        rw [hUUnit.unit_spec]
      _ = 1 := Units.mul_inv hUUnit.unit
  let B : Germ 2 := B₀ * Uinv
  let C : Germ 2 := C₀ * Uinv
  have hBMaximal : B ∈ Germ.maximalIdeal 2 :=
    Ideal.mul_mem_right Uinv (Germ.maximalIdeal 2) hB₀Maximal
  have hCMaximal : C ∈ Germ.maximalIdeal 2 :=
    Ideal.mul_mem_right Uinv (Germ.maximalIdeal 2) hC₀Maximal
  refine ⟨h, B, C, U, hh, hBMaximal, hCMaximal,
    hUUnit, ?_⟩
  have hsubstitution (c : Germ 1) :
      Germ.cubicSubstitutionAlgHom (Germ.hyperplaneExtension 1 c) =
        Germ.hyperplaneExtension 1 c :=
    Germ.cubicSubstitution_hyperplaneExtension c
  rw [hdecomposition, hANormal]
  simp only [map_mul, map_add,
    Germ.cubicSubstitutionAlgHom_coordinate_zero, hsubstitution]
  simp only [B, C, Uinv]
  have hsubInverse : Germ.cubicSubstitutionAlgHom U *
      Germ.cubicSubstitutionAlgHom Uinv = 1 := by
    rw [← map_mul, hUinv, map_one]
  simp only [map_mul]
  linear_combination
    -(Germ.coordinate (0 : Fin 2) * Germ.cubicSubstitutionAlgHom B₀ +
      Germ.coordinate (0 : Fin 2) ^ 2 *
        Germ.cubicSubstitutionAlgHom C₀) * hsubInverse

end Germ

end OnLeConjecture.Analytic
