/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedDepressedPreparation
public import OnLeConjecture.Analytic.SquarefreeScaledResolution
public import OnLeConjecture.Analytic.ParameterTranslationPointBasis

/-!
# Weierstrass preparation from a matched top-order chain

First-axis regularity and the recorded analytic blowup identities construct
the Weierstrass polynomial and all free-chain coefficient bounds. They also
exclude the complementary terminal chart. Depressed preparation is then
constructed with convergent lifts through the chain. No initial polynomial,
Newton weight, or prepared equation is an input.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open Filter
open scoped Topology

/-- A triangular parameter shear with zero constant term fixes the
restriction to the first coordinate axis. -/
theorem firstAxisRestriction_triangularShear
    (b : ℂ → ℂ) (hb : AnalyticAt ℂ b 0) (hbzero : b 0 = 0) (f : Germ 2) :
    lineRestriction (firstCoordinateVector 1)
      ((triangularShearGerm b hb hbzero).pullbackRingHom f) =
        lineRestriction (firstCoordinateVector 1) f := by
  obtain ⟨F, hF, rfl⟩ := exists_ofFunction f
  change compPointed (compPointed (ofFunction F hF) (triangularShearGerm b hb hbzero))
      (lineGerm (firstCoordinateVector 1)) =
    compPointed (ofFunction F hF) (lineGerm (firstCoordinateVector 1))
  simp only [triangularShearGerm, lineGerm, compPointed_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  refine Filter.Eventually.of_forall fun z ↦ ?_
  change F (triangularShear b (lineMap (firstCoordinateVector 1) z)) =
    F (lineMap (firstCoordinateVector 1) z)
  congr 1
  ext i
  fin_cases i
  · change z 0 * 1 + b (z 0 * 0) = z 0 * 1
    simp only [mul_zero, hbzero, add_zero]
  · rfl

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic.AnalyticTopOrderChain

open OnLeConjecture.Analytic.Germ

variable {N : ℕ} {c : AnalyticPointBasis N} (S : AnalyticTopOrderChain c)

theorem straightenedGerm_regular
    (hregular : IsRegularInFirstCoordinateOfOrder (c.germ c.root)
      (c.multiplicity c.root)) :
    IsRegularInFirstCoordinateOfOrder (S.straightenedGerm 0) (c.multiplicity c.root) := by
  rw [S.straightenedGerm_root]
  change vanishingOrder (lineRestriction (firstCoordinateVector 1)
    ((triangularShearGerm (freeChainShift S.chartCenters (S.length - 1))
      (freeChainShift_analyticAt _ _) (freeChainShift_origin _ _)).pullbackRingHom
        (c.germ c.root))) = _
  rw [firstAxisRestriction_triangularShear]
  exact hregular

/-- The prepared equation and every coefficient bound are constructed
from first-axis regularity and the matched analytic free chain. -/
theorem exists_preparation_of_regular_top_chain (d : AnalyticProximityData c)
    (hcoordinates : DFour.TopOrderChartCompatibility d)
    (hregular : IsRegularInFirstCoordinateOfOrder (c.germ c.root)
      (c.multiplicity c.root)) :
    ∃ P : _root_.Polynomial (Germ 1), ∃ U : Germ 2,
      P.Monic ∧ P.natDegree = c.multiplicity c.root ∧ IsUnit U ∧
      S.straightenedGerm 0 = firstCoordinatePolynomialEvaluation P * U ∧
      ∀ j, P.coeff j ∈ maximalIdeal 1 ^ (S.length * (c.multiplicity c.root - j)) := by
  obtain ⟨P, U, hP, hPm, _, hU, hfactor⟩ :=
    hasAnalyticWeierstrassFactorizationOfOrder_of_pos (c.multiplicity_pos c.root)
      (S.straightenedGerm_regular hregular)
  refine ⟨P, U, hP, hPm, hU, hfactor, ?_⟩
  intro j
  by_cases hj : j ≤ c.multiplicity c.root
  · have h := coefficient_mem_pow_of_prepared_freeChain (S.length - 1)
      (c.multiplicity c.root) P S.straightenedGerm U hU hfactor
      (fun k hk ↦ S.straightenedGerm_step d hcoordinates.free_coordinates k (by omega))
      (S.straightenedGerm_exact_order _ (by have := S.length_pos; omega)).1 j hj
    simpa only [Nat.sub_add_cancel S.length_pos] using h
  · simp [Nat.sub_eq_zero_of_le (by omega : c.multiplicity c.root ≤ j)]

/-- First-axis regularity excludes the complementary terminal chart.
The polynomial and its integral root scaling are constructed in the proof. -/
theorem terminal_child_finite_of_regular_top_chain (d : AnalyticProximityData c)
    (hcoordinates : DFour.TopOrderChartCompatibility d)
    (hregular : IsRegularInFirstCoordinateOfOrder (c.germ c.root)
      (c.multiplicity c.root))
    (q : Fin N) (hq : c.ParentRelation q (S.point (S.length - 1))) :
    (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (S.point (S.length - 1))) =
      c.germ (S.point (S.length - 1)) := by
  obtain ⟨P, U, hP, hPm, hU, hfactor, hcoeff⟩ :=
    S.exists_preparation_of_regular_top_chain d hcoordinates hregular
  obtain ⟨Q, hQ, hQm, hscaling, _⟩ :=
    exists_monic_weighted_polynomial_scaling P (c.multiplicity c.root) S.length hP hPm hcoeff
  rw [hscaling] at hfactor
  exact S.terminal_child_uses_finite_chart d hcoordinates rfl Q hQ hQm le_rfl
    U hU hfactor q hq

/-- Depressed preparation with convergent lifts is constructed from the
original regular germ and its matched point-basis data. -/
theorem exists_depressed_preparation_of_regular_top_chain (d : AnalyticProximityData c)
    (hcoordinates : DFour.TopOrderChartCompatibility d)
    (hregular : IsRegularInFirstCoordinateOfOrder (c.germ c.root)
      (c.multiplicity c.root)) :
    ∃ a : Germ 1, ∃ T : ParameterTranslationChain a S.length,
      ∃ P : _root_.Polynomial (Germ 1), ∃ U : Germ 2,
      a ∈ maximalIdeal 1 ^ S.length ∧ P.Monic ∧ P.natDegree = c.multiplicity c.root ∧
      P.coeff (c.multiplicity c.root - 1) = 0 ∧ IsUnit U ∧
      (T.coordinates 0).forward.pullbackRingHom (S.straightenedGerm 0) =
        firstCoordinatePolynomialEvaluation P * U ∧
      ∀ j, P.coeff j ∈ maximalIdeal 1 ^ (S.length * (c.multiplicity c.root - j)) := by
  exact exists_depressed_preparation_of_free_chain S.length (c.multiplicity c.root)
    S.length_pos (c.multiplicity_pos c.root) S.straightenedGerm
    (S.straightenedGerm_regular hregular)
    (fun j hj ↦ S.straightenedGerm_step d hcoordinates.free_coordinates j hj)
    (S.straightenedGerm_exact_order _ (by have := S.length_pos; omega)).1

end OnLeConjecture.Analytic.AnalyticTopOrderChain
