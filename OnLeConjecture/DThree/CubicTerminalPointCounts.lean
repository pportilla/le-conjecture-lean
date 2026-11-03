/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.CubicTerminalGerms
public import OnLeConjecture.Analytic.PureResidueTerminalChain
import Mathlib.Tactic

/-!
# Counts forced by the divided cubic terminal expressions

The terminal centers, their uniqueness, the identities of their analytic
germs, and the multiplicities of all descendants are proved from the
matched chart data. The node and cusp calculations permit arbitrary
source equivalences at their children.
-/

public section

namespace OnLeConjecture.Analytic.AnalyticTopOrderChain

open OnLeConjecture.Analytic.Germ _root_.Polynomial

variable {N : ℕ} {c : AnalyticPointBasis N} (S : AnalyticTopOrderChain c)
    (d : AnalyticProximityData c) (hcoordinates : DFour.TopOrderChartCompatibility d)
    (hroot : c.multiplicity c.root = 3)
    (Q : Polynomial (Germ 1)) (hQ : Q.Monic) (hQm : Q.natDegree = 3)
    (hresidue : Q.map (valueRingHom 1) = X ^ 3)
    (U : Germ 2) (hU : IsUnit U)
    (hprepared : S.straightenedGerm 0 =
      firstCoordinatePolynomialEvaluation
        (Q.scaleRoots (coordinate (0 : Fin 1) ^ S.length)) * U)

include d hcoordinates hroot hQ hQm hresidue hU hprepared in
theorem valueCount_two_eq_zero_of_divided_cubic_mem_cube
    (hmem : firstCoordinatePolynomialEvaluation Q ∈ maximalIdeal 2 ^ 3) :
    Numerical.MultiplicityCounts.valueCount c.multiplicity 2 = 0 := by
  apply S.valueCount_two_eq_zero_of_terminal_smooth d hroot
  intro b hb
  have hidentity := S.terminal_germ_eq_divided_polynomial_of_pure_residue
    d hcoordinates hroot Q hQ hQm hresidue U hU hprepared b hb
  have hmem' : c.germ b ∈ maximalIdeal 2 ^ 3 := by
    rw [hidentity]
    exact (maximalIdeal 2 ^ 3).mul_mem_right _ hmem
  have hne := S.terminal_child_not_top b hb
  have hle := c.multiplicity_le_root b
  rw [hroot] at hne hle
  exact (c.germ_not_mem_succ b
    (Ideal.pow_le_pow_right (by omega : c.multiplicity b + 1 ≤ 3) hmem')).elim

include d hcoordinates hroot hQ hQm hresidue hU hprepared in
theorem valueCount_two_eq_zero_of_divided_constant_order_one
    (B : Germ 1) (hB : IsUnit B)
    (hconstant : Q.coeff 0 = coordinate (0 : Fin 1) * B) :
    Numerical.MultiplicityCounts.valueCount c.multiplicity 2 = 0 := by
  apply S.valueCount_two_eq_zero_of_terminal_smooth d hroot
  intro b hb
  rw [S.terminal_germ_eq_divided_polynomial_of_pure_residue
    d hcoordinates hroot Q hQ hQm hresidue U hU hprepared b hb]
  exact not_mem_pow_of_unit_multiple _ _ (hU.map _) 2
    (polynomialEvaluation_not_mem_square_of_constant_order_one Q B hB hconstant)

include d hcoordinates hroot hQ hQm hresidue hU hprepared in
theorem valueCount_two_le_one_of_divided_cusp
    (hdepressed : Q.coeff 2 = 0) (B : Germ 1) (hB : IsUnit B)
    (hconstant : Q.coeff 0 = coordinate (0 : Fin 1) ^ 2 * B)
    (hlinear : Q.coeff 1 ∈ maximalIdeal 1 ^ 2) :
    Numerical.MultiplicityCounts.valueCount c.multiplicity 2 ≤ 1 := by
  apply S.valueCount_two_le_one_of_terminal_children d hroot
    (S.terminal_children_unique_of_pure_residue d hcoordinates hroot Q hQ hQm
      hresidue U hU hprepared)
  intro b hb q hq
  have hne := S.terminal_child_not_top b hb
  have hle := c.multiplicity_le_root b
  rw [hroot] at hne hle
  by_cases hbOne : c.multiplicity b ≤ 1
  · exact (c.multiplicity_le_of_parent hq).trans hbOne
  have hbTwo : c.multiplicity b = 2 := by omega
  obtain ⟨C, hC, hCexpr⟩ := exists_depressed_cubic_cusp_expression
    Q hQ hQm hdepressed B hB hconstant hlinear
  let W := (centeredFreeChartGerm S.length 0).pullbackRingHom U
  have hW : IsUnit W := hU.map _
  have hidentity : c.germ b = coordinate (0 : Fin 2) ^ 3 * W +
      coordinate (1 : Fin 2) ^ 2 * (C * W) := by
    rw [S.terminal_germ_eq_divided_polynomial_of_pure_residue
      d hcoordinates hroot Q hQ hQm hresidue U hU hprepared b hb, hCexpr]
    dsimp only [W]
    ring
  exact c.multiplicity_le_of_not_mem_pow (k := 1)
    (c.ordinary_cusp_child_not_mem_square b hbTwo (C * W) W (hC.mul hW) hW hidentity q hq)

include d hcoordinates hroot hQ hQm hresidue hU hprepared in
theorem valueCount_two_le_one_of_divided_node
    (hdepressed : Q.coeff 2 = 0) (B : Germ 1) (hB : IsUnit B)
    (hlinear : Q.coeff 1 = coordinate (0 : Fin 1) * B)
    (hconstant : Q.coeff 0 ∈ maximalIdeal 1 ^ 2) :
    Numerical.MultiplicityCounts.valueCount c.multiplicity 2 ≤ 1 := by
  apply S.valueCount_two_le_one_of_terminal_children d hroot
    (S.terminal_children_unique_of_pure_residue d hcoordinates hroot Q hQ hQm
      hresidue U hU hprepared)
  intro b hb q hq
  have hne := S.terminal_child_not_top b hb
  have hle := c.multiplicity_le_root b
  rw [hroot] at hne hle
  by_cases hbOne : c.multiplicity b ≤ 1
  · exact (c.multiplicity_le_of_parent hq).trans hbOne
  have hbTwo : c.multiplicity b = 2 := by omega
  obtain ⟨α, β, hβ, htail⟩ := exists_depressed_cubic_node_initial
    Q hQ hQm hdepressed B hB hlinear hconstant
  have hidentity := S.terminal_germ_eq_divided_polynomial_of_pure_residue
    d hcoordinates hroot Q hQ hQm hresidue U hU hprepared b hb
  exact c.multiplicity_le_of_not_mem_pow (k := 1)
    (c.swapped_node_child_not_mem_square b hbTwo (firstCoordinatePolynomialEvaluation Q)
      _ (hU.map _) hidentity α β hβ htail q hq)

end OnLeConjecture.Analytic.AnalyticTopOrderChain
