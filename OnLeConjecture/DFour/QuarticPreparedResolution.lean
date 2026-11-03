/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DFour.QuarticPreparedCoefficientModel
public import OnLeConjecture.Numerical.QuarticSpineCounts
import Mathlib.Tactic

/-!
# A prepared quartic on a specified free resolution chain

The resolution data provide the germs and chart identities along a
positive-length chain of order-four points. Every child is recorded in
the common finite chart or in the swapped chart centered at zero, which
represents the omitted point of the finite chart. Monicity excludes that
point by restriction to the first coordinate axis.

The square Newton initial form supplies the coefficient expressions.
Cancellation identifies the recorded germs with their computed
transforms times pulled-back units. Child uniqueness and terminal order
at most two follow from these identities. Coverage is then proved from
the root paths, rather than assumed. Existence of such compatible free
chain data for a principalization remains a separate geometric question.
-/

public section

namespace OnLeConjecture.DFour

open Analytic Analytic.Germ _root_.Polynomial

/-- Compatible zero-center coordinates on a specified order-four chain.
The chart alternatives include the point at infinity. Separation is
required only for children represented in the common finite chart. -/
structure QuarticFreeResolutionSpine {N : ℕ} (c : AnalyticPointBasis N) (A : ℕ) where
  length_pos : 0 < A
  point : ℕ → Fin N
  point_zero : point 0 = c.root
  chain : ∀ j, j + 1 < A → c.ParentRelation (point (j + 1)) (point j)
  order : ∀ j < A, c.multiplicity (point j) = 4
  zero_step : ∀ j, j + 1 < A →
    (pointBlowupChartGerm 0).pullbackRingHom (c.germ (point j)) =
      coordinate (1 : Fin 2) ^ 4 * c.germ (point (j + 1))
  coordinates : ∀ j < A, ∀ q, c.ParentRelation q (point j) →
    (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (point j)) =
      c.germ (point j) ∨
    (c.chartCenter q = 0 ∧
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (point j)) =
        (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom (c.germ (point j)))
  separated : ∀ j < A, ∀ q t,
    c.ParentRelation q (point j) → c.ParentRelation t (point j) →
    (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (point j)) = c.germ (point j) →
    (c.sourceCoordinates t).forward.pullbackRingHom (c.germ (point j)) = c.germ (point j) →
    c.chartCenter q = c.chartCenter t → q = t

private theorem infinity_chart_second_axis (f : Germ 2) :
    hyperplaneRestriction 1 ((pointBlowupChartGerm 0).pullbackRingHom
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f)) =
    pointBlowupExceptionalLine.pullbackRingHom f := by
  obtain ⟨F, hF, rfl⟩ := exists_ofFunction f
  change compPointed (compPointed (compPointed (ofFunction F hF)
    (coordinateSwapPointedEquiv (1 : Fin 2)).forward) (pointBlowupChartGerm 0))
    (hyperplaneInclusionGerm 1) = compPointed (ofFunction F hF) pointBlowupExceptionalLine
  simp only [coordinateSwapPointedEquiv, pointedEquivGermOfContinuousLinearEquiv,
    pointBlowupChartGerm, hyperplaneInclusionGerm, pointBlowupExceptionalLine,
    compPointed_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  refine Filter.Eventually.of_forall fun t ↦ ?_
  change F (coordinateSwapEquiv (1 : Fin 2)
    (pointBlowupChart 0 (hyperplaneInclusion 1 t))) = F (![t 0, 0])
  congr 1
  ext i
  fin_cases i
  · simp [coordinateSwapEquiv_apply_zero, pointBlowupChart, hyperplaneInclusion]
    rfl
  · change (Equiv.piCongrLeft (fun _ : Fin 2 ↦ ℂ) (Equiv.swap 0 1)
      (pointBlowupChart 0 (hyperplaneInclusion 1 t))) 1 = 0
    simp [Equiv.piCongrLeft, pointBlowupChart, hyperplaneInclusion]

/-- A monic order-four first-axis restriction excludes a vanishing
strict transform at the point at infinity. This includes an arbitrary
analytic unit factor. -/
theorem no_infinity_child_of_first_axis
    (f g u : Germ 2) (hu : IsUnit u)
    (haxis : pointBlowupExceptionalLine.pullbackRingHom f =
      coordinate (0 : Fin 1) ^ 4 * pointBlowupExceptionalLine.pullbackRingHom u)
    (htransform : (pointBlowupChartGerm 0).pullbackRingHom
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f) =
        coordinate (1 : Fin 2) ^ 4 * g)
    (hg : g ∈ maximalIdeal 2) : False := by
  have h := congrArg (hyperplaneRestriction 1) htransform
  have hy : hyperplaneRestriction 1 (coordinate (1 : Fin 2)) =
      coordinate (0 : Fin 1) := by
    convert hyperplaneRestriction_coordinate_succ 1 (0 : Fin 1) using 1
    congr 2
  rw [infinity_chart_second_axis, haxis, map_mul, map_pow, hy] at h
  have heq := mul_left_cancel₀ (pow_ne_zero 4 coordinate_zero_ne_zero) h
  have hv := congrArg (valueRingHom 1) heq
  rw [hyperplaneRestriction, PointedMapGerm.valueRingHom_pullback,
    PointedMapGerm.valueRingHom_pullback, mem_maximalIdeal_iff.mp hg] at hv
  exact (valueRingHom_ne_zero_of_isUnit hu) hv

private theorem actual_transform_eq_model_mul_unit
    (B : PointedMapGerm 2 2) (D : ℕ) (f u T g : Germ 2)
    (hpolynomial : B.pullbackRingHom f = coordinate (1 : Fin 2) ^ D * T)
    (hactual : B.pullbackRingHom (f * u) = coordinate (1 : Fin 2) ^ D * g) :
    g = T * B.pullbackRingHom u := by
  apply mul_left_cancel₀ (pow_ne_zero D (coordinate_ne_zero (1 : Fin 2)))
  rw [← hactual, map_mul, hpolynomial, mul_assoc]

namespace QuarticFreeResolutionSpine

variable {N A ε : ℕ} {c : AnalyticPointBasis N}
    (S : QuarticFreeResolutionSpine c A)
    {P : Polynomial (Germ 1)} {η : ℂ}

theorem cumulative_transform (j : ℕ) (hj : j < A) :
    (freeChainChartGerm j).pullbackRingHom (c.germ c.root) =
      coordinate (1 : Fin 2) ^ (4 * j) * c.germ (S.point j) := by
  simpa only [S.point_zero, Nat.mul_comm j 4] using
    freeChain_cumulative_transform j 4 (fun k ↦ c.germ (S.point k))
      (fun k hk ↦ S.zero_step k (by omega))

/-- The recorded germ at each spine point is determined by the prepared
root and the chart identities. -/
theorem germ_eq_coefficientModel
    (e : QuarticCoefficientExpansion A ε P η)
    (hmonic : P.Monic) (hdegree : P.natDegree = 4) (hdepressed : P.coeff 3 = 0)
    (u : Germ 2) (hprepared : c.germ c.root = firstCoordinatePolynomialEvaluation P * u)
    (j : ℕ) (hj : j < A) :
    c.germ (S.point j) = quarticCoefficientModel (A - j) ε η 0 e.a₂ e.a₁ e.a₀ *
      (freeChainChartGerm j).pullbackRingHom u := by
  apply actual_transform_eq_model_mul_unit (freeChainChartGerm j) (4 * j)
  · apply e.pullback_factor hmonic hdegree hdepressed j (by omega) 0
    · simpa only [map_zero, add_zero] using freeChainChartGerm_pullback_zero j
    · exact freeChainChartGerm_pullback_hyperplaneExtension j
  · rw [← hprepared]
    exact S.cumulative_transform j hj

/-- Monicity proves that each positive-order child uses the common
finite chart. The alternative at infinity is present in the geometric
data and is excluded by a nonzero first-axis coefficient. -/
theorem child_finite
    (e : QuarticCoefficientExpansion A ε P η)
    (hmonic : P.Monic) (hdegree : P.natDegree = 4) (hdepressed : P.coeff 3 = 0)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : c.germ c.root = firstCoordinatePolynomialEvaluation P * u)
    (j : ℕ) (hj : j < A) (q : Fin N) (hq : c.ParentRelation q (S.point j)) :
    (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (S.point j)) =
      c.germ (S.point j) := by
  rcases S.coordinates j hj q hq with hfinite | ⟨hcenter, hinfinity⟩
  · exact hfinite
  · have htransform := c.transform_identity q hq.1
    rw [hq.2, S.order j hj, hcenter, hinfinity] at htransform
    have haxis : pointBlowupExceptionalLine.pullbackRingHom (c.germ (S.point j)) =
        coordinate (0 : Fin 1) ^ 4 * pointBlowupExceptionalLine.pullbackRingHom
          ((freeChainChartGerm j).pullbackRingHom u) := by
      rw [S.germ_eq_coefficientModel e hmonic hdegree hdepressed u hprepared j hj,
        map_mul, quarticCoefficientModel_first_axis (A - j) ε (by omega)]
    have hg : c.germ q ∈ maximalIdeal 2 := by
      simpa only [pow_one] using
        (Ideal.pow_le_pow_right (c.multiplicity_pos q)) (c.germ_mem q)
    exact (no_infinity_child_of_first_axis _ _ _ (hu.map _) haxis htransform hg).elim

/-- The cumulative chart identity for a child in the common finite
chart is obtained by appending its recorded edge identity. -/
theorem child_cumulative_transform
    (j : ℕ) (hj : j < A) (q : Fin N) (hq : c.ParentRelation q (S.point j))
    (hfinite : (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (S.point j)) =
      c.germ (S.point j)) :
    (centeredFreeChainChart (j + 1) (c.chartCenter q)).pullbackRingHom (c.germ c.root) =
      coordinate (1 : Fin 2) ^ (4 * (j + 1)) * c.germ q := by
  have hedge := c.transform_identity q hq.1
  rw [hq.2, S.order j hj, hfinite] at hedge
  rw [centeredFreeChainChart, Nat.add_sub_cancel, PointedMapGerm.pullbackRingHom_comp,
    RingHom.comp_apply, S.cumulative_transform j hj, map_mul, map_pow,
    pointBlowupChartGerm_pullback_one, hedge, ← mul_assoc, ← pow_add]
  congr 2

/-- The recorded child is the computed chart expression times the
pullback of the original preparation unit. Its exceptional center has
not yet been restricted to a root of the initial polynomial. -/
theorem child_germ_eq_coefficientModel
    (e : QuarticCoefficientExpansion A ε P η)
    (hmonic : P.Monic) (hdegree : P.natDegree = 4) (hdepressed : P.coeff 3 = 0)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : c.germ c.root = firstCoordinatePolynomialEvaluation P * u)
    (j : ℕ) (hj : j < A) (q : Fin N) (hq : c.ParentRelation q (S.point j)) :
    c.germ q = quarticCoefficientModel (A - (j + 1)) ε η (c.chartCenter q)
      e.a₂ e.a₁ e.a₀ *
        (centeredFreeChainChart (j + 1) (c.chartCenter q)).pullbackRingHom u := by
  have hfinite := S.child_finite e hmonic hdegree hdepressed u hu hprepared j hj q hq
  apply actual_transform_eq_model_mul_unit
    (centeredFreeChainChart (j + 1) (c.chartCenter q)) (4 * (j + 1))
  · exact e.pullback_factor hmonic hdegree hdepressed (j + 1) (by omega)
      (c.chartCenter q) _ (centeredFreeChainChart_pullback_zero _ (by omega) _)
      (centeredFreeChainChart_pullback_hyperplaneExtension _ _)
  · rw [← hprepared]
    exact S.child_cumulative_transform j hj q hq hfinite

private theorem child_model_value_zero
    (e : QuarticCoefficientExpansion A ε P η)
    (hmonic : P.Monic) (hdegree : P.natDegree = 4) (hdepressed : P.coeff 3 = 0)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : c.germ c.root = firstCoordinatePolynomialEvaluation P * u)
    (j : ℕ) (hj : j < A) (q : Fin N) (hq : c.ParentRelation q (S.point j)) :
    valueRingHom 2 (quarticCoefficientModel (A - (j + 1)) ε η (c.chartCenter q)
      e.a₂ e.a₁ e.a₀) = 0 := by
  have hg : c.germ q ∈ maximalIdeal 2 := by
    simpa only [pow_one] using
      (Ideal.pow_le_pow_right (c.multiplicity_pos q)) (c.germ_mem q)
  have hvalue := congrArg (valueRingHom 2)
    (S.child_germ_eq_coefficientModel e hmonic hdegree hdepressed u hu hprepared j hj q hq)
  rw [mem_maximalIdeal_iff.mp hg, map_mul, PointedMapGerm.valueRingHom_pullback] at hvalue
  exact (mul_eq_zero.mp hvalue.symm).resolve_right (valueRingHom_ne_zero_of_isUnit hu)

/-- Before the last order-four point, positivity of the child order
forces its finite exceptional center to be zero. -/
theorem child_center_zero_before_terminal
    (e : QuarticCoefficientExpansion A ε P η)
    (hmonic : P.Monic) (hdegree : P.natDegree = 4) (hdepressed : P.coeff 3 = 0)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : c.germ c.root = firstCoordinatePolynomialEvaluation P * u)
    (j : ℕ) (hj : j + 1 < A) (q : Fin N) (hq : c.ParentRelation q (S.point j)) :
    c.chartCenter q = 0 := by
  have hvalue := S.child_model_value_zero e hmonic hdegree hdepressed u hu hprepared
    j (by omega) q hq
  rw [quarticCoefficientModel_value_of_pos _ _ (by omega)] at hvalue
  exact (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp hvalue

/-- Separation of finite exceptional centers and the computed center
condition identify every nonterminal child with the next spine point. -/
theorem child_eq_next_before_terminal
    (e : QuarticCoefficientExpansion A ε P η)
    (hmonic : P.Monic) (hdegree : P.natDegree = 4) (hdepressed : P.coeff 3 = 0)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : c.germ c.root = firstCoordinatePolynomialEvaluation P * u)
    (j : ℕ) (hj : j + 1 < A) (q : Fin N) (hq : c.ParentRelation q (S.point j)) :
    q = S.point (j + 1) := by
  have hnext := S.chain j hj
  apply S.separated j (by omega) q (S.point (j + 1)) hq hnext
  · exact S.child_finite e hmonic hdegree hdepressed u hu hprepared j (by omega) q hq
  · exact S.child_finite e hmonic hdegree hdepressed u hu hprepared j (by omega) _ hnext
  · exact (S.child_center_zero_before_terminal e hmonic hdegree hdepressed
      u hu hprepared j hj q hq).trans
      (S.child_center_zero_before_terminal e hmonic hdegree hdepressed
        u hu hprepared j hj _ hnext).symm

/-- Terminal template identities, with the factor given by pullback of
the original unit. Both possible center conditions are proved from the
recorded child's positive order. -/
theorem terminal_child_expression
    (e : QuarticCoefficientExpansion A ε P η) (hε : ε ≤ 1)
    (hmonic : P.Monic) (hdegree : P.natDegree = 4) (hdepressed : P.coeff 3 = 0)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : c.germ c.root = firstCoordinatePolynomialEvaluation P * u)
    (q : Fin N) (hq : c.ParentRelation q (S.point (A - 1))) :
    (ε = 0 ∧ c.chartCenter q ^ 2 + η = 0 ∧
      c.germ q = integralQuarticTransform η (c.chartCenter q)
        (hyperplaneExtension 1 e.a₂) (hyperplaneExtension 1 e.a₁)
        (hyperplaneExtension 1 e.a₀) *
          (centeredFreeChainChart A (c.chartCenter q)).pullbackRingHom u) ∨
    (ε = 1 ∧ c.chartCenter q = 0 ∧
      c.germ q = halfIntegralQuarticTransform η
        (hyperplaneExtension 1 e.a₂) (hyperplaneExtension 1 e.a₁)
        (hyperplaneExtension 1 e.a₀) * (centeredFreeChainChart A 0).pullbackRingHom u) := by
  have hj : A - 1 < A := by have := S.length_pos; omega
  have hA : A - 1 + 1 = A := Nat.sub_add_cancel S.length_pos
  have hvalue := S.child_model_value_zero e hmonic hdegree hdepressed u hu hprepared
    (A - 1) hj q hq
  have hidentity := S.child_germ_eq_coefficientModel e hmonic hdegree hdepressed
    u hu hprepared (A - 1) hj q hq
  rw [hA, Nat.sub_self] at hvalue hidentity
  rw [quarticCoefficientModel_terminal_value ε hε] at hvalue
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with hzero | hone
  · have hroot : c.chartCenter q ^ 2 + η = 0 := by
      rw [if_pos hzero] at hvalue
      exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hvalue
    exact Or.inl ⟨hzero, hroot,
      by simpa only [hzero, quarticCoefficientModel_integral] using hidentity⟩
  · have hcenter : c.chartCenter q = 0 := by
      rw [if_neg (by omega)] at hvalue
      exact (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp hvalue
    exact Or.inr ⟨hone, hcenter,
      by simpa only [hone, hcenter, quarticCoefficientModel_half_integral] using hidentity⟩

/-- Both Newton cases give order at most two for every terminal child.
The root condition in the integral case and the zero center in the
half-integral case are consequences of the child's positive order. -/
theorem terminal_child_not_mem_cube
    (e : QuarticCoefficientExpansion A ε P η) (hε : ε ≤ 1) (hη : η ≠ 0)
    (hmonic : P.Monic) (hdegree : P.natDegree = 4) (hdepressed : P.coeff 3 = 0)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : c.germ c.root = firstCoordinatePolynomialEvaluation P * u)
    (q : Fin N) (hq : c.ParentRelation q (S.point (A - 1))) :
    c.germ q ∉ maximalIdeal 2 ^ 3 := by
  have hj : A - 1 < A := by have := S.length_pos; omega
  have hA : A - 1 + 1 = A := Nat.sub_add_cancel S.length_pos
  have hvalue := S.child_model_value_zero e hmonic hdegree hdepressed u hu hprepared
    (A - 1) hj q hq
  have hidentity := S.child_germ_eq_coefficientModel e hmonic hdegree hdepressed
    u hu hprepared (A - 1) hj q hq
  rw [hA, Nat.sub_self] at hvalue hidentity
  have hmodel : quarticCoefficientModel 0 ε η (c.chartCenter q) e.a₂ e.a₁ e.a₀ ∉
      maximalIdeal 2 ^ 3 := by
    rw [quarticCoefficientModel_terminal_value ε hε] at hvalue
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with hzero | hone
    · have hroot : c.chartCenter q ^ 2 + η = 0 := by
        rw [if_pos hzero] at hvalue
        exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hvalue
      simpa only [hzero, quarticCoefficientModel_integral] using
        (integralQuarticTransform_at_root η (c.chartCenter q) hη hroot
          (hyperplaneExtension 1 e.a₂) (hyperplaneExtension 1 e.a₁)
          (hyperplaneExtension 1 e.a₀)).2
    · have hcenter : c.chartCenter q = 0 := by
        rw [if_neg (by omega)] at hvalue
        exact (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp hvalue
      simpa only [hone, hcenter, quarticCoefficientModel_half_integral] using
        halfIntegralQuarticTransform_not_mem_cube η hη
          (hyperplaneExtension 1 e.a₂) (hyperplaneExtension 1 e.a₁)
          (hyperplaneExtension 1 e.a₀)
  obtain ⟨v, hv⟩ :=
    (hu.map (centeredFreeChainChart A (c.chartCenter q)).pullbackRingHom).exists_right_inv
  intro hg
  have hmul := Ideal.mul_mem_right v (maximalIdeal 2 ^ 3) hg
  rw [hidentity, mul_assoc, hv, mul_one] at hmul
  exact hmodel hmul

/-- Generation strictly increases along the recorded chain, so its
`A` order-four points are distinct. Injectivity is not assumed. -/
theorem point_injective : Function.Injective (fun i : Fin A ↦ S.point i) := by
  obtain ⟨a, hA⟩ := Nat.exists_eq_succ_of_ne_zero S.length_pos.ne'
  subst A
  have hgen : StrictMono (fun i : Fin (a + 1) ↦ c.generation (S.point i)) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have hparent := S.chain i (by omega)
    have hlt := c.generation_decreases _ hparent.1
    rw [hparent.2] at hlt
    exact hlt
  intro i j hij
  exact hgen.injective (congrArg c.generation hij)

/-- Every point outside the given chain descends from a terminal
child, whose order has already been bounded analytically. -/
theorem off_spine_multiplicity_le_two
    (e : QuarticCoefficientExpansion A ε P η) (hε : ε ≤ 1) (hη : η ≠ 0)
    (hmonic : P.Monic) (hdegree : P.natDegree = 4) (hdepressed : P.coeff 3 = 0)
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : c.germ c.root = firstCoordinatePolynomialEvaluation P * u)
    (q : Fin N) (hoff : q ∉ Set.range (fun i : Fin A ↦ S.point i)) :
    c.multiplicity q ≤ 2 := by
  have hchildren : ∀ j < A - 1, ∀ b,
      c.ParentRelation b (S.point j) → b = S.point (j + 1) := by
    intro j hj b hb
    exact S.child_eq_next_before_terminal e hmonic hdegree hdepressed u hu hprepared
      j (by omega) b hb
  rcases c.spine_frontier_coverage (A - 1) S.point S.point_zero hchildren q with
    ⟨j, hj, rfl⟩ | ⟨b, hb, hpath⟩
  · exact (hoff ⟨⟨j, by have := S.length_pos; omega⟩, rfl⟩).elim
  · exact c.descendant_multiplicity_le_of_not_mem_pow (k := 2) hpath
      (S.terminal_child_not_mem_cube e hε hη hmonic hdegree hdepressed u hu hprepared b hb)

include S in
/-- The square initial chart and the supplied free resolution chain
exclude entry three, count all order-four entries, and give the refined
quartic square-sum estimate. No terminal expression, child uniqueness,
coverage, or multiplicity bound is assumed. -/
theorem square_initial_point_basis_bounds
    (d : SquareQuarticNewtonData P η) (ε : ℕ) (hε : ε ≤ 1)
    (hslope : 2 * d.r = d.s * (2 * A + ε))
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : c.germ c.root = firstCoordinatePolynomialEvaluation P * u) :
    (∀ q, c.multiplicity q ≠ 3) ∧
      Numerical.MultiplicityCounts.valueCount c.multiplicity 4 = A ∧
      Numerical.MultiplicityCounts.squareSum c.multiplicity ≤
        2 * Numerical.MultiplicityCounts.sum c.multiplicity + 8 * A := by
  obtain ⟨e⟩ := d.exists_coefficientExpansion A ε hε hslope
  have hoff := S.off_spine_multiplicity_le_two e hε d.parameter_ne_zero
    d.monic d.degree d.depressed u hu hprepared
  refine ⟨?_, Numerical.MultiplicityCounts.quartic_spine_count_and_squareSum_bound
    c.multiplicity (fun i : Fin A ↦ S.point i) S.point_injective
      (fun i ↦ S.order i i.isLt) hoff⟩
  intro q
  by_cases hq : q ∈ Set.range (fun i : Fin A ↦ S.point i)
  · obtain ⟨i, rfl⟩ := hq
    rw [S.order i i.isLt]
    decide
  · have := hoff q hq
    omega

include S in
/-- The same estimate with the integral/half-integral slope alternatives
in their usual separate form. -/
theorem square_initial_point_basis_bounds_of_slope_alternatives
    (d : SquareQuarticNewtonData P η)
    (hslope : d.r = d.s * A ∨ 2 * d.r = d.s * (2 * A + 1))
    (u : Germ 2) (hu : IsUnit u)
    (hprepared : c.germ c.root = firstCoordinatePolynomialEvaluation P * u) :
    (∀ q, c.multiplicity q ≠ 3) ∧
      Numerical.MultiplicityCounts.valueCount c.multiplicity 4 = A ∧
      Numerical.MultiplicityCounts.squareSum c.multiplicity ≤
        2 * Numerical.MultiplicityCounts.sum c.multiplicity + 8 * A := by
  rcases hslope with hintegral | hhalf
  · exact S.square_initial_point_basis_bounds d 0 (by decide)
      (by rw [hintegral]; ring) u hu hprepared
  · exact S.square_initial_point_basis_bounds d 1 (by decide) hhalf u hu hprepared

end QuarticFreeResolutionSpine

end OnLeConjecture.DFour
