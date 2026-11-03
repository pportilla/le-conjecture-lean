/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TwoWeightMonomialIdeal
public import OnLeConjecture.DThree.WeightedOrderExpansion
public import OnLeConjecture.DTwo.ResidualNoninjectivity

/-!
# Residual weighted order tails

Membership in the finite monomial ideal for source weights `(L, 2)` gives a
shared analytic remainder for residual weighted rescaling. Combining this
remainder with the residual collision gives the terminal noninjectivity
statement.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.DThree

/-- Polynomial substitution that converts bivariate weights `(1, 2)` into
source weights `(L, 2)`. -/
@[expose]
noncomputable def residualParameterPolynomialSubstitution
    (L : ℕ) (T : ℂ) : Fin 2 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.X 0,
    MvPolynomial.C T * MvPolynomial.X 1 ^ L]

/-- The polynomial map whose evaluation is the residual initial map. -/
@[expose]
noncomputable def residualWeightedInitialPolynomials
    {N : ℕ} (k L : ℕ) (c T : ℂ) (Psi : PreparedOddFamily N)
    (model : Psi.BivariateModel) :
    Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.X 1 ^ k,
    MvPolynomial.C (-c) *
      (MvPolynomial.X 0 ^ 2 +
        MvPolynomial.C T * MvPolynomial.X 1 ^ L),
    MvPolynomial.bind₁
      (residualParameterPolynomialSubstitution L T) model.polynomial]

/-- Evaluation of the polynomial model gives the exported residual initial
map exactly. -/
theorem weightedPolynomialMap_residualWeightedInitialPolynomials
    {N : ℕ} (k L : ℕ) (c T : ℂ) (Psi : PreparedOddFamily N)
    (model : Psi.BivariateModel) :
    weightedPolynomialMap
        (residualWeightedInitialPolynomials k L c T Psi model) =
      residualWeightedInitialMap k L N c T Psi := by
  funext z i
  fin_cases i
  · simp [weightedPolynomialMap, residualWeightedInitialPolynomials,
      residualWeightedInitialMap]
  · simp [weightedPolynomialMap, residualWeightedInitialPolynomials,
      residualWeightedInitialMap]
  · change MvPolynomial.eval
        ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z)
        (MvPolynomial.bind₁
          (residualParameterPolynomialSubstitution L T)
            model.polynomial) =
      (Psi.polynomial (T * z.2 ^ L)).eval z.1
    change MvPolynomial.eval₂Hom (RingHom.id ℂ)
        ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z)
        (MvPolynomial.bind₁
          (residualParameterPolynomialSubstitution L T)
            model.polynomial) = _
    rw [MvPolynomial.eval₂Hom_bind₁]
    have hcoordinates :
        (fun i : Fin 2 ↦ MvPolynomial.eval₂Hom (RingHom.id ℂ)
          ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z)
            (residualParameterPolynomialSubstitution L T i)) =
          ![z.1, T * z.2 ^ L] := by
      funext i
      fin_cases i <;>
        simp [residualParameterPolynomialSubstitution]
    rw [hcoordinates]
    change MvPolynomial.eval ![z.1, T * z.2 ^ L]
      model.polynomial = _
    rw [← parameterSpecialization_eval, ← model.specialization]

theorem residualParameterPolynomialSubstitution_isWeightedHomogeneous
    (L : ℕ) (T : ℂ) (i : Fin 2) :
    MvPolynomial.IsWeightedHomogeneous ![L, 2]
      (residualParameterPolynomialSubstitution L T i)
        (L * (![1, 2] i)) := by
  fin_cases i
  · simpa [residualParameterPolynomialSubstitution] using
      MvPolynomial.isWeightedHomogeneous_X
        ℂ (![L, 2] : Fin 2 → ℕ) (0 : Fin 2)
  · have hy := MvPolynomial.isWeightedHomogeneous_X
      ℂ (![L, 2] : Fin 2 → ℕ) (1 : Fin 2)
    simpa [residualParameterPolynomialSubstitution, mul_comm] using
      (hy.pow L).C_mul T

/-- Each coordinate of the polynomial model has the residual target
degree for source weights `(L, 2)`. -/
theorem residualWeightedInitialPolynomials_isWeightedHomogeneous
    {N : ℕ} (k L : ℕ) (c T : ℂ) (Psi : PreparedOddFamily N)
    (model : Psi.BivariateModel) (i : Fin 3) :
    MvPolynomial.IsWeightedHomogeneous ![L, 2]
      (residualWeightedInitialPolynomials k L c T Psi model i)
      (residualWeightedDegrees k L N i) := by
  fin_cases i
  · have hy := MvPolynomial.isWeightedHomogeneous_X
      ℂ (![L, 2] : Fin 2 → ℕ) (1 : Fin 2)
    simpa [residualWeightedInitialPolynomials, residualWeightedDegrees,
      mul_comm] using hy.pow k
  · have hx := MvPolynomial.isWeightedHomogeneous_X
      ℂ (![L, 2] : Fin 2 → ℕ) (0 : Fin 2)
    have hy := MvPolynomial.isWeightedHomogeneous_X
      ℂ (![L, 2] : Fin 2 → ℕ) (1 : Fin 2)
    have hxTwo : (MvPolynomial.X (0 : Fin 2) ^ 2 :
        MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous ![L, 2]
          (2 * L) := by
      simpa [mul_comm] using hx.pow 2
    have hyL :
        (MvPolynomial.C T * MvPolynomial.X (1 : Fin 2) ^ L :
          MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous ![L, 2]
            (2 * L) := by
      simpa [mul_comm] using (hy.pow L).C_mul T
    simpa [residualWeightedInitialPolynomials,
      residualWeightedDegrees] using (hxTwo.add hyL).C_mul (-c)
  · have hbind :=
      OnLeConjecture.Analytic.MvPolynomial.IsWeightedHomogeneous.bind₁_scaled
        model.weightedHomogeneous
          (residualParameterPolynomialSubstitution L T)
            (residualParameterPolynomialSubstitution_isWeightedHomogeneous
              L T)
    simpa [residualWeightedInitialPolynomials, residualWeightedDegrees,
      mul_comm] using hbind

/-- Evaluation of a polynomial map commutes with radial substitution of
source weights `(L, 2)`. -/
theorem weightedPolynomialMap_residualWeightedRadialSource
    (L : ℕ) (degrees : Fin 3 → ℕ)
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous ![L, 2] (degrees i))
    (lambda : ℂ) (z : ℂ × ℂ) (i : Fin 3) :
    weightedPolynomialMap P (residualWeightedRadialSource L lambda z) i =
      lambda ^ degrees i * weightedPolynomialMap P z i := by
  have hcoordinates :
      (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
          (residualWeightedRadialSource L lambda z) =
        fun j : Fin 2 ↦ lambda ^ (![L, 2] j) *
          ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z) j := by
    ext j
    fin_cases j <;> simp [residualWeightedRadialSource]
  rw [weightedPolynomialMap, hcoordinates]
  exact eval_weighted_smul_of_isWeightedHomogeneous
    (hP i) lambda ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z)

/-- Analytic coefficient representatives for membership in a finite two
weight order ideal. -/
theorem exists_twoWeightOrderCoefficientRepresentatives
    (L D : ℕ) (P : MvPolynomial (Fin 2) ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (i : Fin 3)
    (htail : pairRepresentativeComponentGerm representative
        hrepresentative i - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.twoWeightOrderIdeal L 2 D) :
    ∃ q : Germ.TwoWeightOrderIndex L 2 D → Source 2 → ℂ,
      (∀ k, AnalyticAt ℂ (q k) 0) ∧
      ∀ᶠ z in nhds 0,
        representative (ContinuousLinearEquiv.finTwoArrow ℂ ℂ z) i =
          MvPolynomial.eval z P +
            ∑ k, q k z * z 0 ^ (k.1.1 : ℕ) *
              z 1 ^ (k.1.2 : ℕ) := by
  obtain ⟨c, hc⟩ :=
    (Germ.mem_twoWeightOrderIdeal_iff L 2 D _).mp htail
  have hcrep : ∀ k, ∃ Q : Source 2 → ℂ,
      ∃ hQ : AnalyticAt ℂ Q 0, c k = Germ.ofFunction Q hQ :=
    fun k ↦ Germ.exists_ofFunction (c k)
  choose q hq hcq using hcrep
  refine ⟨q, hq, ?_⟩
  have hcoefficientEquality :
      (fun z : Source 2 ↦
        ∑ k, q k z * z 0 ^ (k.1.1 : ℕ) *
          z 1 ^ (k.1.2 : ℕ)) =ᶠ[nhds 0]
      (fun z ↦
        representative (ContinuousLinearEquiv.finTwoArrow ℂ ℂ z) i -
          MvPolynomial.eval z P) := by
    have hsubtype := congrArg (analyticGermSubring 2).subtype hc
    simp only [map_sum, map_mul, map_pow, map_sub,
      Germ.twoWeightOrderGenerator] at hsubtype
    simp only [hcq, Germ.coordinatePolynomialAlgHom_eq_ofFunction,
      pairRepresentativeComponentGerm] at hsubtype
    have hleft :
        ((fun z : Source 2 ↦
          ∑ k, q k z * z 0 ^ (k.1.1 : ℕ) *
            z 1 ^ (k.1.2 : ℕ)) : FunctionGerm 2) =
          ∑ k,
            (((fun z : Source 2 ↦ q k z) : FunctionGerm 2) *
              (((fun z : Source 2 ↦ z 0) : FunctionGerm 2) ^
                  (k.1.1 : ℕ) *
                ((fun z : Source 2 ↦ z 1) : FunctionGerm 2) ^
                  (k.1.2 : ℕ))) := by
      calc
        ((fun z : Source 2 ↦
          ∑ k, q k z * z 0 ^ (k.1.1 : ℕ) *
            z 1 ^ (k.1.2 : ℕ)) : FunctionGerm 2) =
            (Filter.Germ.coeRingHom (nhds 0))
              (∑ k, fun z : Source 2 ↦
                q k z * z 0 ^ (k.1.1 : ℕ) *
                  z 1 ^ (k.1.2 : ℕ)) := by
              congr 1
              funext z
              simp
        _ = _ := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro k _
          change
            ((fun z : Source 2 ↦
              q k z * z 0 ^ (k.1.1 : ℕ) *
                z 1 ^ (k.1.2 : ℕ)) : FunctionGerm 2) =
              ((fun z : Source 2 ↦
                q k z * (z 0 ^ (k.1.1 : ℕ) *
                  z 1 ^ (k.1.2 : ℕ))) : FunctionGerm 2)
          apply Filter.Germ.coe_eq.mpr
          exact Eventually.of_forall fun z ↦ by ring
    have hright :
        ((fun z : Source 2 ↦
          representative (ContinuousLinearEquiv.finTwoArrow ℂ ℂ z) i -
            MvPolynomial.eval z P) : FunctionGerm 2) =
          ((fun z : Source 2 ↦
            representative (ContinuousLinearEquiv.finTwoArrow ℂ ℂ z) i) :
              FunctionGerm 2) -
            ((fun z : Source 2 ↦ MvPolynomial.eval z P) :
              FunctionGerm 2) :=
      rfl
    apply Filter.Germ.coe_eq.mp
    exact hleft.trans (hsubtype.trans hright.symm)
  filter_upwards [hcoefficientEquality] with z hz
  rw [hz]
  ring

/-- The source vector obtained from radial substitution with weights
`(L, 2)`. -/
@[expose]
noncomputable def residualWeightedRadialSourceVector
    (L : ℕ) (s : ℂ × (ℂ × ℂ)) : Source 2 :=
  (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
    (residualWeightedRadialSource L s.1 s.2)

@[simp]
theorem residualWeightedRadialSourceVector_zero
    (L : ℕ) (hL : 0 < L) (z : ℂ × ℂ) :
    residualWeightedRadialSourceVector L (0, z) = 0 := by
  simp [residualWeightedRadialSourceVector,
    residualWeightedRadialSource, zero_pow hL.ne']

theorem analyticAt_residualWeightedRadialSourceVector
    (L : ℕ) (z : ℂ × ℂ) :
    AnalyticAt ℂ (residualWeightedRadialSourceVector L) (0, z) := by
  have hzFirst : AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦ s.2.1) (0, z) :=
    analyticAt_fst.fun_comp analyticAt_snd
  have hzSecond : AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦ s.2.2) (0, z) :=
    analyticAt_snd.fun_comp analyticAt_snd
  have hsource : AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦
        residualWeightedRadialSource L s.1 s.2) (0, z) := by
    change AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦
        (s.1 ^ L * s.2.1, s.1 ^ 2 * s.2.2)) (0, z)
    exact ((analyticAt_fst.pow L).mul hzFirst).prod
      ((analyticAt_fst.pow 2).mul hzSecond)
  have hinverse : AnalyticAt ℂ
      ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm :
        ℂ × ℂ → Source 2)
      (residualWeightedRadialSource L (0 : ℂ) z) :=
    (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm.analyticAt _
  change AnalyticAt ℂ
    (fun s : ℂ × (ℂ × ℂ) ↦
      (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
        (residualWeightedRadialSource L s.1 s.2)) (0, z)
  exact AnalyticAt.fun_comp (x := (0, z)) hinverse hsource

/-- The analytic remainder obtained from a finite two weight ideal
decomposition in each target coordinate. -/
@[expose]
noncomputable def residualWeightedOrderRemainder
    (L : ℕ) (degrees : Fin 3 → ℕ)
    (q : (i : Fin 3) →
      Germ.TwoWeightOrderIndex L 2 (degrees i + 1) → Source 2 → ℂ)
    (s : ℂ × (ℂ × ℂ)) : Fin 3 → ℂ :=
  fun i ↦ ∑ k,
    s.1 ^ Germ.twoWeightOrderExcess L 2 (degrees i + 1) k *
      q i k (residualWeightedRadialSourceVector L s) *
        s.2.1 ^ (k.1.1 : ℕ) * s.2.2 ^ (k.1.2 : ℕ)

theorem analyticAt_residualWeightedOrderRemainder
    (L : ℕ) (hL : 0 < L) (degrees : Fin 3 → ℕ)
    (q : (i : Fin 3) →
      Germ.TwoWeightOrderIndex L 2 (degrees i + 1) → Source 2 → ℂ)
    (hq : ∀ i k, AnalyticAt ℂ (q i k) 0)
    (z : ℂ × ℂ) :
    AnalyticAt ℂ (residualWeightedOrderRemainder L degrees q) (0, z) := by
  rw [analyticAt_pi_iff]
  intro i
  change AnalyticAt ℂ
    (fun s : ℂ × (ℂ × ℂ) ↦ ∑ k,
      s.1 ^ Germ.twoWeightOrderExcess L 2 (degrees i + 1) k *
        q i k (residualWeightedRadialSourceVector L s) *
          s.2.1 ^ (k.1.1 : ℕ) * s.2.2 ^ (k.1.2 : ℕ)) (0, z)
  have hsource := analyticAt_residualWeightedRadialSourceVector L z
  have hzFirst : AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦ s.2.1) (0, z) :=
    analyticAt_fst.fun_comp analyticAt_snd
  have hzSecond : AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦ s.2.2) (0, z) :=
    analyticAt_snd.fun_comp analyticAt_snd
  have hterm : ∀ k : Germ.TwoWeightOrderIndex L 2 (degrees i + 1),
      AnalyticAt ℂ
        (fun s : ℂ × (ℂ × ℂ) ↦
          s.1 ^ Germ.twoWeightOrderExcess L 2 (degrees i + 1) k *
            q i k (residualWeightedRadialSourceVector L s) *
              s.2.1 ^ (k.1.1 : ℕ) *
                s.2.2 ^ (k.1.2 : ℕ)) (0, z) := by
    intro k
    have hcoefficientAt : AnalyticAt ℂ (q i k)
        (residualWeightedRadialSourceVector L (0, z)) := by
      rw [residualWeightedRadialSourceVector_zero L hL z]
      exact hq i k
    have hcoefficient : AnalyticAt ℂ
        (fun s : ℂ × (ℂ × ℂ) ↦
          q i k (residualWeightedRadialSourceVector L s)) (0, z) :=
      hcoefficientAt.fun_comp hsource
    exact (((analyticAt_fst.pow
      (Germ.twoWeightOrderExcess L 2 (degrees i + 1) k)).mul
        hcoefficient).mul (hzFirst.pow (k.1.1 : ℕ))).mul
          (hzSecond.pow (k.1.2 : ℕ))
  have hsum := Finset.analyticAt_sum Finset.univ (fun k _ ↦ hterm k)
  convert hsum using 1
  funext s
  simp

/-- A finite two weight coefficient decomposition yields the exact residual
radial expansion. -/
theorem residualWeightedRadialExpansion_of_coefficientEquality
    (L : ℕ) (degrees : Fin 3 → ℕ)
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous ![L, 2] (degrees i))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (q : (i : Fin 3) →
      Germ.TwoWeightOrderIndex L 2 (degrees i + 1) → Source 2 → ℂ)
    (lambda : ℂ) (z : ℂ × ℂ) (i : Fin 3)
    (hcoefficient :
      representative
          (ContinuousLinearEquiv.finTwoArrow ℂ ℂ
            (residualWeightedRadialSourceVector L (lambda, z))) i =
        MvPolynomial.eval
            (residualWeightedRadialSourceVector L (lambda, z)) (P i) +
          ∑ k,
            q i k (residualWeightedRadialSourceVector L (lambda, z)) *
              (residualWeightedRadialSourceVector L (lambda, z)) 0 ^
                (k.1.1 : ℕ) *
              (residualWeightedRadialSourceVector L (lambda, z)) 1 ^
                (k.1.2 : ℕ)) :
    representative (residualWeightedRadialSource L lambda z) i =
      lambda ^ degrees i *
        (weightedPolynomialMap P z i +
          lambda * residualWeightedOrderRemainder L degrees q
            (lambda, z) i) := by
  have hcoefficient' :
      representative (residualWeightedRadialSource L lambda z) i =
        weightedPolynomialMap P
            (residualWeightedRadialSource L lambda z) i +
          ∑ k,
            q i k (residualWeightedRadialSourceVector L (lambda, z)) *
              (lambda ^ L * z.1) ^ (k.1.1 : ℕ) *
                (lambda ^ 2 * z.2) ^ (k.1.2 : ℕ) := by
    simpa [residualWeightedRadialSourceVector, weightedPolynomialMap,
      residualWeightedRadialSource] using hcoefficient
  rw [hcoefficient',
    weightedPolynomialMap_residualWeightedRadialSource L degrees P hP]
  have hterm
      (k : Germ.TwoWeightOrderIndex L 2 (degrees i + 1)) :
      q i k (residualWeightedRadialSourceVector L (lambda, z)) *
          (lambda ^ L * z.1) ^ (k.1.1 : ℕ) *
            (lambda ^ 2 * z.2) ^ (k.1.2 : ℕ) =
        q i k (residualWeightedRadialSourceVector L (lambda, z)) *
          (lambda ^ (degrees i + 1) *
            (lambda ^ Germ.twoWeightOrderExcess L 2
                (degrees i + 1) k *
              z.1 ^ (k.1.1 : ℕ) * z.2 ^ (k.1.2 : ℕ))) := by
    rw [mul_assoc,
      Germ.twoWeightOrderGenerator_radial_factor L 2 (degrees i + 1)]
  simp_rw [hterm]
  rw [residualWeightedOrderRemainder]
  have hsum :
      (∑ k,
        q i k (residualWeightedRadialSourceVector L (lambda, z)) *
          (lambda ^ (degrees i + 1) *
            (lambda ^ Germ.twoWeightOrderExcess L 2
                (degrees i + 1) k *
              z.1 ^ (k.1.1 : ℕ) * z.2 ^ (k.1.2 : ℕ)))) =
        lambda ^ (degrees i + 1) *
          ∑ k,
            lambda ^ Germ.twoWeightOrderExcess L 2
                (degrees i + 1) k *
              q i k (residualWeightedRadialSourceVector L (lambda, z)) *
                z.1 ^ (k.1.1 : ℕ) * z.2 ^ (k.1.2 : ℕ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum, pow_succ]
  ring

/-- Membership of all three tails in the finite `(L, 2)` order ideals
produces one radial remainder valid at every affine chart point. -/
theorem exists_hasResidualWeightedRadialExpansionAt_of_mem_twoWeightOrderIdeal
    (L : ℕ) (hL : 0 < L) (degrees : Fin 3 → ℕ)
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous ![L, 2] (degrees i))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hrepresentative i -
          Germ.coordinatePolynomialAlgHom 2 (P i) ∈
        Germ.twoWeightOrderIdeal L 2 (degrees i + 1)) :
    ∃ remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ,
      ∀ z : ℂ × ℂ,
        HasResidualWeightedRadialExpansionAt L degrees
          (weightedPolynomialMap P) representative remainder z := by
  have hextract : ∀ i : Fin 3,
      ∃ q : Germ.TwoWeightOrderIndex L 2 (degrees i + 1) →
          Source 2 → ℂ,
        (∀ k, AnalyticAt ℂ (q k) 0) ∧
        ∀ᶠ u in nhds 0,
          representative (ContinuousLinearEquiv.finTwoArrow ℂ ℂ u) i =
            MvPolynomial.eval u (P i) +
              ∑ k, q k u * u 0 ^ (k.1.1 : ℕ) *
                u 1 ^ (k.1.2 : ℕ) := by
    intro i
    exact exists_twoWeightOrderCoefficientRepresentatives
      L (degrees i + 1) (P i) representative hrepresentative i (htail i)
  choose q hq using hextract
  refine ⟨residualWeightedOrderRemainder L degrees q, ?_⟩
  intro z
  refine
    { remainder_analyticAt :=
        analyticAt_residualWeightedOrderRemainder L hL degrees q
          (fun i k ↦ (hq i).1 k) z
      expansion := ?_ }
  apply Filter.eventually_all.mpr
  intro i
  have htendsto : Tendsto (residualWeightedRadialSourceVector L)
      (nhds (0, z)) (nhds 0) := by
    have hcontinuous :=
      (analyticAt_residualWeightedRadialSourceVector L z).continuousAt.tendsto
    simpa [residualWeightedRadialSourceVector_zero L hL z] using hcontinuous
  have heventual := htendsto.eventually ((hq i).2)
  filter_upwards [heventual] with s hs
  exact residualWeightedRadialExpansion_of_coefficientEquality
    L degrees P hP representative q s.1 s.2 i hs

/-- Finite `(L, 2)` order tails and the residual collision exclude an
injective representative of the pointed map germ. -/
theorem residualWeightedOrderTails_not_hasInjectiveRepresentative
    {k L N : ℕ} {c T : ℂ} {Psi : PreparedOddFamily N}
    (model : Psi.BivariateModel)
    (certificate : InitialCollisionCertificate k L N c T Psi)
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous ![L, 2]
      (residualWeightedDegrees k L N i))
    (hmap : weightedPolynomialMap P =
      residualWeightedInitialMap k L N c T Psi)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hrepresentative i -
          Germ.coordinatePolynomialAlgHom 2 (P i) ∈
        Germ.twoWeightOrderIdeal L 2
          (residualWeightedDegrees k L N i + 1))
    (hL : 0 < L) :
    ¬ (PointedMapGerm.ofPairFunction representative
      hrepresentative hzero).HasInjectiveRepresentative := by
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasResidualWeightedRadialExpansionAt_of_mem_twoWeightOrderIdeal
      L hL (residualWeightedDegrees k L N) P hP representative
        hrepresentative htail
  have hfirst := hexpansion (certificate.x, 1)
  have hsecond := hexpansion (-certificate.x, certificate.eta)
  rw [hmap] at hfirst hsecond
  exact residualWeightedCollision_not_hasInjectiveRepresentative
    model certificate representative remainder hrepresentative hzero
      hfirst hsecond hL

/-- Membership of the tails relative to the canonical polynomial model
gives the terminal noninjectivity conclusion. -/
theorem residualWeightedModelOrderTails_not_hasInjectiveRepresentative
    {k L N : ℕ} {c T : ℂ} {Psi : PreparedOddFamily N}
    (model : Psi.BivariateModel)
    (certificate : InitialCollisionCertificate k L N c T Psi)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hrepresentative i -
          Germ.coordinatePolynomialAlgHom 2
            (residualWeightedInitialPolynomials k L c T Psi model i) ∈
        Germ.twoWeightOrderIdeal L 2
          (residualWeightedDegrees k L N i + 1))
    (hL : 0 < L) :
    ¬ (PointedMapGerm.ofPairFunction representative
      hrepresentative hzero).HasInjectiveRepresentative := by
  exact residualWeightedOrderTails_not_hasInjectiveRepresentative
    model certificate
      (residualWeightedInitialPolynomials k L c T Psi model)
      (residualWeightedInitialPolynomials_isWeightedHomogeneous
        k L c T Psi model)
      (weightedPolynomialMap_residualWeightedInitialPolynomials
        k L c T Psi model)
      representative hrepresentative hzero htail hL

end OnLeConjecture.DTwo
