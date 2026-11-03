/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PolynomialCoordinates
public import OnLeConjecture.Analytic.WeightedMonomialDivision
public import OnLeConjecture.DThree.WeightedResidueRescaling

/-!
# Weighted radial expansion from a finite monomial ideal

Membership in the finite weighted order ideal supplies analytic coefficient
functions. After weighted radial substitution, their finite sum defines one
analytic remainder over every point of the affine chart.
-/

public section

namespace OnLeConjecture.DThree

open Filter
open scoped Topology
open OnLeConjecture.Analytic

/-- The analytic germ of one component of a representative written on the
two coordinate function space. -/
@[expose]
noncomputable def pairRepresentativeComponentGerm
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (i : Fin 3) : Germ 2 :=
  Germ.ofFunction
    (fun z : Source 2 ↦
      representative (ContinuousLinearEquiv.finTwoArrow ℂ ℂ z) i)
    (by
      have hcomponent : AnalyticAt ℂ
          (fun z : ℂ × ℂ ↦ representative z i) 0 :=
        analyticAt_pi_iff.mp hrepresentative i
      have hcomponent' : AnalyticAt ℂ
          (fun z : ℂ × ℂ ↦ representative z i)
            (ContinuousLinearEquiv.finTwoArrow ℂ ℂ (0 : Source 2)) := by
        have hzero :
            ContinuousLinearEquiv.finTwoArrow ℂ ℂ (0 : Source 2) =
              (0 : ℂ × ℂ) := by
          simp
        rw [hzero]
        exact hcomponent
      exact hcomponent'.fun_comp
        ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).analyticAt 0))

/-- Evaluation of three polynomials after identifying the two coordinate
function space with a product. -/
@[expose]
noncomputable def weightedPolynomialMap
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ) :
    ℂ × ℂ → Fin 3 → ℂ :=
  fun z i ↦ MvPolynomial.eval
    ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z) (P i)

/-- Evaluation of a weighted homogeneous polynomial commutes with weighted
scalar multiplication. -/
theorem eval_weighted_smul_of_isWeightedHomogeneous
    {P : MvPolynomial (Fin 2) ℂ} {w : Fin 2 → ℕ} {D : ℕ}
    (hP : P.IsWeightedHomogeneous w D) (lambda : ℂ) (z : Fin 2 → ℂ) :
    MvPolynomial.eval (fun i ↦ lambda ^ w i * z i) P =
      lambda ^ D * MvPolynomial.eval z P := by
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      simp only [MvPolynomial.eval_add, ihp, ihq, mul_add]
  | monomial d c hd =>
      rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      rw [Finsupp.prod_pow, Finsupp.prod_pow]
      simp_rw [mul_pow, ← pow_mul]
      rw [Finset.prod_mul_distrib]
      rw [Finset.prod_pow_eq_pow_sum]
      have hsum : ∑ i, w i * d i = D := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hd
      rw [hsum]
      ring

/-- The polynomial map has the prescribed weighted homogeneity. -/
theorem weightedPolynomialMap_weightedRadialSource
    (a : ℕ) (degrees : Fin 3 → ℕ)
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous ![a, 1] (degrees i))
    (lambda : ℂ) (z : ℂ × ℂ) (i : Fin 3) :
    weightedPolynomialMap P (weightedRadialSource a lambda z) i =
      lambda ^ degrees i * weightedPolynomialMap P z i := by
  have hcoordinates :
      (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
          (weightedRadialSource a lambda z) =
        fun j : Fin 2 ↦ lambda ^ (![a, 1] j) *
          ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z) j := by
    ext j
    fin_cases j
    · simp [weightedRadialSource]
    · simp [weightedRadialSource]
  rw [weightedPolynomialMap, hcoordinates]
  exact eval_weighted_smul_of_isWeightedHomogeneous
    (hP i) lambda ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z)

/-- The excess of the weight of a monomial ideal generator above its
threshold. -/
noncomputable def weightedOrderExcess
    (a D : ℕ) (k : Fin (D + 1)) : ℕ :=
  a * (k : ℕ) + (D - a * (k : ℕ)) - D

theorem weightedOrderThreshold_le_weight
    (a D : ℕ) (k : Fin (D + 1)) :
    D ≤ a * (k : ℕ) + (D - a * (k : ℕ)) := by
  omega

theorem weightedOrderWeight_eq_threshold_add_excess
    (a D : ℕ) (k : Fin (D + 1)) :
    a * (k : ℕ) + (D - a * (k : ℕ)) =
      D + weightedOrderExcess a D k := by
  rw [weightedOrderExcess]
  omega

/-- Every generator of the weighted order ideal has the required radial
factor. -/
theorem weightedOrderGenerator_radial_factor
    (a D : ℕ) (k : Fin (D + 1))
    (lambda x y : ℂ) :
    (lambda ^ a * x) ^ (k : ℕ) *
        (lambda * y) ^ (D - a * (k : ℕ)) =
      lambda ^ D *
        (lambda ^ weightedOrderExcess a D k *
          x ^ (k : ℕ) * y ^ (D - a * (k : ℕ))) := by
  calc
    (lambda ^ a * x) ^ (k : ℕ) *
        (lambda * y) ^ (D - a * (k : ℕ)) =
      (lambda ^ (a * (k : ℕ)) *
        lambda ^ (D - a * (k : ℕ))) *
          (x ^ (k : ℕ) * y ^ (D - a * (k : ℕ))) := by
            rw [mul_pow, mul_pow, ← pow_mul]
            ring
    _ = lambda ^ (a * (k : ℕ) + (D - a * (k : ℕ))) *
          (x ^ (k : ℕ) * y ^ (D - a * (k : ℕ))) := by
            rw [pow_add]
    _ = lambda ^ (D + weightedOrderExcess a D k) *
          (x ^ (k : ℕ) * y ^ (D - a * (k : ℕ))) := by
            rw [weightedOrderWeight_eq_threshold_add_excess]
    _ = lambda ^ D *
        (lambda ^ weightedOrderExcess a D k *
          x ^ (k : ℕ) * y ^ (D - a * (k : ℕ))) := by
            rw [pow_add]
            ring

/-- Coefficients in a weighted order ideal have simultaneous analytic
function representatives. -/
theorem exists_weightedOrderCoefficientRepresentatives
    (a D : ℕ) (P : MvPolynomial (Fin 2) ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (i : Fin 3)
    (htail : pairRepresentativeComponentGerm representative
        hrepresentative i - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a D) :
    ∃ q : Fin (D + 1) → Source 2 → ℂ,
      (∀ k, AnalyticAt ℂ (q k) 0) ∧
      ∀ᶠ z in nhds 0,
        representative (ContinuousLinearEquiv.finTwoArrow ℂ ℂ z) i =
          MvPolynomial.eval z P +
            ∑ k, q k z * z 0 ^ (k : ℕ) *
              z 1 ^ (D - a * (k : ℕ)) := by
  obtain ⟨c, hc⟩ :=
    (Germ.mem_weightedOrderIdeal_iff a D _).mp htail
  have hcrep : ∀ k, ∃ Q : Source 2 → ℂ,
      ∃ hQ : AnalyticAt ℂ Q 0, c k = Germ.ofFunction Q hQ :=
    fun k ↦ Germ.exists_ofFunction (c k)
  choose q hq hcq using hcrep
  refine ⟨q, hq, ?_⟩
  have hcoefficientEquality :
      (fun z : Source 2 ↦
        ∑ k, q k z * z 0 ^ (k : ℕ) *
          z 1 ^ (D - a * (k : ℕ))) =ᶠ[nhds 0]
      (fun z ↦
        representative (ContinuousLinearEquiv.finTwoArrow ℂ ℂ z) i -
          MvPolynomial.eval z P) := by
    have hsubtype := congrArg (analyticGermSubring 2).subtype hc
    simp only [map_sum, map_mul, map_pow, map_sub,
      Germ.weightedOrderGenerator] at hsubtype
    simp only [hcq, Germ.coordinatePolynomialAlgHom_eq_ofFunction,
      pairRepresentativeComponentGerm] at hsubtype
    have hleft :
        ((fun z : Source 2 ↦
          ∑ k, q k z * z 0 ^ (k : ℕ) *
            z 1 ^ (D - a * (k : ℕ))) : FunctionGerm 2) =
          ∑ k,
            (((fun z : Source 2 ↦ q k z) : FunctionGerm 2) *
              (((fun z : Source 2 ↦ z 0) : FunctionGerm 2) ^ (k : ℕ) *
                ((fun z : Source 2 ↦ z 1) : FunctionGerm 2) ^
                  (D - a * (k : ℕ)))) := by
      calc
        ((fun z : Source 2 ↦
          ∑ k, q k z * z 0 ^ (k : ℕ) *
            z 1 ^ (D - a * (k : ℕ))) : FunctionGerm 2) =
            (Filter.Germ.coeRingHom (nhds 0))
              (∑ k, fun z : Source 2 ↦
                q k z * z 0 ^ (k : ℕ) *
                  z 1 ^ (D - a * (k : ℕ))) := by
              congr 1
              funext z
              simp
        _ = _ := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro k _
          change
            ((fun z : Source 2 ↦
              q k z * z 0 ^ (k : ℕ) *
                z 1 ^ (D - a * (k : ℕ))) : FunctionGerm 2) =
              ((fun z : Source 2 ↦
                q k z * (z 0 ^ (k : ℕ) *
                  z 1 ^ (D - a * (k : ℕ)))) : FunctionGerm 2)
          apply Filter.Germ.coe_eq.mpr
          exact Eventually.of_forall fun z ↦ by ring
    have hright :
        ((fun z : Source 2 ↦
          representative (ContinuousLinearEquiv.finTwoArrow ℂ ℂ z) i -
            MvPolynomial.eval z P) : FunctionGerm 2) =
          ((fun z : Source 2 ↦
            representative (ContinuousLinearEquiv.finTwoArrow ℂ ℂ z) i) :
              FunctionGerm 2) -
            ((fun z : Source 2 ↦ MvPolynomial.eval z P) : FunctionGerm 2) :=
      rfl
    apply Filter.Germ.coe_eq.mp
    exact hleft.trans (hsubtype.trans hright.symm)
  filter_upwards [hcoefficientEquality] with z hz
  rw [hz]
  ring

/-- The source vector after weighted radial substitution. -/
@[expose]
noncomputable def weightedRadialSourceVector
    (a : ℕ) (s : ℂ × (ℂ × ℂ)) : Source 2 :=
  (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
    (weightedRadialSource a s.1 s.2)

@[simp]
theorem weightedRadialSourceVector_zero
    (a : ℕ) (ha : 0 < a) (z : ℂ × ℂ) :
    weightedRadialSourceVector a (0, z) = 0 := by
  simp [weightedRadialSourceVector, weightedRadialSource,
    zero_pow ha.ne']

theorem analyticAt_weightedRadialSourceVector
    (a : ℕ) (z : ℂ × ℂ) :
    AnalyticAt ℂ (weightedRadialSourceVector a) (0, z) := by
  have hzFirst : AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦ s.2.1) (0, z) :=
    analyticAt_fst.fun_comp analyticAt_snd
  have hzSecond : AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦ s.2.2) (0, z) :=
    analyticAt_snd.fun_comp analyticAt_snd
  have hsource : AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦
        weightedRadialSource a s.1 s.2) (0, z) := by
    change AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦
        (s.1 ^ a * s.2.1, s.1 * s.2.2)) (0, z)
    exact ((analyticAt_fst.pow a).mul hzFirst).prod
      (analyticAt_fst.mul hzSecond)
  have hinverse : AnalyticAt ℂ
      ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm :
        ℂ × ℂ → Source 2)
      (weightedRadialSource a (0 : ℂ) z) :=
    (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm.analyticAt _
  change AnalyticAt ℂ
    (fun s : ℂ × (ℂ × ℂ) ↦
      (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
        (weightedRadialSource a s.1 s.2)) (0, z)
  exact AnalyticAt.fun_comp (x := (0, z)) hinverse hsource

/-- The analytic remainder obtained from coefficient representatives of the
three weighted order ideals. -/
@[expose]
noncomputable def weightedOrderRemainder
    (a : ℕ) (degrees : Fin 3 → ℕ)
    (q : (i : Fin 3) → Fin (degrees i + 1 + 1) → Source 2 → ℂ)
    (s : ℂ × (ℂ × ℂ)) : Fin 3 → ℂ :=
  fun i ↦ ∑ k,
    s.1 ^ weightedOrderExcess a (degrees i + 1) k *
      q i k (weightedRadialSourceVector a s) *
        s.2.1 ^ (k : ℕ) *
          s.2.2 ^ (degrees i + 1 - a * (k : ℕ))

theorem analyticAt_weightedOrderRemainder
    (a : ℕ) (ha : 0 < a) (degrees : Fin 3 → ℕ)
    (q : (i : Fin 3) → Fin (degrees i + 1 + 1) → Source 2 → ℂ)
    (hq : ∀ i k, AnalyticAt ℂ (q i k) 0)
    (z : ℂ × ℂ) :
    AnalyticAt ℂ (weightedOrderRemainder a degrees q) (0, z) := by
  rw [analyticAt_pi_iff]
  intro i
  change AnalyticAt ℂ
    (fun s : ℂ × (ℂ × ℂ) ↦ ∑ k,
      s.1 ^ weightedOrderExcess a (degrees i + 1) k *
        q i k (weightedRadialSourceVector a s) *
          s.2.1 ^ (k : ℕ) *
            s.2.2 ^ (degrees i + 1 - a * (k : ℕ))) (0, z)
  have hterm : ∀ k : Fin (degrees i + 1 + 1),
      AnalyticAt ℂ
        (fun s : ℂ × (ℂ × ℂ) ↦
          s.1 ^ weightedOrderExcess a (degrees i + 1) k *
            q i k (weightedRadialSourceVector a s) *
              s.2.1 ^ (k : ℕ) *
                s.2.2 ^ (degrees i + 1 - a * (k : ℕ))) (0, z) := by
    intro k
    have hcoefficientAt : AnalyticAt ℂ (q i k)
        (weightedRadialSourceVector a (0, z)) := by
      rw [weightedRadialSourceVector_zero a ha z]
      exact hq i k
    have hcoefficient : AnalyticAt ℂ
        (fun s : ℂ × (ℂ × ℂ) ↦
          q i k (weightedRadialSourceVector a s)) (0, z) :=
      hcoefficientAt.fun_comp (analyticAt_weightedRadialSourceVector a z)
    have hzFirst : AnalyticAt ℂ
        (fun s : ℂ × (ℂ × ℂ) ↦ s.2.1) (0, z) :=
      analyticAt_fst.fun_comp analyticAt_snd
    have hzSecond : AnalyticAt ℂ
        (fun s : ℂ × (ℂ × ℂ) ↦ s.2.2) (0, z) :=
      analyticAt_snd.fun_comp analyticAt_snd
    exact (((analyticAt_fst.pow
        (weightedOrderExcess a (degrees i + 1) k)).mul hcoefficient).mul
          (hzFirst.pow (k : ℕ))).mul
            (hzSecond.pow (degrees i + 1 - a * (k : ℕ)))
  have hsum := Finset.analyticAt_sum Finset.univ
    (fun k _ ↦ hterm k)
  convert hsum using 1
  funext s
  simp

/-- A coefficient decomposition in the weighted order ideal gives the exact
radial expansion identity. -/
theorem weightedRadialExpansion_of_coefficientEquality
    (a : ℕ) (degrees : Fin 3 → ℕ)
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous ![a, 1] (degrees i))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (q : (i : Fin 3) → Fin (degrees i + 1 + 1) → Source 2 → ℂ)
    (lambda : ℂ) (z : ℂ × ℂ) (i : Fin 3)
    (hcoefficient :
      representative
          (ContinuousLinearEquiv.finTwoArrow ℂ ℂ
            (weightedRadialSourceVector a (lambda, z))) i =
        MvPolynomial.eval (weightedRadialSourceVector a (lambda, z)) (P i) +
          ∑ k, q i k (weightedRadialSourceVector a (lambda, z)) *
            (weightedRadialSourceVector a (lambda, z)) 0 ^ (k : ℕ) *
              (weightedRadialSourceVector a (lambda, z)) 1 ^
                (degrees i + 1 - a * (k : ℕ))) :
    representative (weightedRadialSource a lambda z) i =
      lambda ^ degrees i *
        (weightedPolynomialMap P z i +
          lambda * weightedOrderRemainder a degrees q (lambda, z) i) := by
  have hcoefficient' :
      representative (weightedRadialSource a lambda z) i =
        weightedPolynomialMap P (weightedRadialSource a lambda z) i +
          ∑ k, q i k (weightedRadialSourceVector a (lambda, z)) *
            (lambda ^ a * z.1) ^ (k : ℕ) *
              (lambda * z.2) ^ (degrees i + 1 - a * (k : ℕ)) := by
    simpa [weightedRadialSourceVector, weightedPolynomialMap,
      weightedRadialSource] using hcoefficient
  rw [hcoefficient',
    weightedPolynomialMap_weightedRadialSource a degrees P hP]
  have hterm (k : Fin (degrees i + 1 + 1)) :
      q i k (weightedRadialSourceVector a (lambda, z)) *
          (lambda ^ a * z.1) ^ (k : ℕ) *
            (lambda * z.2) ^ (degrees i + 1 - a * (k : ℕ)) =
        q i k (weightedRadialSourceVector a (lambda, z)) *
          (lambda ^ (degrees i + 1) *
            (lambda ^ weightedOrderExcess a (degrees i + 1) k *
              z.1 ^ (k : ℕ) *
                z.2 ^ (degrees i + 1 - a * (k : ℕ)))) := by
    rw [mul_assoc,
      weightedOrderGenerator_radial_factor a (degrees i + 1)]
  simp_rw [hterm]
  rw [weightedOrderRemainder]
  have hsum :
      (∑ k, q i k (weightedRadialSourceVector a (lambda, z)) *
        (lambda ^ (degrees i + 1) *
          (lambda ^ weightedOrderExcess a (degrees i + 1) k *
            z.1 ^ (k : ℕ) *
              z.2 ^ (degrees i + 1 - a * (k : ℕ))))) =
      lambda ^ (degrees i + 1) *
        ∑ k,
          lambda ^ weightedOrderExcess a (degrees i + 1) k *
            q i k (weightedRadialSourceVector a (lambda, z)) *
              z.1 ^ (k : ℕ) *
                z.2 ^ (degrees i + 1 - a * (k : ℕ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum, pow_succ]
  ring

/-- Membership of the three correction germs in their weighted order ideals
produces one analytic radial remainder over every affine chart point. -/
theorem exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
    (a : ℕ) (ha : 0 < a) (degrees : Fin 3 → ℕ)
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous ![a, 1] (degrees i))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hrepresentative i -
          Germ.coordinatePolynomialAlgHom 2 (P i) ∈
        Germ.weightedOrderIdeal a (degrees i + 1)) :
    ∃ remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ,
      ∀ z : ℂ × ℂ,
        HasWeightedRadialExpansionAt a degrees
          (weightedPolynomialMap P) representative remainder z := by
  have hextract : ∀ i : Fin 3,
      ∃ q : Fin (degrees i + 1 + 1) → Source 2 → ℂ,
        (∀ k, AnalyticAt ℂ (q k) 0) ∧
        ∀ᶠ u in nhds 0,
          representative (ContinuousLinearEquiv.finTwoArrow ℂ ℂ u) i =
            MvPolynomial.eval u (P i) +
              ∑ k, q k u * u 0 ^ (k : ℕ) *
                u 1 ^ (degrees i + 1 - a * (k : ℕ)) := by
    intro i
    exact exists_weightedOrderCoefficientRepresentatives
      a (degrees i + 1) (P i) representative hrepresentative i (htail i)
  choose q hq using hextract
  refine ⟨weightedOrderRemainder a degrees q, ?_⟩
  intro z
  refine
    { remainder_analyticAt :=
        analyticAt_weightedOrderRemainder a ha degrees q
          (fun i k ↦ (hq i).1 k) z
      expansion := ?_ }
  apply Filter.eventually_all.mpr
  intro i
  have htendsto : Tendsto (weightedRadialSourceVector a)
      (nhds (0, z)) (nhds 0) := by
    have hcontinuous :=
      (analyticAt_weightedRadialSourceVector a z).continuousAt.tendsto
    simpa [weightedRadialSourceVector_zero a ha z] using hcontinuous
  have heventual := htendsto.eventually ((hq i).2)
  filter_upwards [heventual] with s hs
  exact weightedRadialExpansion_of_coefficientEquality
    a degrees P hP representative q s.1 s.2 i hs

end OnLeConjecture.DThree
