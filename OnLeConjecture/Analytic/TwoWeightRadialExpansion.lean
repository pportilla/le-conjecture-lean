/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TwoWeightMonomialIdeal
public import OnLeConjecture.DThree.WeightedOrderExpansion

/-!
# Analytic radial expansion for two arbitrary positive weights

Finite monomial ideal membership constructs a single analytic remainder
for weighted radial rescaling, valid near every affine chart point.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.DThree

/-- The weighted radial source substitution. -/
@[expose] noncomputable def twoWeightRadialSource
    (a b : ℕ) (lambda : ℂ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (lambda ^ a * z.1, lambda ^ b * z.2)

/-- A local expansion with a strict weighted remainder. -/
structure HasTwoWeightRadialExpansionAt
    (a b : ℕ) (degrees : Fin 3 → ℕ)
    (initialMap representative : ℂ × ℂ → Fin 3 → ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (z : ℂ × ℂ) : Prop where
  remainder_analyticAt : AnalyticAt ℂ remainder (0, z)
  expansion :
    ∀ᶠ s in nhds (0, z), ∀ i,
      representative (twoWeightRadialSource a b s.1 s.2) i =
        s.1 ^ degrees i * (initialMap s.2 i + s.1 * remainder s i)

/-- Evaluation of a polynomial map commutes with radial substitution of
source weights `(a, b)`. -/
theorem weightedPolynomialMap_twoWeightRadialSource
    (a b : ℕ) (degrees : Fin 3 → ℕ)
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous ![a, b] (degrees i))
    (lambda : ℂ) (z : ℂ × ℂ) (i : Fin 3) :
    weightedPolynomialMap P (twoWeightRadialSource a b lambda z) i =
      lambda ^ degrees i * weightedPolynomialMap P z i := by
  have hcoordinates :
      (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
          (twoWeightRadialSource a b lambda z) =
        fun j : Fin 2 ↦ lambda ^ (![a, b] j) *
          ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z) j := by
    ext j
    fin_cases j <;> simp [twoWeightRadialSource]
  rw [weightedPolynomialMap, hcoordinates]
  exact eval_weighted_smul_of_isWeightedHomogeneous
    (hP i) lambda ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm z)

/-- Analytic coefficient representatives for membership in a finite two
weight order ideal. -/
theorem exists_twoWeightOrderCoefficientRepresentatives
    (a b D : ℕ) (P : MvPolynomial (Fin 2) ℂ)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (i : Fin 3)
    (htail : pairRepresentativeComponentGerm representative
        hrepresentative i - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.twoWeightOrderIdeal a b D) :
    ∃ q : Germ.TwoWeightOrderIndex a b D → Source 2 → ℂ,
      (∀ k, AnalyticAt ℂ (q k) 0) ∧
      ∀ᶠ z in nhds 0,
        representative (ContinuousLinearEquiv.finTwoArrow ℂ ℂ z) i =
          MvPolynomial.eval z P +
            ∑ k, q k z * z 0 ^ (k.1.1 : ℕ) *
              z 1 ^ (k.1.2 : ℕ) := by
  obtain ⟨c, hc⟩ :=
    (Germ.mem_twoWeightOrderIdeal_iff a b D _).mp htail
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
`(a, b)`. -/
@[expose]
noncomputable def twoWeightRadialSourceVector
    (a b : ℕ) (s : ℂ × (ℂ × ℂ)) : Source 2 :=
  (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
    (twoWeightRadialSource a b s.1 s.2)

@[simp]
theorem twoWeightRadialSourceVector_zero
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (z : ℂ × ℂ) :
    twoWeightRadialSourceVector a b (0, z) = 0 := by
  simp [twoWeightRadialSourceVector,
    twoWeightRadialSource, zero_pow ha.ne', zero_pow hb.ne']

theorem analyticAt_twoWeightRadialSourceVector
    (a b : ℕ) (z : ℂ × ℂ) :
    AnalyticAt ℂ (twoWeightRadialSourceVector a b) (0, z) := by
  have hzFirst : AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦ s.2.1) (0, z) :=
    analyticAt_fst.fun_comp analyticAt_snd
  have hzSecond : AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦ s.2.2) (0, z) :=
    analyticAt_snd.fun_comp analyticAt_snd
  have hsource : AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦
        twoWeightRadialSource a b s.1 s.2) (0, z) := by
    change AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦
        (s.1 ^ a * s.2.1, s.1 ^ b * s.2.2)) (0, z)
    exact ((analyticAt_fst.pow a).mul hzFirst).prod
      ((analyticAt_fst.pow b).mul hzSecond)
  have hinverse : AnalyticAt ℂ
      ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm :
        ℂ × ℂ → Source 2)
      (twoWeightRadialSource a b (0 : ℂ) z) :=
    (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm.analyticAt _
  change AnalyticAt ℂ
    (fun s : ℂ × (ℂ × ℂ) ↦
      (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm
        (twoWeightRadialSource a b s.1 s.2)) (0, z)
  exact AnalyticAt.fun_comp (x := (0, z)) hinverse hsource

/-- The analytic remainder obtained from a finite two weight ideal
decomposition in each target coordinate. -/
@[expose]
noncomputable def twoWeightOrderRemainder
    (a b : ℕ) (degrees : Fin 3 → ℕ)
    (q : (i : Fin 3) →
      Germ.TwoWeightOrderIndex a b (degrees i + 1) → Source 2 → ℂ)
    (s : ℂ × (ℂ × ℂ)) : Fin 3 → ℂ :=
  fun i ↦ ∑ k,
    s.1 ^ Germ.twoWeightOrderExcess a b (degrees i + 1) k *
      q i k (twoWeightRadialSourceVector a b s) *
        s.2.1 ^ (k.1.1 : ℕ) * s.2.2 ^ (k.1.2 : ℕ)

theorem analyticAt_twoWeightOrderRemainder
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (degrees : Fin 3 → ℕ)
    (q : (i : Fin 3) →
      Germ.TwoWeightOrderIndex a b (degrees i + 1) → Source 2 → ℂ)
    (hq : ∀ i k, AnalyticAt ℂ (q i k) 0)
    (z : ℂ × ℂ) :
    AnalyticAt ℂ (twoWeightOrderRemainder a b degrees q) (0, z) := by
  rw [analyticAt_pi_iff]
  intro i
  change AnalyticAt ℂ
    (fun s : ℂ × (ℂ × ℂ) ↦ ∑ k,
      s.1 ^ Germ.twoWeightOrderExcess a b (degrees i + 1) k *
        q i k (twoWeightRadialSourceVector a b s) *
          s.2.1 ^ (k.1.1 : ℕ) * s.2.2 ^ (k.1.2 : ℕ)) (0, z)
  have hsource := analyticAt_twoWeightRadialSourceVector a b z
  have hzFirst : AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦ s.2.1) (0, z) :=
    analyticAt_fst.fun_comp analyticAt_snd
  have hzSecond : AnalyticAt ℂ
      (fun s : ℂ × (ℂ × ℂ) ↦ s.2.2) (0, z) :=
    analyticAt_snd.fun_comp analyticAt_snd
  have hterm : ∀ k : Germ.TwoWeightOrderIndex a b (degrees i + 1),
      AnalyticAt ℂ
        (fun s : ℂ × (ℂ × ℂ) ↦
          s.1 ^ Germ.twoWeightOrderExcess a b (degrees i + 1) k *
            q i k (twoWeightRadialSourceVector a b s) *
              s.2.1 ^ (k.1.1 : ℕ) *
                s.2.2 ^ (k.1.2 : ℕ)) (0, z) := by
    intro k
    have hcoefficientAt : AnalyticAt ℂ (q i k)
        (twoWeightRadialSourceVector a b (0, z)) := by
      rw [twoWeightRadialSourceVector_zero a b ha hb z]
      exact hq i k
    have hcoefficient : AnalyticAt ℂ
        (fun s : ℂ × (ℂ × ℂ) ↦
          q i k (twoWeightRadialSourceVector a b s)) (0, z) :=
      hcoefficientAt.fun_comp hsource
    exact (((analyticAt_fst.pow
      (Germ.twoWeightOrderExcess a b (degrees i + 1) k)).mul
        hcoefficient).mul (hzFirst.pow (k.1.1 : ℕ))).mul
          (hzSecond.pow (k.1.2 : ℕ))
  have hsum := Finset.analyticAt_sum Finset.univ (fun k _ ↦ hterm k)
  convert hsum using 1
  funext s
  simp

/-- A finite two weight coefficient decomposition yields the exact residual
radial expansion. -/
theorem twoWeightRadialExpansion_of_coefficientEquality
    (a b : ℕ) (degrees : Fin 3 → ℕ)
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous ![a, b] (degrees i))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (q : (i : Fin 3) →
      Germ.TwoWeightOrderIndex a b (degrees i + 1) → Source 2 → ℂ)
    (lambda : ℂ) (z : ℂ × ℂ) (i : Fin 3)
    (hcoefficient :
      representative
          (ContinuousLinearEquiv.finTwoArrow ℂ ℂ
            (twoWeightRadialSourceVector a b (lambda, z))) i =
        MvPolynomial.eval
            (twoWeightRadialSourceVector a b (lambda, z)) (P i) +
          ∑ k,
            q i k (twoWeightRadialSourceVector a b (lambda, z)) *
              (twoWeightRadialSourceVector a b (lambda, z)) 0 ^
                (k.1.1 : ℕ) *
              (twoWeightRadialSourceVector a b (lambda, z)) 1 ^
                (k.1.2 : ℕ)) :
    representative (twoWeightRadialSource a b lambda z) i =
      lambda ^ degrees i *
        (weightedPolynomialMap P z i +
          lambda * twoWeightOrderRemainder a b degrees q
            (lambda, z) i) := by
  have hcoefficient' :
      representative (twoWeightRadialSource a b lambda z) i =
        weightedPolynomialMap P
            (twoWeightRadialSource a b lambda z) i +
          ∑ k,
            q i k (twoWeightRadialSourceVector a b (lambda, z)) *
              (lambda ^ a * z.1) ^ (k.1.1 : ℕ) *
                (lambda ^ b * z.2) ^ (k.1.2 : ℕ) := by
    simpa [twoWeightRadialSourceVector, weightedPolynomialMap,
      twoWeightRadialSource] using hcoefficient
  rw [hcoefficient',
    weightedPolynomialMap_twoWeightRadialSource a b degrees P hP]
  have hterm
      (k : Germ.TwoWeightOrderIndex a b (degrees i + 1)) :
      q i k (twoWeightRadialSourceVector a b (lambda, z)) *
          (lambda ^ a * z.1) ^ (k.1.1 : ℕ) *
            (lambda ^ b * z.2) ^ (k.1.2 : ℕ) =
        q i k (twoWeightRadialSourceVector a b (lambda, z)) *
          (lambda ^ (degrees i + 1) *
            (lambda ^ Germ.twoWeightOrderExcess a b
                (degrees i + 1) k *
              z.1 ^ (k.1.1 : ℕ) * z.2 ^ (k.1.2 : ℕ))) := by
    rw [mul_assoc,
      Germ.twoWeightOrderGenerator_radial_factor a b (degrees i + 1)]
  simp_rw [hterm]
  rw [twoWeightOrderRemainder]
  have hsum :
      (∑ k,
        q i k (twoWeightRadialSourceVector a b (lambda, z)) *
          (lambda ^ (degrees i + 1) *
            (lambda ^ Germ.twoWeightOrderExcess a b
                (degrees i + 1) k *
              z.1 ^ (k.1.1 : ℕ) * z.2 ^ (k.1.2 : ℕ)))) =
        lambda ^ (degrees i + 1) *
          ∑ k,
            lambda ^ Germ.twoWeightOrderExcess a b
                (degrees i + 1) k *
              q i k (twoWeightRadialSourceVector a b (lambda, z)) *
                z.1 ^ (k.1.1 : ℕ) * z.2 ^ (k.1.2 : ℕ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum, pow_succ]
  ring

/-- Membership of all three tails in the finite `(a, b)` order ideals
produces one radial remainder valid at every affine chart point. -/
theorem exists_hasTwoWeightRadialExpansionAt_of_mem_twoWeightOrderIdeal
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (degrees : Fin 3 → ℕ)
    (P : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous ![a, b] (degrees i))
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hrepresentative i -
          Germ.coordinatePolynomialAlgHom 2 (P i) ∈
        Germ.twoWeightOrderIdeal a b (degrees i + 1)) :
    ∃ remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ,
      ∀ z : ℂ × ℂ,
        HasTwoWeightRadialExpansionAt a b degrees
          (weightedPolynomialMap P) representative remainder z := by
  have hextract : ∀ i : Fin 3,
      ∃ q : Germ.TwoWeightOrderIndex a b (degrees i + 1) →
          Source 2 → ℂ,
        (∀ k, AnalyticAt ℂ (q k) 0) ∧
        ∀ᶠ u in nhds 0,
          representative (ContinuousLinearEquiv.finTwoArrow ℂ ℂ u) i =
            MvPolynomial.eval u (P i) +
              ∑ k, q k u * u 0 ^ (k.1.1 : ℕ) *
                u 1 ^ (k.1.2 : ℕ) := by
    intro i
    exact exists_twoWeightOrderCoefficientRepresentatives
      a b (degrees i + 1) (P i) representative hrepresentative i (htail i)
  choose q hq using hextract
  refine ⟨twoWeightOrderRemainder a b degrees q, ?_⟩
  intro z
  refine
    { remainder_analyticAt :=
        analyticAt_twoWeightOrderRemainder a b ha hb degrees q
          (fun i k ↦ (hq i).1 k) z
      expansion := ?_ }
  apply Filter.eventually_all.mpr
  intro i
  have htendsto : Tendsto (twoWeightRadialSourceVector a b)
      (nhds (0, z)) (nhds 0) := by
    have hcontinuous :=
      (analyticAt_twoWeightRadialSourceVector a b z).continuousAt.tendsto
    simpa [twoWeightRadialSourceVector_zero a b ha hb z] using hcontinuous
  have heventual := htendsto.eventually ((hq i).2)
  filter_upwards [heventual] with s hs
  exact twoWeightRadialExpansion_of_coefficientEquality
    a b degrees P hP representative q s.1 s.2 i hs


end OnLeConjecture.Analytic

