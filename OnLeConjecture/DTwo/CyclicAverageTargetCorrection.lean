/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableCyclicAverageJet
public import OnLeConjecture.Analytic.TwoWeightPolynomialComposition
public import OnLeConjecture.Analytic.SecondCoordinateSubtraction

/-!
# The analytic target correction by the descended cyclic average

The divided difference used below is analytic: division by a coordinate
is applied before the substitution of its square. This supplies the
strict weighted remainder in the target correction.
-/

public section

open Filter
open scoped BigOperators
open OnLeConjecture.Analytic OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.DTwo

/-- The scalar germ `x^e+y^k`, with both exponents positive. -/
@[expose] noncomputable def cyclicPowerSumMap (e k : ℕ) (he : 0 < e) (hk : 0 < k) :
    PointedMapGerm 2 1 :=
  PointedMapGerm.ofFunction (fun z => fun _ => z 0 ^ e + z 1 ^ k)
    (by
      apply AnalyticAt.pi
      intro i
      exact (((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin 2 => ℂ) 0).analyticAt 0).pow e).add
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).analyticAt 0).pow k))
    (by funext i; simp [zero_pow he.ne', zero_pow hk.ne'])

@[simp] theorem cyclicPowerSumMap_pullback_coordinate
    (e k : ℕ) (he : 0 < e) (hk : 0 < k) :
    (cyclicPowerSumMap e k he hk).pullbackRingHom (coordinate (0 : Fin 1)) =
      coordinate (0 : Fin 2) ^ e + coordinate (1 : Fin 2) ^ k := by
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  simp only [cyclicPowerSumMap, PointedMapGerm.ofFunction, MapGerm.component_ofFunction]
  rfl

private theorem cyclicPowerSumMap_comp_hyperplane
    (e k : ℕ) (he : 0 < e) (hk : 0 < k) :
    (cyclicPowerSumMap e k he hk).comp (hyperplaneInclusionGerm 1) =
      oneVariablePowerMapGerm k hk := by
  simp only [cyclicPowerSumMap, hyperplaneInclusionGerm, oneVariablePowerMapGerm,
    PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by
    funext i
    change 0 ^ e + z 0 ^ k = z 0 ^ k
    simp [zero_pow he.ne']

private noncomputable def firstSquareMap : PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction (fun z => ![z 0 ^ 2, z 1])
    (by
      apply AnalyticAt.pi
      intro i
      fin_cases i
      · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt 0).pow 2
      · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).analyticAt 0)
    (by ext i; fin_cases i <;> simp)

private theorem firstSquareMap_coordinate :
    firstSquareMap.pullbackRingHom (coordinate (0 : Fin 2)) = coordinate (0 : Fin 2) ^ 2 := by
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  simp only [firstSquareMap, PointedMapGerm.ofFunction, MapGerm.component_ofFunction]
  rfl

private theorem firstSquareMap_extension (a : Germ 1) :
    firstSquareMap.pullbackRingHom (hyperplaneExtension 1 a) = hyperplaneExtension 1 a := by
  have hcomp : (hyperplaneTailGerm 1).comp firstSquareMap = hyperplaneTailGerm 1 := by
    simp only [hyperplaneTailGerm, firstSquareMap, PointedMapGerm.comp_ofFunction]
    apply Subtype.ext
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
  change (firstSquareMap.pullbackRingHom.comp (hyperplaneTailGerm 1).pullbackRingHom) a = _
  rw [← PointedMapGerm.pullbackRingHom_comp, hcomp]
  rfl

/-- The analytic difference `a(x²+y^k)-a(y^k)` is divisible by `x²`. -/
theorem cyclicPowerSum_divided_difference (k : ℕ) (hk : 0 < k) (a : Germ 1) :
    coordinate (0 : Fin 2) ^ 2 ∣
      (cyclicPowerSumMap 2 k (by omega) hk).pullbackRingHom a -
        hyperplaneExtension 1 ((oneVariablePowerMapGerm k hk).pullbackRingHom a) := by
  let F := (cyclicPowerSumMap 1 k (by omega) hk).pullbackRingHom a -
    hyperplaneExtension 1 ((oneVariablePowerMapGerm k hk).pullbackRingHom a)
  have hF : hyperplaneRestriction 1 F = 0 := by
    have hp : hyperplaneRestriction 1
        ((cyclicPowerSumMap 1 k (by omega) hk).pullbackRingHom a) =
        (oneVariablePowerMapGerm k hk).pullbackRingHom a := by
      change ((hyperplaneInclusionGerm 1).pullbackRingHom.comp
        (cyclicPowerSumMap 1 k (by omega) hk).pullbackRingHom) a = _
      rw [← PointedMapGerm.pullbackRingHom_comp, cyclicPowerSumMap_comp_hyperplane]
    simp only [F, map_sub, hp]
    have hres : hyperplaneRestriction 1 (hyperplaneExtension 1
        ((oneVariablePowerMapGerm k hk).pullbackRingHom a)) =
        (oneVariablePowerMapGerm k hk).pullbackRingHom a :=
      DFunLike.congr_fun (hyperplaneRestriction_comp_extension 1) _
    rw [hres, sub_self]
  have hdiv : coordinate (0 : Fin 2) ∣ F := by
    apply Ideal.mem_span_singleton.mp
    rw [← ker_hyperplaneRestriction_eq_span_coordinate_zero 1]
    exact hF
  have hcomp : (cyclicPowerSumMap 1 k (by omega) hk).comp firstSquareMap =
      cyclicPowerSumMap 2 k (by omega) hk := by
    simp only [cyclicPowerSumMap, firstSquareMap, PointedMapGerm.comp_ofFunction]
    apply Subtype.ext
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => by funext i; simp
  have h := map_dvd firstSquareMap.pullbackRingHom hdiv
  rw [firstSquareMap_coordinate] at h
  convert h using 1
  dsimp only [F]
  rw [map_sub, firstSquareMap_extension]
  change _ = ((firstSquareMap.pullbackRingHom.comp
    (cyclicPowerSumMap 1 k (by omega) hk).pullbackRingHom) a - _)
  rw [← PointedMapGerm.pullbackRingHom_comp, hcomp]

/-- The corrected second component uses the convergent descended average. -/
@[expose] noncomputable def cyclicAverageCorrectedSecond
    (k p : ℕ) (hk : 0 < k) (β a : Germ 1) : Germ 2 :=
  coordinate (0 : Fin 2) ^ p + coordinate (1 : Fin 2) ^ k * hyperplaneExtension 1 β -
    (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k) *
      (cyclicPowerSumMap 2 k (by omega) hk).pullbackRingHom a

private theorem extension_mem_twoWeightOrderIdeal (a b N : ℕ) (ha : 0 < a) (hb : 0 < b)
    (f : Germ 1) (hf : f ∈ maximalIdeal 1 ^ N) :
    hyperplaneExtension 1 f ∈ twoWeightOrderIdeal a b (b * N) := by
  rw [maximalIdeal_one_pow_eq_span_coordinate_pow, Ideal.mem_span_singleton] at hf
  obtain ⟨u, hu⟩ := hf
  rw [hu, map_mul, map_pow, hyperplaneExtension_coordinate]
  have hy : coordinate (1 : Fin 2) ^ N ∈ twoWeightOrderIdeal a b (b * N) := by
    simpa only [pow_zero, one_mul] using
      monomial_mem_twoWeightOrderIdeal_of_threshold a b (b * N) 0 N ha hb (by simp)
  exact Ideal.mul_mem_right _ _ hy

/-- A descended average with its proved first noninvariant term gives the
strict two-weight remainder of the corrected analytic component. -/
theorem cyclicAverageCorrectedSecond_weighted_tail
    (k j p : ℕ) (hk : 0 < k) (hj : 0 < j) (hp : 3 ≤ p)
    (β a : Germ 1) (b : ℂ)
    (htail : β - (oneVariablePowerMapGerm k hk).pullbackRingHom a -
      constRingHom 1 b * coordinate (0 : Fin 1) ^ j ∈ maximalIdeal 1 ^ (j + 1)) :
    cyclicAverageCorrectedSecond k p hk β a -
      (-(constRingHom 2 (valueRingHom 1 a) * coordinate (0 : Fin 2) ^ 2) +
        constRingHom 2 b * coordinate (1 : Fin 2) ^ (k + j)) ∈
      twoWeightOrderIdeal (k + j) 2 (2 * (k + j) + 1) := by
  let A := (cyclicPowerSumMap 2 k (by omega) hk).pullbackRingHom a
  let B := hyperplaneExtension 1 ((oneVariablePowerMapGerm k hk).pullbackRingHom a)
  have hL : 0 < k + j := by omega
  have htwo : 0 < (2 : ℕ) := by omega
  have hx2 : coordinate (0 : Fin 2) ^ 2 ∈ twoWeightOrderIdeal (k + j) 2 (2 * (k + j)) := by
    simpa only [pow_zero, mul_one] using
      monomial_mem_twoWeightOrderIdeal_of_threshold (k + j) 2 (2 * (k + j)) 2 0 hL htwo
        (by omega)
  have hyk : coordinate (1 : Fin 2) ^ k ∈ twoWeightOrderIdeal (k + j) 2 (2 * k) := by
    simpa only [pow_zero, one_mul] using
      monomial_mem_twoWeightOrderIdeal_of_threshold (k + j) 2 (2 * k) 0 k hL htwo (by simp)
  have hxP : coordinate (0 : Fin 2) ^ p ∈
      twoWeightOrderIdeal (k + j) 2 (2 * (k + j) + 1) := by
    simpa only [pow_zero, mul_one] using
      monomial_mem_twoWeightOrderIdeal_of_threshold (k + j) 2 (2 * (k + j) + 1) p 0 hL htwo
        (by nlinarith)
  have hA : A - constRingHom 2 (valueRingHom 1 a) ∈ twoWeightOrderIdeal (k + j) 2 1 := by
    rw [twoWeightOrderIdeal_one_eq_maximalIdeal (k + j) 2 hL htwo,
      mem_maximalIdeal_iff, map_sub, valueRingHom_const]
    exact sub_eq_zero.mpr (PointedMapGerm.valueRingHom_pullback _ a)
  have hxA := twoWeightOrderIdeal_mul_mem (k + j) 2 (2 * (k + j)) 1 hL htwo hx2 hA
  have hD : A - B ∈ twoWeightOrderIdeal (k + j) 2 (2 * (k + j)) := by
    obtain ⟨u, hu⟩ := cyclicPowerSum_divided_difference k hk a
    change A - B = coordinate (0 : Fin 2) ^ 2 * u at hu
    rw [hu]
    exact Ideal.mul_mem_right _ _ hx2
  have hyD := twoWeightOrderIdeal_mul_mem (k + j) 2 (2 * k) (2 * (k + j)) hL htwo hyk hD
  have hyD' := twoWeightOrderIdeal_antitone (k + j) 2 (2 * (k + j) + 1)
    (2 * k + 2 * (k + j)) hL htwo (by omega) hyD
  have hT := extension_mem_twoWeightOrderIdeal (k + j) 2 (j + 1) hL htwo _ htail
  have hextc (c : ℂ) : hyperplaneExtension 1 (constRingHom 1 c) = constRingHom 2 c :=
    (hyperplaneTailGerm 1).pullback_constRingHom c
  simp only [map_sub, map_mul, map_pow, hextc, hyperplaneExtension_coordinate,
    show (0 : Fin 1).succ = (1 : Fin 2) from rfl] at hT
  have hyT := twoWeightOrderIdeal_mul_mem (k + j) 2 (2 * k) (2 * (j + 1)) hL htwo hyk hT
  have hyT' := twoWeightOrderIdeal_antitone (k + j) 2 (2 * (k + j) + 1)
    (2 * k + 2 * (j + 1)) hL htwo (by omega) hyT
  have hsum := (twoWeightOrderIdeal (k + j) 2 (2 * (k + j) + 1)).sub_mem
    ((twoWeightOrderIdeal (k + j) 2 (2 * (k + j) + 1)).add_mem
      ((twoWeightOrderIdeal (k + j) 2 (2 * (k + j) + 1)).sub_mem hxP hxA) hyT') hyD'
  convert hsum using 1
  simp only [cyclicAverageCorrectedSecond, A, B, pow_add]
  ring

/-- The first component has initial term `y^k` for the same weights. -/
theorem cyclicPowerSum_first_weighted_tail (k j : ℕ) (hk : 0 < k) (hj : 0 < j) :
    (coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k) -
      coordinate (1 : Fin 2) ^ k ∈ twoWeightOrderIdeal (k + j) 2 (2 * k + 1) := by
  rw [add_sub_cancel_right]
  simpa only [pow_zero, mul_one] using
    monomial_mem_twoWeightOrderIdeal_of_threshold (k + j) 2 (2 * k + 1) 2 0
      (by omega) (by omega) (by omega)

/-- The polynomial initial pair after subtracting the cyclic average. -/
@[expose] noncomputable def cyclicAverageInitialPair (k j : ℕ) (c b : ℂ) :
    Fin 2 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.X 1 ^ k,
    -(MvPolynomial.C c * MvPolynomial.X 0 ^ 2) +
      MvPolynomial.C b * MvPolynomial.X 1 ^ (k + j)]

theorem cyclicAverageInitialPair_homogeneous (k j : ℕ) (c b : ℂ) (i : Fin 2) :
    (cyclicAverageInitialPair k j c b i).IsWeightedHomogeneous
      ![k + j, 2] (![2 * k, 2 * (k + j)] i) := by
  fin_cases i
  · simpa [cyclicAverageInitialPair, nsmul_eq_mul, mul_comm] using
      (MvPolynomial.isWeightedHomogeneous_X ℂ ![k + j, 2] 1).pow k
  · apply MvPolynomial.IsWeightedHomogeneous.add
    · simpa [cyclicAverageInitialPair, nsmul_eq_mul] using
        (((MvPolynomial.isWeightedHomogeneous_X ℂ ![k + j, 2] 0).pow 2).C_mul c).neg
    · simpa [cyclicAverageInitialPair, nsmul_eq_mul, mul_comm] using
        ((MvPolynomial.isWeightedHomogeneous_X ℂ ![k + j, 2] 1).pow (k + j)).C_mul b

theorem cyclicAverageInitialPair_ne_zero (k j : ℕ) (c b : ℂ) (hb : b ≠ 0) (i : Fin 2) :
    cyclicAverageInitialPair k j c b i ≠ 0 := by
  intro hz
  have heval := congrArg (MvPolynomial.eval (![0, 1] : Fin 2 → ℂ)) hz
  fin_cases i
  · simp [cyclicAverageInitialPair] at heval
  · exact hb (by simpa [cyclicAverageInitialPair] using heval)

/-- Construction of the analytic target change and its nonzero initial
pair from a first noninvariant coefficient in an actual finite jet.
No convergence, descent, or weighted remainder is assumed. -/
theorem exists_cyclicAverage_target_correction
    (k j p : ℕ) (hk : 0 < k) (hj : 0 < j) (hp : 3 ≤ p)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ k)
    (β : Germ 1) (B : MvPolynomial (Fin 1) ℂ)
    (hjet : β - coordinatePolynomialAlgHom 1 B ∈ maximalIdeal 1 ^ (j + 1))
    (hprevious : ∀ i < j, B.coeff (Finsupp.single 0 i) = 0 ∨ ζ ^ i = 1)
    (hcharacter : ζ ^ j ≠ 1) (hcoefficient : B.coeff (Finsupp.single 0 j) ≠ 0)
    (f : PointedMapGerm 2 2)
    (hf0 : f.1.component 0 = coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k)
    (hf1 : f.1.component 1 =
      coordinate (0 : Fin 2) ^ p + coordinate (1 : Fin 2) ^ k * hyperplaneExtension 1 β) :
    ∃ a : Germ 1, ∃ h : PointedMapGerm 2 2,
      (oneVariablePowerMapGerm k hk).pullbackRingHom a = oneVariableCyclicAverage k ζ β ∧
      valueRingHom 1 a = valueRingHom 1 β ∧
      f.RightLeftEquivalent h ∧ h.ImageRing = f.ImageRing ∧
      h.1.coordinateIdeal = f.1.coordinateIdeal ∧
      h.1.component 0 = f.1.component 0 ∧
      h.1.component 1 = cyclicAverageCorrectedSecond k p hk β a ∧
      ∀ i : Fin 2,
        (cyclicAverageInitialPair k j (valueRingHom 1 β)
          (B.coeff (Finsupp.single 0 j)) i).IsWeightedHomogeneous
            ![k + j, 2] (![2 * k, 2 * (k + j)] i) ∧
        cyclicAverageInitialPair k j (valueRingHom 1 β)
          (B.coeff (Finsupp.single 0 j)) i ≠ 0 ∧
        h.1.component i - coordinatePolynomialAlgHom 2
          (cyclicAverageInitialPair k j (valueRingHom 1 β)
            (B.coeff (Finsupp.single 0 j)) i) ∈
          twoWeightOrderIdeal (k + j) 2 (![2 * k, 2 * (k + j)] i + 1) := by
  obtain ⟨a, ha⟩ := exists_oneVariable_cyclicAverage_descent k hk ζ hζ β
  have havalue : valueRingHom 1 a = valueRingHom 1 β := by
    have hv := congrArg (valueRingHom 1) ha
    rwa [PointedMapGerm.valueRingHom_pullback, value_oneVariableCyclicAverage k hk] at hv
  have htail := first_noninvariant_cyclicAverage_tail k hk ζ hζ β j B hjet hprevious hcharacter
  rw [← ha] at htail
  obtain ⟨h, hequiv, hh0, hh1, himage, hideal⟩ :=
    PointedMapGerm.exists_target_second_subtraction f (coordinate (0 : Fin 1) * a)
      (Ideal.mul_mem_right _ _ (coordinate_mem_maximalIdeal (0 : Fin 1)))
  have hproj : PointedMapGerm.firstCoordinateProjection.comp f =
      cyclicPowerSumMap 2 k (by omega) hk := by
    apply PointedMapGerm.ext_components
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [PointedMapGerm.component_comp_eq_pullback,
      PointedMapGerm.firstCoordinateProjection_component, PointedMapGerm.pullback_coordinate, hf0,
      ← PointedMapGerm.pullback_coordinate, cyclicPowerSumMap_pullback_coordinate]
  have hh1' : h.1.component 1 = cyclicAverageCorrectedSecond k p hk β a := by
    rw [hproj, hf1, map_mul, cyclicPowerSumMap_pullback_coordinate] at hh1
    exact hh1
  refine ⟨a, h, ha, havalue, hequiv, himage, hideal, hh0, hh1', fun i =>
    ⟨cyclicAverageInitialPair_homogeneous k j _ _ i,
      cyclicAverageInitialPair_ne_zero k j _ _ hcoefficient i, ?_⟩⟩
  fin_cases i
  · change h.1.component 0 - coordinatePolynomialAlgHom 2 (MvPolynomial.X 1 ^ k) ∈
      twoWeightOrderIdeal (k + j) 2 (2 * k + 1)
    rw [hh0, hf0, map_pow, coordinatePolynomialAlgHom_X]
    exact cyclicPowerSum_first_weighted_tail k j hk hj
  · change h.1.component 1 - coordinatePolynomialAlgHom 2
      (-(MvPolynomial.C (valueRingHom 1 β) * MvPolynomial.X 0 ^ 2) +
        MvPolynomial.C (B.coeff (Finsupp.single 0 j)) * MvPolynomial.X 1 ^ (k + j)) ∈
      twoWeightOrderIdeal (k + j) 2 (2 * (k + j) + 1)
    have ht := cyclicAverageCorrectedSecond_weighted_tail k j p hk hj hp β a
      (B.coeff (Finsupp.single 0 j)) htail
    rw [havalue] at ht
    simpa only [map_add, map_neg, map_mul, map_pow, coordinatePolynomialAlgHom_C,
      coordinatePolynomialAlgHom_X, hh1'] using ht

/-- The first exponent, its nonzero coefficient, the convergent average,
and the corrected pair are all constructed from a nonzero rotation
difference. In particular the first exponent need not be less than `k`. -/
theorem exists_cyclicAverage_target_correction_of_noninvariant
    (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ k) (β : Germ 1)
    (hne : β - (oneVariableRotationGerm ζ).pullbackRingHom β ≠ 0)
    (f : PointedMapGerm 2 2)
    (hf0 : f.1.component 0 = coordinate (0 : Fin 2) ^ 2 + coordinate (1 : Fin 2) ^ k)
    (hf1 : f.1.component 1 =
      coordinate (0 : Fin 2) ^ p + coordinate (1 : Fin 2) ^ k * hyperplaneExtension 1 β) :
    ∃ j : ℕ, 0 < j ∧ ζ ^ j ≠ 1 ∧ ∃ b : ℂ, b ≠ 0 ∧
      ∃ a : Germ 1, ∃ h : PointedMapGerm 2 2,
        (oneVariablePowerMapGerm k hk).pullbackRingHom a = oneVariableCyclicAverage k ζ β ∧
        valueRingHom 1 a = valueRingHom 1 β ∧
        f.RightLeftEquivalent h ∧ h.ImageRing = f.ImageRing ∧
        h.1.coordinateIdeal = f.1.coordinateIdeal ∧
        h.1.component 0 = f.1.component 0 ∧
        h.1.component 1 = cyclicAverageCorrectedSecond k p hk β a ∧
        ∀ i : Fin 2,
          (cyclicAverageInitialPair k j (valueRingHom 1 β) b i).IsWeightedHomogeneous
            ![k + j, 2] (![2 * k, 2 * (k + j)] i) ∧
          cyclicAverageInitialPair k j (valueRingHom 1 β) b i ≠ 0 ∧
          h.1.component i - coordinatePolynomialAlgHom 2
            (cyclicAverageInitialPair k j (valueRingHom 1 β) b i) ∈
            twoWeightOrderIdeal (k + j) 2 (![2 * k, 2 * (k + j)] i + 1) := by
  obtain ⟨j, hj, hcharacter, B, hjet, hcoefficient, hprevious⟩ :=
    exists_first_noninvariant_jet ζ (hζ.ne_zero hk.ne') β hne
  obtain ⟨a, h, ha⟩ := exists_cyclicAverage_target_correction k j p hk hj hp ζ hζ β B
    hjet hprevious hcharacter hcoefficient f hf0 hf1
  exact ⟨j, hj, hcharacter, B.coeff (Finsupp.single 0 j), hcoefficient, a, h, ha⟩

end OnLeConjecture.DTwo
