/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IntersectionResultant
public import OnLeConjecture.Analytic.OneVariablePowerSubstitution
public import OnLeConjecture.Analytic.JacobianPullback
public import OnLeConjecture.Analytic.WeightedIntersectionBound

/-!
# Intersection multiplicity under ramification of the second coordinate

The analytic substitution `(x,y) ↦ (x,y^s)` agrees with the coefficient
substitution on Weierstrass polynomials. The resultant formula therefore
multiplies finite intersection multiplicity by `s`.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- The plane substitution that raises only the second coordinate to a
positive integral power. -/
@[expose] noncomputable def secondCoordinatePowerGerm (s : ℕ) (hs : 0 < s) :
    PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction (fun z : Source 2 ↦ ![z 0, z 1 ^ s])
    (by
      apply AnalyticAt.pi
      intro i
      fin_cases i
      · exact (ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt 0
      · exact ((ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticAt 0).pow s)
    (by ext i; fin_cases i <;> simp [zero_pow hs.ne'])

@[simp] theorem secondCoordinatePowerGerm_pullback_zero
    (s : ℕ) (hs : 0 < s) :
    (secondCoordinatePowerGerm s hs).pullbackRingHom (coordinate (0 : Fin 2)) =
      coordinate (0 : Fin 2) := by
  rw [PointedMapGerm.pullback_coordinate]
  simp only [secondCoordinatePowerGerm, PointedMapGerm.ofFunction]
  apply Subtype.ext
  rw [MapGerm.component_ofFunction]
  rfl

@[simp] theorem secondCoordinatePowerGerm_pullback_one
    (s : ℕ) (hs : 0 < s) :
    (secondCoordinatePowerGerm s hs).pullbackRingHom (coordinate (1 : Fin 2)) =
      coordinate (1 : Fin 2) ^ s := by
  rw [PointedMapGerm.pullback_coordinate]
  simp only [secondCoordinatePowerGerm, PointedMapGerm.ofFunction]
  apply Subtype.ext
  rw [MapGerm.component_ofFunction]
  rfl

/-- The coordinate Jacobian of ramification is its expected parameter
power times the nonzero constant exponent. -/
theorem coordinateJacobian_secondCoordinatePowerGerm
    (s : ℕ) (hs : 0 < s) :
    coordinateJacobian (secondCoordinatePowerGerm s hs) =
      constRingHom 2 (s : ℂ) * coordinate (1 : Fin 2) ^ (s - 1) := by
  rw [coordinateJacobian, ← PointedMapGerm.pullback_coordinate,
    ← PointedMapGerm.pullback_coordinate,
    secondCoordinatePowerGerm_pullback_zero, secondCoordinatePowerGerm_pullback_one,
    jacobian_eq, partialDerivative_pow, partialDerivative_pow]
  simp [nsmul_eq_mul, smul_eq_mul]

/-- The chain rule for the actual ramified analytic germs. -/
theorem jacobian_secondCoordinatePowerGerm_pullback
    (s : ℕ) (hs : 0 < s) (f g : Germ 2) :
    jacobian ((secondCoordinatePowerGerm s hs).pullbackRingHom f)
        ((secondCoordinatePowerGerm s hs).pullbackRingHom g) =
      constRingHom 2 (s : ℂ) * coordinate (1 : Fin 2) ^ (s - 1) *
        (secondCoordinatePowerGerm s hs).pullbackRingHom (jacobian f g) := by
  change jacobian (compPointed f _) (compPointed g _) = _
  rw [jacobian_compPointed, coordinateJacobian_secondCoordinatePowerGerm]
  rw [PointedMapGerm.pullbackRingHom_apply]
  ring

/-- A transverse Jacobian divisor pulls back with exponent `s*t-1`,
including the extra factor supplied by the chain rule. -/
theorem secondCoordinatePowerGerm_jacobian_divisor
    (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (f g : Germ 2)
    (hdiv : coordinate (1 : Fin 2) ^ (t - 1) ∣ jacobian f g) :
    coordinate (1 : Fin 2) ^ (s * t - 1) ∣
      jacobian ((secondCoordinatePowerGerm s hs).pullbackRingHom f)
        ((secondCoordinatePowerGerm s hs).pullbackRingHom g) := by
  obtain ⟨q, hq⟩ := hdiv
  rw [jacobian_secondCoordinatePowerGerm_pullback, hq, map_mul, map_pow,
    secondCoordinatePowerGerm_pullback_one]
  refine ⟨constRingHom 2 (s : ℂ) * (secondCoordinatePowerGerm s hs).pullbackRingHom q, ?_⟩
  have hexp : s * t - 1 = (s - 1) + s * (t - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have hst : s ≤ s * t := by nlinarith
    omega
  rw [hexp, pow_add, pow_mul]
  ring

/-- Coefficient extension commutes with the actual ramified substitution. -/
theorem secondCoordinatePowerGerm_pullback_hyperplaneExtension
    (s : ℕ) (hs : 0 < s) (f : Germ 1) :
    (secondCoordinatePowerGerm s hs).pullbackRingHom (hyperplaneExtension 1 f) =
      hyperplaneExtension 1 ((oneVariablePowerMapGerm s hs).pullbackRingHom f) := by
  rcases f with ⟨f, hf⟩
  induction f using Filter.Germ.inductionOn with
  | _ f =>
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    apply Filter.Eventually.of_forall
    intro z
    change f (hyperplaneTail 1 ![z 0, z 1 ^ s]) =
      f (oneVariablePowerMap s (hyperplaneTail 1 z))
    congr 1
    ext i
    fin_cases i
    rfl

/-- Analytic pullback of a polynomial germ is coefficientwise power
substitution in its Weierstrass polynomial. -/
theorem secondCoordinatePowerGerm_pullback_polynomial
    (s : ℕ) (hs : 0 < s) (P : Polynomial (Germ 1)) :
    (secondCoordinatePowerGerm s hs).pullbackRingHom
        (firstCoordinatePolynomialEvaluation P) =
      firstCoordinatePolynomialEvaluation
        (P.map (oneVariablePowerMapGerm s hs).pullbackRingHom) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [firstCoordinatePolynomialEvaluation, Polynomial.eval₂_add,
      Polynomial.map_add, map_add] at hP hQ ⊢
    rw [hP, hQ]
  | monomial n c =>
    simp only [firstCoordinatePolynomialEvaluation, Polynomial.map_monomial,
      Polynomial.eval₂_monomial, map_mul, map_pow,
      secondCoordinatePowerGerm_pullback_hyperplaneExtension,
      secondCoordinatePowerGerm_pullback_zero]

/-- The actual polynomial resultant commutes with positive power
substitution in its analytic coefficients, with no degree loss. -/
theorem resultant_map_oneVariablePowerMapGerm
    (s : ℕ) (hs : 0 < s) (P Q : Polynomial (Germ 1)) :
    (P.map (oneVariablePowerMapGerm s hs).pullbackRingHom).resultant
        (Q.map (oneVariablePowerMapGerm s hs).pullbackRingHom) =
      (oneVariablePowerMapGerm s hs).pullbackRingHom (P.resultant Q) := by
  simp only [Polynomial.natDegree_map_eq_of_injective
    (oneVariablePowerMapGerm_pullback_injective s hs), Polynomial.resultant_map_map]

/-- A rational Newton-order inequality becomes an integral coefficient
bound under the actual positive power substitution. -/
theorem coefficient_mem_maximalIdeal_pow_after_ramification
    (s r m : ℕ) (hs : 0 < s) (P : Polynomial (Germ 1))
    (horder : ∀ i, i < m →
      ((r * (m - i) : ℕ) : ℕ∞) ≤ s • vanishingOrder (P.coeff i)) :
    ∀ i, i < m →
      (P.map (oneVariablePowerMapGerm s hs).pullbackRingHom).coeff i ∈
        maximalIdeal 1 ^ (r * (m - i)) := by
  intro i hi
  rw [Polynomial.coeff_map, maximalIdeal_one_pow_eq_span_coordinate_pow,
    Ideal.mem_span_singleton, ← vanishingOrder_le_iff_dvd,
    vanishingOrder_coordinate_pow, vanishingOrder_oneVariablePowerMapGerm_pullback]
  exact horder i hi

/-- An attained Newton-order equality remains exact after ramification. -/
theorem coefficient_vanishingOrder_after_ramification
    (s r m i : ℕ) (hs : 0 < s) (P : Polynomial (Germ 1))
    (horder : s • vanishingOrder (P.coeff i) = ((r * (m - i) : ℕ) : ℕ∞)) :
    vanishingOrder ((P.map (oneVariablePowerMapGerm s hs).pullbackRingHom).coeff i) =
      ((r * (m - i) : ℕ) : ℕ∞) := by
  rw [Polynomial.coeff_map, vanishingOrder_oneVariablePowerMapGerm_pullback]
  exact horder

/-- Ramification preserves finite intersection for distinguished
polynomial germs. -/
theorem hasFiniteIntersection_ramified_polynomials
    (s d : ℕ) (hs : 0 < s) (P Q : Polynomial (Germ 1))
    (hPMonic : P.Monic) (hPDegree : P.natDegree = d + 1)
    (hPCoeff : ∀ k, k < d + 1 → P.coeff k ∈ maximalIdeal 1)
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P)
      (firstCoordinatePolynomialEvaluation Q)) :
    PlaneCurve.HasFiniteIntersection
      (firstCoordinatePolynomialEvaluation
        (P.map (oneVariablePowerMapGerm s hs).pullbackRingHom))
      (firstCoordinatePolynomialEvaluation
        (Q.map (oneVariablePowerMapGerm s hs).pullbackRingHom)) := by
  let φ := (oneVariablePowerMapGerm s hs).pullbackRingHom
  have hmonic : (P.map φ).Monic := hPMonic.map φ
  have hdegree : (P.map φ).natDegree = d + 1 := (hPMonic.natDegree_map φ).trans hPDegree
  have hcoeff : ∀ k, k < d + 1 → (P.map φ).coeff k ∈ maximalIdeal 1 := by
    intro k hk
    rw [Polynomial.coeff_map]
    exact PointedMapGerm.pullback_mem_maximalIdeal _ (hPCoeff k hk)
  apply hasFiniteIntersection_of_resultant_ne_zero d (P.map φ) (Q.map φ)
    hmonic hdegree hcoeff
  rw [resultant_map_oneVariablePowerMapGerm]
  exact (map_ne_zero_iff _ (oneVariablePowerMapGerm_pullback_injective s hs)).mpr
    (resultant_ne_zero_of_hasFiniteIntersection d P Q hPMonic hPDegree hPCoeff hfinite)

/-- Positive ramification multiplies the analytic intersection number by
its exponent. Both sides are defined by their analytic local algebras. -/
theorem intersectionMultiplicity_ramified_polynomials
    (s d : ℕ) (hs : 0 < s) (P Q : Polynomial (Germ 1))
    (hPMonic : P.Monic) (hPDegree : P.natDegree = d + 1)
    (hPCoeff : ∀ k, k < d + 1 → P.coeff k ∈ maximalIdeal 1)
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P)
      (firstCoordinatePolynomialEvaluation Q))
    (hfinite' : PlaneCurve.HasFiniteIntersection
      (firstCoordinatePolynomialEvaluation
        (P.map (oneVariablePowerMapGerm s hs).pullbackRingHom))
      (firstCoordinatePolynomialEvaluation
        (Q.map (oneVariablePowerMapGerm s hs).pullbackRingHom))) :
    PlaneCurve.intersectionMultiplicity
      (firstCoordinatePolynomialEvaluation
        (P.map (oneVariablePowerMapGerm s hs).pullbackRingHom))
      (firstCoordinatePolynomialEvaluation
        (Q.map (oneVariablePowerMapGerm s hs).pullbackRingHom)) hfinite' =
      s * PlaneCurve.intersectionMultiplicity (firstCoordinatePolynomialEvaluation P)
        (firstCoordinatePolynomialEvaluation Q) hfinite := by
  let φ := (oneVariablePowerMapGerm s hs).pullbackRingHom
  have hmonic : (P.map φ).Monic := hPMonic.map φ
  have hdegree : (P.map φ).natDegree = d + 1 := (hPMonic.natDegree_map φ).trans hPDegree
  have hcoeff : ∀ k, k < d + 1 → (P.map φ).coeff k ∈ maximalIdeal 1 := by
    intro k hk
    rw [Polynomial.coeff_map]
    exact PointedMapGerm.pullback_mem_maximalIdeal _ (hPCoeff k hk)
  rw [intersectionMultiplicity_eq_resultant_order d (P.map φ) (Q.map φ)
    hmonic hdegree hcoeff hfinite',
    intersectionMultiplicity_eq_resultant_order d P Q hPMonic hPDegree hPCoeff hfinite,
    resultant_map_oneVariablePowerMapGerm, vanishingOrder_oneVariablePowerMapGerm_pullback]
  simp [nsmul_eq_mul]

/-- Ramification multiplies intersection multiplicity also when the
second germ is an arbitrary convergent analytic germ. -/
theorem exists_finite_ramified_intersection_eq
    (s d : ℕ) (hs : 0 < s) (P : Polynomial (Germ 1))
    (hPMonic : P.Monic) (hPDegree : P.natDegree = d + 1)
    (hPCoeff : ∀ k, k < d + 1 → P.coeff k ∈ maximalIdeal 1)
    (H : Germ 2)
    (hfinite : PlaneCurve.HasFiniteIntersection (firstCoordinatePolynomialEvaluation P) H) :
    ∃ hfinite' : PlaneCurve.HasFiniteIntersection
        ((secondCoordinatePowerGerm s hs).pullbackRingHom
          (firstCoordinatePolynomialEvaluation P))
        ((secondCoordinatePowerGerm s hs).pullbackRingHom H),
      PlaneCurve.intersectionMultiplicity
        ((secondCoordinatePowerGerm s hs).pullbackRingHom
          (firstCoordinatePolynomialEvaluation P))
        ((secondCoordinatePowerGerm s hs).pullbackRingHom H) hfinite' =
      s * PlaneCurve.intersectionMultiplicity
        (firstCoordinatePolynomialEvaluation P) H hfinite := by
  let φ := (secondCoordinatePowerGerm s hs).pullbackRingHom
  let ψ := (oneVariablePowerMapGerm s hs).pullbackRingHom
  obtain ⟨Q, hQ⟩ := exists_polynomial_mod_distinguished d P hPMonic hPDegree hPCoeff H
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hQ
  have hdivision : H = firstCoordinatePolynomialEvaluation P * q +
      firstCoordinatePolynomialEvaluation Q := by
    rw [← hq]
    ring
  have hideal := PlaneCurve.pairIdeal_eq_of_remainder
    (firstCoordinatePolynomialEvaluation P) H (firstCoordinatePolynomialEvaluation Q) q hdivision
  have hfiniteQ := hfinite.of_pairIdeal_eq hideal
  have hfinitePQ := hasFiniteIntersection_ramified_polynomials
    s d hs P Q hPMonic hPDegree hPCoeff hfiniteQ
  have hpolyP : φ (firstCoordinatePolynomialEvaluation P) =
      firstCoordinatePolynomialEvaluation (P.map ψ) :=
    secondCoordinatePowerGerm_pullback_polynomial s hs P
  have hpolyQ : φ (firstCoordinatePolynomialEvaluation Q) =
      firstCoordinatePolynomialEvaluation (Q.map ψ) :=
    secondCoordinatePowerGerm_pullback_polynomial s hs Q
  have hdivision' : φ H = firstCoordinatePolynomialEvaluation (P.map ψ) * φ q +
      firstCoordinatePolynomialEvaluation (Q.map ψ) := by
    rw [hdivision, map_add, map_mul, hpolyP, hpolyQ]
  have hideal' := PlaneCurve.pairIdeal_eq_of_remainder
    (firstCoordinatePolynomialEvaluation (P.map ψ)) (φ H)
    (firstCoordinatePolynomialEvaluation (Q.map ψ)) (φ q) hdivision'
  have hfiniteH := hfinitePQ.of_pairIdeal_eq hideal'.symm
  have hfinite' : PlaneCurve.HasFiniteIntersection
      (φ (firstCoordinatePolynomialEvaluation P)) (φ H) := by
    rw [hpolyP]
    exact hfiniteH
  refine ⟨hfinite', ?_⟩
  change PlaneCurve.intersectionMultiplicity
    (φ (firstCoordinatePolynomialEvaluation P)) (φ H) hfinite' = _
  trans PlaneCurve.intersectionMultiplicity
    (firstCoordinatePolynomialEvaluation (P.map ψ)) (φ H) hfiniteH
  · change Module.finrank ℂ _ = Module.finrank ℂ _
    rw [hpolyP]
  calc
    PlaneCurve.intersectionMultiplicity
        (firstCoordinatePolynomialEvaluation (P.map ψ)) (φ H) _ =
      PlaneCurve.intersectionMultiplicity
        (firstCoordinatePolynomialEvaluation (P.map ψ))
        (firstCoordinatePolynomialEvaluation (Q.map ψ)) hfinitePQ :=
      PlaneCurve.intersectionMultiplicity_eq_of_pairIdeal_eq hfiniteH hfinitePQ hideal'
    _ = s * PlaneCurve.intersectionMultiplicity (firstCoordinatePolynomialEvaluation P)
        (firstCoordinatePolynomialEvaluation Q) hfiniteQ :=
      intersectionMultiplicity_ramified_polynomials s d hs P Q
        hPMonic hPDegree hPCoeff hfiniteQ hfinitePQ
    _ = s * PlaneCurve.intersectionMultiplicity
        (firstCoordinatePolynomialEvaluation P) H hfinite := by
      rw [PlaneCurve.intersectionMultiplicity_eq_of_pairIdeal_eq hfinite hfiniteQ hideal]

end OnLeConjecture.Analytic.Germ
