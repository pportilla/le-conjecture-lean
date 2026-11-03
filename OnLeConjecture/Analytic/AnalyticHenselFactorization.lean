/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CoprimePolynomialMultiplication
public import OnLeConjecture.Analytic.LocalRing
public import OnLeConjecture.Analytic.Pullback
public import OnLeConjecture.Analytic.WeightedMonomialDivision

/-!
# Convergent lifting of coprime polynomial factors

The analytic local inverse of coefficient multiplication lifts a coprime
monic factorization of the residue polynomial to monic polynomials with
analytic germ coefficients. The analytic germ ring is not replaced by its
formal completion.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial OnLeConjecture.Polynomial Filter
open scoped Topology

private theorem map_function_polynomial_eq_of_eventually_specialization_eq
    {d : ℕ} (F G : Polynomial (Source d → ℂ))
    (heq : ∀ᶠ z in nhds (0 : Source d),
      F.map (Pi.evalRingHom (fun _ : Source d ↦ ℂ) z) =
        G.map (Pi.evalRingHom (fun _ : Source d ↦ ℂ) z)) :
    F.map (Filter.Germ.coeRingHom (nhds (0 : Source d))) =
      G.map (Filter.Germ.coeRingHom (nhds (0 : Source d))) := by
  ext j
  simp only [Polynomial.coeff_map]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [heq] with z hz
  simpa only [Polynomial.coeff_map, Pi.evalRingHom_apply] using congrArg (fun p ↦ p.coeff j) hz

private theorem function_coefficient_polynomial_specialization
    {d : ℕ} (m : ℕ) (P : ℂ[X]) (u : Fin m → Source d → ℂ) (z : Source d) :
    (P.map (algebraMap ℂ (Source d → ℂ)) + coefficientPolynomial m u).map
        (Pi.evalRingHom (fun _ : Source d ↦ ℂ) z) =
      P + coefficientPolynomial m (fun j ↦ u j z) := by
  rw [Polynomial.map_add, Polynomial.map_map, coefficientPolynomial_map]
  have hcomp : (Pi.evalRingHom (fun _ : Source d ↦ ℂ) z).comp
      (algebraMap ℂ (Source d → ℂ)) = RingHom.id ℂ := by ext c; rfl
  rw [hcomp, Polynomial.map_id]
  rfl

private theorem function_coefficient_polynomial_map_germs
    {d : ℕ} (m : ℕ) (P : ℂ[X]) (u : Fin m → Source d → ℂ)
    (hu : ∀ j, AnalyticAt ℂ (u j) 0) :
    (P.map (algebraMap ℂ (Source d → ℂ)) + coefficientPolynomial m u).map
        (Filter.Germ.coeRingHom (nhds (0 : Source d))) =
      (P.map (constRingHom d) +
        coefficientPolynomial m (fun j ↦ ofFunction (u j) (hu j))).map
          (analyticGermSubring d).subtype := by
  rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_map, Polynomial.map_map,
    coefficientPolynomial_map, coefficientPolynomial_map]
  have hconst : (Filter.Germ.coeRingHom (nhds (0 : Source d))).comp
      (algebraMap ℂ (Source d → ℂ)) =
        (analyticGermSubring d).subtype.comp (constRingHom d) := by
    ext c
    rfl
  rw [hconst]
  rfl

private theorem map_constPolynomial_value {d : ℕ} (P : ℂ[X]) :
    (P.map (constRingHom d)).map (valueRingHom d) = P := by
  rw [Polynomial.map_map]
  have hconst : (valueRingHom d).comp (constRingHom d) = RingHom.id ℂ := by
    ext c
    exact valueRingHom_const d c
  rw [hconst, Polynomial.map_id]

/-- A prescribed coprime monic factorization of the residue polynomial
lifts to analytic monic factors of exactly the prescribed degrees. The
original polynomial need not be distinguished. Both degree-zero cases
are included. -/
theorem exists_analytic_hensel_factorization
    (m n : ℕ) (P : Polynomial (Germ 1)) (hP : P.Monic) (hPdegree : P.natDegree = m + n)
    (A₀ B₀ : ℂ[X]) (hA₀ : A₀.Monic) (hB₀ : B₀.Monic)
    (hAm : A₀.natDegree = m) (hBn : B₀.natDegree = n)
    (hcoprime : IsCoprime A₀ B₀)
    (hresidue : P.map (valueRingHom 1) = A₀ * B₀) :
    ∃ A B : Polynomial (Germ 1), A.Monic ∧ A.natDegree = m ∧ B.Monic ∧ B.natDegree = n ∧
      A.map (valueRingHom 1) = A₀ ∧ B.map (valueRingHom 1) = B₀ ∧ P = A * B := by
  classical
  let C := (A₀ * B₀).map (constRingHom 1)
  let D := P - C
  have hCmonic : C.Monic := (hA₀.mul hB₀).map (constRingHom 1)
  have hCdegree : C.natDegree = m + n := by
    rw [(hA₀.mul hB₀).natDegree_map, hA₀.natDegree_mul hB₀, hAm, hBn]
  have hDdegree : D.degree < (m + n : ℕ) := by
    have hdegree : P.degree = C.degree := by
      rw [degree_eq_natDegree hP.ne_zero, degree_eq_natDegree hCmonic.ne_zero,
        hPdegree, hCdegree]
    have h := degree_sub_lt_left hdegree hP.ne_zero (hP.trans hCmonic.symm)
    simpa only [degree_eq_natDegree hP.ne_zero, hPdegree] using h
  have hDresidue : D.map (valueRingHom 1) = 0 := by
    change (P - (A₀ * B₀).map (constRingHom 1)).map (valueRingHom 1) = 0
    rw [Polynomial.map_sub, hresidue, map_constPolynomial_value, sub_self]
  obtain ⟨ψ, hψ, hψ0, hfactor⟩ := exists_analytic_polynomial_factor_coefficients
    m n A₀ B₀ hA₀ hAm hBn hcoprime
  choose F hF hrepresentative using fun j : Fin (m + n) ↦ exists_ofFunction (D.coeff j)
  let z : Source 1 → Source (m + n) := fun t j ↦ F j t
  have hz : AnalyticAt ℂ z 0 := AnalyticAt.pi hF
  have hz0 : z 0 = 0 := by
    ext j
    have hc := congrArg (fun q ↦ q.coeff j) hDresidue
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, hrepresentative j,
      valueRingHom_ofFunction] at hc
    exact hc
  have hψz : AnalyticAt ℂ (fun t ↦ ψ (z t)) 0 := by
    apply AnalyticAt.comp (x := (0 : Source 1)) _ hz
    simpa only [hz0] using hψ
  let a : Fin m → Source 1 → ℂ := fun j t ↦ (ψ (z t)).1 j
  let b : Fin n → Source 1 → ℂ := fun j t ↦ (ψ (z t)).2 j
  have ha : ∀ j, AnalyticAt ℂ (a j) 0 := fun j ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m ↦ ℂ) j).analyticAt _).comp
      (((ContinuousLinearMap.fst ℂ (Source m) (Source n)).analyticAt _).comp hψz)
  have hb : ∀ j, AnalyticAt ℂ (b j) 0 := fun j ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) j).analyticAt _).comp
      (((ContinuousLinearMap.snd ℂ (Source m) (Source n)).analyticAt _).comp hψz)
  let A := A₀.map (constRingHom 1) + coefficientPolynomial m (fun j ↦ ofFunction (a j) (ha j))
  let B := B₀.map (constRingHom 1) + coefficientPolynomial n (fun j ↦ ofFunction (b j) (hb j))
  have hADegree := monic_add_coefficientPolynomial m (A₀.map (constRingHom 1))
    (hA₀.map _) ((hA₀.natDegree_map _).trans hAm) (fun j ↦ ofFunction (a j) (ha j))
  have hBDegree := monic_add_coefficientPolynomial n (B₀.map (constRingHom 1))
    (hB₀.map _) ((hB₀.natDegree_map _).trans hBn) (fun j ↦ ofFunction (b j) (hb j))
  refine ⟨A, B, hADegree.1, hADegree.2, hBDegree.1, hBDegree.2, ?_, ?_, ?_⟩
  · change (A₀.map (constRingHom 1) +
      coefficientPolynomial m (fun j ↦ ofFunction (a j) (ha j))).map (valueRingHom 1) = A₀
    rw [Polynomial.map_add, map_constPolynomial_value, coefficientPolynomial_map]
    have hzero : (fun j ↦ valueRingHom 1 (ofFunction (a j) (ha j))) = 0 := by
      ext j
      simp only [valueRingHom_ofFunction, a, hz0, hψ0, Prod.fst_zero, Pi.zero_apply]
    rw [hzero, map_zero, add_zero]
  · change (B₀.map (constRingHom 1) +
      coefficientPolynomial n (fun j ↦ ofFunction (b j) (hb j))).map (valueRingHom 1) = B₀
    rw [Polynomial.map_add, map_constPolynomial_value, coefficientPolynomial_map]
    have hzero : (fun j ↦ valueRingHom 1 (ofFunction (b j) (hb j))) = 0 := by
      ext j
      simp only [valueRingHom_ofFunction, b, hz0, hψ0, Prod.snd_zero, Pi.zero_apply]
    rw [hzero, map_zero, add_zero]
  · let AF := A₀.map (algebraMap ℂ (Source 1 → ℂ)) + coefficientPolynomial m a
    let BF := B₀.map (algebraMap ℂ (Source 1 → ℂ)) + coefficientPolynomial n b
    let PF := (A₀ * B₀).map (algebraMap ℂ (Source 1 → ℂ)) + coefficientPolynomial (m + n) F
    have hnear : ∀ᶠ t in nhds (0 : Source 1),
        (AF * BF).map (Pi.evalRingHom (fun _ : Source 1 ↦ ℂ) t) =
          PF.map (Pi.evalRingHom (fun _ : Source 1 ↦ ℂ) t) := by
      have htend : Tendsto z (nhds 0) (nhds 0) := by simpa only [hz0] using hz.continuousAt.tendsto
      filter_upwards [htend.eventually hfactor] with t ht
      change ((A₀.map (algebraMap ℂ (Source 1 → ℂ)) + coefficientPolynomial m a) *
        (B₀.map (algebraMap ℂ (Source 1 → ℂ)) + coefficientPolynomial n b)).map _ =
          ((A₀ * B₀).map (algebraMap ℂ (Source 1 → ℂ)) +
            coefficientPolynomial (m + n) F).map _
      rw [Polynomial.map_mul, function_coefficient_polynomial_specialization,
        function_coefficient_polynomial_specialization,
        function_coefficient_polynomial_specialization]
      exact ht
    have hfunctionGerm := map_function_polynomial_eq_of_eventually_specialization_eq
      (AF * BF) PF hnear
    rw [Polynomial.map_mul, function_coefficient_polynomial_map_germs m A₀ a ha,
      function_coefficient_polynomial_map_germs n B₀ b hb,
      function_coefficient_polynomial_map_germs (m + n) (A₀ * B₀) F hF] at hfunctionGerm
    have hDP : (A₀ * B₀).map (constRingHom 1) +
        coefficientPolynomial (m + n) (fun j ↦ ofFunction (F j) (hF j)) = P := by
      have hcoeff : (fun j ↦ ofFunction (F j) (hF j)) =
          (fun j : Fin (m + n) ↦ D.coeff j) := funext fun j ↦ (hrepresentative j).symm
      rw [hcoeff, coefficientPolynomial_coefficients (m + n) D hDdegree]
      change C + (P - C) = P
      ring
    rw [hDP, ← Polynomial.map_mul] at hfunctionGerm
    exact (Polynomial.map_injective (analyticGermSubring 1).subtype
      (analyticGermSubring 1).subtype_injective hfunctionGerm).symm

end OnLeConjecture.Analytic.Germ
