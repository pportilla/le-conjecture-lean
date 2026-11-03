/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.DiscriminantBraidExponent
public import OnLeConjecture.PlaneCurve.FirstAxisFiniteIntersection
public import OnLeConjecture.KnotTheory.PositiveWordNormalForms

/-!
# The root braid exponent of a reduced plane germ, and the full-twist word

Let `f` be a reduced pointed plane germ, regular of order `m` in the first
coordinate `ζ`, with Weierstrass factorization `f = P u` in that coordinate. The
pair ideals `(f, f_ζ)` and `(P, P_ζ)` coincide because `u` is a unit. Teissier's
polar identity with the parameter `ξ` (the second coordinate) gives
`i₀(f, f_ζ) + 1 = μ(f) + m`. Hence the discriminant of `P` is nonzero and, by
M1155, every signed crossing count `Exp` of a labelled root family of `P` over a
sufficiently small circle satisfies `Exp + 1 = μ(f) + m` (J15, Theorem
`J15:thm:reduced`).

Part (b) of J15 concerns the word `d v` of J14, where `d = fullTwistWord S` and `v`
is positive. The J14 construction is not formalized. The corollary below takes as
an explicit hypothesis that `d v` is a signed event word of the root braid on
arbitrarily small circles, in the precise sense that its exponent sum is the
signed crossing count of crossing data of a labelled root family of `P`. Under
that hypothesis it proves `length (d v) + 1 = μ(f) + S` and the tail identity
`length v + S² + b = 2 δ(f) + 2 S`. It is therefore a conditional theorem.
-/

@[expose] public noncomputable section

open Set Filter Topology Real Polynomial

namespace OnLeConjecture.Analytic

open KnotTheory OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

/-- A unit factor does not change the pair ideal of an equation and its first
partial derivative. -/
theorem pairIdeal_mul_unit_partialDerivative (P u : Germ 2) (hu : IsUnit u) :
    pairIdeal (P * u) (partialDerivative (0 : Fin 2) (P * u)) =
      pairIdeal P (partialDerivative (0 : Fin 2) P) := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  apply le_antisymm
  · rw [pairIdeal, Ideal.span_le]
    intro x hx
    rcases (by simpa using hx : x = P * u ∨ x = partialDerivative 0 (P * u)) with rfl | rfl
    · exact Ideal.mul_mem_right u _ (Ideal.subset_span (by simp))
    · rw [partialDerivative_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_right u _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  · rw [pairIdeal, Ideal.span_le]
    intro x hx
    rcases (by simpa using hx : x = P ∨ x = partialDerivative 0 P) with rfl | rfl
    · have h : x * u * v = x := by rw [mul_assoc, hv, mul_one]
      have hmem : x * u * v ∈ Ideal.span {x * u, partialDerivative 0 (x * u)} :=
        Ideal.mul_mem_right v _ (Ideal.subset_span (by simp))
      rwa [h] at hmem
    · have h : partialDerivative 0 P = partialDerivative 0 (P * u) * v -
          (P * u) * (v * partialDerivative 0 u * v) := by
        rw [partialDerivative_mul]
        linear_combination (-(partialDerivative 0 P - P * partialDerivative 0 u * v)) * hv
      rw [h]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right v _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

/-- The polar ideal of the second coordinate is the pair ideal of the first
partial derivative. -/
theorem polarIdeal_coordinate_one (f : Germ 2) :
    polarIdeal f (coordinate (1 : Fin 2)) = pairIdeal f (partialDerivative (0 : Fin 2) f) := by
  rw [polarIdeal, jacobian_eq]
  simp only [partialDerivative_coordinate_same,
    partialDerivative_coordinate_ne (by decide : (0 : Fin 2) ≠ 1), mul_zero, mul_one, sub_zero]

/-- Theorem J15:thm:reduced. For a reduced germ regular of order `m` in the first
coordinate, with Weierstrass factorization `f = P u`, every signed crossing count
of a labelled root family of `P` over every sufficiently small circle satisfies
`Exp + 1 = μ(f) + m`. -/
theorem reduced_signedCount_add_one (f : Germ 2) (hf : f ∈ maximalIdeal 2)
    (hsq : Squarefree f) {m : ℕ} (hm : 0 < m) (hreg : IsRegularInFirstCoordinateOfOrder f m)
    (P : Polynomial (Germ 1)) (u : Germ 2) (hPm : P.Monic) (hPdeg : P.natDegree = m)
    (hdist : ∀ k < m, P.coeff k ∈ maximalIdeal 1) (hu : IsUnit u)
    (hfac : f = firstCoordinatePolynomialEvaluation P * u)
    (A : ℕ → Source 1 → ℂ)
    (hA : ∀ k < m, ∃ hk : AnalyticAt ℂ (A k) 0, P.coeff k = Germ.ofFunction (A k) hk) :
    P.discr ≠ 0 ∧
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ (b : ℝ) (y : Fin m → ℝ → ℂ),
      (∀ k, ContinuousOn (y k) (Icc b (b + 2 * π))) →
      (∀ θ ∈ Icc b (b + 2 * π), ∀ k, (specializedPolynomial m A
        (curveParameterEquiv.symm (circlePath r θ))).eval (y k θ) = 0) →
      (∀ θ ∈ Icc b (b + 2 * π), Function.Injective fun k => y k θ) →
      ∀ (c : ℂ), c ≠ 0 → ∀ D : SheetCrossingData m y b c,
        D.signedCount + 1 = (Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) : ℤ) + m := by
  -- The intersection with the parameter coordinate.
  have hfx1 : HasFiniteIntersection f (coordinate 1) :=
    (hasFiniteIntersection_comm _ _).mp (hasFiniteIntersection_secondCoordinate_of_regular f m hreg)
  have hix : intersectionMultiplicity f (coordinate 1) hfx1 = m := by
    rw [intersectionMultiplicity_comm]
    exact intersectionMultiplicity_secondCoordinate_of_regular f m hreg _
  -- Teissier's polar identity.
  obtain ⟨hpolar, _hJ, heq⟩ := exists_polar_intersection_identity f (coordinate 1) hf
    (coordinate_mem_maximalIdeal 1) hsq hfx1
  have hideal : polarIdeal f (coordinate (1 : Fin 2)) =
      pairIdeal (firstCoordinatePolynomialEvaluation P)
        (firstCoordinatePolynomialEvaluation P.derivative) := by
    rw [polarIdeal_coordinate_one, hfac, pairIdeal_mul_unit_partialDerivative _ u hu,
      partialDerivative_firstCoordinatePolynomialEvaluation]
  have hfinP : HasFiniteIntersection (firstCoordinatePolynomialEvaluation P)
      (firstCoordinatePolynomialEvaluation P.derivative) := by
    have h : Module.Finite ℂ (Germ 2 ⧸ polarIdeal f (coordinate (1 : Fin 2))) := hpolar
    rw [hideal] at h
    exact h
  have hpol : polarIntersectionMultiplicity f (coordinate 1) hpolar =
      intersectionMultiplicity (firstCoordinatePolynomialEvaluation P)
        (firstCoordinatePolynomialEvaluation P.derivative) hfinP := by
    change Module.finrank ℂ (Germ 2 ⧸ polarIdeal f (coordinate (1 : Fin 2))) = _
    rw [hideal]
    rfl
  -- The discriminant is nonzero.
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
  have hder : P.derivative.natDegree = d := by
    rw [natDegree_derivative_germ, hPdeg]
    omega
  have hres' := Germ.resultant_ne_zero_of_hasFiniteIntersection d P P.derivative hPm hPdeg
    (fun k hk => hdist k hk) hfinP
  have hres : P.resultant P.derivative (d + 1) (d + 1 - 1) ≠ 0 := by
    have h : P.resultant P.derivative P.natDegree P.derivative.natDegree ≠ 0 := hres'
    rw [hPdeg, hder] at h
    simpa using h
  have hord := vanishingOrder_discr_eq_resultant (Nat.succ_pos d) P hPm hPdeg
  have hD : P.discr ≠ 0 := by
    intro h0
    apply hres
    rw [← vanishingOrder_eq_top_iff, ← hord, h0, vanishingOrder_zero]
  obtain ⟨⟨hfin', hieq⟩, r₀, hr₀, hall⟩ :=
    discriminant_braid_exponent (Nat.succ_pos d) P hPm hPdeg hdist hD A hA
  refine ⟨hD, r₀, hr₀, fun r hr hrr b y hy hroot hinj c hc D => ?_⟩
  rw [hall r hr hrr b y hy hroot hinj c hc D, ← hieq]
  have hcongr : intersectionMultiplicity (firstCoordinatePolynomialEvaluation P)
      (partialDerivative (0 : Fin 2) (firstCoordinatePolynomialEvaluation P)) hfin' =
      intersectionMultiplicity (firstCoordinatePolynomialEvaluation P)
        (firstCoordinatePolynomialEvaluation P.derivative) hfinP :=
    intersectionMultiplicity_congr rfl (partialDerivative_firstCoordinatePolynomialEvaluation P)
      hfin' hfinP
  rw [hcongr, ← hpol]
  have := heq
  rw [hix] at this
  push_cast
  omega

/-- Part (b) of J15, conditional on the J14 word. Let `f` be reduced, regular of
order `S` in the first coordinate (for a germ of multiplicity `S`, this is the
transversality of the projection), with Weierstrass factorization `f = P u`.
Assume that the word `fullTwistWord S ++ v`, with `v` positive, is a signed event
word of the root braid of `P` over arbitrarily small circles: its exponent is the
signed crossing count of crossing data of a labelled root family. Then its length
is `μ(f) + S - 1`, and `length v + S² + b = 2 δ(f) + 2 S`. -/
theorem fullTwistWord_append_length_of_rootBraid (f : Germ 2) (hf : f ∈ maximalIdeal 2)
    (hsq : Squarefree f) {S : ℕ} (hS : 0 < S) (hreg : IsRegularInFirstCoordinateOfOrder f S)
    (P : Polynomial (Germ 1)) (u : Germ 2) (hPm : P.Monic) (hPdeg : P.natDegree = S)
    (hdist : ∀ k < S, P.coeff k ∈ maximalIdeal 1) (hu : IsUnit u)
    (hfac : f = firstCoordinatePolynomialEvaluation P * u)
    (A : ℕ → Source 1 → ℂ)
    (hA : ∀ k < S, ∃ hk : AnalyticAt ℂ (A k) 0, P.coeff k = Germ.ofFunction (A k) hk)
    (v : PositiveAdjacentWord S)
    (hword : ∀ r₀ : ℝ, 0 < r₀ → ∃ r : ℝ, 0 < r ∧ r < r₀ ∧
      ∃ (b : ℝ) (y : Fin S → ℝ → ℂ),
        (∀ k, ContinuousOn (y k) (Icc b (b + 2 * π))) ∧
        (∀ θ ∈ Icc b (b + 2 * π), ∀ k, (specializedPolynomial S A
          (curveParameterEquiv.symm (circlePath r θ))).eval (y k θ) = 0) ∧
        (∀ θ ∈ Icc b (b + 2 * π), Function.Injective fun k => y k θ) ∧
        ∃ (c : ℂ), c ≠ 0 ∧ ∃ D : SheetCrossingData S y b c,
          SignedAdjacentWord.exponentSum
            (PositiveAdjacentWord.toSigned (fullTwistWord S ++ v)) = D.signedCount) :
    (fullTwistWord S ++ v).length + 1 =
        Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) + S ∧
      v.length + S ^ 2 + irreducibleBranchCount f = 2 * deltaInvariant f + 2 * S := by
  obtain ⟨-, r₀, hr₀, hall⟩ := reduced_signedCount_add_one f hf hsq hS hreg P u hPm hPdeg hdist
    hu hfac A hA
  obtain ⟨r, hr, hrr, b, y, hy, hroot, hinj, c, hc, D, hexp⟩ := hword r₀ hr₀
  have h := hall r hr hrr b y hy hroot hinj c hc D
  rw [← hexp, PositiveAdjacentWord.exponentSum_toSigned] at h
  have hlen : (fullTwistWord S ++ v).length + 1 =
      Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) + S := by exact_mod_cast h
  refine ⟨hlen, ?_⟩
  have hmilnor := jacobianColength_add_irreducibleBranchCount hf hsq
  have htwist : (fullTwistWord S).length = S * (S - 1) := by
    rw [fullTwistWord, torusWord_length]
  rw [List.length_append, htwist] at hlen
  obtain ⟨T, rfl⟩ : ∃ T, S = T + 1 := ⟨S - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlen
  nlinarith [hlen, hmilnor]

/-- Part (b) of J15 with the Weierstrass data supplied by the existing analytic
preparation theorem and by analytic representatives of the coefficients. The
conclusion for a positive word `v` remains conditional on the hypothesis that
`fullTwistWord S ++ v` is a signed event word of the root braid of `P` over
arbitrarily small circles. -/
theorem exists_weierstrass_data_fullTwistWord_append_length (f : Germ 2)
    (hf : f ∈ maximalIdeal 2) (hsq : Squarefree f) {S : ℕ} (hS : 0 < S)
    (hreg : IsRegularInFirstCoordinateOfOrder f S) :
    ∃ (P : Polynomial (Germ 1)) (u : Germ 2) (A : ℕ → Source 1 → ℂ),
      P.Monic ∧ P.natDegree = S ∧ (∀ k < S, P.coeff k ∈ maximalIdeal 1) ∧ IsUnit u ∧
      f = firstCoordinatePolynomialEvaluation P * u ∧
      (∀ k, ∃ hk : AnalyticAt ℂ (A k) 0, P.coeff k = Germ.ofFunction (A k) hk) ∧
      ∀ v : PositiveAdjacentWord S,
        (∀ r₀ : ℝ, 0 < r₀ → ∃ r : ℝ, 0 < r ∧ r < r₀ ∧
          ∃ (b : ℝ) (y : Fin S → ℝ → ℂ),
            (∀ k, ContinuousOn (y k) (Icc b (b + 2 * π))) ∧
            (∀ θ ∈ Icc b (b + 2 * π), ∀ k, (specializedPolynomial S A
              (curveParameterEquiv.symm (circlePath r θ))).eval (y k θ) = 0) ∧
            (∀ θ ∈ Icc b (b + 2 * π), Function.Injective fun k => y k θ) ∧
            ∃ (c : ℂ), c ≠ 0 ∧ ∃ D : SheetCrossingData S y b c,
              SignedAdjacentWord.exponentSum
                (PositiveAdjacentWord.toSigned (fullTwistWord S ++ v)) = D.signedCount) →
        (fullTwistWord S ++ v).length + 1 =
            Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) + S ∧
          v.length + S ^ 2 + irreducibleBranchCount f = 2 * deltaInvariant f + 2 * S := by
  obtain ⟨P, u, hPm, hdeg, hdist, hu, hfac⟩ := hasAnalyticWeierstrassFactorizationOfOrder_of_pos
    hS hreg
  choose A hAan hA using fun k => Germ.exists_ofFunction (P.coeff k)
  refine ⟨P, u, A, hPm, hdeg, hdist, hu, hfac, fun k => ⟨hAan k, hA k⟩, fun v hword => ?_⟩
  exact fullTwistWord_append_length_of_rootBraid f hf hsq hS hreg P u hPm hdeg hdist hu hfac A
    (fun k _ => ⟨hAan k, hA k⟩) v hword

end OnLeConjecture.Analytic
