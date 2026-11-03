/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitProjective
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Scalar points of the orbit conic

This file proves that the polynomial parametrization of the orbit conic is
surjective on complex points. It also transfers a polynomial identity on the
parametrization to every residual pair.
-/

public section

namespace OnLeConjecture.DTwo

/-- The two equations defining an ordered pair in the residual fibre
relation. -/
@[expose]
def IsOrbitResidualPair (s lambda t zeta : ℂ) : Prop :=
  t ^ 2 + s * t - 2 * s ^ 2 + 3 * lambda ^ 2 = 0 ∧
    zeta ^ 2 = t ^ 2 - s ^ 2 + lambda ^ 2

theorem orbitConicRhoValue_eq (delta u v : ℂ) :
    orbitConicRhoValue delta u v = delta * (u ^ 2 + v ^ 2) := by
  rw [← orbitConicRho_eval]
  simp [orbitConicRho, orbitParameterU, orbitParameterV]

theorem orbitConicAlphaValue_eq (u v : ℂ) :
    orbitConicAlphaValue u v = u ^ 2 - v ^ 2 := by
  rw [← orbitConicAlpha_eval]
  simp [orbitConicAlpha, orbitParameterU, orbitParameterV]

theorem orbitConicBetaValue_eq (u v : ℂ) :
    orbitConicBetaValue u v = 2 * u * v := by
  rw [← orbitConicBeta_eval]
  simp [orbitConicBeta, orbitParameterU, orbitParameterV]

/-- Every complex point of the orbit conic lies in the image of its
polynomial parametrization. -/
theorem exists_orbitConicValues_eq
    {delta rho alpha beta : ℂ}
    (hdelta : delta ^ 2 = 3)
    (hconic : rho ^ 2 = 3 * (alpha ^ 2 + beta ^ 2)) :
    ∃ u v : ℂ,
      orbitConicRhoValue delta u v = rho ∧
        orbitConicAlphaValue u v = alpha ∧
        orbitConicBetaValue u v = beta := by
  have hdeltaNe : delta ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hdelta
    norm_num at hdelta
  let a : ℂ := rho / delta
  have ha : a ^ 2 = alpha ^ 2 + beta ^ 2 := by
    dsimp only [a]
    field_simp [hdeltaNe]
    linear_combination hconic - (alpha ^ 2 + beta ^ 2) * hdelta
  have hrhoA : delta * a = rho := by
    dsimp only [a]
    field_simp [hdeltaNe]
  obtain ⟨u, hu⟩ :=
    IsAlgClosed.exists_eq_mul_self ((a + alpha) / 2)
  have huSq : u ^ 2 = (a + alpha) / 2 := by
    simpa [pow_two] using hu.symm
  by_cases huZero : u = 0
  · have haAlpha : a + alpha = 0 := by
      rw [huZero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at huSq
      have hquotient : (a + alpha) / 2 = 0 := huSq.symm
      exact ((div_eq_zero_iff).mp hquotient).resolve_right (by norm_num)
    have hbeta : beta = 0 := by
      have hbetaSq : beta ^ 2 = 0 := by
        rw [show a = -alpha by linear_combination haAlpha] at ha
        linear_combination -ha
      exact sq_eq_zero_iff.mp hbetaSq
    obtain ⟨v, hv⟩ :=
      IsAlgClosed.exists_eq_mul_self ((a - alpha) / 2)
    have hvSq : v ^ 2 = (a - alpha) / 2 := by
      simpa [pow_two] using hv.symm
    refine ⟨0, v, ?_, ?_, ?_⟩
    · rw [orbitConicRhoValue_eq,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        zero_add, hvSq]
      rw [← hrhoA]
      linear_combination -(delta / 2) * haAlpha
    · rw [orbitConicAlphaValue_eq,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub, hvSq]
      linear_combination -(1 / 2 : ℂ) * haAlpha
    · rw [orbitConicBetaValue_eq, hbeta]
      ring
  · let v : ℂ := beta / (2 * u)
    have hfactor : beta ^ 2 = (a + alpha) * (a - alpha) := by
      linear_combination -ha
    have huMul : 2 * u ^ 2 = a + alpha := by
      linear_combination 2 * huSq
    have hbetaFactor : beta ^ 2 = 2 * u ^ 2 * (a - alpha) := by
      rw [hfactor, ← huMul]
    have hvSq : v ^ 2 = (a - alpha) / 2 := by
      dsimp only [v]
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero 2
        (mul_ne_zero (by norm_num) huZero))).2
      calc
        beta ^ 2 = 2 * u ^ 2 * (a - alpha) := hbetaFactor
        _ = (a - alpha) / 2 * (2 * u) ^ 2 := by ring
    refine ⟨u, v, ?_, ?_, ?_⟩
    · rw [orbitConicRhoValue_eq, huSq, hvSq]
      rw [← hrhoA]
      ring
    · rw [orbitConicAlphaValue_eq, huSq, hvSq]
      ring
    · rw [orbitConicBetaValue_eq]
      dsimp only [v]
      field_simp [huZero]

/-- The residual equations imply the quadratic equation used to invert the
conic parametrization. -/
theorem IsOrbitResidualPair.conicEquation
    {s lambda t zeta : ℂ}
    (hresidual : IsOrbitResidualPair s lambda t zeta) :
    (t - s) ^ 2 = 3 * (zeta ^ 2 + lambda ^ 2) := by
  rcases hresidual with ⟨hfirst, hsecond⟩
  rw [hsecond]
  linear_combination -2 * hfirst

/-- A pure power identity on the conic parametrization holds on every
residual pair satisfying the conic equation. -/
theorem orbitConicDifference_identity_on_residualPair
    {delta coefficient s lambda t zeta : ℂ}
    {R : OrbitSourceForm} {r : ℕ}
    (hdelta : delta ^ 2 = 3)
    (hidentity : orbitConicDifference delta R =
      MvPolynomial.C coefficient * (orbitConicT - orbitConicS) ^ r)
    (hresidual : IsOrbitResidualPair s lambda t zeta)
    (hconic : (t - s) ^ 2 = 3 * (zeta ^ 2 + lambda ^ 2)) :
    MvPolynomial.eval ![s, lambda] R -
        MvPolynomial.eval ![t, zeta] R =
      coefficient * (t - s) ^ r := by
  rcases hresidual with ⟨hfirst, hsecond⟩
  by_cases hst : s = t
  · subst t
    have hlambda : lambda = 0 := by
      have hlambdaSq : lambda ^ 2 = 0 := by
        linear_combination (1 / 3 : ℂ) * hfirst
      exact sq_eq_zero_iff.mp hlambdaSq
    have hzeta : zeta = 0 := by
      rw [hlambda, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsecond
      have hzetaSq : zeta ^ 2 = 0 := by
        linear_combination hsecond
      exact sq_eq_zero_iff.mp hzetaSq
    subst lambda
    subst zeta
    by_cases hr : r = 0
    · subst r
      have heval := congrArg
        (fun form : OrbitParameterForm ↦
          MvPolynomial.eval ![(0 : ℂ), 0] form) hidentity
      rw [orbitConicDifference_eval] at heval
      simp only [MvPolynomial.eval_C, pow_zero, mul_one] at heval
      rw [orbitConicRhoValue_eq, orbitConicAlphaValue_eq,
        orbitConicBetaValue_eq] at heval
      norm_num at heval
      simpa only [sub_self, pow_zero, mul_one] using heval
    · simp [hr]
  · have htSubS : t - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hst)
    obtain ⟨rho, hrho⟩ := IsAlgClosed.exists_eq_mul_self (t - s)
    have hrhoSq : rho ^ 2 = t - s := by
      simpa [pow_two] using hrho.symm
    have hrhoNe : rho ≠ 0 := by
      intro hrhoZero
      rw [hrhoZero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hrhoSq
      exact htSubS hrhoSq.symm
    let alpha : ℂ := zeta / rho
    let beta : ℂ := lambda / rho
    have hparameterConic :
        rho ^ 2 = 3 * (alpha ^ 2 + beta ^ 2) := by
      have hfour : rho ^ 4 = 3 * (zeta ^ 2 + lambda ^ 2) := by
        rw [show rho ^ 4 = (rho ^ 2) ^ 2 by ring, hrhoSq]
        exact hconic
      dsimp only [alpha, beta]
      field_simp [hrhoNe]
      exact hfour
    obtain ⟨u, v, hrhoValue, halphaValue, hbetaValue⟩ :=
      exists_orbitConicValues_eq hdelta hparameterConic
    have hsValue :
        -(orbitConicAlphaValue u v ^ 2 +
            2 * orbitConicBetaValue u v ^ 2) = s := by
      rw [halphaValue, hbetaValue]
      dsimp only [alpha, beta]
      field_simp [hrhoNe]
      rw [hrhoSq]
      linear_combination -hfirst - hsecond
    have hlambdaValue :
        orbitConicRhoValue delta u v * orbitConicBetaValue u v =
          lambda := by
      rw [hrhoValue, hbetaValue]
      dsimp only [beta]
      field_simp [hrhoNe]
    have htValue :
        2 * orbitConicAlphaValue u v ^ 2 +
            orbitConicBetaValue u v ^ 2 = t := by
      rw [halphaValue, hbetaValue]
      dsimp only [alpha, beta]
      field_simp [hrhoNe]
      rw [hrhoSq]
      linear_combination hfirst + 2 * hsecond
    have hzetaValue :
        orbitConicRhoValue delta u v * orbitConicAlphaValue u v =
          zeta := by
      rw [hrhoValue, halphaValue]
      dsimp only [alpha]
      field_simp [hrhoNe]
    have heval := congrArg
      (fun form : OrbitParameterForm ↦ MvPolynomial.eval ![u, v] form)
        hidentity
    rw [orbitConicDifference_eval] at heval
    simp only [map_mul, MvPolynomial.eval_C, map_pow, map_sub] at heval
    rw [orbitConicT_eval, orbitConicS_eval] at heval
    rw [hsValue, hlambdaValue, htValue, hzetaValue] at heval
    exact heval

end OnLeConjecture.DTwo
