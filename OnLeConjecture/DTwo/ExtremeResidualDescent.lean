/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.ExtremeResidualFourier
public import OnLeConjecture.DTwo.RamifiedOrbitPolynomials
public import OnLeConjecture.Polynomial.CoordinatePowerDivisibility

/-!
# Polynomial descent of the extreme residual

The invariant terms and the pure second-coordinate power descend through
`(x,y) ↦ (x,I yᵃ)` exactly when the total weighted degree is divisible by
`a`. Coordinate divisibility also descends. In the other degree class,
the invariant part vanishes.
-/

public section

namespace OnLeConjecture.DTwo

open MvPolynomial

theorem extreme_invariant_degree_dvd (a D : ℕ)
    (U : OrbitSourceForm) (hU : U ∈ cyclicInvariantAlgebra (2 * a))
    (hhom : U.IsWeightedHomogeneous ![a, 1] D) (hne : U ≠ 0) : a ∣ D := by
  let G : Fin 2 → OrbitSourceForm := ![X 0, X 1 ^ (2 * a)]
  have hG : ∀ i, (G i).IsWeightedHomogeneous ![a, 1] (![a, 2 * a] i) := by
    intro i
    fin_cases i
    · exact isWeightedHomogeneous_X ℂ (![a, 1] : Fin 2 → ℕ) 0
    · simpa [G] using (isWeightedHomogeneous_X ℂ (![a, 1] : Fin 2 → ℕ) 1).pow (2 * a)
  obtain ⟨V, hV, hVU⟩ := OnLeConjecture.Polynomial.exists_homogeneous_preimage_of_mem_range
    ![a, 2 * a] ![a, 1] G hG hhom hU
  have hVne : V ≠ 0 := by intro hz; simp [hz] at hVU; exact hne hVU.symm
  obtain ⟨d, hd⟩ : ∃ d, coeff d V ≠ 0 := by
    by_contra! hall
    apply hVne
    ext d
    simpa using hall d
  have hdD : a * d 0 + (2 * a) * d 1 = D := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hV hd
  exact ⟨d 0 + 2 * d 1, by rw [← hdD]; ring⟩

theorem extreme_residual_eq_pure_power_of_degree_not_dvd
    (a D : ℕ) (R U : OrbitSourceForm) (c : ℂ)
    (hU : U ∈ cyclicInvariantAlgebra (2 * a))
    (hhom : U.IsWeightedHomogeneous ![a, 1] D)
    (heq : R = U + C c * X 1 ^ D) (hdegree : ¬ a ∣ D) :
    R = C c * X 1 ^ D := by
  have hzero : U = 0 := by
    by_contra hne
    exact hdegree (extreme_invariant_degree_dvd a D U hU hhom hne)
  simpa only [hzero, zero_add] using heq

theorem extreme_invariant_mem_ramified_range (a : ℕ)
    (U : OrbitSourceForm) (hU : U ∈ cyclicInvariantAlgebra (2 * a)) :
    U ∈ (ramifiedOrbitSubstitution a).range := by
  obtain ⟨V, hV⟩ := hU
  let q : OrbitSourceForm →ₐ[ℂ] OrbitSourceForm := aeval ![X 0, -X 1 ^ 2]
  have hcomp : (ramifiedOrbitSubstitution a).comp q =
      aeval (![X 0, X 1 ^ (2 * a)] : Fin 2 → OrbitSourceForm) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [q, ramifiedOrbitSubstitution]
    · simp only [AlgHom.comp_apply, q, aeval_X]
      change ramifiedOrbitSubstitution a (-X 1 ^ 2) = X 1 ^ (2 * a)
      rw [map_neg, map_pow]
      have hX : ramifiedOrbitSubstitution a (X 1) = C Complex.I * X 1 ^ a := by
        simp [ramifiedOrbitSubstitution]
      rw [hX, mul_pow, ← map_pow, Complex.I_sq, map_neg, map_one,
        neg_mul, one_mul, neg_neg, ← pow_mul, Nat.mul_comm a 2]
  refine ⟨q V, ?_⟩
  change ((ramifiedOrbitSubstitution a).comp q) V = U
  rw [hcomp]
  exact hV

theorem extreme_residual_mem_ramified_range
    (a D : ℕ) (R U : OrbitSourceForm) (c : ℂ)
    (hU : U ∈ cyclicInvariantAlgebra (2 * a))
    (heq : R = U + C c * X 1 ^ D) (hdegree : a ∣ D) :
    R ∈ (ramifiedOrbitSubstitution a).range := by
  rw [heq]
  apply Subalgebra.add_mem _ (extreme_invariant_mem_ramified_range a U hU)
  obtain ⟨n, hn⟩ := hdegree
  refine ⟨C (c / Complex.I ^ n) * X 1 ^ n, ?_⟩
  change ramifiedOrbitSubstitution a (C (c / Complex.I ^ n) * X 1 ^ n) = _
  rw [map_mul, map_pow]
  have hC : ramifiedOrbitSubstitution a (C (c / Complex.I ^ n)) =
      C (c / Complex.I ^ n) := by simp [ramifiedOrbitSubstitution]
  have hX : ramifiedOrbitSubstitution a (X 1) = C Complex.I * X 1 ^ a := by
    simp [ramifiedOrbitSubstitution]
  rw [hC, hX, mul_pow, ← pow_mul, ← map_pow, ← mul_assoc, ← map_mul,
    div_mul_cancel₀ c (pow_ne_zero n Complex.I_ne_zero), ← hn]

/-- Positive ramification has the expected effect on coordinate powers. -/
theorem variable_pow_dvd_of_ramifiedOrbit_dvd
    (a N : ℕ) (ha : 0 < a) (R : OrbitSourceForm)
    (hdiv : X (1 : Fin 2) ^ (a * N) ∣ ramifiedOrbitSubstitution a R) :
    X (1 : Fin 2) ^ N ∣ R := by
  let q : OrbitSourceForm →ₐ[ℂ] OrbitSourceForm := aeval ![X 0, C Complex.I * X 1]
  let qinv : OrbitSourceForm →ₐ[ℂ] OrbitSourceForm := aeval ![X 0, C (-Complex.I) * X 1]
  have hcomp : (aeval (![X 0, X 1 ^ a] : Fin 2 → OrbitSourceForm)).comp q =
      ramifiedOrbitSubstitution a := by
    ext i
    fin_cases i <;> simp [q, ramifiedOrbitSubstitution]
  have hcancel : qinv.comp q = AlgHom.id ℂ OrbitSourceForm := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [q, qinv]
    · simp only [AlgHom.comp_apply, q, aeval_X, AlgHom.id_apply]
      change qinv (C Complex.I * X 1) = X 1
      rw [map_mul]
      simp only [qinv, aeval_C, aeval_X]
      change C Complex.I * (C (-Complex.I) * X 1) = X 1
      rw [← mul_assoc, ← map_mul]
      simp
  have hplain : X (1 : Fin 2) ^ (a * N) ∣
      aeval (![X 0, X 1 ^ a] : Fin 2 → OrbitSourceForm) (q R) := by
    change X (1 : Fin 2) ^ (a * N) ∣ ((aeval _).comp q) R
    rwa [hcomp]
  have hqdiv := OnLeConjecture.Polynomial.second_variable_pow_dvd_of_ramified_dvd
    a N ha (q R) hplain
  have hpull := map_dvd qinv hqdiv
  have hR : qinv (q R) = R := congrArg (fun e => e R) hcancel
  rw [hR] at hpull
  have hleft : X (1 : Fin 2) ^ N ∣ qinv (X 1 ^ N) := by
    simp only [qinv, map_pow, aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [mul_pow]
    exact dvd_mul_left _ _
  exact hleft.trans hpull

/-- A homogeneous preimage is constructed, and its ordinary degree and
fourth coordinate factor are deduced rather than assumed. -/
theorem extreme_residual_homogeneous_descent
    (a D : ℕ) (ha : 0 < a) (R U : OrbitSourceForm) (c : ℂ)
    (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (hU : U ∈ cyclicInvariantAlgebra (2 * a))
    (heq : R = U + C c * X 1 ^ D) (hdegree : a ∣ D)
    (hdiv : X (1 : Fin 2) ^ (4 * a) ∣ R) :
    ∃ S : OrbitSourceForm, S.IsHomogeneous (D / a) ∧
      X (1 : Fin 2) ^ 4 ∣ S ∧ ramifiedOrbitSubstitution a S = R := by
  have hG : ∀ i, (![X 0, C Complex.I * X 1 ^ a] : Fin 2 → OrbitSourceForm) i
      |>.IsWeightedHomogeneous ![a, 1] (![a, a] i) := by
    intro i
    fin_cases i
    · exact isWeightedHomogeneous_X ℂ (![a, 1] : Fin 2 → ℕ) 0
    · simpa using ((isWeightedHomogeneous_X ℂ (![a, 1] : Fin 2 → ℕ) 1).pow a).C_mul
        Complex.I
  obtain ⟨S, hS, hSR⟩ := OnLeConjecture.Polynomial.exists_homogeneous_preimage_of_mem_range
    ![a, a] ![a, 1] ![X 0, C Complex.I * X 1 ^ a] hG hR
    (extreme_residual_mem_ramified_range a D R U c hU heq hdegree)
  have hSord : S.IsHomogeneous (D / a) := by
    intro d hd
    have hweight : a * (d 0 + d 1) = D := by
      have hh := hS hd
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm, Nat.mul_add] using hh
    have hsum : d 0 + d 1 = D / a := by rw [← hweight, Nat.mul_div_right _ ha]
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using hsum
  refine ⟨S, hSord, ?_, hSR⟩
  apply variable_pow_dvd_of_ramifiedOrbit_dvd a 4 ha S
  change X (1 : Fin 2) ^ (a * 4) ∣ aeval _ S
  rw [hSR, Nat.mul_comm a 4]
  exact hdiv

end OnLeConjecture.DTwo
