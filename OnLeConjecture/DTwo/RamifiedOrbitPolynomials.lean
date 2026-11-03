/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitWeightedOrderExpansion
public import OnLeConjecture.Analytic.TwoWeightMonomialIdeal

/-!
# The finite power substitution for the extreme orbit pair

Substitution `(s,lambda)=(x,I*y^a)` carries the ordinary quadratic and
cubic orbit polynomials to the extreme weighted pair. The substitution
is injective for positive `a`, but is not asserted to be a source
coordinate equivalence.
-/

public section

namespace OnLeConjecture.DTwo

open DThree

@[expose] noncomputable def ramifiedOrbitSubstitution (a : ℕ) :
    OrbitSourceForm →ₐ[ℂ] OrbitSourceForm :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.C Complex.I * MvPolynomial.X 1 ^ a]

theorem ramifiedOrbitSubstitution_eval (a : ℕ) (R : OrbitSourceForm) (z : Fin 2 → ℂ) :
    MvPolynomial.eval z (ramifiedOrbitSubstitution a R) =
      MvPolynomial.eval ![z 0, Complex.I * z 1 ^ a] R := by
  change MvPolynomial.aeval z (MvPolynomial.aeval _ R) = MvPolynomial.aeval _ R
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f : Fin 2 → ℂ => MvPolynomial.aeval f R)
  ext i
  fin_cases i <;> simp

theorem ramifiedOrbitSubstitution_injective (a : ℕ) (ha : 0 < a) :
    Function.Injective (ramifiedOrbitSubstitution a) := by
  intro R S hRS
  apply MvPolynomial.funext
  intro z
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (z 1 / Complex.I) ha
  have hh := congrArg (MvPolynomial.eval ![z 0, y]) hRS
  rw [ramifiedOrbitSubstitution_eval, ramifiedOrbitSubstitution_eval] at hh
  have hz : (![z 0, Complex.I * y ^ a] : Fin 2 → ℂ) = z := by
    ext i
    fin_cases i
    · rfl
    · change Complex.I * y ^ a = z 1
      rw [hy, mul_div_cancel₀ _ Complex.I_ne_zero]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, hz] using hh

theorem ramifiedOrbitSubstitution_phi (a : ℕ) :
    ramifiedOrbitSubstitution a (orbitPolynomialPhi ℂ) =
      MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ (2 * a) := by
  have hI : (MvPolynomial.C Complex.I : OrbitSourceForm) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  simp only [ramifiedOrbitSubstitution, orbitPolynomialPhi, orbitPolynomialS,
    orbitPolynomialLambda, map_sub, map_pow, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow, hI, neg_mul, one_mul,
    sub_neg_eq_add]
  rw [← pow_mul, Nat.mul_comm a 2]

theorem ramifiedOrbitSubstitution_psi (a : ℕ) :
    ramifiedOrbitSubstitution a (orbitPolynomialPsi ℂ) =
      2 * MvPolynomial.X 0 ^ 3 + 3 * MvPolynomial.X 0 * MvPolynomial.X 1 ^ (2 * a) := by
  have hI : (MvPolynomial.C Complex.I : OrbitSourceForm) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  simp only [ramifiedOrbitSubstitution, orbitPolynomialPsi, orbitPolynomialS,
    orbitPolynomialLambda, map_sub, map_mul, map_pow, map_ofNat, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow, hI]
  rw [← pow_mul, Nat.mul_comm a 2]
  ring

theorem ramifiedOrbitSubstitution_homogeneous
    (a r : ℕ) (R : OrbitSourceForm) (hR : R.IsHomogeneous r) :
    (ramifiedOrbitSubstitution a R).IsWeightedHomogeneous ![a, 1] (a * r) := by
  rw [ramifiedOrbitSubstitution, MvPolynomial.aeval_eq_bind₁]
  apply OnLeConjecture.Analytic.MvPolynomial.IsWeightedHomogeneous.bind₁_scaled hR
  intro i
  fin_cases i
  · simpa using MvPolynomial.isWeightedHomogeneous_X ℂ (![a, 1] : Fin 2 → ℕ) 0
  · simpa using ((MvPolynomial.isWeightedHomogeneous_X ℂ
      (![a, 1] : Fin 2 → ℕ) 1).pow a).C_mul Complex.I

@[expose] noncomputable def ramifiedOrbitPolynomials (a : ℕ) (R : OrbitSourceForm) :
    Fin 3 → OrbitSourceForm := fun i => ramifiedOrbitSubstitution a (orbitInitialPolynomialMap R i)

@[expose] def ramifiedOrbitDegrees (a r : ℕ) : Fin 3 → ℕ := ![2 * a, 3 * a, a * r]

theorem ramifiedOrbitPolynomials_homogeneous
    (a r : ℕ) (R : OrbitSourceForm) (hR : R.IsHomogeneous r) (i : Fin 3) :
    (ramifiedOrbitPolynomials a R i).IsWeightedHomogeneous ![a, 1]
      (ramifiedOrbitDegrees a r i) := by
  fin_cases i
  · simpa [ramifiedOrbitPolynomials, orbitInitialPolynomialMap, ramifiedOrbitDegrees,
      Nat.mul_comm a 2] using
      ramifiedOrbitSubstitution_homogeneous a 2 (orbitPolynomialPhi ℂ)
        orbitPolynomialPhi_isHomogeneous
  · simpa [ramifiedOrbitPolynomials, orbitInitialPolynomialMap, ramifiedOrbitDegrees,
      Nat.mul_comm a 3] using
      ramifiedOrbitSubstitution_homogeneous a 3 (orbitPolynomialPsi ℂ)
        orbitPolynomialPsi_isHomogeneous
  · exact ramifiedOrbitSubstitution_homogeneous a r R hR

theorem ramifiedOrbitPolynomials_eval (a : ℕ) (R : OrbitSourceForm) (z : ℂ × ℂ) :
    weightedPolynomialMap (ramifiedOrbitPolynomials a R) z =
      weightedPolynomialMap (orbitInitialPolynomialMap R) (z.1, Complex.I * z.2 ^ a) := by
  ext i
  exact ramifiedOrbitSubstitution_eval a (orbitInitialPolynomialMap R i) _

@[expose] noncomputable def ramifiedOrbitBaseHom (a : ℕ) :
    OrbitBaseRing ℂ →ₐ[ℂ] OrbitSourceForm :=
  (ramifiedOrbitSubstitution a).comp (orbitBaseToSource ℂ)

theorem not_orbitBase_of_ramified_not_base (a : ℕ) (R : OrbitSourceForm)
    (hR : ramifiedOrbitSubstitution a R ∉ Set.range (ramifiedOrbitBaseHom a)) :
    R ∉ Set.range (orbitBaseToSource ℂ) := by
  rintro ⟨P, rfl⟩
  exact hR ⟨P, rfl⟩

end OnLeConjecture.DTwo

