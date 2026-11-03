/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Injectivity
public import OnLeConjecture.Analytic.LinearCoordinates
public import OnLeConjecture.Analytic.PolynomialCoordinates
public import OnLeConjecture.Analytic.PullbackEquivalence

/-!
# Diagonal analytic coordinate changes

Nonzero coordinate scalars define invertible linear pointed germs. Their
pullbacks agree with diagonal substitution on polynomials and preserve every
power of the maximal ideal.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

/-- The continuous linear equivalence that multiplies coordinate `i` by
`a i`. -/
@[expose]
noncomputable def diagonalContinuousLinearEquiv {n : ℕ}
    (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0) :
    Source n ≃L[ℂ] Source n :=
  ContinuousLinearEquiv.piCongrRight fun i ↦
    ContinuousLinearEquiv.smulLeft (Units.mk0 (a i) (ha i))

@[simp]
theorem diagonalContinuousLinearEquiv_apply {n : ℕ}
    (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0)
    (z : Source n) (i : Fin n) :
    diagonalContinuousLinearEquiv a ha z i = a i * z i := by
  rw [diagonalContinuousLinearEquiv,
    ContinuousLinearEquiv.piCongrRight_apply]
  rfl

/-- The pointed germ induced by a diagonal linear equivalence. -/
@[expose]
noncomputable def diagonalPointedEquiv {n : ℕ}
    (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0) :
    PointedEquivGerm n :=
  Germ.pointedEquivGermOfContinuousLinearEquiv
    (diagonalContinuousLinearEquiv a ha)

/-- The scalar components of a diagonal pointed equivalence. -/
theorem diagonalPointedEquiv_component {n : ℕ}
    (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0) (i : Fin n) :
    (diagonalPointedEquiv a ha).forward.1.component i =
      Germ.constRingHom n (a i) * Germ.coordinate i := by
  simp only [diagonalPointedEquiv,
    Germ.pointedEquivGermOfContinuousLinearEquiv]
  apply Subtype.ext
  change
    ((MapGerm.ofFunction (diagonalContinuousLinearEquiv a ha)
      ((diagonalContinuousLinearEquiv a ha).analyticAt 0)).component i).1 =
      (Germ.constRingHom n (a i) * Germ.coordinate i).1
  rw [MapGerm.component_ofFunction]
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦
    diagonalContinuousLinearEquiv_apply a ha z i

/-- Diagonal substitution in a multivariate polynomial. -/
@[expose]
noncomputable def diagonalPolynomialSubstitution {n : ℕ}
    (a : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →+* MvPolynomial (Fin n) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i ↦ MvPolynomial.C (a i) * MvPolynomial.X i)

/-- Diagonal polynomial substitution as a complex algebra homomorphism. -/
@[expose]
noncomputable def diagonalPolynomialSubstitutionAlgHom {n : ℕ}
    (a : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  MvPolynomial.aeval
    (fun i ↦ MvPolynomial.C (a i) * MvPolynomial.X i)

@[simp]
theorem diagonalPolynomialSubstitutionAlgHom_apply {n : ℕ}
    (a : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    diagonalPolynomialSubstitutionAlgHom a p =
      diagonalPolynomialSubstitution a p := by
  rfl

@[simp]
theorem diagonalPolynomialSubstitution_C {n : ℕ}
    (a : Fin n → ℂ) (c : ℂ) :
    diagonalPolynomialSubstitution a (MvPolynomial.C c) =
      MvPolynomial.C c := by
  simp [diagonalPolynomialSubstitution]

@[simp]
theorem diagonalPolynomialSubstitution_X {n : ℕ}
    (a : Fin n → ℂ) (i : Fin n) :
    diagonalPolynomialSubstitution a (MvPolynomial.X i) =
      MvPolynomial.C (a i) * MvPolynomial.X i := by
  simp [diagonalPolynomialSubstitution]

/-- Substitution by the coordinatewise inverses is a left inverse to a
diagonal substitution by nonzero scalars. -/
theorem diagonalPolynomialSubstitution_inverse_comp {n : ℕ}
    (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0) :
    ((diagonalPolynomialSubstitution (fun i ↦ (a i)⁻¹)).comp
      (diagonalPolynomialSubstitution a)) =
        RingHom.id (MvPolynomial (Fin n) ℂ) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    simp only [RingHom.comp_apply, diagonalPolynomialSubstitution_X,
      map_mul, diagonalPolynomialSubstitution_C]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (ha i), map_one,
      one_mul]
    rfl

/-- Diagonal substitution by nonzero coordinate scalars is injective. -/
theorem diagonalPolynomialSubstitution_injective {n : ℕ}
    (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0) :
    Function.Injective (diagonalPolynomialSubstitution a) := by
  apply Function.LeftInverse.injective
    (g := diagonalPolynomialSubstitution fun i ↦ (a i)⁻¹)
  intro p
  change (((diagonalPolynomialSubstitution (fun i ↦ (a i)⁻¹)).comp
    (diagonalPolynomialSubstitution a)) p) = p
  rw [diagonalPolynomialSubstitution_inverse_comp a ha]
  rfl

/-- Pullback by a diagonal pointed equivalence agrees with diagonal
substitution followed by coordinate evaluation. -/
theorem diagonalPointedEquiv_pullback_coordinatePolynomial {n : ℕ}
    (a : Fin n → ℂ) (ha : ∀ i, a i ≠ 0)
    (p : MvPolynomial (Fin n) ℂ) :
    (diagonalPointedEquiv a ha).forward.pullbackRingHom
        (Germ.coordinatePolynomialAlgHom n p) =
      Germ.coordinatePolynomialAlgHom n
        (diagonalPolynomialSubstitution a p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [Germ.coordinatePolynomialAlgHom_C,
        PointedMapGerm.pullback_constRingHom,
        diagonalPolynomialSubstitution_C,
        Germ.coordinatePolynomialAlgHom_C]
  | add p q hp hq =>
      calc
        (diagonalPointedEquiv a ha).forward.pullbackRingHom
            (Germ.coordinatePolynomialAlgHom n (p + q)) =
          (diagonalPointedEquiv a ha).forward.pullbackRingHom
              (Germ.coordinatePolynomialAlgHom n p) +
            (diagonalPointedEquiv a ha).forward.pullbackRingHom
              (Germ.coordinatePolynomialAlgHom n q) := by rw [map_add, map_add]
        _ = Germ.coordinatePolynomialAlgHom n
              (diagonalPolynomialSubstitution a p) +
            Germ.coordinatePolynomialAlgHom n
              (diagonalPolynomialSubstitution a q) := by rw [hp, hq]
        _ = Germ.coordinatePolynomialAlgHom n
            (diagonalPolynomialSubstitution a (p + q)) := by
              rw [map_add, map_add]
  | mul_X p i hp =>
      calc
        (diagonalPointedEquiv a ha).forward.pullbackRingHom
            (Germ.coordinatePolynomialAlgHom n
              (p * MvPolynomial.X i)) =
          (diagonalPointedEquiv a ha).forward.pullbackRingHom
              (Germ.coordinatePolynomialAlgHom n p) *
            (diagonalPointedEquiv a ha).forward.pullbackRingHom
              (Germ.coordinatePolynomialAlgHom n
                (MvPolynomial.X i)) := by rw [map_mul, map_mul]
        _ = Germ.coordinatePolynomialAlgHom n
              (diagonalPolynomialSubstitution a p) *
            (Germ.constRingHom n (a i) * Germ.coordinate i) := by
              rw [hp, Germ.coordinatePolynomialAlgHom_X,
                (diagonalPointedEquiv a ha).forward.pullback_coordinate,
                diagonalPointedEquiv_component]
        _ = Germ.coordinatePolynomialAlgHom n
            (diagonalPolynomialSubstitution a
              (p * MvPolynomial.X i)) := by
              rw [(diagonalPolynomialSubstitution a).map_mul,
                diagonalPolynomialSubstitution_X]
              calc
                Germ.coordinatePolynomialAlgHom n
                      (diagonalPolynomialSubstitution a p) *
                    (Germ.constRingHom n (a i) * Germ.coordinate i) =
                  Germ.coordinatePolynomialAlgHom n
                      (diagonalPolynomialSubstitution a p) *
                    Germ.coordinatePolynomialAlgHom n
                      (MvPolynomial.C (a i) * MvPolynomial.X i) := by
                        rw [map_mul, Germ.coordinatePolynomialAlgHom_C,
                          Germ.coordinatePolynomialAlgHom_X]
                _ = Germ.coordinatePolynomialAlgHom n
                    (diagonalPolynomialSubstitution a p *
                      (MvPolynomial.C (a i) * MvPolynomial.X i)) := by
                        exact (map_mul (Germ.coordinatePolynomialAlgHom n)
                          (diagonalPolynomialSubstitution a p)
                          (MvPolynomial.C (a i) *
                            MvPolynomial.X i)).symm

/-- Pullback by an analytic equivalence preserves membership in every power
of the maximal ideal. -/
theorem PointedEquivGerm.pullback_mem_maximalIdeal_pow {n k : ℕ}
    (e : PointedEquivGerm n) {q : Germ n}
    (hq : q ∈ Germ.maximalIdeal n ^ k) :
    e.forward.pullbackRingHom q ∈ Germ.maximalIdeal n ^ k := by
  have hmap := Ideal.mem_map_of_mem e.pullbackRingEquiv.toRingHom hq
  rw [Ideal.map_pow, e.map_maximalIdeal_pullbackRingEquiv] at hmap
  exact hmap

/-- A right left diagonal coordinate change has an injective representative
exactly when the original pointed germ does. -/
theorem diagonal_rightLeft_hasInjectiveRepresentative_iff
    {n m : ℕ} (f : PointedMapGerm n m)
    (sourceScale : Fin n → ℂ) (targetScale : Fin m → ℂ)
    (hsource : ∀ i, sourceScale i ≠ 0)
    (htarget : ∀ i, targetScale i ≠ 0) :
    ((diagonalPointedEquiv targetScale htarget).forward.comp
      (f.comp (diagonalPointedEquiv sourceScale hsource).forward)
        ).HasInjectiveRepresentative ↔ f.HasInjectiveRepresentative := by
  let source := diagonalPointedEquiv sourceScale hsource
  let target := diagonalPointedEquiv targetScale htarget
  have hequivalent : f.RightLeftEquivalent
      (target.forward.comp (f.comp source.forward)) :=
    ⟨source, target, rfl⟩
  exact hequivalent.hasInjectiveRepresentative_iff

end OnLeConjecture.Analytic
