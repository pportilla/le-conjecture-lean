/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PolynomialJets
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# Evaluation of analytic germs at nilpotent tuples

A tuple of nilpotent elements in a complex algebra admits evaluation of
analytic germs. Only a finite polynomial jet is needed. The resulting
homomorphism is uniquely determined among homomorphisms annihilating a
power of the analytic maximal ideal. No convergence or completeness
assumption on the target algebra is required.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic.Germ

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Polynomial coordinate evaluation maps the variable ideal onto the ideal
spanned by the assigned coordinates. -/
theorem map_idealOfVars_aeval {n : ℕ} (x : Fin n → R) :
    Ideal.map (MvPolynomial.aeval x) (MvPolynomial.idealOfVars (Fin n) ℂ) =
      Ideal.span (Set.range x) := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span]
  congr 1
  ext y
  simp

/-- Evaluation through a finite polynomial jet at a tuple whose generated
ideal has zero `N`th power. -/
def nilpotentEvaluation {n N : ℕ} (x : Fin n → R)
    (hx : (Ideal.span (Set.range x) : Ideal R) ^ N = ⊥) : Germ n →ₐ[ℂ] R := by
  let ev : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R := MvPolynomial.aeval x
  have hker : MvPolynomial.idealOfVars (Fin n) ℂ ^ N ≤ RingHom.ker ev := by
    change _ ≤ Ideal.comap ev ⊥
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, map_idealOfVars_aeval, hx]
  exact (Ideal.Quotient.liftₐ _ ev (fun _ hp ↦ RingHom.mem_ker.mp (hker hp))).comp
    ((coordinatePolynomialQuotientAlgEquiv n N).symm.toAlgHom.comp
      (Ideal.Quotient.mkₐ ℂ (maximalIdeal n ^ N)))

/-- The assigned values are the images of the coordinate germs. -/
@[simp]
theorem nilpotentEvaluation_coordinate {n N : ℕ} (x : Fin n → R)
    (hx : (Ideal.span (Set.range x) : Ideal R) ^ N = ⊥) (i : Fin n) :
    nilpotentEvaluation x hx (coordinate i) = x i := by
  have heq : Ideal.Quotient.mk (maximalIdeal n ^ N) (coordinate i) =
      coordinatePolynomialQuotientAlgEquiv n N
        (Ideal.Quotient.mk (MvPolynomial.idealOfVars (Fin n) ℂ ^ N) (MvPolynomial.X i)) := by
    simp [coordinatePolynomialQuotientAlgEquiv, coordinatePolynomialQuotientAlgHom_mk]
  simp only [nilpotentEvaluation, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    AlgEquiv.coe_toAlgHom, heq, AlgEquiv.symm_apply_apply]
  exact MvPolynomial.aeval_X x i

/-- The evaluation annihilates the prescribed maximal-ideal power. -/
theorem maximalIdeal_pow_le_ker_nilpotentEvaluation {n N : ℕ} (x : Fin n → R)
    (hx : (Ideal.span (Set.range x) : Ideal R) ^ N = ⊥) :
    maximalIdeal n ^ N ≤ RingHom.ker (nilpotentEvaluation x hx) := by
  intro g hg
  change nilpotentEvaluation x hx g = 0
  simp only [nilpotentEvaluation, AlgHom.comp_apply]
  rw [show (Ideal.Quotient.mkₐ ℂ (maximalIdeal n ^ N)) g = 0 from
    Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero, map_zero]

/-- Homomorphisms annihilating a maximal-ideal power are determined by the
images of the coordinate germs. -/
theorem algHom_ext_of_maximalIdeal_pow_le_ker {n N : ℕ}
    (φ ψ : Germ n →ₐ[ℂ] R)
    (hφ : maximalIdeal n ^ N ≤ RingHom.ker φ)
    (hψ : maximalIdeal n ^ N ≤ RingHom.ker ψ)
    (hcoord : ∀ i, φ (coordinate i) = ψ (coordinate i)) : φ = ψ := by
  have hpolynomial : φ.comp (coordinatePolynomialAlgHom n) =
      ψ.comp (coordinatePolynomialAlgHom n) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa using hcoord i
  apply AlgHom.ext
  intro g
  obtain ⟨p, hp⟩ := exists_coordinatePolynomial_mod_maximalIdeal_pow n N g
  have hφp : φ g = φ (coordinatePolynomialAlgHom n p) := by
    apply sub_eq_zero.mp
    simpa only [RingHom.mem_ker, map_sub] using hφ hp
  have hψp : ψ g = ψ (coordinatePolynomialAlgHom n p) := by
    apply sub_eq_zero.mp
    simpa only [RingHom.mem_ker, map_sub] using hψ hp
  rw [hφp, hψp]
  exact AlgHom.congr_fun hpolynomial p

/-- Every finite tuple of nilpotent elements permits analytic germ
evaluation, with some maximal-ideal power annihilated. -/
theorem exists_evaluation_of_isNilpotent {n : ℕ} (x : Fin n → R)
    (hx : ∀ i, IsNilpotent (x i)) :
    ∃ (φ : Germ n →ₐ[ℂ] R) (N : ℕ),
      maximalIdeal n ^ N ≤ RingHom.ker φ ∧ ∀ i, φ (coordinate i) = x i := by
  have hfg : (Ideal.span (Set.range x) : Ideal R).FG :=
    Submodule.fg_span (Set.finite_range x)
  have hnil : IsNilpotent (Ideal.span (Set.range x) : Ideal R) := by
    apply hfg.isNilpotent_iff_le_nilradical.mpr
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hx i
  obtain ⟨N, hN⟩ := hnil
  exact ⟨nilpotentEvaluation x hN, N,
    maximalIdeal_pow_le_ker_nilpotentEvaluation x hN,
    nilpotentEvaluation_coordinate x hN⟩

/-- Coordinate values determine maps annihilating possibly different
powers of the maximal ideal. -/
theorem algHom_ext_of_exists_maximalIdeal_pow_le_ker {n : ℕ}
    (φ ψ : Germ n →ₐ[ℂ] R)
    (hφ : ∃ N, maximalIdeal n ^ N ≤ RingHom.ker φ)
    (hψ : ∃ N, maximalIdeal n ^ N ≤ RingHom.ker ψ)
    (hcoord : ∀ i, φ (coordinate i) = ψ (coordinate i)) : φ = ψ := by
  obtain ⟨N, hN⟩ := hφ
  obtain ⟨M, hM⟩ := hψ
  exact algHom_ext_of_maximalIdeal_pow_le_ker φ ψ
    ((Ideal.pow_le_pow_right (Nat.le_max_left N M)).trans hN)
    ((Ideal.pow_le_pow_right (Nat.le_max_right N M)).trans hM) hcoord

end OnLeConjecture.Analytic.Germ
