/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicResidualFourier
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Polynomial decomposition over the invariant cyclic pair

For odd `p` and nonzero `c`, every polynomial in `x,t` has a unique
expression `A(x²,xᵖ+ct) + x B(x²,xᵖ+ct)`. Homogeneous polynomials have
homogeneous coefficients with the corresponding degrees.
-/

public section

namespace OnLeConjecture.DTwo

open MvPolynomial

/-- Substitution of the invariant cyclic pair in a polynomial. -/
@[expose] noncomputable def cyclicInvariantBaseHom (p : ℕ) (c : ℂ) :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  aeval ![X 0 ^ 2, X 0 ^ p + C c * X 1]

/-- The involution fixing the invariant cyclic pair. -/
@[expose] noncomputable def cyclicInvariantReflection (p : ℕ) (c : ℂ) :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  aeval ![-X 0, X 1 + C (2 / c) * X 0 ^ p]

theorem cyclicInvariantBaseHom_eval (p : ℕ) (c : ℂ)
    (A : MvPolynomial (Fin 2) ℂ) (z : Fin 2 → ℂ) :
    eval z (cyclicInvariantBaseHom p c A) =
      eval ![z 0 ^ 2, z 0 ^ p + c * z 1] A := by
  change aeval z (aeval _ A) = aeval _ A
  rw [comp_aeval_apply]
  apply congrArg (fun f : Fin 2 → ℂ ↦ aeval f A)
  funext i
  fin_cases i <;> simp

/-- The invariant pair is algebraically independent. -/
theorem cyclicInvariantBaseHom_injective (p : ℕ) (c : ℂ) (hc : c ≠ 0) :
    Function.Injective (cyclicInvariantBaseHom p c) := by
  intro A B hAB
  apply MvPolynomial.funext
  intro z
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (z 0) (show 0 < 2 by omega)
  have heq := congrArg (eval ![x, (z 1 - x ^ p) / c]) hAB
  rw [cyclicInvariantBaseHom_eval, cyclicInvariantBaseHom_eval] at heq
  have hz : (![x ^ 2, x ^ p + c * ((z 1 - x ^ p) / c)] : Fin 2 → ℂ) = z := by
    ext i
    fin_cases i
    · exact hx
    · change x ^ p + c * ((z 1 - x ^ p) / c) = z 1
      field_simp
      ring
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, hz] using heq

@[simp] theorem cyclicInvariantReflection_base (p : ℕ) (hp : Odd p)
    (c : ℂ) (hc : c ≠ 0) (A : MvPolynomial (Fin 2) ℂ) :
    cyclicInvariantReflection p c (cyclicInvariantBaseHom p c A) =
      cyclicInvariantBaseHom p c A := by
  have heq : (cyclicInvariantReflection p c).comp (cyclicInvariantBaseHom p c) =
      cyclicInvariantBaseHom p c := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [cyclicInvariantBaseHom, cyclicInvariantReflection]
    · change cyclicInvariantReflection p c (cyclicInvariantBaseHom p c (X (1 : Fin 2))) =
        cyclicInvariantBaseHom p c (X 1)
      simp only [cyclicInvariantBaseHom, cyclicInvariantReflection, aeval_X,
        Matrix.cons_val_one, Matrix.cons_val_zero, map_add, map_mul, map_pow,
        aeval_C, hp.neg_pow]
      have hscalar : c * (2 / c) = 2 := by field_simp
      calc
        -(X (0 : Fin 2) ^ p) + C c * (X 1 + C (2 / c) * X 0 ^ p) =
            C c * X 1 + (C (c * (2 / c)) - 1) * X 0 ^ p := by
          rw [map_mul]
          ring
        _ = _ := by
          rw [hscalar, show (C (2 : ℂ) : MvPolynomial (Fin 2) ℂ) = 2 from map_ofNat C 2]
          ring
  exact congrArg (fun f : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ ↦ f A) heq

/-- Every polynomial has a rank two expression over the invariant pair. -/
theorem cyclicInvariant_polynomial_decomposition (p : ℕ) (hp : Odd p)
    (c : ℂ) (hc : c ≠ 0) (F : MvPolynomial (Fin 2) ℂ) :
    ∃ A B : MvPolynomial (Fin 2) ℂ,
      F = cyclicInvariantBaseHom p c A + X 0 * cyclicInvariantBaseHom p c B := by
  obtain ⟨r, hr⟩ := hp
  have hp' : p = 2 * r + 1 := by omega
  have hpower : (X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ^ p =
      X 0 * (X 0 ^ 2) ^ r := by
    rw [← pow_mul, hp', pow_add, pow_one]
    ring
  have hscalar : (C c : MvPolynomial (Fin 2) ℂ) * C c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  induction F using MvPolynomial.induction_on with
  | C d =>
      refine ⟨C d, 0, ?_⟩
      simp [cyclicInvariantBaseHom]
  | add F G hF hG =>
      obtain ⟨A, B, rfl⟩ := hF
      obtain ⟨A', B', rfl⟩ := hG
      refine ⟨A + A', B + B', ?_⟩
      simp only [map_add]
      ring
  | mul_X F i hF =>
      obtain ⟨A, B, rfl⟩ := hF
      fin_cases i
      · refine ⟨X 0 * B, A, ?_⟩
        change (cyclicInvariantBaseHom p c A + X 0 * cyclicInvariantBaseHom p c B) *
          X 0 = cyclicInvariantBaseHom p c (X 0 * B) + X 0 * cyclicInvariantBaseHom p c A
        have hx : cyclicInvariantBaseHom p c (X 0) = X 0 ^ 2 := by
          simp [cyclicInvariantBaseHom]
        rw [map_mul, hx]
        ring
      · refine ⟨C c⁻¹ * (X 1 * A - X 0 ^ (r + 1) * B),
          C c⁻¹ * (X 1 * B - X 0 ^ r * A), ?_⟩
        have hx : cyclicInvariantBaseHom p c (X 0) = X 0 ^ 2 := by
          simp [cyclicInvariantBaseHom]
        have ht : cyclicInvariantBaseHom p c (X 1) = X 0 ^ p + C c * X 1 := by
          simp [cyclicInvariantBaseHom]
        have hinv : cyclicInvariantBaseHom p c (C c⁻¹) = C c⁻¹ := by
          simp [cyclicInvariantBaseHom]
        change (cyclicInvariantBaseHom p c A + X 0 * cyclicInvariantBaseHom p c B) *
          X 1 = _
        simp only [map_mul, map_sub, map_pow, hx, ht, hinv]
        rw [hpower, pow_succ]
        linear_combination
          -(X (1 : Fin 2) * cyclicInvariantBaseHom p c A +
            X 0 * X 1 * cyclicInvariantBaseHom p c B) * hscalar

/-- The two coefficients in the rank two expression are unique. -/
theorem cyclicInvariant_polynomial_decomposition_unique (p : ℕ) (hp : Odd p)
    (c : ℂ) (hc : c ≠ 0) (A B A' B' : MvPolynomial (Fin 2) ℂ)
    (heq : cyclicInvariantBaseHom p c A + X 0 * cyclicInvariantBaseHom p c B =
      cyclicInvariantBaseHom p c A' + X 0 * cyclicInvariantBaseHom p c B') :
    A = A' ∧ B = B' := by
  have hreflection := congrArg (cyclicInvariantReflection p c) heq
  simp only [map_add, map_mul, cyclicInvariantReflection_base p hp c hc] at hreflection
  have hx : cyclicInvariantReflection p c (X 0) = -X 0 := by
    simp [cyclicInvariantReflection]
  rw [hx] at hreflection
  have hA : cyclicInvariantBaseHom p c A = cyclicInvariantBaseHom p c A' := by
    have htwo : (2 : MvPolynomial (Fin 2) ℂ) *
        (cyclicInvariantBaseHom p c A - cyclicInvariantBaseHom p c A') = 0 := by
      linear_combination heq + hreflection
    exact sub_eq_zero.mp ((mul_eq_zero.mp htwo).resolve_left (by norm_num))
  have hB : cyclicInvariantBaseHom p c B = cyclicInvariantBaseHom p c B' := by
    have hmul : (X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) *
        (cyclicInvariantBaseHom p c B - cyclicInvariantBaseHom p c B') = 0 := by
      linear_combination heq - hA
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (X_ne_zero 0))
  exact ⟨cyclicInvariantBaseHom_injective p c hc hA,
    cyclicInvariantBaseHom_injective p c hc hB⟩

theorem cyclicInvariantBaseHom_generators_homogeneous (p : ℕ) (c : ℂ) (i : Fin 2) :
    IsWeightedHomogeneous ![1, p]
      (![X 0 ^ 2, X 0 ^ p + C c * X 1] i : MvPolynomial (Fin 2) ℂ) (![2, p] i) := by
  have hx := isWeightedHomogeneous_X ℂ (![1, p] : Fin 2 → ℕ) 0
  have ht := isWeightedHomogeneous_X ℂ (![1, p] : Fin 2 → ℕ) 1
  fin_cases i
  · simpa [nsmul_eq_mul] using hx.pow 2
  · have hxp : IsWeightedHomogeneous ![1, p]
        (X (0 : Fin 2) ^ p : MvPolynomial (Fin 2) ℂ) p := by
      simpa [nsmul_eq_mul] using hx.pow p
    exact hxp.add (ht.C_mul c)

theorem cyclicInvariantReflection_homogeneous (p N : ℕ) (c : ℂ)
    (F : MvPolynomial (Fin 2) ℂ) (hF : F.IsWeightedHomogeneous ![1, p] N) :
    (cyclicInvariantReflection p c F).IsWeightedHomogeneous ![1, p] N := by
  apply OnLeConjecture.Polynomial.isWeightedHomogeneous_aeval ![1, p] ![1, p] _ _ hF
  intro i
  have hx := isWeightedHomogeneous_X ℂ (![1, p] : Fin 2 → ℕ) 0
  have ht := isWeightedHomogeneous_X ℂ (![1, p] : Fin 2 → ℕ) 1
  fin_cases i
  · exact hx.neg
  · have hxp : IsWeightedHomogeneous ![1, p]
        (X (0 : Fin 2) ^ p : MvPolynomial (Fin 2) ℂ) p := by
      simpa [nsmul_eq_mul] using hx.pow p
    exact ht.add (hxp.C_mul (2 / c))

private theorem homogeneous_of_two_mul (p N : ℕ) (F : MvPolynomial (Fin 2) ℂ)
    (hF : (C (2 : ℂ) * F).IsWeightedHomogeneous ![1, p] N) :
    F.IsWeightedHomogeneous ![1, p] N := by
  intro d hd
  apply hF
  rw [coeff_C_mul]
  exact mul_ne_zero (by norm_num) hd

private theorem homogeneous_of_firstVariable_mul (p N : ℕ)
    (F : MvPolynomial (Fin 2) ℂ)
    (hF : (X 0 * F).IsWeightedHomogeneous ![1, p] N) :
    F.IsWeightedHomogeneous ![1, p] (N - 1) := by
  intro d hd
  have hc : coeff (Finsupp.single 0 1 + d) (X 0 * F) ≠ 0 := by
    simpa only [coeff_X_mul] using hd
  have hdegree := hF hc
  simp only [map_add, Finsupp.weight_single, Matrix.cons_val_zero, one_nsmul] at hdegree
  omega

/-- A homogeneous polynomial has homogeneous rank two coefficients. -/
theorem cyclicInvariant_homogeneous_decomposition (p N : ℕ) (hp : Odd p)
    (c : ℂ) (hc : c ≠ 0) (F : MvPolynomial (Fin 2) ℂ)
    (hF : F.IsWeightedHomogeneous ![1, p] N) :
    ∃ A B : MvPolynomial (Fin 2) ℂ,
      A.IsWeightedHomogeneous ![2, p] N ∧
      B.IsWeightedHomogeneous ![2, p] (N - 1) ∧
      F = cyclicInvariantBaseHom p c A + X 0 * cyclicInvariantBaseHom p c B := by
  obtain ⟨A, B, hdecomp⟩ := cyclicInvariant_polynomial_decomposition p hp c hc F
  have hreflect := congrArg (cyclicInvariantReflection p c) hdecomp
  simp only [map_add, map_mul, cyclicInvariantReflection_base p hp c hc] at hreflect
  have hx : cyclicInvariantReflection p c (X 0) = -X 0 := by
    simp [cyclicInvariantReflection]
  rw [hx] at hreflect
  have hreflectHom := cyclicInvariantReflection_homogeneous p N c F hF
  have hAimage : (cyclicInvariantBaseHom p c A).IsWeightedHomogeneous ![1, p] N := by
    apply homogeneous_of_two_mul
    have heq : C (2 : ℂ) * cyclicInvariantBaseHom p c A =
        F + cyclicInvariantReflection p c F := by
      rw [show (C (2 : ℂ) : MvPolynomial (Fin 2) ℂ) = 2 from map_ofNat C 2]
      linear_combination -hdecomp - hreflect
    rw [heq]
    exact hF.add hreflectHom
  have hBimage : (cyclicInvariantBaseHom p c B).IsWeightedHomogeneous ![1, p] (N - 1) := by
    apply homogeneous_of_firstVariable_mul
    apply homogeneous_of_two_mul
    have heq : C (2 : ℂ) * (X 0 * cyclicInvariantBaseHom p c B) =
        F - cyclicInvariantReflection p c F := by
      rw [show (C (2 : ℂ) : MvPolynomial (Fin 2) ℂ) = 2 from map_ofNat C 2]
      linear_combination -hdecomp + hreflect
    rw [heq]
    exact hF.sub hreflectHom
  obtain ⟨A', hA', hAA'⟩ := OnLeConjecture.Polynomial.exists_homogeneous_preimage_of_mem_range
    ![2, p] ![1, p] ![X 0 ^ 2, X 0 ^ p + C c * X 1]
    (cyclicInvariantBaseHom_generators_homogeneous p c) hAimage ⟨A, rfl⟩
  obtain ⟨B', hB', hBB'⟩ := OnLeConjecture.Polynomial.exists_homogeneous_preimage_of_mem_range
    ![2, p] ![1, p] ![X 0 ^ 2, X 0 ^ p + C c * X 1]
    (cyclicInvariantBaseHom_generators_homogeneous p c) hBimage ⟨B, rfl⟩
  have hAeq : A' = A := cyclicInvariantBaseHom_injective p c hc hAA'
  have hBeq : B' = B := cyclicInvariantBaseHom_injective p c hc hBB'
  exact ⟨A, B, by simpa only [hAeq] using hA', by simpa only [hBeq] using hB', hdecomp⟩

/-- Nonmembership in the invariant pair algebra forces a nonzero odd
coefficient, with degree one less than the original homogeneous polynomial. -/
theorem cyclicInvariant_nonbase_homogeneous_decomposition (p N : ℕ) (hp : Odd p)
    (c : ℂ) (hc : c ≠ 0) (F : MvPolynomial (Fin 2) ℂ)
    (hF : F.IsWeightedHomogeneous ![1, p] N)
    (hbase : F ∉ Set.range (cyclicInvariantBaseHom p c)) :
    ∃ A B : MvPolynomial (Fin 2) ℂ,
      A.IsWeightedHomogeneous ![2, p] N ∧
      B.IsWeightedHomogeneous ![2, p] (N - 1) ∧ B ≠ 0 ∧
      F = cyclicInvariantBaseHom p c A + X 0 * cyclicInvariantBaseHom p c B := by
  obtain ⟨A, B, hA, hB, heq⟩ := cyclicInvariant_homogeneous_decomposition p N hp c hc F hF
  refine ⟨A, B, hA, hB, ?_, heq⟩
  intro hzero
  apply hbase
  refine ⟨A, ?_⟩
  simpa [hzero] using heq.symm

/-- Applied to `tΛ`, the odd coefficient has weighted degree
`N₀+p-1`, and nonmembership in the pair algebra makes it nonzero. -/
theorem cyclicInvariant_t_mul_nonbase_decomposition
    (p N₀ : ℕ) (hp : Odd p) (c : ℂ) (hc : c ≠ 0)
    (Λ : MvPolynomial (Fin 2) ℂ) (hΛ : Λ.IsWeightedHomogeneous ![1, p] N₀)
    (hbase : X 1 * Λ ∉ Set.range (cyclicInvariantBaseHom p c)) :
    ∃ A B : MvPolynomial (Fin 2) ℂ,
      A.IsWeightedHomogeneous ![2, p] (N₀ + p) ∧
      B.IsWeightedHomogeneous ![2, p] (N₀ + p - 1) ∧ B ≠ 0 ∧
      X 1 * Λ = cyclicInvariantBaseHom p c A + X 0 * cyclicInvariantBaseHom p c B := by
  have hF : (X 1 * Λ).IsWeightedHomogeneous ![1, p] (N₀ + p) := by
    simpa [Nat.add_comm] using (isWeightedHomogeneous_X ℂ ![1, p] 1).mul hΛ
  exact cyclicInvariant_nonbase_homogeneous_decomposition p (N₀ + p) hp c hc _ hF hbase

/-- The difference along the involution is twice the odd summand. -/
theorem cyclicInvariant_reflection_difference (p : ℕ) (hp : Odd p)
    (c : ℂ) (hc : c ≠ 0) (F A B : MvPolynomial (Fin 2) ℂ)
    (hdecomp : F = cyclicInvariantBaseHom p c A + X 0 * cyclicInvariantBaseHom p c B) :
    F - cyclicInvariantReflection p c F =
      C (2 : ℂ) * X 0 * cyclicInvariantBaseHom p c B := by
  have hreflect := congrArg (cyclicInvariantReflection p c) hdecomp
  simp only [map_add, map_mul, cyclicInvariantReflection_base p hp c hc] at hreflect
  have hx : cyclicInvariantReflection p c (X 0) = -X 0 := by
    simp [cyclicInvariantReflection]
  rw [hx] at hreflect
  rw [show (C (2 : ℂ) : MvPolynomial (Fin 2) ℂ) = 2 from map_ofNat C 2]
  linear_combination hdecomp - hreflect

end OnLeConjecture.DTwo
