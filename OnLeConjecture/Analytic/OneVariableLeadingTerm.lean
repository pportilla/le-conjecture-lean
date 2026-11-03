/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.OneVariableOrder

/-!
# Leading terms of one variable analytic germs

Every germ in a power of the one variable maximal ideal has a scalar leading
coefficient modulo the next power.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- A one variable germ in the `d`th power of the maximal ideal is congruent
modulo the next power to a scalar multiple of the `d`th coordinate power. -/
theorem exists_scalar_leadingTerm_of_mem_maximalIdeal_pow
    (q : Germ 1) (d : ℕ)
    (hq : q ∈ Germ.maximalIdeal 1 ^ d) :
    ∃ c : ℂ,
      q - Germ.constRingHom 1 c * Germ.coordinate (0 : Fin 1) ^ d ∈
        Germ.maximalIdeal 1 ^ (d + 1) := by
  rw [Germ.maximalIdeal_one_pow_eq_span_coordinate_pow,
    Ideal.mem_span_singleton] at hq
  obtain ⟨u, hu⟩ := hq
  let c : ℂ := Germ.valueRingHom 1 u
  have huTail : u - Germ.constRingHom 1 c ∈ Germ.maximalIdeal 1 := by
    rw [Germ.mem_maximalIdeal_iff, map_sub,
      Germ.valueRingHom_const]
    simp [c]
  have hx : Germ.coordinate (0 : Fin 1) ∈ Germ.maximalIdeal 1 :=
    Germ.coordinate_mem_maximalIdeal 0
  have hxPow : Germ.coordinate (0 : Fin 1) ^ d ∈
      Germ.maximalIdeal 1 ^ d :=
    Ideal.pow_mem_pow hx d
  have hproduct := Ideal.mul_mem_mul hxPow huTail
  refine ⟨c, ?_⟩
  have hequality :
      q - Germ.constRingHom 1 c * Germ.coordinate (0 : Fin 1) ^ d =
        Germ.coordinate (0 : Fin 1) ^ d *
          (u - Germ.constRingHom 1 c) := by
    rw [hu]
    ring
  rw [hequality]
  simpa only [Submodule.pow_succ] using hproduct

/-- If the order is exactly `d`, the scalar coefficient of the degree `d`
term is nonzero. -/
theorem exists_nonzero_scalar_leadingTerm_of_exact_maximalIdeal_pow
    (q : Germ 1) (d : ℕ)
    (hq : q ∈ Germ.maximalIdeal 1 ^ d)
    (hnext : q ∉ Germ.maximalIdeal 1 ^ (d + 1)) :
    ∃ c : ℂ, c ≠ 0 ∧
      q - Germ.constRingHom 1 c * Germ.coordinate (0 : Fin 1) ^ d ∈
        Germ.maximalIdeal 1 ^ (d + 1) := by
  obtain ⟨c, hc⟩ :=
    Germ.exists_scalar_leadingTerm_of_mem_maximalIdeal_pow q d hq
  refine ⟨c, ?_, hc⟩
  intro hcZero
  subst c
  simp only [map_zero, zero_mul, sub_zero] at hc
  exact hnext hc

end Germ

end OnLeConjecture.Analytic
