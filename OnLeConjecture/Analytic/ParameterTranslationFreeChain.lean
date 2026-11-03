/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeightedParameterTranslation

/-!
# Analytic translations on a finite free chain

A parameter translation of order at least `A` lifts coherently through
the first `A-1` blowups without moving their centers. At the last point
the residue of the divided translation gives the exact translation of
every finite exceptional center. The commuting squares are constructed
from analytic divisibility, not imposed on the coordinate changes.
-/

public section

namespace OnLeConjecture.Analytic.Germ

/-- Coherent analytic translations on a specified finite free chain,
including their action on every finite chart leaving its final point. -/
structure ParameterTranslationChain (a : Germ 1) (A : ℕ) where
  shift : ℕ → Germ 1
  coordinates : ℕ → PointedEquivGerm 2
  shift_zero : shift 0 = a
  shift_order : ∀ j, j < A → shift j ∈ maximalIdeal 1 ^ (A - j)
  first_coordinate : ∀ j, (coordinates j).forward.pullbackRingHom (coordinate (0 : Fin 2)) =
    coordinate 0 + hyperplaneExtension 1 (shift j)
  coefficients : ∀ j, ∀ b : Germ 1,
    (coordinates j).forward.pullbackRingHom (hyperplaneExtension 1 b) = hyperplaneExtension 1 b
  chart_identity : ∀ j, j + 1 < A → ∀ ζ : ℂ,
    (coordinates j).forward.comp (pointBlowupChartGerm ζ) =
      (pointBlowupChartGerm ζ).comp (coordinates (j + 1)).forward
  terminal_center_shift : ℂ
  terminal_coordinates : PointedEquivGerm 2
  terminal_coefficients : ∀ b : Germ 1,
    terminal_coordinates.forward.pullbackRingHom (hyperplaneExtension 1 b) = hyperplaneExtension 1 b
  terminal_chart_identity : ∀ ζ : ℂ,
    (coordinates (A - 1)).forward.comp (pointBlowupChartGerm (ζ - terminal_center_shift)) =
      (pointBlowupChartGerm ζ).comp terminal_coordinates.forward

/-- An order-`A` analytic translation constructs all compatible free
chart lifts and the translation of the terminal exceptional centers. -/
theorem exists_parameterTranslationChain
    (A : ℕ) (hA : 0 < A) (a : Germ 1) (ha : a ∈ maximalIdeal 1 ^ A) :
    Nonempty (ParameterTranslationChain a A) := by
  classical
  have hdiv : coordinate (0 : Fin 1) ^ A ∣ a := by
    rwa [← Ideal.mem_span_singleton, ← maximalIdeal_one_pow_eq_span_coordinate_pow]
  obtain ⟨q, hq⟩ := hdiv
  let b (j : ℕ) : Germ 1 := if j < A then coordinate (0 : Fin 1) ^ (A - j) * q else 0
  have hbOrder (j : ℕ) (hj : j < A) : b j ∈ maximalIdeal 1 ^ (A - j) := by
    dsimp only [b]
    rw [if_pos hj]
    exact (maximalIdeal 1 ^ (A - j)).mul_mem_right q
      (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal 0) _)
  have hb (j : ℕ) : b j ∈ maximalIdeal 1 := by
    by_cases hj : j < A
    · simpa only [pow_one] using Ideal.pow_le_pow_right (by omega : 1 ≤ A - j) (hbOrder j hj)
    · simp only [b, if_neg hj, Ideal.zero_mem]
  choose E hEx hEa using fun j ↦ exists_parameterTranslation (b j) (hb j)
  have hstep (j : ℕ) (hj : j + 1 < A) :
      b j = coordinate (0 : Fin 1) * b (j + 1) := by
    simp only [b, if_pos (by omega : j < A), if_pos hj]
    rw [← mul_assoc, ← pow_succ', show A - j = (A - (j + 1)) + 1 by omega]
  let c := valueRingHom 1 q
  let bLast := q - constRingHom 1 c
  have hbLast : bLast ∈ maximalIdeal 1 := by simp [bLast, c, mem_maximalIdeal_iff]
  obtain ⟨last, hlastX, hlastA⟩ := exists_parameterTranslation bLast hbLast
  have hterminalFactor : b (A - 1) = coordinate (0 : Fin 1) * (bLast + constRingHom 1 c) := by
    simp only [b, if_pos (by omega : A - 1 < A), show A - (A - 1) = 1 by omega,
      pow_one, bLast, sub_add_cancel]
  refine ⟨{
    shift := b
    coordinates := E
    shift_zero := ?_
    shift_order := hbOrder
    first_coordinate := hEx
    coefficients := hEa
    chart_identity := ?_
    terminal_center_shift := c
    terminal_coordinates := last
    terminal_coefficients := hlastA
    terminal_chart_identity := ?_ }⟩
  · simpa only [b, if_pos hA, Nat.sub_zero] using hq.symm
  · intro j hj ζ
    have h := parameterTranslation_blowup_identity (b j) (b (j + 1)) 0 ζ
      (by simpa only [map_zero, add_zero] using hstep j hj)
      (E j) (E (j + 1)) (hEx j) (hEa j) (hEx (j + 1)) (hEa (j + 1))
    simpa only [sub_zero] using h
  · intro ζ
    exact parameterTranslation_blowup_identity (b (A - 1)) bLast c ζ hterminalFactor
      (E (A - 1)) last (hEx _) (hEa _) hlastX hlastA

end OnLeConjecture.Analytic.Germ
