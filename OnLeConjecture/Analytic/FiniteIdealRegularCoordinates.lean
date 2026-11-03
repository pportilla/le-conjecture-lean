/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeakBlowupFiniteColength
public import OnLeConjecture.Analytic.CoordinateOrder
import Mathlib.Tactic

/-!
# Regular coordinates for a finite-colength plane ideal

Adic separatedness gives the exact ideal order. Some generator attains that
order, and a linear source change makes it regular of the same order in the
first coordinate. The normalized ideal contains a power of the second
coordinate. These are constructed inputs for a blowup termination argument.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem exists_exact_ideal_order_of_finite_colength
    (I : Ideal (Germ 2)) (hfinite : Module.Finite ℂ (Germ 2 ⧸ I)) :
    ∃ m : ℕ, I ≤ maximalIdeal 2 ^ m ∧ ¬ I ≤ maximalIdeal 2 ^ (m + 1) := by
  classical
  obtain ⟨N, hN⟩ := (quotient_moduleFinite_iff_exists_maximalIdeal_pow_le I).mp hfinite
  have hI : I ≠ ⊥ := by
    intro hbot
    have hp := hN (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal (0 : Fin 2)) N)
    rw [hbot, Ideal.mem_bot] at hp
    exact pow_ne_zero N (coordinate_ne_zero (0 : Fin 2)) hp
  have hex : ∃ k : ℕ, ¬ I ≤ maximalIdeal 2 ^ (k + 1) := by
    by_contra hn
    push Not at hn
    have hall : ∀ k : ℕ, I ≤ maximalIdeal 2 ^ k := by
      intro k
      cases k with
      | zero => simp only [pow_zero, Ideal.one_eq_top, le_top]
      | succ k => exact hn k
    have hle := le_iInf hall
    rw [iInf_maximalIdeal_pow] at hle
    exact hI (le_bot_iff.mp hle)
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  by_cases hz : Nat.find hex = 0
  · simp only [hz, pow_zero, Ideal.one_eq_top, le_top]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
    rw [hk]
    exact not_not.mp hmin

/-- A proper finite-colength ideal has a positive exact order, attained by
one of any specified generating family. -/
theorem exists_exact_generator_order_of_finite_colength
    {ι : Type*} (F : ι → Germ 2) (hproper : ∀ i, F i ∈ maximalIdeal 2)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F))) :
    ∃ m : ℕ, 0 < m ∧ (∀ i, F i ∈ maximalIdeal 2 ^ m) ∧
      ∃ i, F i ∉ maximalIdeal 2 ^ (m + 1) := by
  obtain ⟨m, hm, hnext⟩ := exists_exact_ideal_order_of_finite_colength _ hfinite
  have hmpos : 0 < m := by
    by_contra hn
    have hz : m = 0 := by omega
    apply hnext
    simp only [hz, zero_add, pow_one]
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hproper i
  refine ⟨m, hmpos, fun i => hm (Ideal.subset_span (Set.mem_range_self i)), ?_⟩
  by_contra hn
  push Not at hn
  apply hnext
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact hn i

/-- Both the regular generator and the coordinate power are constructed
from finite colength, without an assumed principalization or order bound. -/
theorem exists_regular_coordinates_for_finite_ideal
    {ι : Type*} (F : ι → Germ 2) (hproper : ∀ i, F i ∈ maximalIdeal 2)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F))) :
    ∃ (m : ℕ) (e : PointedEquivGerm 2) (N : ℕ), 0 < m ∧
      (∀ i, e.forward.pullbackRingHom (F i) ∈ maximalIdeal 2 ^ m) ∧
      (∃ i, IsRegularInFirstCoordinateOfOrder (e.forward.pullbackRingHom (F i)) m ∧
        e.forward.pullbackRingHom (F i) ∉ maximalIdeal 2 ^ (m + 1)) ∧
      maximalIdeal 2 ^ N ≤ Ideal.span (Set.range (fun i => e.forward.pullbackRingHom (F i))) ∧
      coordinate (1 : Fin 2) ^ N ∈
        Ideal.span (Set.range (fun i => e.forward.pullbackRingHom (F i))) := by
  obtain ⟨m, hm, horder, i, hi⟩ :=
    exists_exact_generator_order_of_finite_colength F hproper hfinite
  obtain ⟨e, hregular⟩ :=
    exists_linear_equiv_regularInFirstCoordinateOfOrder (horder i) hi
  obtain ⟨N, hN⟩ :=
    (quotient_moduleFinite_iff_exists_maximalIdeal_pow_le _).mp hfinite
  have hmap : Ideal.map e.pullbackRingEquiv.toRingHom (Ideal.span (Set.range F)) =
      Ideal.span (Set.range (fun i => e.forward.pullbackRingHom (F i))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hpower : Ideal.map e.pullbackRingEquiv.toRingHom (maximalIdeal 2 ^ N) =
      maximalIdeal 2 ^ N := by
    rw [Ideal.map_pow, e.map_maximalIdeal_pullbackRingEquiv]
  have hN' := Ideal.map_mono (f := e.pullbackRingEquiv.toRingHom) hN
  rw [hmap, hpower] at hN'
  refine ⟨m, e, N, hm, fun j => e.forward.pullback_mem_maximalIdeal_pow (horder j),
    ⟨i, hregular, ?_⟩, hN', ?_⟩
  · intro hnext
    apply hi
    have hback := e.inverse.pullback_mem_maximalIdeal_pow hnext
    change e.pullbackAlgEquiv.symm (e.pullbackAlgEquiv (F i)) ∈
      maximalIdeal 2 ^ (m + 1) at hback
    simpa only [AlgEquiv.symm_apply_apply] using hback
  · exact hN' (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal (1 : Fin 2)) N)

end OnLeConjecture.Analytic.Germ
