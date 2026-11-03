/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.LinearAlgebra.End.LocallyNilpotent

/-!
# Finite inverse expansion on a matching-path input

Only local nilpotence on the input vector is required. The geometric-series
identity from Mathlib identifies the actual unit inverse, then a linear map
killing all paths of length at least two truncates the result to two terms.
This is the algebra needed after the concrete stabilization path exclusion.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- A vectorwise finite geometric series computes the specified unit inverse. -/
theorem matchingInverse_apply_eq_geom_sum (T : Module.End R M)
    (u : (Module.End R M)ˣ) (hu : (u : Module.End R M) = 1 + T)
    (v : M) (k : ℕ) (hk : (T ^ k) v = 0) :
    (↑(u⁻¹) : Module.End R M) v = (∑ j ∈ Finset.range k, (-T) ^ j) v := by
  let w := (∑ j ∈ Finset.range k, (-T) ^ j) v
  have hw : (u : Module.End R M) w = v := by
    rw [hu]
    have h := LinearMap.congr_fun (mul_neg_geom_sum (-T) k) v
    rwa [sub_neg_eq_add, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      neg_pow, Module.End.mul_apply, hk, map_zero, sub_zero] at h
  have hi : (↑(u⁻¹) : Module.End R M) ((u : Module.End R M) w) = w :=
    congrArg (fun f : Module.End R M => f w) u.inv_val
  exact (congrArg (fun x => (↑(u⁻¹) : Module.End R M) x) hw).symm.trans hi

private theorem neg_pow_apply_eq_smul (T : Module.End R M) (k : ℕ) (v : M) :
    ((-T) ^ k) v = (-1 : R) ^ k • (T ^ k) v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply, ih, map_smul]
    simp only [pow_succ', Module.End.mul_apply, mul_smul, neg_one_smul]

/-- If the exit map kills every path of length at least two on the input,
the actual inverse contributes only the direct and single-transition terms. -/
theorem matchingInverse_apply_truncate_two (T : Module.End R M)
    (u : (Module.End R M)ˣ) (hu : (u : Module.End R M) = 1 + T)
    (E : M →ₗ[R] N) (v : M) (hnil : ∃ k : ℕ, (T ^ k) v = 0)
    (hkill : ∀ k : ℕ, E ((T ^ (k + 2)) v) = 0) :
    E ((↑(u⁻¹) : Module.End R M) v) = E v - E (T v) := by
  obtain ⟨k, hk⟩ := hnil
  have hk' : (T ^ (2 + k)) v = 0 :=
    Module.End.pow_map_zero_of_le (by omega) hk
  rw [matchingInverse_apply_eq_geom_sum T u hu v (2 + k) hk',
    LinearMap.sum_apply, map_sum, Finset.sum_range_add]
  have hrest : ∑ j ∈ Finset.range k, E (((-T) ^ (2 + j)) v) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [neg_pow_apply_eq_smul, map_smul, Nat.add_comm 2 j, hkill, smul_zero]
  rw [hrest, add_zero]
  simp [Finset.sum_range_succ, pow_zero, pow_one, Module.End.one_apply,
    LinearMap.neg_apply, sub_eq_add_neg]

end OnLeConjecture.KnotFloer
