/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.ExteriorIncidencePairing
public import Mathlib.LinearAlgebra.Pi

/-!
# The determinant pairing along a sequence of modules

The written proof of Statement E (`statement_E_complete_proof.tex`, equation
`determinant-pairing`) applies its determinant formula to the homologies `V 0, V 1, …` of the grids
along a sequence of O switches. This file states the formula for such a sequence: maps
`φ e, κ e : V e → V (e + 1)`, operators `ψ e c` on each `V e`, with

  `ψ (e + 1) c ∘ φ e = φ e ∘ ψ e c + b c e • κ e`,  `ψ (e + 1) c ∘ κ e = κ e ∘ ψ e c`,
  `ψ 0 c x = 0`.

Then `ψ d (c 0) ∘ ⋯ ∘ ψ d (c (d - 1))` applied to `φ (d - 1) ∘ ⋯ ∘ φ 0 x` equals `det B` times
`κ (d - 1) ∘ ⋯ ∘ κ 0 x`, with `B r e = b (c r) e` (`derivativeProduct_familyProduct_eq_det`). The
proof applies `derivativeProduct_switchProduct_eq_det` to the product module `Π e, V e`.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer

open Finset Matrix

variable {R C : Type*} [CommRing R] {V : ℕ → Type*} [∀ e, AddCommGroup (V e)]
  [∀ e, Module R (V e)]

/-- The composite `φ (d - 1) ∘ ⋯ ∘ φ 0 : V 0 → V d`. -/
def familyProduct (φ : ∀ e, V e →ₗ[R] V (e + 1)) : (d : ℕ) → V 0 →ₗ[R] V d
  | 0 => LinearMap.id
  | d + 1 => φ d ∘ₗ familyProduct φ d

theorem familyProduct_zero (φ : ∀ e, V e →ₗ[R] V (e + 1)) :
    familyProduct φ 0 = LinearMap.id := rfl

theorem familyProduct_succ (φ : ∀ e, V e →ₗ[R] V (e + 1)) (d : ℕ) :
    familyProduct φ (d + 1) = φ d ∘ₗ familyProduct φ d := rfl

/-- The block map of a sequence of maps on the product module. -/
def blockMap (φ : ∀ e, V e →ₗ[R] V (e + 1)) (e : ℕ) : (∀ i, V i) →ₗ[R] ∀ i, V i :=
  LinearMap.single R V (e + 1) ∘ₗ φ e ∘ₗ LinearMap.proj e

/-- The block-diagonal operator of a family of operators. -/
def blockDiagonal (ψ : ∀ e, C → V e →ₗ[R] V e) (c : C) : (∀ i, V i) →ₗ[R] ∀ i, V i :=
  LinearMap.pi fun e => ψ e c ∘ₗ LinearMap.proj e

theorem blockDiagonal_single (ψ : ∀ e, C → V e →ₗ[R] V e) (c : C) (e : ℕ) (v : V e) :
    blockDiagonal ψ c (Pi.single e v) = Pi.single e (ψ e c v) := by
  classical
  funext i
  by_cases h : i = e
  · subst h
    simp [blockDiagonal]
  · simp [blockDiagonal, Pi.single_eq_of_ne h]

theorem blockMap_single (φ : ∀ e, V e →ₗ[R] V (e + 1)) (e : ℕ) (v : V e) :
    blockMap φ e (Pi.single e v) = Pi.single (e + 1) (φ e v) := by
  simp [blockMap]

theorem switchProduct_blockMap_single (φ : ∀ e, V e →ₗ[R] V (e + 1)) (x : V 0) :
    ∀ d, switchProduct (blockMap φ) d (Pi.single 0 x) = Pi.single d (familyProduct φ d x)
  | 0 => rfl
  | d + 1 => by
    rw [switchProduct_succ, LinearMap.comp_apply, switchProduct_blockMap_single φ x d,
      blockMap_single, familyProduct_succ, LinearMap.comp_apply]

theorem derivativeProduct_blockDiagonal_single (ψ : ∀ e, C → V e →ₗ[R] V e) (d : ℕ) (v : V d) :
    ∀ {m : ℕ} (c : Fin m → C),
      derivativeProduct (blockDiagonal ψ) c (Pi.single d v) =
        Pi.single d (derivativeProduct (ψ d) c v)
  | 0, _ => rfl
  | m + 1, c => by
    rw [derivativeProduct_succ, LinearMap.comp_apply,
      derivativeProduct_blockDiagonal_single ψ d v (Fin.tail c), blockDiagonal_single,
      derivativeProduct_succ, LinearMap.comp_apply]

/-- **The determinant pairing along a sequence of modules.** -/
theorem derivativeProduct_familyProduct_eq_det [CharP R 2] (φ κ : ∀ e, V e →ₗ[R] V (e + 1))
    (ψ : ∀ e, C → V e →ₗ[R] V e) (b : C → ℕ → R) (x : V 0)
    (hφ : ∀ c e, ψ (e + 1) c ∘ₗ φ e = φ e ∘ₗ ψ e c + b c e • κ e)
    (hκ : ∀ c e, ψ (e + 1) c ∘ₗ κ e = κ e ∘ₗ ψ e c) (hx : ∀ c, ψ 0 c x = 0) {d : ℕ}
    (c : Fin d → C) :
    derivativeProduct (ψ d) c (familyProduct φ d x) =
      (Matrix.of fun r e : Fin d => b (c r) e).det • familyProduct κ d x := by
  classical
  have hF : ∀ c e, blockDiagonal ψ c ∘ₗ blockMap φ e =
      blockMap φ e ∘ₗ blockDiagonal ψ c + b c e • blockMap κ e := by
    intro c e
    apply LinearMap.ext
    intro m
    funext i
    simp only [blockDiagonal, blockMap, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.pi_apply, LinearMap.proj_apply, Pi.add_apply,
      Pi.smul_apply]
    by_cases hi : i = e + 1
    · subst hi
      simp only [LinearMap.coe_single, Pi.single_eq_same]
      have h := LinearMap.congr_fun (hφ c e) (m e)
      simpa [LinearMap.add_apply, LinearMap.smul_apply] using h
    · simp [LinearMap.coe_single, Pi.single_eq_of_ne hi]
  have hK : ∀ c e, blockDiagonal ψ c ∘ₗ blockMap κ e = blockMap κ e ∘ₗ blockDiagonal ψ c := by
    intro c e
    apply LinearMap.ext
    intro m
    funext i
    simp only [blockDiagonal, blockMap, LinearMap.comp_apply, LinearMap.pi_apply,
      LinearMap.proj_apply]
    by_cases hi : i = e + 1
    · subst hi
      simp only [LinearMap.coe_single, Pi.single_eq_same]
      exact LinearMap.congr_fun (hκ c e) (m e)
    · simp [LinearMap.coe_single, Pi.single_eq_of_ne hi]
  have hx' : ∀ c, blockDiagonal ψ c (Pi.single 0 x) = 0 := by
    intro c
    rw [blockDiagonal_single, hx, Pi.single_zero]
  have key := derivativeProduct_switchProduct_eq_det hF hK hx' c
  rw [switchProduct_blockMap_single, switchProduct_blockMap_single,
    derivativeProduct_blockDiagonal_single] at key
  have := congrFun key d
  simpa using this

end OnLeConjecture.KnotFloer
