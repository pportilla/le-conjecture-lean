/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositivePermutationWords
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Fin

/-! # Concatenating ordered positive event words -/

public section

namespace OnLeConjecture.KnotTheory

open Equiv

theorem PositiveAdjacentWord.permutation_append {a : ℕ}
    (u v : PositiveAdjacentWord a) :
    (u ++ v).toSigned.permutation = u.toSigned.permutation * v.toSigned.permutation := by
  change (u ++ v).permutation = u.permutation * v.permutation
  induction u with
  | nil => simp
  | cons i u ih =>
    simpa only [List.cons_append, PositiveAdjacentWord.permutation_cons, mul_assoc] using
      congrArg (fun q => adjacentSwap i * q) ih

/-- The number of letters in the concatenated event words is their total length. -/
theorem positiveWordSequence_length {a N : ℕ} (w : Fin N → PositiveAdjacentWord a) :
    (List.ofFn w).flatten.length = ∑ j, (w j).length := by
  simp [List.length_flatten, List.map_ofFn, List.sum_ofFn]

/-- Successive chamber transitions telescope in the actual list order. -/
theorem positiveWordSequence_permutation {a N : ℕ}
    (p : Fin (N + 1) → Perm (Fin a)) (w : Fin N → PositiveAdjacentWord a)
    (hstep : ∀ j, p j.castSucc * (w j).toSigned.permutation = p j.succ) :
    p 0 * (PositiveAdjacentWord.toSigned (List.ofFn w).flatten).permutation = p (Fin.last N) := by
  induction N with
  | zero =>
    change p 0 * PositiveAdjacentWord.permutation [] = p 0
    simp
  | succ N ih =>
    have hs : p 0 * (w 0).toSigned.permutation = p (Fin.succ 0) := by
      simpa only [Fin.castSucc_zero] using hstep 0
    rw [List.ofFn_succ, List.flatten_cons, PositiveAdjacentWord.permutation_append,
      ← mul_assoc, hs]
    simpa only [Fin.succ_last] using ih (fun j => p j.succ) (fun j => w j.succ)
      (fun j => by simpa only [Fin.succ_castSucc] using hstep j.succ)

end OnLeConjecture.KnotTheory
