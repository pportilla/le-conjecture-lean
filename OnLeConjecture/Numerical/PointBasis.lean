/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Numerical.RootBound

public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Order

/-!
# Numerical consequences of a point basis

This file isolates the two elementary inequalities for the point basis of a
complete plane ideal. The geometric construction of that point basis is kept
separate.
-/

public section

namespace OnLeConjecture.Numerical

open scoped BigOperators

/-- Numerical data supplied by the point basis of a complete plane ideal. -/
structure PointBasisCertificate (N : ℕ) where
  multiplicity : Fin N → ℕ
  root : Fin N
  d : ℕ
  root_multiplicity : multiplicity root = d
  multiplicity_le_root : ∀ p, multiplicity p ≤ d

namespace PointBasisCertificate

/-- Sum of the entries of a point basis. -/
@[expose]
def S {N : ℕ} (c : PointBasisCertificate N) : ℕ :=
  ∑ p, c.multiplicity p

/-- Sum of the squares of the entries of a point basis. -/
@[expose]
def M {N : ℕ} (c : PointBasisCertificate N) : ℕ :=
  ∑ p, c.multiplicity p ^ 2

/-- The sum of the point basis entries is at least its root entry. -/
theorem d_le_S {N : ℕ} (c : PointBasisCertificate N) :
    c.d ≤ c.S := by
  rw [← c.root_multiplicity]
  exact Finset.single_le_sum
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ c.root)

/-- The sum of the squares of the point basis entries is at most the root
entry multiplied by their sum. -/
theorem M_le_d_mul_S {N : ℕ} (c : PointBasisCertificate N) :
    c.M ≤ c.d * c.S := by
  calc
    c.M = ∑ p, c.multiplicity p ^ 2 := rfl
    _ ≤ ∑ p, c.d * c.multiplicity p := by
      apply Finset.sum_le_sum
      intro p _hp
      rw [pow_two]
      exact Nat.mul_le_mul_right _ (c.multiplicity_le_root p)
    _ = c.d * c.S := by
      simp only [S, Finset.mul_sum]

/-- The point basis inequalities and the remaining geometric estimates form
a reduction certificate. -/
def reductionCertificate {N : ℕ} (c : PointBasisCertificate N)
    (m n b : ℕ) (htwo : 2 ≤ c.d) (hb : 1 ≤ b) (hm : 2 ≤ m)
    (hglobal : c.M + c.S ≤ 3 * m) (hn : c.d ≤ n)
    (hpolar : n * (m - 1) + c.S + b ≤ 2 * c.M) :
    ReductionCertificate where
  d := c.d
  M := c.M
  S := c.S
  m := m
  n := n
  b := b
  two_le_d := htwo
  d_le_S := c.d_le_S
  b_positive := hb
  M_le_dS := c.M_le_d_mul_S
  m_at_least_two := hm
  global_estimate := hglobal
  d_le_n := hn
  polar_estimate := hpolar

/-- The point basis inequalities and the polar estimates force the root
multiplicity to be at most four. -/
theorem d_le_four_of_estimates {N : ℕ} (c : PointBasisCertificate N)
    (m n b : ℕ) (htwo : 2 ≤ c.d) (hb : 1 ≤ b) (hm : 2 ≤ m)
    (hglobal : c.M + c.S ≤ 3 * m) (hn : c.d ≤ n)
    (hpolar : n * (m - 1) + c.S + b ≤ 2 * c.M) :
    c.d ≤ 4 := by
  exact (c.reductionCertificate m n b htwo hb hm hglobal hn hpolar).d_le_four

/-- Under the reduction estimates, the root multiplicity is two, three, or
four. -/
theorem d_eq_two_or_three_or_four_of_estimates {N : ℕ}
    (c : PointBasisCertificate N) (m n b : ℕ)
    (htwo : 2 ≤ c.d) (hb : 1 ≤ b) (hm : 2 ≤ m)
    (hglobal : c.M + c.S ≤ 3 * m) (hn : c.d ≤ n)
    (hpolar : n * (m - 1) + c.S + b ≤ 2 * c.M) :
    c.d = 2 ∨ c.d = 3 ∨ c.d = 4 := by
  exact ReductionCertificate.d_eq_two_or_three_or_four
    (c.reductionCertificate m n b htwo hb hm hglobal hn hpolar)

end PointBasisCertificate

end OnLeConjecture.Numerical
