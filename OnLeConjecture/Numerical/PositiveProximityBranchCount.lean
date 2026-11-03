/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Numerical.ProximityReduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Positive branch count from positive acyclic proximity data

A point of maximal generation has no proximate successor, so its whole
positive multiplicity contributes to the sum of excesses.
-/

public section

namespace OnLeConjecture.Numerical.ProximityCertificate

theorem branchCount_pos_of_positive_and_generation
    {N : ℕ} (c : ProximityCertificate (Fin N)) (generation : Fin N → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p → generation p < generation q)
    (hpositive : ∀ p, 0 < c.multiplicity p) : 0 < c.branchCount := by
  classical
  obtain ⟨p, _hp, hmax⟩ := Finset.exists_max_image Finset.univ generation
    ⟨c.root, Finset.mem_univ _⟩
  have hnone (q : Fin N) : p ∉ c.parents q := by
    intro hpq
    have hlt := hdecrease hpq
    have hle := hmax q (Finset.mem_univ _)
    omega
  have hsuccessor : c.successorMultiplicity p = 0 := by
    simp [successorMultiplicity, hnone]
  have hexcess : c.excess p = c.multiplicity p := by
    rw [excess, hsuccessor, Nat.sub_zero]
  have hle : c.excess p ≤ c.branchCount :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
  rw [hexcess] at hle
  exact (hpositive p).trans_le hle

end OnLeConjecture.Numerical.ProximityCertificate
