/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Coefficient tables of the second torus correction

The coefficients of the second torus correction are functions of cyclic
distances on a grid with `2p+1` columns. They are recorded here as natural
numbers. Only their residues modulo two enter the chains.

* `tcE p d` is the transposition coefficient: for `d < 2p+1`, the parity of the
  shorter of the two cyclic distances `d` and `2p+1-d`.
* `tcHp`, `tcC` and `tcT` are the functions `h_p`, `C_p^0` and `T_p^0` of the
  four-cycle density.
* `tcW4 p r₁ r₂ r₃` is the contribution of one adjacent pair `(u, u+1)` to the
  coefficient of a four-cycle, where `r_i` is the distance from `u` to the
  `i`-th iterate of `u`.
* `tcF p r_a r_v r_z` is the four-point function `F(u, a, v, z)` of the
  three-cycle and transposition coefficient, where the arguments are the
  distances of `a`, `v`, `z` from `u`.

These definitions encode the tables `(H4D.1)`, `(H4D.3)`, `(H4D.5)` and `(M6.3)`
of the written proof. The half-turn word of `(M6.3)` is evaluated by direct
comparisons of the distances with `p`. The tables are written without truncated
subtraction.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

/-- The transposition coefficient. For `d < 2p+1` it is the parity of the shorter of
the two cyclic distances `d` and `2p+1-d`. -/
def tcE (p d : ℕ) : ℕ := if d ≤ p then d % 2 else (d + 1) % 2

/-- The function `h_p` of the four-cycle density. -/
def tcHp (p d : ℕ) : ℕ := if d ≤ p then d % 2 else if d = p + 1 then (1 + p) % 2 else 1

/-- The convex coefficient `C_p^0(A, B) = h_p(A) + h_p(B)`. -/
def tcC (p A B : ℕ) : ℕ := tcHp p A + tcHp p B

/-- The function `T_p^0(A, B)`, for `2 ≤ A < B ≤ 2p`. -/
def tcT (p A B : ℕ) : ℕ :=
  if B ≤ p then (1 + B) % 2
  else if A ≤ p ∧ p + 2 ≤ B ∧ p + 1 + A ≤ B then (1 + B) % 2
  else if A ≤ p ∧ p + 2 ≤ B then 0
  else if B = p + 1 then (1 + A + p) % 2
  else if A = p + 1 then 1
  else (1 + A) % 2

/-- The contribution of an adjacent pair to a four-cycle coefficient. The pair
`(u, u+1)` is fixed, and `r₁, r₂, r₃` are the distances from `u` to its three
iterates; exactly one of them equals one. -/
def tcW4 (p r₁ r₂ r₃ : ℕ) : ℕ :=
  if r₁ = 1 then tcC p (min r₂ r₃) (max r₂ r₃)
  else if r₂ = 1 then (if r₁ < r₃ then tcT p r₁ r₃ else tcT p r₃ r₁ + tcC p r₃ r₁)
  else 0

/-- The four-point function `F(u, a, v, z)`, written through the distances
`ra < rv < rz` of `a, v, z` from `u`. -/
def tcF (p ra rv rz : ℕ) : ℕ :=
  if rz ≤ p then 0
  else if rv ≤ p then
    (if rz ≤ p + ra then (1 + rv) % 2 else if rz ≤ p + rv then (1 + ra) % 2 else (1 + rz) % 2)
  else if ra ≤ p then (if rz ≤ p + ra then (1 + rz) % 2 else 0)
  else 0

theorem tcE_lt_two (p d : ℕ) : tcE p d < 2 := by
  unfold tcE; split_ifs <;> omega

theorem tcE_symm {p d : ℕ} (hd : d < 2 * p + 1) : tcE p (2 * p + 1 - d) = tcE p d := by
  unfold tcE; split_ifs <;> omega


/-- The sum of the contributions of an adjacent pair to a four-cycle and to its
inverse. It depends only on the set of the three distances. -/
def tcVS (p x y z : ℕ) : ℕ :=
  if x = 1 then tcC p (min y z) (max y z)
  else if y = 1 then tcC p (min x z) (max x z)
  else if z = 1 then tcC p (min x y) (max x y)
  else 0

theorem tcW4_add_rev {p x y z : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (tcW4 p x y z + tcW4 p z y x) % 2 = tcVS p x y z % 2 := by
  unfold tcW4 tcVS
  by_cases hx : x = 1
  · subst hx
    rw [if_pos rfl, if_neg (Ne.symm hxz), if_neg (Ne.symm hxy), if_pos rfl]
    simp
  · by_cases hy : y = 1
    · subst hy
      rw [if_neg hx, if_pos rfl, if_neg (Ne.symm hyz), if_pos rfl, if_neg hx, if_pos rfl]
      rcases Nat.lt_or_gt_of_ne hxz with h | h
      · rw [if_pos h, if_neg (by omega), min_eq_left h.le, max_eq_right h.le]
        unfold tcC; omega
      · rw [if_neg (by omega), if_pos h, min_eq_right h.le, max_eq_left h.le]
        unfold tcC; omega
    · by_cases hz : z = 1
      · subst hz
        rw [if_neg hx, if_neg hy, if_pos rfl, if_neg hx, if_neg hy, if_pos rfl,
          min_comm, max_comm]
        simp
      · simp [hx, hy, hz]

theorem tcVS_swap12 {p x y z : ℕ} (hxy : x ≠ y) : tcVS p x y z = tcVS p y x z := by
  unfold tcVS
  by_cases hx : x = 1
  · subst hx
    rw [if_pos rfl, if_neg (Ne.symm hxy), if_pos rfl]
  · by_cases hy : y = 1
    · subst hy; rw [if_neg hx, if_pos rfl, if_pos rfl]
    · rw [if_neg hx, if_neg hy, if_neg hy, if_neg hx, min_comm, max_comm]

theorem tcVS_swap23 {p x y z : ℕ} (hyz : y ≠ z) : tcVS p x y z = tcVS p x z y := by
  unfold tcVS
  by_cases hx : x = 1
  · rw [if_pos hx, if_pos hx, min_comm, max_comm]
  · rw [if_neg hx, if_neg hx]
    by_cases hy : y = 1
    · subst hy; rw [if_pos rfl, if_neg (Ne.symm hyz), if_pos rfl]
    · by_cases hz : z = 1
      · subst hz; rw [if_neg hy, if_pos rfl, if_pos rfl]
      · rw [if_neg hy, if_neg hz, if_neg hz, if_neg hy]


/-- `tcVS` is a symmetric function of three distinct arguments. -/
theorem tcVS_perm {p a b c x y z : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : (x = a ∧ y = b ∧ z = c) ∨ (x = a ∧ y = c ∧ z = b) ∨ (x = b ∧ y = a ∧ z = c) ∨
      (x = b ∧ y = c ∧ z = a) ∨ (x = c ∧ y = a ∧ z = b) ∨ (x = c ∧ y = b ∧ z = a)) :
    tcVS p x y z = tcVS p a b c := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h1, h2, h3]
  · exact tcVS_swap23 (Ne.symm hbc)
  · exact tcVS_swap12 (Ne.symm hab)
  · exact (tcVS_swap23 (Ne.symm hac)).trans (tcVS_swap12 (Ne.symm hab))
  · exact (tcVS_swap12 (Ne.symm hac)).trans (tcVS_swap23 (Ne.symm hbc))
  · exact (tcVS_swap12 (Ne.symm hbc)).trans ((tcVS_swap23 (Ne.symm hac)).trans
      (tcVS_swap12 (Ne.symm hab)))


end OnLeConjecture.KnotFloer.GridFull
