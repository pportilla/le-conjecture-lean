/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusSecondIdentities

/-!
# Targets moving six columns

At a target moving six columns, the coefficient formula at exponent `-3` is the
sum of the three-cycle and transposition coefficients of the removals of single
columns (`coefFormula_six_eq_removals`). This file evaluates that sum at the
fourteen patterns of grading six, up to cyclic relabelling.

* `m66` and `m67` are the identities `(M6.6)` and `(M6.7)` of the written proof
  for the four-point function `F`, with the auxiliary functions `K` of `(M6.4)`
  (`tcK`) and `G` of `(M6.7)` (`tcG`).
* For a four-cycle and a transposition the sum vanishes. For two three-cycles an
  odd sum forces both triangles to be balanced, and the displacements then
  satisfy the linear Alexander inequality.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

/-- The function `K(u, a, v)` of `(M6.4)`, written through the distances `ra < rv`
of `a` and `v` from `u`. -/
def tcK (p ra rv : ℕ) : ℕ :=
  if rv ≤ p then 0 else if ra ≤ p then (if rv ≤ p + ra then rv % 2 else 0) else (ra + rv) % 2

/-- The right side of `(M6.7)` for four points in positive cyclic order with
successive gaps `x, y, z`, where `xy = x + y` and `yz = y + z`. -/
def tcG (p x y z xy yz : ℕ) : ℕ :=
  (if x ≤ p ∧ y ≤ p then x % 2 else 0) + (if xy ≤ p ∧ ¬ yz ≤ p then 1 else 0) +
    (if ¬ z ≤ p then yz % 2 else 0)

/-- The identity `(M6.6)`: `F(u,a,v,b) + F(v,b,u,a) = K(u,a,v) + K(v,b,u)`. The
arguments are the distances of `a, v, b` from `u` and of `b, u, a` from `v`. -/
theorem m66 (p A1 A2 A3 B1 B2 B3 : ℕ) (h1 : 0 < A1) (h12 : A1 < A2) (h23 : A2 < A3)
    (h3 : A3 < 2 * p + 1) (hB1 : A2 + B1 = A3) (hB2 : A2 + B2 = 2 * p + 1)
    (hB3 : B2 + A1 = B3) :
    (tcF p A1 A2 A3 + tcF p B1 B2 B3) % 2 = (tcK p A1 A2 + tcK p B1 B2) % 2 := by
  simp only [tcF, tcK]
  prune_ifs

/-- The identity `(M6.7)`: `F(u,a,v,b) + F(a,v,b,u) = G(u,a,v,b)`. The arguments
are the distances of `a, v, b` from `u`, of `v, b, u` from `a`, and of `b` from `v`. -/
theorem m67 (p A1 A2 A3 C1 C2 C3 Z : ℕ) (h1 : 0 < A1) (h12 : A1 < A2) (h23 : A2 < A3)
    (h3 : A3 < 2 * p + 1) (hC1 : A1 + C1 = A2) (hC2 : A1 + C2 = A3)
    (hC3 : A1 + C3 = 2 * p + 1) (hZ : A2 + Z = A3) :
    (tcF p A1 A2 A3 + tcF p C1 C2 C3) % 2 = tcG p A1 C1 Z A2 C2 % 2 := by
  simp only [tcF, tcG]
  prune_ifs


/-- The two-triangle sum `(M6.16)` of the functions `G` over six points: if it is odd,
every sum of two successive gaps is at most `p`. This is the case analysis of the proof of
`(M6.13)` for the partition into alternate triangles. -/
theorem hex_alt_arith (p a0 a1 a2 a3 a4 a5 : ℕ) (h0 : 0 < a0) (h1 : 0 < a1) (h2 : 0 < a2)
    (h3 : 0 < a3) (h4 : 0 < a4) (h5 : 0 < a5) (hN : a0 + a1 + a2 + a3 + a4 + a5 = 2 * p + 1)
    (h : (tcG p a0 a1 a2 (a0 + a1) (a1 + a2) + tcG p a1 a2 a3 (a1 + a2) (a2 + a3) +
      tcG p a2 a3 a4 (a2 + a3) (a3 + a4) + tcG p a3 a4 a5 (a3 + a4) (a4 + a5) +
      tcG p a4 a5 a0 (a4 + a5) (a5 + a0) + tcG p a5 a0 a1 (a5 + a0) (a0 + a1)) % 2 = 1) :
    a0 + a1 ≤ p ∧ a1 + a2 ≤ p ∧ a2 + a3 ≤ p ∧ a3 + a4 ≤ p ∧ a4 + a5 ≤ p ∧ a5 + a0 ≤ p := by
  simp only [tcG] at h
  by_cases A0 : a0 ≤ p <;> by_cases A1 : a1 ≤ p <;> by_cases A2 : a2 ≤ p <;>
    by_cases A3 : a3 ≤ p <;> by_cases A4 : a4 ≤ p <;> by_cases A5 : a5 ≤ p <;>
    (try (exfalso; omega)) <;>
    by_cases B0 : a0 + a1 ≤ p <;> by_cases B1 : a1 + a2 ≤ p <;> by_cases B2 : a2 + a3 ≤ p <;>
    by_cases B3 : a3 + a4 ≤ p <;> by_cases B4 : a4 + a5 ≤ p <;> by_cases B5 : a5 + a0 ≤ p <;>
    (try (exfalso; omega)) <;>
    simp only [A0, A1, A2, A3, A4, A5, B0, B1, B2, B3, B4, B5, and_self, and_true,
      and_false, if_true, if_false, not_true_eq_false, not_false_eq_true,
      add_zero, zero_add] at h <;>
    omega

variable (n : ℕ)

/-- The removal sum of a transported permutation, written on labels. -/
theorem removal_sum_cfgPerm {k : ℕ} (c : Fin k ↪ Fin (consecutiveTorusGridSize n))
    (ρ : Equiv.Perm (Fin k)) :
    (∑ q : Fin (consecutiveTorusGridSize n),
        if cfgPerm c ρ (cfgPerm c ρ q) ≠ q then
          torusFiveCoeff n (cfgPerm c ρ * Equiv.swap q ((cfgPerm c ρ).symm q)) else 0) =
      ∑ i : Fin k, if ρ (ρ i) ≠ i then torusFiveCoeff n (cfgPerm c (ρ * Equiv.swap (ρ i) i))
        else 0 := by
  classical
  rw [← Equiv.sum_comp (cfgPerm c ρ)]
  simp only [Equiv.symm_apply_apply]
  rw [sum_eq_sum_emb c _ (fun x hx => by
    have hfix := cfgPerm_apply_of_notMem c ρ hx
    simp [hfix])]
  apply Finset.sum_congr rfl
  intro i _
  simp only [cfgPerm_apply_emb, ne_eq, c.injective.eq_iff, cfgPerm_mul_swap]
  congr 1
  apply propext
  constructor
  · intro h h'; exact h (by rw [h'])
  · intro h h'; exact h (ρ.injective h')

set_option hygiene false in
/-- The evaluation of the removal sum at a transported pattern of six labels. It
expects `n`, `c` and `hc` in context. -/
macro "hex_tac" : tactic => `(tactic| (
    simp (config := {decide := true}) only [Fin.sum_univ_six, Equiv.Perm.mul_apply,
      Equiv.swap_apply_def, ite_true, ite_false, Fin.isValue, add_zero, zero_add, ne_eq,
      not_true_eq_false, not_false_eq_true]
    try simp (disch := decide) only [torusFiveCoeff_cfgPerm_of_card]
    simp only [torusFiveCoeff_cfgPerm n hc]
    simp (config := {decide := true}) only [Fin.sum_univ_six, Equiv.Perm.mul_apply,
      Equiv.swap_apply_def, ite_true, ite_false, Fin.isValue, ite_self, add_zero, zero_add]
    obtain ⟨⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17,
      e18, e19, e20, e21, e22, e23, e24⟩, ⟨g1, g2, g3, g4, g5, g6⟩, hN⟩ := cycDist_gaps_6 hc
    simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17,
      e18, e19, e20, e21, e22, e23, e24]
    generalize cycDist (c 0) (c 1) = a0 at *
    generalize cycDist (c 1) (c 2) = a1 at *
    generalize cycDist (c 2) (c 3) = a2 at *
    generalize cycDist (c 3) (c 4) = a3 at *
    generalize cycDist (c 4) (c 5) = a4 at *
    generalize cycDist (c 5) (c 0) = a5 at *
    clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22
      e23 e24
    unfold consecutiveTorusGridSize at hN))

variable {c : Fin 6 ↪ Fin (consecutiveTorusGridSize n)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the removal sum produces a large expression.
/-- The removal sum at the pattern `(0 1 2 4)(3 5)`: if it is odd, the displacements
satisfy the linear Alexander inequality. -/
theorem hexagon_a (hc : CycSorted c) :
    (∑ i : Fin 6, if (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 3 5 :
        Equiv.Perm (Fin 6)) ((Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 3 5 :
        Equiv.Perm (Fin 6)) i) ≠ i then
        torusFiveCoeff n (cfgPerm c ((Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap
            3 5 : Equiv.Perm (Fin 6)) * Equiv.swap ((Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2
            4 * Equiv.swap 3 5 : Equiv.Perm (Fin 6)) i) i)) else 0) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 4 *
          Equiv.swap 3 5 : Equiv.Perm (Fin 6)) i)) - (n + 2)) ≤ (n + 1) * 2 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 3 5 :
            Equiv.Perm (Fin 6)) i)) = 2 * (2 * n + 3) := by
  hex_tac
  try simp only [tcG]
  prune_ifs'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the removal sum produces a large expression.
/-- The removal sum at the pattern `(0 1 3 4)(2 5)`: if it is odd, the displacements
satisfy the linear Alexander inequality. -/
theorem hexagon_b (hc : CycSorted c) :
    (∑ i : Fin 6, if (Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 2 5 :
        Equiv.Perm (Fin 6)) ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 2 5 :
        Equiv.Perm (Fin 6)) i) ≠ i then
        torusFiveCoeff n (cfgPerm c ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap
            2 5 : Equiv.Perm (Fin 6)) * Equiv.swap ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3
            4 * Equiv.swap 2 5 : Equiv.Perm (Fin 6)) i) i)) else 0) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 *
          Equiv.swap 2 5 : Equiv.Perm (Fin 6)) i)) - (n + 2)) ≤ (n + 1) * 2 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 2 5 :
            Equiv.Perm (Fin 6)) i)) = 2 * (2 * n + 3) := by
  hex_tac
  have r1 := m66 (n + 1) (a2) (a2 + a3 + a4) (a2 + a3 + a4 + a5)
    (a5) (a5 + a0 + a1) (a5 + a0 + a1 + a2) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have r2 := m66 (n + 1) (a2) (a2 + a3 + a4) (a2 + a3 + a4 + a5 + a0)
    (a5 + a0) (a5 + a0 + a1) (a5 + a0 + a1 + a2) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have r3 := m66 (n + 1) (a2 + a3) (a2 + a3 + a4) (a2 + a3 + a4 + a5)
    (a5) (a5 + a0 + a1) (a5 + a0 + a1 + a2 + a3) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have r4 := m66 (n + 1) (a2 + a3) (a2 + a3 + a4) (a2 + a3 + a4 + a5 + a0)
    (a5 + a0) (a5 + a0 + a1) (a5 + a0 + a1 + a2 + a3) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  revert r1 r2 r3 r4
  try simp only [tcG]
  prune_ifs'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the removal sum produces a large expression.
/-- The removal sum at the pattern `(0 1 4 2)(3 5)`: if it is odd, the displacements
satisfy the linear Alexander inequality. -/
theorem hexagon_c (hc : CycSorted c) :
    (∑ i : Fin 6, if (Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 2 * Equiv.swap 3 5 :
        Equiv.Perm (Fin 6)) ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 2 * Equiv.swap 3 5 :
        Equiv.Perm (Fin 6)) i) ≠ i then
        torusFiveCoeff n (cfgPerm c ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 2 * Equiv.swap
            3 5 : Equiv.Perm (Fin 6)) * Equiv.swap ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4
            2 * Equiv.swap 3 5 : Equiv.Perm (Fin 6)) i) i)) else 0) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 2 *
          Equiv.swap 3 5 : Equiv.Perm (Fin 6)) i)) - (n + 2)) ≤ (n + 1) * 3 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 2 * Equiv.swap 3 5 :
            Equiv.Perm (Fin 6)) i)) = 3 * (2 * n + 3) := by
  hex_tac
  try simp only [tcG]
  prune_ifs'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the removal sum produces a large expression.
/-- The removal sum at the pattern `(0 1 4 3)(2 5)`: if it is odd, the displacements
satisfy the linear Alexander inequality. -/
theorem hexagon_d (hc : CycSorted c) :
    (∑ i : Fin 6, if (Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 3 * Equiv.swap 2 5 :
        Equiv.Perm (Fin 6)) ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 3 * Equiv.swap 2 5 :
        Equiv.Perm (Fin 6)) i) ≠ i then
        torusFiveCoeff n (cfgPerm c ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 3 * Equiv.swap
            2 5 : Equiv.Perm (Fin 6)) * Equiv.swap ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4
            3 * Equiv.swap 2 5 : Equiv.Perm (Fin 6)) i) i)) else 0) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 3 *
          Equiv.swap 2 5 : Equiv.Perm (Fin 6)) i)) - (n + 2)) ≤ (n + 1) * 3 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 4 3 * Equiv.swap 2 5 :
            Equiv.Perm (Fin 6)) i)) = 3 * (2 * n + 3) := by
  hex_tac
  have r1 := m66 (n + 1) (a2) (a2 + a3 + a4) (a2 + a3 + a4 + a5)
    (a5) (a5 + a0 + a1) (a5 + a0 + a1 + a2) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have r2 := m66 (n + 1) (a2) (a2 + a3 + a4) (a2 + a3 + a4 + a5 + a0)
    (a5 + a0) (a5 + a0 + a1) (a5 + a0 + a1 + a2) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have r3 := m66 (n + 1) (a2 + a3) (a2 + a3 + a4) (a2 + a3 + a4 + a5)
    (a5) (a5 + a0 + a1) (a5 + a0 + a1 + a2 + a3) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have r4 := m66 (n + 1) (a2 + a3) (a2 + a3 + a4) (a2 + a3 + a4 + a5 + a0)
    (a5 + a0) (a5 + a0 + a1) (a5 + a0 + a1 + a2 + a3) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  revert r1 r2 r3 r4
  try simp only [tcG]
  prune_ifs'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the removal sum produces a large expression.
/-- The removal sum at the pattern `(0 1 5 3)(2 4)`: if it is odd, the displacements
satisfy the linear Alexander inequality. -/
theorem hexagon_e (hc : CycSorted c) :
    (∑ i : Fin 6, if (Equiv.swap 0 1 * Equiv.swap 1 5 * Equiv.swap 5 3 * Equiv.swap 2 4 :
        Equiv.Perm (Fin 6)) ((Equiv.swap 0 1 * Equiv.swap 1 5 * Equiv.swap 5 3 * Equiv.swap 2 4 :
        Equiv.Perm (Fin 6)) i) ≠ i then
        torusFiveCoeff n (cfgPerm c ((Equiv.swap 0 1 * Equiv.swap 1 5 * Equiv.swap 5 3 * Equiv.swap
            2 4 : Equiv.Perm (Fin 6)) * Equiv.swap ((Equiv.swap 0 1 * Equiv.swap 1 5 * Equiv.swap 5
            3 * Equiv.swap 2 4 : Equiv.Perm (Fin 6)) i) i)) else 0) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 5 * Equiv.swap 5 3 *
          Equiv.swap 2 4 : Equiv.Perm (Fin 6)) i)) - (n + 2)) ≤ (n + 1) * 3 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 5 * Equiv.swap 5 3 * Equiv.swap 2 4 :
            Equiv.Perm (Fin 6)) i)) = 3 * (2 * n + 3) := by
  hex_tac
  try simp only [tcG]
  prune_ifs'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the removal sum produces a large expression.
/-- The removal sum at the pattern `(0 2 4 1)(3 5)`: if it is odd, the displacements
satisfy the linear Alexander inequality. -/
theorem hexagon_f (hc : CycSorted c) :
    (∑ i : Fin 6, if (Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 1 * Equiv.swap 3 5 :
        Equiv.Perm (Fin 6)) ((Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 1 * Equiv.swap 3 5 :
        Equiv.Perm (Fin 6)) i) ≠ i then
        torusFiveCoeff n (cfgPerm c ((Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 1 * Equiv.swap
            3 5 : Equiv.Perm (Fin 6)) * Equiv.swap ((Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4
            1 * Equiv.swap 3 5 : Equiv.Perm (Fin 6)) i) i)) else 0) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 1 *
          Equiv.swap 3 5 : Equiv.Perm (Fin 6)) i)) - (n + 2)) ≤ (n + 1) * 3 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 1 * Equiv.swap 3 5 :
            Equiv.Perm (Fin 6)) i)) = 3 * (2 * n + 3) := by
  hex_tac
  try simp only [tcG]
  prune_ifs'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the removal sum produces a large expression.
/-- The removal sum at the pattern `(0 2)(1 3 5 4)`: if it is odd, the displacements
satisfy the linear Alexander inequality. -/
theorem hexagon_g (hc : CycSorted c) :
    (∑ i : Fin 6, if (Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 3 5 * Equiv.swap 5 4 :
        Equiv.Perm (Fin 6)) ((Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 3 5 * Equiv.swap 5 4 :
        Equiv.Perm (Fin 6)) i) ≠ i then
        torusFiveCoeff n (cfgPerm c ((Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 3 5 * Equiv.swap
            5 4 : Equiv.Perm (Fin 6)) * Equiv.swap ((Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 3
            5 * Equiv.swap 5 4 : Equiv.Perm (Fin 6)) i) i)) else 0) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 3 5 *
          Equiv.swap 5 4 : Equiv.Perm (Fin 6)) i)) - (n + 2)) ≤ (n + 1) * 3 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 3 5 * Equiv.swap 5 4 :
            Equiv.Perm (Fin 6)) i)) = 3 * (2 * n + 3) := by
  hex_tac
  try simp only [tcG]
  prune_ifs'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the removal sum produces a large expression.
/-- The removal sum at the pattern `(0 2)(1 5 4 3)`: if it is odd, the displacements
satisfy the linear Alexander inequality. -/
theorem hexagon_h (hc : CycSorted c) :
    (∑ i : Fin 6, if (Equiv.swap 0 2 * Equiv.swap 1 5 * Equiv.swap 5 4 * Equiv.swap 4 3 :
        Equiv.Perm (Fin 6)) ((Equiv.swap 0 2 * Equiv.swap 1 5 * Equiv.swap 5 4 * Equiv.swap 4 3 :
        Equiv.Perm (Fin 6)) i) ≠ i then
        torusFiveCoeff n (cfgPerm c ((Equiv.swap 0 2 * Equiv.swap 1 5 * Equiv.swap 5 4 * Equiv.swap
            4 3 : Equiv.Perm (Fin 6)) * Equiv.swap ((Equiv.swap 0 2 * Equiv.swap 1 5 * Equiv.swap 5
            4 * Equiv.swap 4 3 : Equiv.Perm (Fin 6)) i) i)) else 0) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 2 * Equiv.swap 1 5 * Equiv.swap 5 4 *
          Equiv.swap 4 3 : Equiv.Perm (Fin 6)) i)) - (n + 2)) ≤ (n + 1) * 4 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 2 * Equiv.swap 1 5 * Equiv.swap 5 4 * Equiv.swap 4 3 :
            Equiv.Perm (Fin 6)) i)) = 4 * (2 * n + 3) := by
  hex_tac
  try simp only [tcG]
  prune_ifs'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the removal sum produces a large expression.
/-- The removal sum at the pattern `(0 3)(1 5 4 2)`: if it is odd, the displacements
satisfy the linear Alexander inequality. -/
theorem hexagon_i (hc : CycSorted c) :
    (∑ i : Fin 6, if (Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 5 4 * Equiv.swap 4 2 :
        Equiv.Perm (Fin 6)) ((Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 5 4 * Equiv.swap 4 2 :
        Equiv.Perm (Fin 6)) i) ≠ i then
        torusFiveCoeff n (cfgPerm c ((Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 5 4 * Equiv.swap
            4 2 : Equiv.Perm (Fin 6)) * Equiv.swap ((Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 5
            4 * Equiv.swap 4 2 : Equiv.Perm (Fin 6)) i) i)) else 0) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 5 4 *
          Equiv.swap 4 2 : Equiv.Perm (Fin 6)) i)) - (n + 2)) ≤ (n + 1) * 4 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 5 4 * Equiv.swap 4 2 :
            Equiv.Perm (Fin 6)) i)) = 4 * (2 * n + 3) := by
  hex_tac
  have r1 := m66 (n + 1) (a0) (a0 + a1 + a2) (a0 + a1 + a2 + a3)
    (a3) (a3 + a4 + a5) (a3 + a4 + a5 + a0) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have r2 := m66 (n + 1) (a0) (a0 + a1 + a2) (a0 + a1 + a2 + a3 + a4)
    (a3 + a4) (a3 + a4 + a5) (a3 + a4 + a5 + a0) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have r3 := m66 (n + 1) (a0 + a1) (a0 + a1 + a2) (a0 + a1 + a2 + a3)
    (a3) (a3 + a4 + a5) (a3 + a4 + a5 + a0 + a1) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have r4 := m66 (n + 1) (a0 + a1) (a0 + a1 + a2) (a0 + a1 + a2 + a3 + a4)
    (a3 + a4) (a3 + a4 + a5) (a3 + a4 + a5 + a0 + a1) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  revert r1 r2 r3 r4
  try simp only [tcG]
  prune_ifs'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the removal sum produces a large expression.
/-- The removal sum at the pattern `(0 1 3)(2 4 5)`: if it is odd, the displacements
satisfy the linear Alexander inequality. -/
theorem hexagon_j (hc : CycSorted c) :
    (∑ i : Fin 6, if (Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 4 * Equiv.swap 4 5 :
        Equiv.Perm (Fin 6)) ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 4 * Equiv.swap 4 5 :
        Equiv.Perm (Fin 6)) i) ≠ i then
        torusFiveCoeff n (cfgPerm c ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 4 * Equiv.swap
            4 5 : Equiv.Perm (Fin 6)) * Equiv.swap ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2
            4 * Equiv.swap 4 5 : Equiv.Perm (Fin 6)) i) i)) else 0) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 4 *
          Equiv.swap 4 5 : Equiv.Perm (Fin 6)) i)) - (n + 2)) ≤ (n + 1) * 2 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 4 * Equiv.swap 4 5 :
            Equiv.Perm (Fin 6)) i)) = 2 * (2 * n + 3) := by
  hex_tac
  have r1 := m67 (n + 1) (a0 + a1) (a0 + a1 + a2) (a0 + a1 + a2 + a3)
    (a2) (a2 + a3) (a2 + a3 + a4 + a5) (a3) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r2 := m67 (n + 1) (a0 + a1) (a0 + a1 + a2) (a0 + a1 + a2 + a3 + a4)
    (a2) (a2 + a3 + a4) (a2 + a3 + a4 + a5) (a3 + a4) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r3 := m67 (n + 1) (a1) (a1 + a2) (a1 + a2 + a3)
    (a2) (a2 + a3) (a2 + a3 + a4 + a5 + a0) (a3) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r4 := m67 (n + 1) (a1) (a1 + a2) (a1 + a2 + a3 + a4)
    (a2) (a2 + a3 + a4) (a2 + a3 + a4 + a5 + a0) (a3 + a4) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  revert r1 r2 r3 r4
  try simp only [tcG]
  prune_ifs'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the removal sum produces a large expression.
/-- The removal sum at the pattern `(0 1 3)(2 5 4)`: if it is odd, the displacements
satisfy the linear Alexander inequality. -/
theorem hexagon_k (hc : CycSorted c) :
    (∑ i : Fin 6, if (Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 5 * Equiv.swap 5 4 :
        Equiv.Perm (Fin 6)) ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 5 * Equiv.swap 5 4 :
        Equiv.Perm (Fin 6)) i) ≠ i then
        torusFiveCoeff n (cfgPerm c ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 5 * Equiv.swap
            5 4 : Equiv.Perm (Fin 6)) * Equiv.swap ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2
            5 * Equiv.swap 5 4 : Equiv.Perm (Fin 6)) i) i)) else 0) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 5 *
          Equiv.swap 5 4 : Equiv.Perm (Fin 6)) i)) - (n + 2)) ≤ (n + 1) * 3 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 5 * Equiv.swap 5 4 :
            Equiv.Perm (Fin 6)) i)) = 3 * (2 * n + 3) := by
  hex_tac
  have r1 := m67 (n + 1) (a0 + a1) (a0 + a1 + a2) (a0 + a1 + a2 + a3)
    (a2) (a2 + a3) (a2 + a3 + a4 + a5) (a3) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r2 := m67 (n + 1) (a0 + a1) (a0 + a1 + a2) (a0 + a1 + a2 + a3 + a4)
    (a2) (a2 + a3 + a4) (a2 + a3 + a4 + a5) (a3 + a4) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r3 := m67 (n + 1) (a1) (a1 + a2) (a1 + a2 + a3)
    (a2) (a2 + a3) (a2 + a3 + a4 + a5 + a0) (a3) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r4 := m67 (n + 1) (a1) (a1 + a2) (a1 + a2 + a3 + a4)
    (a2) (a2 + a3 + a4) (a2 + a3 + a4 + a5 + a0) (a3 + a4) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  revert r1 r2 r3 r4
  try simp only [tcG]
  prune_ifs'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the removal sum produces a large expression.
/-- The removal sum at the pattern `(0 1 4)(2 5 3)`: if it is odd, the displacements
satisfy the linear Alexander inequality. -/
theorem hexagon_l (hc : CycSorted c) :
    (∑ i : Fin 6, if (Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 2 5 * Equiv.swap 5 3 :
        Equiv.Perm (Fin 6)) ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 2 5 * Equiv.swap 5 3 :
        Equiv.Perm (Fin 6)) i) ≠ i then
        torusFiveCoeff n (cfgPerm c ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 2 5 * Equiv.swap
            5 3 : Equiv.Perm (Fin 6)) * Equiv.swap ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 2
            5 * Equiv.swap 5 3 : Equiv.Perm (Fin 6)) i) i)) else 0) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 2 5 *
          Equiv.swap 5 3 : Equiv.Perm (Fin 6)) i)) - (n + 2)) ≤ (n + 1) * 3 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 1 * Equiv.swap 1 4 * Equiv.swap 2 5 * Equiv.swap 5 3 :
            Equiv.Perm (Fin 6)) i)) = 3 * (2 * n + 3) := by
  hex_tac
  have r1 := m67 (n + 1) (a2 + a3) (a2 + a3 + a4) (a2 + a3 + a4 + a5)
    (a4) (a4 + a5) (a4 + a5 + a0 + a1) (a5) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r2 := m67 (n + 1) (a2 + a3) (a2 + a3 + a4) (a2 + a3 + a4 + a5 + a0)
    (a4) (a4 + a5 + a0) (a4 + a5 + a0 + a1) (a5 + a0) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r3 := m67 (n + 1) (a3) (a3 + a4) (a3 + a4 + a5)
    (a4) (a4 + a5) (a4 + a5 + a0 + a1 + a2) (a5) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r4 := m67 (n + 1) (a3) (a3 + a4) (a3 + a4 + a5 + a0)
    (a4) (a4 + a5 + a0) (a4 + a5 + a0 + a1 + a2) (a5 + a0) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  revert r1 r2 r3 r4
  try simp only [tcG]
  prune_ifs'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the removal sum produces a large expression.
/-- The removal sum at the pattern `(0 2 4)(1 5 3)`: if it is odd, the displacements
satisfy the linear Alexander inequality. -/
theorem hexagon_m (hc : CycSorted c) :
    (∑ i : Fin 6, if (Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 1 5 * Equiv.swap 5 3 :
        Equiv.Perm (Fin 6)) ((Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 1 5 * Equiv.swap 5 3 :
        Equiv.Perm (Fin 6)) i) ≠ i then
        torusFiveCoeff n (cfgPerm c ((Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 1 5 * Equiv.swap
            5 3 : Equiv.Perm (Fin 6)) * Equiv.swap ((Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 1
            5 * Equiv.swap 5 3 : Equiv.Perm (Fin 6)) i) i)) else 0) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 1 5 *
          Equiv.swap 5 3 : Equiv.Perm (Fin 6)) i)) - (n + 2)) ≤ (n + 1) * 3 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 1 5 * Equiv.swap 5 3 :
            Equiv.Perm (Fin 6)) i)) = 3 * (2 * n + 3) := by
  hex_tac
  have r1 := m67 (n + 1) (a0) (a0 + a1) (a0 + a1 + a2)
    (a1) (a1 + a2) (a1 + a2 + a3 + a4 + a5) (a2) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r2 := m67 (n + 1) (a1) (a1 + a2) (a1 + a2 + a3)
    (a2) (a2 + a3) (a2 + a3 + a4 + a5 + a0) (a3) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r3 := m67 (n + 1) (a2) (a2 + a3) (a2 + a3 + a4)
    (a3) (a3 + a4) (a3 + a4 + a5 + a0 + a1) (a4) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r4 := m67 (n + 1) (a3) (a3 + a4) (a3 + a4 + a5)
    (a4) (a4 + a5) (a4 + a5 + a0 + a1 + a2) (a5) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r5 := m67 (n + 1) (a4) (a4 + a5) (a4 + a5 + a0)
    (a5) (a5 + a0) (a5 + a0 + a1 + a2 + a3) (a0) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r6 := m67 (n + 1) (a5) (a5 + a0) (a5 + a0 + a1)
    (a0) (a0 + a1) (a0 + a1 + a2 + a3 + a4) (a1) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  intro hodd
  have hs := hex_alt_arith (n + 1) a0 a1 a2 a3 a4 a5 g1 g2 g3 g4 g5 g6 (by omega) (by omega)
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The evaluation of the removal sum produces a large expression.
/-- The removal sum at the pattern `(0 3 1)(2 5 4)`: if it is odd, the displacements
satisfy the linear Alexander inequality. -/
theorem hexagon_n (hc : CycSorted c) :
    (∑ i : Fin 6, if (Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 2 5 * Equiv.swap 5 4 :
        Equiv.Perm (Fin 6)) ((Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 2 5 * Equiv.swap 5 4 :
        Equiv.Perm (Fin 6)) i) ≠ i then
        torusFiveCoeff n (cfgPerm c ((Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 2 5 * Equiv.swap
            5 4 : Equiv.Perm (Fin 6)) * Equiv.swap ((Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 2
            5 * Equiv.swap 5 4 : Equiv.Perm (Fin 6)) i) i)) else 0) % 2 = 1 →
      2 * (n + 1) + ∑ i, (cycDist (c i) (c ((Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 2 5 *
          Equiv.swap 5 4 : Equiv.Perm (Fin 6)) i)) - (n + 2)) ≤ (n + 1) * 4 ∧
        ∑ i, cycDist (c i) (c ((Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 2 5 * Equiv.swap 5 4 :
            Equiv.Perm (Fin 6)) i)) = 4 * (2 * n + 3) := by
  hex_tac
  have r1 := m67 (n + 1) (a0 + a1) (a0 + a1 + a2) (a0 + a1 + a2 + a3)
    (a2) (a2 + a3) (a2 + a3 + a4 + a5) (a3) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r2 := m67 (n + 1) (a0 + a1) (a0 + a1 + a2) (a0 + a1 + a2 + a3 + a4)
    (a2) (a2 + a3 + a4) (a2 + a3 + a4 + a5) (a3 + a4) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r3 := m67 (n + 1) (a1) (a1 + a2) (a1 + a2 + a3)
    (a2) (a2 + a3) (a2 + a3 + a4 + a5 + a0) (a3) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have r4 := m67 (n + 1) (a1) (a1 + a2) (a1 + a2 + a3 + a4)
    (a2) (a2 + a3 + a4) (a2 + a3 + a4 + a5 + a0) (a3 + a4) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  revert r1 r2 r3 r4
  try simp only [tcG]
  prune_ifs'

end OnLeConjecture.KnotFloer.GridFull
