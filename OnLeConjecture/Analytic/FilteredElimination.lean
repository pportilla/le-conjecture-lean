/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CompletionClosure
import Mathlib.Tactic.Push

/-!
# Finite termination of filtered elimination

The quotient by a submodule of a finite module over a Noetherian local ring
is separated. Consequently, an element outside the submodule has a finite
bound on its possible approximation order. Choosing the first failed order
produces a remainder whose initial class cannot be removed.

This is the module argument in `lem:filtered-escape` of
`cases_234_codex.tex`. The cofinality hypothesis below is with the base ring's
maximal ideal. Applications to analytic weighted filtrations must establish
that cofinality from finiteness of the analytic plane map.
-/

public section

namespace OnLeConjecture.Analytic

variable {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Approximation to every maximal-ideal order implies membership in the
submodule. No assertion about convergence of the individual approximants is
needed. -/
theorem mem_submodule_of_adic_approximations
    (S : Submodule R M) (x : M)
    (happrox : ∀ n : ℕ, ∃ a ∈ S,
      x - a ∈ (IsLocalRing.maximalIdeal R) ^ n • (⊤ : Submodule R M)) :
    x ∈ S := by
  have hquotient : S.mkQ x = 0 := by
    apply IsHausdorff.haus' (I := IsLocalRing.maximalIdeal R)
    intro n
    obtain ⟨a, ha, hxa⟩ := happrox n
    have hmap := Submodule.smul_top_le_comap_smul_top
      (IsLocalRing.maximalIdeal R ^ n) S.mkQ hxa
    have haZero : S.mkQ a = 0 := by simpa using ha
    simpa [map_sub, haZero, SModEq.zero] using hmap
  simpa using hquotient

/-- An element outside the submodule fails to admit an approximation at
some finite filtration order. -/
theorem exists_order_without_submodule_approximation
    (S : Submodule R M) (F : ℕ → Submodule R M)
    (hcofinal : ∀ n : ℕ, ∃ q : ℕ,
      F q ≤ (IsLocalRing.maximalIdeal R) ^ n • (⊤ : Submodule R M))
    (x : M) (hx : x ∉ S) :
    ∃ q : ℕ, ¬ ∃ a ∈ S, x - a ∈ F q := by
  classical
  by_contra h
  push Not at h
  apply hx
  apply mem_submodule_of_adic_approximations S x
  intro n
  obtain ⟨q, hq⟩ := hcofinal n
  obtain ⟨a, ha, hxa⟩ := h q
  exact ⟨a, ha, hq hxa⟩

/-- Filtered elimination reaches a remainder whose initial class cannot
be removed by an element of the submodule, unless the original element
already belongs to that submodule. -/
theorem filtered_elimination
    (S : Submodule R M) (F : ℕ → Submodule R M)
    (hzero : F 0 = ⊤)
    (hcofinal : ∀ n : ℕ, ∃ q : ℕ,
      F q ≤ (IsLocalRing.maximalIdeal R) ^ n • (⊤ : Submodule R M))
    (x : M) :
    x ∈ S ∨ ∃ n : ℕ, ∃ a ∈ S,
      x - a ∈ F n ∧ ∀ b ∈ S, x - a - b ∉ F (n + 1) := by
  classical
  by_cases hx : x ∈ S
  · exact Or.inl hx
  · right
    have hex := exists_order_without_submodule_approximation S F hcofinal x hx
    let q := Nat.find hex
    have hfail : ¬ ∃ a ∈ S, x - a ∈ F q := Nat.find_spec hex
    have hq : q ≠ 0 := by
      intro hqZero
      apply hfail
      refine ⟨0, S.zero_mem, ?_⟩
      rw [hqZero, hzero]
      exact Submodule.mem_top
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hq
    have hfailNext : ¬ ∃ a ∈ S, x - a ∈ F (n + 1) := by
      simpa only [hn, Nat.succ_eq_add_one] using hfail
    have hprevious : ∃ a ∈ S, x - a ∈ F n := by
      by_contra hnone
      have hnlt : n < Nat.find hex := by change n < q; omega
      have hmin := Nat.find_min hex hnlt
      exact hmin hnone
    obtain ⟨a, ha, hxa⟩ := hprevious
    refine ⟨n, a, ha, hxa, ?_⟩
    intro b hb himprove
    apply hfailNext
    exact ⟨a + b, S.add_mem ha hb, by simpa [sub_sub] using himprove⟩

end OnLeConjecture.Analytic
