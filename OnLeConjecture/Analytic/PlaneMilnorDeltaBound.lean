/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MilnorDelta

/-!
# The delta invariant bounds the number of branches

For a reduced plane curve germ with `b` branches, `b ≤ δ + 1`. By Hironaka's
additivity formula, adding a branch `p` to a set `s` of branches increases the
codimension by `δ(p) + i(p, ∏ s)`, and the intersection multiplicity of two
curves through the origin is positive. Combined with Milnor's formula
`2δ = μ + b − 1`, the number `g = δ + 1 − b` satisfies `2g + b = μ + 1` and
`g + b = δ + 1`.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic OnLeConjecture.Analytic.Germ Module

theorem mem_maximalIdeal_of_irreducible {g : Germ 2} (hg : Irreducible g) :
    g ∈ maximalIdeal 2 := by
  rw [mem_maximalIdeal_iff]
  by_contra h
  exact hg.not_isUnit (isUnit_iff_valueRingHom_ne_zero.mpr h)

theorem intersectionMultiplicity_pos_of_mem {g h : Germ 2} (hg : g ∈ maximalIdeal 2)
    (hh : h ∈ maximalIdeal 2) (hfin : HasFiniteIntersection g h) :
    0 < intersectionMultiplicity g h hfin := by
  have hle : pairIdeal g h ≤ maximalIdeal 2 := by
    rw [pairIdeal_eq_span, Ideal.span_le]
    intro q hq
    rcases hq with rfl | hq
    · exact hg
    · rw [Set.mem_singleton_iff] at hq
      subst hq
      exact hh
  have hne : pairIdeal g h ≠ ⊤ :=
    fun htop => (maximalIdeal_isMaximal 2).ne_top (top_le_iff.mp (htop ▸ hle))
  have : Nontrivial (Germ 2 ⧸ pairIdeal g h) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : Module.Finite ℂ (Germ 2 ⧸ pairIdeal g h) := hfin
  exact Module.finrank_pos

/-- Each branch beyond the first increases the codimension by at least one. -/
theorem card_le_branchCodim_add_one (s : Finset (Associates (Germ 2)))
    (hs : ∀ b ∈ s, Irreducible (branchEquation b)) : s.card ≤ branchCodim s + 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    obtain ⟨hfin, heq⟩ := branchCodim_insert hp hs
    have ih' := ih fun b hb => hs b (Finset.mem_insert_of_mem hb)
    rw [Finset.card_insert_of_notMem hp, heq]
    rcases s.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
    · simp
    · have hpm := mem_maximalIdeal_of_irreducible (hs p (Finset.mem_insert_self p s))
      have hqm := mem_maximalIdeal_of_irreducible (hs q (Finset.mem_insert_of_mem hq))
      have hprod : branchProduct s ∈ maximalIdeal 2 := by
        unfold branchProduct
        rw [← Finset.mul_prod_erase s _ hq]
        exact Ideal.mul_mem_right _ _ hqm
      have := intersectionMultiplicity_pos_of_mem hpm hprod hfin
      omega

/-- A reduced plane germ has at most `δ + 1` branches. -/
theorem irreducibleBranchCount_le_deltaInvariant_add_one (f : Germ 2) :
    irreducibleBranchCount f ≤ deltaInvariant f + 1 := by
  rw [← card_branchSet, deltaInvariant_eq_branchCodim]
  exact card_le_branchCodim_add_one _ fun b hb => irreducible_branchEquation_of_mem hb

/-- **Genus from Milnor's formula.** For a reduced germ in the maximal ideal,
`g = δ + 1 − b` satisfies `2g + b = μ + 1` and `g + b = δ + 1`. -/
theorem exists_genus {f : Germ 2} (hf : f ∈ maximalIdeal 2) (hsq : Squarefree f) :
    ∃ g : ℕ, 2 * g + irreducibleBranchCount f =
        Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal f) + 1 ∧
      g + irreducibleBranchCount f = deltaInvariant f + 1 := by
  have hnu : ¬ IsUnit f := fun hu =>
    (isUnit_iff_valueRingHom_ne_zero.mp hu) (mem_maximalIdeal_iff.mp hf)
  have h2 := two_mul_deltaInvariant hsq
  have hb := irreducibleBranchCount_pos_of_nonzero_nonunit f hsq.ne_zero hnu
  have hle := irreducibleBranchCount_le_deltaInvariant_add_one f
  rw [milnorBranchDefect, if_neg hnu] at h2
  refine ⟨deltaInvariant f + 1 - irreducibleBranchCount f, ?_, ?_⟩ <;> omega

end OnLeConjecture.PlaneCurve
