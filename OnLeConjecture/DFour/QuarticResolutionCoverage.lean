/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBlowupCenters
public import OnLeConjecture.DFour.QuarticNewtonTransforms
import Mathlib.Tactic

/-!
# Coverage of a rooted analytic point basis by a spine and its frontier

Coverage is proved from root reachability and uniqueness of children before
the terminal spine point. The uniqueness is in turn proved using actual
ordinary initial forms and separation of exceptional chart centers.

The coordinate compatibility hypotheses identify each edge with either
the common finite chart or its complementary coordinate chart. The latter
is excluded analytically for a pure first-coordinate initial form. These
are explicit geometric identification requirements on the supplied data,
not existence assertions about principalizations.
-/

public section

namespace OnLeConjecture.Analytic.AnalyticPointBasis

open OnLeConjecture.Analytic.Germ

/-- In common coordinates with pure tangent `κ*x^m`, a positive-order
child cannot lie in the complementary chart, and its finite chart center
is zero. Both alternatives are actual identities of the parent germs. -/
theorem child_finite_and_center_zero_of_common_pure_initial
    {N : ℕ} (c : AnalyticPointBasis N) (p : Fin N) (e : PointedEquivGerm 2)
    (κ : ℂ) (hκ : κ ≠ 0)
    (htail : e.forward.pullbackRingHom (c.germ p) -
      constRingHom 2 κ * coordinate (0 : Fin 2) ^ c.multiplicity p ∈
        maximalIdeal 2 ^ (c.multiplicity p + 1))
    (hcoordinates : ∀ q, c.ParentRelation q p →
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ p) =
          e.forward.pullbackRingHom (c.germ p) ∨
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ p) =
        (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom
          (e.forward.pullbackRingHom (c.germ p)))
    (q : Fin N) (hq : c.ParentRelation q p) :
    (c.sourceCoordinates q).forward.pullbackRingHom (c.germ p) =
      e.forward.pullbackRingHom (c.germ p) ∧ c.chartCenter q = 0 := by
  have hf := (e.pullback_mem_maximalIdeal_pow_iff (c.germ p)).mpr (c.germ_mem p)
  have hn := (e.pullback_mem_maximalIdeal_pow_iff (k := c.multiplicity p + 1)
    (c.germ p)).not.mpr (c.germ_not_mem_succ p)
  have hg : c.germ q ∈ maximalIdeal 2 := by
    simpa only [pow_one] using
      (Ideal.pow_le_pow_right (c.multiplicity_pos q)) (c.germ_mem q)
  have htransform := c.transform_identity q hq.1
  rw [hq.2] at htransform
  rcases hcoordinates q hq with hfinite | hinfinity
  · rw [hfinite] at htransform
    exact ⟨hfinite, center_eq_zero_of_initial_first_power (c.chartCenter q) κ hκ
      (c.multiplicity p) (c.multiplicity_pos p) _ _ hf hn htail htransform hg⟩
  · rw [hinfinity] at htransform
    have hswapMem :=
      ((coordinateSwapPointedEquiv (1 : Fin 2)).pullback_mem_maximalIdeal_pow_iff _).mpr hf
    have hswapNot :=
      ((coordinateSwapPointedEquiv (1 : Fin 2)).pullback_mem_maximalIdeal_pow_iff
        (k := c.multiplicity p + 1) _).not.mpr hn
    exact (no_vanishing_transform_of_initial_second_power (c.chartCenter q) κ hκ
      (c.multiplicity p) _ _ hswapMem hswapNot
      (coordinateSwap_initial_first_power κ (c.multiplicity p) _ htail)
      htransform hg).elim

/-- Distinct geometric children have distinct centers in their common
finite exceptional chart. Together with the tangent calculation, this
proves uniqueness of the child without assuming it. -/
theorem children_unique_of_common_pure_initial
    {N : ℕ} (c : AnalyticPointBasis N) (p : Fin N) (e : PointedEquivGerm 2)
    (κ : ℂ) (hκ : κ ≠ 0)
    (htail : e.forward.pullbackRingHom (c.germ p) -
      constRingHom 2 κ * coordinate (0 : Fin 2) ^ c.multiplicity p ∈
        maximalIdeal 2 ^ (c.multiplicity p + 1))
    (hcoordinates : ∀ q, c.ParentRelation q p →
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ p) =
          e.forward.pullbackRingHom (c.germ p) ∨
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ p) =
        (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom
          (e.forward.pullbackRingHom (c.germ p)))
    (hseparated : ∀ q t, c.ParentRelation q p → c.ParentRelation t p →
      c.chartCenter q = c.chartCenter t → q = t)
    {q t : Fin N} (hq : c.ParentRelation q p) (ht : c.ParentRelation t p) : q = t := by
  have hqzero := (c.child_finite_and_center_zero_of_common_pure_initial p e κ hκ
    htail hcoordinates q hq).2
  have htzero := (c.child_finite_and_center_zero_of_common_pure_initial p e κ hκ
    htail hcoordinates t ht).2
  exact hseparated q t hq ht (hqzero.trans htzero.symm)

/-- Root paths prove coverage by a finite spine and the descendants of
its terminal children. No coverage hypothesis is assumed. -/
theorem spine_frontier_coverage
    {N : ℕ} (c : AnalyticPointBasis N) (L : ℕ) (spine : ℕ → Fin N)
    (hroot : spine 0 = c.root)
    (hchildren : ∀ j < L, ∀ q, c.ParentRelation q (spine j) → q = spine (j + 1)) :
    ∀ q, (∃ j ≤ L, q = spine j) ∨
      ∃ b, c.ParentRelation b (spine L) ∧ c.Ancestor b q := by
  intro q
  have hpath := c.root_ancestor q
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl ⟨0, Nat.zero_le L, hroot.symm⟩
  | @head q p hparent _hpath ih =>
      rcases ih with ⟨j, hj, rfl⟩ | ⟨b, hb, hbp⟩
      · by_cases hjlt : j < L
        · exact Or.inl ⟨j + 1, by omega, hchildren j hjlt q hparent⟩
        · have hjL : j = L := by omega
          subst j
          exact Or.inr ⟨q, hparent, Relation.ReflTransGen.refl⟩
      · exact Or.inr ⟨b, hb, Relation.ReflTransGen.head hparent hbp⟩

/-- Actual pure initial forms at the nonterminal spine points, together
with common-chart compatibility and separated centers, imply coverage of
every recorded point by the spine and its terminal frontier descendants. -/
theorem spine_frontier_coverage_of_common_pure_initial
    {N : ℕ} (c : AnalyticPointBasis N) (L : ℕ) (spine : ℕ → Fin N)
    (hroot : spine 0 = c.root)
    (hchain : ∀ j < L, c.ParentRelation (spine (j + 1)) (spine j))
    (e : ℕ → PointedEquivGerm 2) (κ : ℕ → ℂ)
    (hκ : ∀ j < L, κ j ≠ 0)
    (htail : ∀ j < L, (e j).forward.pullbackRingHom (c.germ (spine j)) -
      constRingHom 2 (κ j) * coordinate (0 : Fin 2) ^ c.multiplicity (spine j) ∈
        maximalIdeal 2 ^ (c.multiplicity (spine j) + 1))
    (hcoordinates : ∀ j < L, ∀ q, c.ParentRelation q (spine j) →
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (spine j)) =
          (e j).forward.pullbackRingHom (c.germ (spine j)) ∨
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (spine j)) =
        (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom
          ((e j).forward.pullbackRingHom (c.germ (spine j))))
    (hseparated : ∀ j < L, ∀ q t,
      c.ParentRelation q (spine j) → c.ParentRelation t (spine j) →
        c.chartCenter q = c.chartCenter t → q = t) :
    ∀ q, (∃ j ≤ L, q = spine j) ∨
      ∃ b, c.ParentRelation b (spine L) ∧ c.Ancestor b q := by
  apply c.spine_frontier_coverage L spine hroot
  intro j hj q hq
  exact c.children_unique_of_common_pure_initial (spine j) (e j) (κ j) (hκ j hj)
    (htail j hj) (hcoordinates j hj) (hseparated j hj) hq (hchain j hj)

end OnLeConjecture.Analytic.AnalyticPointBasis

namespace OnLeConjecture.DFour

open Analytic Analytic.Germ

private theorem not_mem_cube_of_unit_multiple
    (g T u : Germ 2) (hu : IsUnit u) (hg : g = T * u)
    (hT : T ∉ maximalIdeal 2 ^ 3) : g ∉ maximalIdeal 2 ^ 3 := by
  apply unit_multiple_transform_not_mem_cube (PointedMapGerm.identity 2) 0 T u T g hu
  · simp [PointedMapGerm.pullbackRingHom_identity]
  · simpa only [PointedMapGerm.pullbackRingHom_identity, RingHom.id_apply,
      pow_zero, one_mul] using hg.symm
  · exact hT

/-- Actual quartic terminal expressions, possibly multiplied by analytic
units, exclude entry three throughout the rooted tree. The child condition
is supplied by `children_unique_of_common_pure_initial`; coverage itself
is derived from the root paths rather than assumed. -/
theorem no_entry_three_of_spine_with_quartic_terminal_children
    {N : ℕ} (c : AnalyticPointBasis N) (L : ℕ) (spine : ℕ → Fin N)
    (hroot : spine 0 = c.root)
    (hchildren : ∀ j < L, ∀ q, c.ParentRelation q (spine j) → q = spine (j + 1))
    (hspine : ∀ j ≤ L, c.multiplicity (spine j) = 4)
    (hterminal : ∀ b, c.ParentRelation b (spine L) → ∃ u : Germ 2, IsUnit u ∧
      ((∃ (η ζ : ℂ) (a₂ a₁ a₀ : Germ 2), η ≠ 0 ∧ ζ ^ 2 + η = 0 ∧
        c.germ b = integralQuarticTransform η ζ a₂ a₁ a₀ * u) ∨
       (∃ (η : ℂ) (a₂ a₁ a₀ : Germ 2), η ≠ 0 ∧
        c.germ b = halfIntegralQuarticTransform η a₂ a₁ a₀ * u))) :
    ∀ q, c.multiplicity q ≠ 3 := by
  have hterminalBound : ∀ b, c.ParentRelation b (spine L) →
      c.germ b ∉ maximalIdeal 2 ^ 3 := by
    intro b hb
    obtain ⟨u, hu, h | h⟩ := hterminal b hb
    · obtain ⟨η, ζ, a₂, a₁, a₀, hη, hroot, hidentity⟩ := h
      exact not_mem_cube_of_unit_multiple _ _ u hu hidentity
        (integralQuarticTransform_at_root η ζ hη hroot a₂ a₁ a₀).2
    · obtain ⟨η, a₂, a₁, a₀, hη, hidentity⟩ := h
      exact not_mem_cube_of_unit_multiple _ _ u hu hidentity
        (halfIntegralQuarticTransform_not_mem_cube η hη a₂ a₁ a₀)
  intro q
  rcases c.spine_frontier_coverage L spine hroot hchildren q with
    ⟨j, hj, rfl⟩ | ⟨b, hb, hpath⟩
  · rw [hspine j hj]
    decide
  · have hle := c.descendant_multiplicity_le_of_not_mem_pow
      (k := 2) hpath (hterminalBound b hb)
    omega

end OnLeConjecture.DFour
