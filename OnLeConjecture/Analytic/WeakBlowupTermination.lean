/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeakBlowupFiniteColength
public import OnLeConjecture.Analytic.ExactLinearCoordinates
public import Mathlib.Order.WellFounded

/-!
# Termination of adapted analytic weak blowups

Each state consists of a proper finite-colength analytic ideal, its exact
order, and a distinguished generator regular of that order in the first
coordinate. The second component of its rank is defined, not supplied:
it is the least exponent of the second coordinate belonging to the ideal.

A step is an actual finite-chart weak transform followed by an analytic
source equivalence. When the order is unchanged that equivalence must
preserve the second coordinate. The analytic transform identities imply
lexicographic decrease of the two integers and hence well-foundedness.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

structure AdaptedWeakIdealState (ι : Type*) [Fintype ι] where
  generators : ι → Germ 2
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  generator_mem : ∀ i, generators i ∈ maximalIdeal 2 ^ multiplicity
  distinguished : ι
  distinguished_exact : generators distinguished ∉ maximalIdeal 2 ^ (multiplicity + 1)
  distinguished_regular : IsRegularInFirstCoordinateOfOrder
    (generators distinguished) multiplicity
  finite_colength : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range generators))

namespace AdaptedWeakIdealState

variable {ι : Type*} [Fintype ι]

@[expose] noncomputable def ideal (s : AdaptedWeakIdealState ι) : Ideal (Germ 2) :=
  Ideal.span (Set.range s.generators)

theorem ideal_le_order (s : AdaptedWeakIdealState ι) :
    s.ideal ≤ maximalIdeal 2 ^ s.multiplicity := by
  rw [ideal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact s.generator_mem i

theorem exists_exceptional_power (s : AdaptedWeakIdealState ι) :
    ∃ N : ℕ, coordinate (1 : Fin 2) ^ N ∈ s.ideal := by
  obtain ⟨N, hN⟩ :=
    (quotient_moduleFinite_iff_exists_maximalIdeal_pow_le s.ideal).mp s.finite_colength
  exact ⟨N, hN (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal (1 : Fin 2)) N)⟩

/-- The least exceptional-coordinate power in the analytic ideal. -/
@[expose] noncomputable def exceptionalOrder (s : AdaptedWeakIdealState ι) : ℕ := by
  classical
  exact Nat.find s.exists_exceptional_power

theorem exceptional_power_mem (s : AdaptedWeakIdealState ι) :
    coordinate (1 : Fin 2) ^ s.exceptionalOrder ∈ s.ideal := by
  classical
  exact Nat.find_spec s.exists_exceptional_power

theorem exceptionalOrder_le (s : AdaptedWeakIdealState ι) (N : ℕ)
    (hN : coordinate (1 : Fin 2) ^ N ∈ s.ideal) : s.exceptionalOrder ≤ N := by
  classical
  exact Nat.find_min' s.exists_exceptional_power hN

theorem multiplicity_le_exceptionalOrder (s : AdaptedWeakIdealState ι) :
    s.multiplicity ≤ s.exceptionalOrder := by
  have hmem := (hyperplaneInclusionGerm 1).pullback_mem_maximalIdeal_pow
    (s.ideal_le_order s.exceptional_power_mem)
  change hyperplaneRestriction 1 (coordinate (1 : Fin 2) ^ s.exceptionalOrder) ∈
    maximalIdeal 1 ^ s.multiplicity at hmem
  rw [map_pow, show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    hyperplaneRestriction_coordinate_succ, mem_maximalIdeal_one_pow_iff,
    vanishingOrder_coordinate_pow] at hmem
  exact_mod_cast hmem

@[expose] noncomputable def rank (s : AdaptedWeakIdealState ι) : ℕ × ℕ :=
  (s.multiplicity, s.exceptionalOrder)

/-- The source equivalence may change the parameter after an order drop.
At equal order it preserves the parameter. No inequality of ranks is assumed. -/
@[expose] def Step (child parent : AdaptedWeakIdealState ι) : Prop :=
  ∃ ζ : ℂ, ∃ e : PointedEquivGerm 2, ∃ G : ι → Germ 2,
    (∀ i, (pointBlowupChartGerm ζ).pullbackRingHom (parent.generators i) =
      coordinate (1 : Fin 2) ^ parent.multiplicity * G i) ∧
    (∀ i, child.generators i = e.forward.pullbackRingHom (G i)) ∧
    (child.multiplicity = parent.multiplicity →
      e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1)

theorem multiplicity_le_of_transformed_generators
    {child parent : AdaptedWeakIdealState ι}
    (ζ : ℂ) (e : PointedEquivGerm 2) (G : ι → Germ 2)
    (htransform : ∀ i, (pointBlowupChartGerm ζ).pullbackRingHom (parent.generators i) =
      coordinate (1 : Fin 2) ^ parent.multiplicity * G i)
    (hchild : ∀ i, child.generators i = e.forward.pullbackRingHom (G i)) :
    child.multiplicity ≤ parent.multiplicity := by
  have hnext := pointBlowupTransform_not_mem_succ ζ parent.multiplicity
    (parent.generators parent.distinguished) (G parent.distinguished)
    (parent.generator_mem _) parent.distinguished_exact (htransform _)
  by_contra hn
  have hchildmem := child.generator_mem parent.distinguished
  rw [hchild] at hchildmem
  have hGmem := (e.pullback_mem_maximalIdeal_pow_iff _).mp hchildmem
  exact hnext ((Ideal.pow_le_pow_right (by omega)) hGmem)

theorem multiplicity_le_of_step {child parent : AdaptedWeakIdealState ι}
    (hstep : Step child parent) : child.multiplicity ≤ parent.multiplicity := by
  obtain ⟨ζ, e, G, htransform, hchild, _⟩ := hstep
  exact multiplicity_le_of_transformed_generators ζ e G htransform hchild

/-- Exact cancellation of the parent's minimal exceptional power bounds
the child's minimal exceptional power when the ideal order is unchanged. -/
theorem exceptionalOrder_le_sub_of_step_of_equal_order
    {child parent : AdaptedWeakIdealState ι} (hstep : Step child parent)
    (horder : child.multiplicity = parent.multiplicity) :
    child.exceptionalOrder ≤ parent.exceptionalOrder - parent.multiplicity := by
  obtain ⟨ζ, e, G, htransform, hchild, hpreserve⟩ := hstep
  have hpower : coordinate (1 : Fin 2) ^
      (parent.multiplicity + (parent.exceptionalOrder - parent.multiplicity)) ∈ parent.ideal := by
    rw [Nat.add_sub_of_le parent.multiplicity_le_exceptionalOrder]
    exact parent.exceptional_power_mem
  have hweak := exceptional_power_mem_weakIdeal ζ parent.multiplicity
    (parent.exceptionalOrder - parent.multiplicity) parent.generators G hpower htransform
  have hmap : Ideal.map e.forward.pullbackRingHom (Ideal.span (Set.range G)) = child.ideal := by
    rw [ideal, Ideal.map_span, ← Set.range_comp]
    have hfun : e.forward.pullbackRingHom ∘ G = child.generators :=
      funext (fun i => (hchild i).symm)
    rw [hfun]
  have hchildPower := Ideal.mem_map_of_mem e.forward.pullbackRingHom hweak
  rw [map_pow, hpreserve horder, hmap] at hchildPower
  exact child.exceptionalOrder_le _ hchildPower

theorem rank_decreases_of_step {child parent : AdaptedWeakIdealState ι}
    (hstep : Step child parent) :
    Prod.Lex (· < ·) (· < ·) child.rank parent.rank := by
  have hle := multiplicity_le_of_step hstep
  by_cases horder : child.multiplicity = parent.multiplicity
  · have hexp := exceptionalOrder_le_sub_of_step_of_equal_order hstep horder
    have hpos := parent.multiplicity_pos
    have hbound := parent.multiplicity_le_exceptionalOrder
    have hlt : child.exceptionalOrder < parent.exceptionalOrder := by omega
    change Prod.Lex (· < ·) (· < ·)
      (child.multiplicity, child.exceptionalOrder) (parent.multiplicity, parent.exceptionalOrder)
    rw [horder]
    exact Prod.Lex.right _ hlt
  · exact Prod.Lex.left _ _ (lt_of_le_of_ne hle horder)

/-- Well-foundedness is a consequence of the analytic factor identities
and the least-power definition, rather than a principalization assumption. -/
theorem step_wellFounded : WellFounded (Step (ι := ι)) := by
  apply (InvImage.wf rank (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)).mono
  intro child parent hstep
  exact rank_decreases_of_step hstep

/-- There is no infinite sequence of these actual adapted analytic
weak blowups. -/
theorem no_infinite_step_sequence (s : ℕ → AdaptedWeakIdealState ι) :
    ¬ ∀ n, Step (s (n + 1)) (s n) := by
  intro hstep
  have hnot : ¬ Acc Step (s 0) :=
    not_acc_iff_exists_descending_chain.mpr ⟨s, rfl, hstep⟩
  exact hnot (step_wellFounded.apply (s 0))

end AdaptedWeakIdealState

end OnLeConjecture.Analytic
