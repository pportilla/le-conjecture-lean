/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AnalyticPointBasis
import Mathlib.Tactic

/-!
# Weak transforms of a base ideal along an analytic point basis

Each generator has an actual analytic germ and an actual chart identity.
The specified generic member belongs to the generated ideal, and all
generators have at least its recorded order. These are the exact generic
member compatibility properties that identify the ideal order with the
point-basis entry.

Completeness records common zeros of weakly transformed generators,
including smooth points of the specified generic member. No existence of
principalization is asserted here.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- Analytic weak generators compatible with a specified generic member
at every recorded point. -/
structure WeakTransformIdealData {N : ℕ} (c : AnalyticPointBasis N) (ι : Type*) where
  generators : Fin N → ι → Germ 2
  generator_mem_pow : ∀ p i, generators p i ∈ maximalIdeal 2 ^ c.multiplicity p
  generic_member_mem : ∀ p, c.germ p ∈ Ideal.span (Set.range (generators p))
  transform_identity : ∀ p, p ≠ c.root → ∀ i,
    (pointBlowupChartGerm (c.chartCenter p)).pullbackRingHom
      ((c.sourceCoordinates p).forward.pullbackRingHom (generators (c.predecessor p) i)) =
        coordinate (1 : Fin 2) ^ c.multiplicity (c.predecessor p) * generators p i

namespace WeakTransformIdealData

variable {N : ℕ} {c : AnalyticPointBasis N} {ι : Type*}
variable (d : WeakTransformIdealData c ι)

/-- The weakly transformed base ideal at a recorded center. -/
@[expose] noncomputable def ideal (p : Fin N) : Ideal (Germ 2) :=
  Ideal.span (Set.range (d.generators p))

theorem ideal_le_pow (p : Fin N) : d.ideal p ≤ maximalIdeal 2 ^ c.multiplicity p := by
  rw [ideal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact d.generator_mem_pow p i

/-- The generic member proves that the ideal order is no greater than
the recorded entry, complementing the generator lower bounds. -/
theorem ideal_not_le_succ (p : Fin N) :
    ¬ d.ideal p ≤ maximalIdeal 2 ^ (c.multiplicity p + 1) := by
  intro hle
  exact c.germ_not_mem_succ p (hle (d.generic_member_mem p))

theorem multiplicity_le_of_generator_not_mem_pow
    (p : Fin N) (i : ι) (k : ℕ)
    (hnot : d.generators p i ∉ maximalIdeal 2 ^ (k + 1)) : c.multiplicity p ≤ k := by
  by_contra hn
  exact hnot ((Ideal.pow_le_pow_right (by omega)) (d.generator_mem_pow p i))

end WeakTransformIdealData

/-- Every nonunit weak ideal on a finite exceptional chart is recorded
as a child in that chart. The hypothesis concerns all generators, not
singularity of the generic member. -/
structure FiniteWeakBasepointCompleteness {N : ℕ} {c : AnalyticPointBasis N}
    {ι : Type*} (d : WeakTransformIdealData c ι) : Prop where
  realizes_common_zero : ∀ (p : Fin N) (ζ : ℂ) (G : ι → Germ 2),
    (∀ i, (pointBlowupChartGerm ζ).pullbackRingHom (d.generators p i) =
      coordinate (1 : Fin 2) ^ c.multiplicity p * G i) →
    (∀ i, G i ∈ maximalIdeal 2) →
    ∃ q, c.ParentRelation q p ∧ c.chartCenter q = ζ ∧
      ∀ i, (c.sourceCoordinates q).forward.pullbackRingHom (d.generators p i) = d.generators p i

namespace AnalyticPointBasis

/-- Root paths propagate a bound on immediate root children to every
nonroot point. The paths and multiplicity monotonicity are proved from
the analytic chart data. -/
theorem nonroot_multiplicity_le_of_root_children
    {N : ℕ} (c : AnalyticPointBasis N) (k : ℕ)
    (hchildren : ∀ q, c.ParentRelation q c.root → c.multiplicity q ≤ k)
    (q : Fin N) (hq : q ≠ c.root) : c.multiplicity q ≤ k := by
  generalize hn : c.generation q = n
  induction n using Nat.strong_induction_on generalizing q with
  | h n ih =>
      by_cases hp : c.predecessor q = c.root
      · exact hchildren q ⟨hq, hp⟩
      · have hlt : c.generation (c.predecessor q) < n := by
          rw [← hn]
          exact c.generation_decreases q hq
        exact (c.multiplicity_le_predecessor q hq).trans
          (ih _ hlt (c.predecessor q) hp rfl)

end AnalyticPointBasis

end OnLeConjecture.Analytic
