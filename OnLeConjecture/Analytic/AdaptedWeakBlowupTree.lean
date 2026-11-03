/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AdaptedWeakBlowupSuccessor

/-!
# Finite trees of adapted analytic weak blowups

Each vertex records a regular finite-colength ideal. Its children are
exactly the common zeros of its weak generators on the exceptional line.
There is no missing complementary-chart child because a distinguished
generator is regular in the first coordinate. Every edge records the
analytic weak transform and a subsequent source equivalence.

Well-founded descent and finite exceptional-point enumeration construct
such a finite tree. This does not yet flatten the tree into the coordinate
conventions of `AnalyticPointBasis` or transport its completeness records.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

universe u

variable {ι : Type u} [Fintype ι]

/-- An adapted analytic weak-blowup tree, with all nonunit weak ideals
recorded as children and with their subsequent coordinate changes. -/
inductive AdaptedWeakBlowupTree : AdaptedWeakIdealState ι → Type u where
  | node (s : AdaptedWeakIdealState ι) (points : Finset ℂ)
      (card_le : points.card ≤ s.multiplicity)
      (complete : ∀ ζ, ζ ∈ points ↔ ∀ i, s.weakGenerators ζ i ∈ maximalIdeal 2)
      (next : points → AdaptedWeakIdealState ι)
      (successor : ∀ ζ, AdaptedWeakIdealState.SuccessorAt ζ.val (next ζ) s)
      (children : ∀ ζ, AdaptedWeakBlowupTree (next ζ)) : AdaptedWeakBlowupTree s

namespace AdaptedWeakBlowupTree

/-- Finite branching and the proved decreasing rank yield a tree for
every adapted state. No termination certificate is part of the input. -/
theorem exists_tree (s : AdaptedWeakIdealState ι) : Nonempty (AdaptedWeakBlowupTree s) := by
  classical
  induction s using AdaptedWeakIdealState.step_wellFounded.induction with
  | h s ih =>
      obtain ⟨points, hcard, hpoints⟩ := s.exists_exceptional_finset
      have hsuccessor : ∀ ζ : points, ∃ child : AdaptedWeakIdealState ι,
          AdaptedWeakIdealState.SuccessorAt ζ.val child s := by
        intro ζ
        exact s.exists_successorAt_of_common_zero ζ.val ((hpoints ζ.val).mp ζ.property)
      choose next hnext using hsuccessor
      have htrees : ∀ ζ : points, Nonempty (AdaptedWeakBlowupTree (next ζ)) := by
        intro ζ
        exact ih (next ζ) (AdaptedWeakIdealState.step_of_successorAt (hnext ζ))
      exact ⟨.node s points hcard hpoints next hnext (fun ζ => Classical.choice (htrees ζ))⟩

/-- A natural-number count of all vertices, including the root. -/
@[expose] noncomputable def nodeCount :
    {s : AdaptedWeakIdealState ι} → AdaptedWeakBlowupTree s → ℕ
  | _, .node _ points _ _ _ _ children => 1 + ∑ ζ : points, nodeCount (children ζ)

theorem nodeCount_pos {s : AdaptedWeakIdealState ι} (T : AdaptedWeakBlowupTree s) :
    0 < T.nodeCount := by
  cases T
  simp only [nodeCount]
  omega

/-- A proper finite-colength ideal admits regular source coordinates and
a finite adapted analytic weak-blowup tree. No point-basis completeness
under a different chart convention is claimed. -/
theorem exists_of_finite_colength
    (F : ι → Germ 2) (hproper : ∀ i, F i ∈ maximalIdeal 2)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F))) :
    ∃ (e : PointedEquivGerm 2) (s : AdaptedWeakIdealState ι),
      (∀ i, s.generators i = e.forward.pullbackRingHom (F i)) ∧
      Nonempty (AdaptedWeakBlowupTree s) := by
  obtain ⟨e, s, hgenerators⟩ :=
    AdaptedWeakIdealState.exists_of_finite_colength F hproper hfinite
  exact ⟨e, s, hgenerators, exists_tree s⟩

end AdaptedWeakBlowupTree

end OnLeConjecture.Analytic
