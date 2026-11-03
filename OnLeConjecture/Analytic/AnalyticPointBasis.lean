/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBlowupChart
public import OnLeConjecture.Analytic.PullbackEquivalence
public import OnLeConjecture.Numerical.PointBasis
public import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Analytic germs at a finite rooted collection of blowup centers

The input records exact orders of analytic germs and actual strict-transform
identities. It does not assume order monotonicity. This module derives that
property from the analytic point blowup theorem, and then supplies the root
bound required by the numerical point basis certificate.

Existence of these data for a chosen generic member, completeness of the
collection of centers, and the proximity inequalities are not asserted here.
They are separate resolution and generic-member results. The immediate
predecessor used here must not be confused with the one or two points to
which a center is proximate.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedEquivGerm

/-- A source coordinate equivalence preserves the full ordinary order
filtration, in both directions. -/
theorem pullback_mem_maximalIdeal_pow_iff {n k : ℕ}
    (e : PointedEquivGerm n) (f : Germ n) :
    e.forward.pullbackRingHom f ∈ Germ.maximalIdeal n ^ k ↔
      f ∈ Germ.maximalIdeal n ^ k := by
  constructor
  · intro h
    have hi := PointedMapGerm.pullback_mem_maximalIdeal_pow e.inverse h
    change e.pullbackRingEquiv.symm (e.pullbackRingEquiv f) ∈
      Germ.maximalIdeal n ^ k at hi
    simpa only [RingEquiv.symm_apply_apply] using hi
  · exact PointedMapGerm.pullback_mem_maximalIdeal_pow e.forward

end PointedEquivGerm

/-- Finite rooted analytic strict-transform data. An edge first chooses
analytic coordinates at its predecessor, then uses the actual chart
`(x,y) ↦ (y(x+c),y)`. Source coordinate equivalences allow the choice of
chart to vary from edge to edge, including interchange of the coordinates.

The positivity and exact-order fields are properties of the supplied
generic member at these centers. Neither existence of a resolution nor
coverage of every center of a principalization is part of this definition. -/
structure AnalyticPointBasis (N : ℕ) where
  root : Fin N
  predecessor : Fin N → Fin N
  predecessor_root : predecessor root = root
  generation : Fin N → ℕ
  generation_decreases : ∀ p, p ≠ root →
    generation (predecessor p) < generation p
  germ : Fin N → Germ 2
  multiplicity : Fin N → ℕ
  multiplicity_pos : ∀ p, 0 < multiplicity p
  germ_mem : ∀ p, germ p ∈ Germ.maximalIdeal 2 ^ multiplicity p
  germ_not_mem_succ : ∀ p,
    germ p ∉ Germ.maximalIdeal 2 ^ (multiplicity p + 1)
  sourceCoordinates : Fin N → PointedEquivGerm 2
  chartCenter : Fin N → ℂ
  transform_identity : ∀ p, p ≠ root →
    (Germ.pointBlowupChartGerm (chartCenter p)).pullbackRingHom
        ((sourceCoordinates p).forward.pullbackRingHom (germ (predecessor p))) =
      Germ.coordinate (1 : Fin 2) ^ multiplicity (predecessor p) * germ p

namespace AnalyticPointBasis

variable {N : ℕ} (c : AnalyticPointBasis N)

/-- The oriented immediate-predecessor relation, from a child to its
predecessor. The root has no edge to itself. -/
@[expose] def ParentRelation (q p : Fin N) : Prop :=
  q ≠ c.root ∧ c.predecessor q = p

/-- `Ancestor p q` means that `p` is an ancestor of `q`, allowing equality. -/
@[expose] def Ancestor (p q : Fin N) : Prop :=
  Relation.ReflTransGen c.ParentRelation q p

/-- The strict-transform theorem proves monotonicity at each edge. -/
theorem multiplicity_le_predecessor (p : Fin N) (hp : p ≠ c.root) :
    c.multiplicity p ≤ c.multiplicity (c.predecessor p) := by
  have hf := ((c.sourceCoordinates p).pullback_mem_maximalIdeal_pow_iff
    (c.germ (c.predecessor p))).mpr (c.germ_mem (c.predecessor p))
  have hnext :
      (c.sourceCoordinates p).forward.pullbackRingHom (c.germ (c.predecessor p)) ∉
        Germ.maximalIdeal 2 ^ (c.multiplicity (c.predecessor p) + 1) := by
    intro h
    exact c.germ_not_mem_succ (c.predecessor p)
      (((c.sourceCoordinates p).pullback_mem_maximalIdeal_pow_iff _).mp h)
  have hbound := Germ.pointBlowupTransform_not_mem_succ
    (c.chartCenter p) (c.multiplicity (c.predecessor p))
    ((c.sourceCoordinates p).forward.pullbackRingHom (c.germ (c.predecessor p)))
    (c.germ p) hf hnext (c.transform_identity p hp)
  by_contra h
  exact hbound ((Ideal.pow_le_pow_right (by omega)) (c.germ_mem p))

theorem multiplicity_le_of_parent {q p : Fin N}
    (h : c.ParentRelation q p) : c.multiplicity q ≤ c.multiplicity p := by
  obtain ⟨hq, rfl⟩ := h
  exact c.multiplicity_le_predecessor q hq

/-- The generation function proves that the recorded centers form a
rooted collection, with no missing predecessor on any ancestral path. -/
theorem root_ancestor (q : Fin N) : c.Ancestor c.root q := by
  change Relation.ReflTransGen c.ParentRelation q c.root
  generalize hn : c.generation q = n
  induction n using Nat.strong_induction_on generalizing q with
  | h n ih =>
      by_cases hroot : q = c.root
      · subst q
        exact Relation.ReflTransGen.refl
      · have hlt : c.generation (c.predecessor q) < n := by
          rw [← hn]
          exact c.generation_decreases q hroot
        exact Relation.ReflTransGen.head ⟨hroot, rfl⟩
          (ih (c.generation (c.predecessor q)) hlt (c.predecessor q) rfl)

/-- Multiplicity is nonincreasing along every ancestral path, by repeated
application of the analytic strict-transform theorem. -/
theorem multiplicity_le_ancestor {p q : Fin N} (h : c.Ancestor p q) :
    c.multiplicity q ≤ c.multiplicity p := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | @head q r hparent _hpath ih =>
      exact (c.multiplicity_le_of_parent hparent).trans ih

theorem multiplicity_le_root (q : Fin N) :
    c.multiplicity q ≤ c.multiplicity c.root :=
  c.multiplicity_le_ancestor (c.root_ancestor q)

/-- The numerical point basis bound is a consequence, not a field, of
the supplied analytic resolution data. -/
@[expose] def toPointBasisCertificate : Numerical.PointBasisCertificate N where
  root := c.root
  multiplicity := c.multiplicity
  d := c.multiplicity c.root
  root_multiplicity := rfl
  multiplicity_le_root := c.multiplicity_le_root

/-- A local analytic upper order bound bounds the recorded entry. -/
theorem multiplicity_le_of_not_mem_pow {p : Fin N} {k : ℕ}
    (h : c.germ p ∉ Germ.maximalIdeal 2 ^ (k + 1)) :
    c.multiplicity p ≤ k := by
  by_contra hle
  exact h ((Ideal.pow_le_pow_right (by omega)) (c.germ_mem p))

/-- Once the analytic transform at a center has order at most `k`, every
recorded descendant also has order at most `k`. -/
theorem descendant_multiplicity_le_of_not_mem_pow {p q : Fin N} {k : ℕ}
    (hpath : c.Ancestor p q)
    (hlocal : c.germ p ∉ Germ.maximalIdeal 2 ^ (k + 1)) :
    c.multiplicity q ≤ k :=
  (c.multiplicity_le_ancestor hpath).trans (c.multiplicity_le_of_not_mem_pow hlocal)

theorem descendant_multiplicity_le_two {p q : Fin N}
    (hpath : c.Ancestor p q) (hp : c.multiplicity p ≤ 2) :
    c.multiplicity q ≤ 2 :=
  (c.multiplicity_le_ancestor hpath).trans hp

/-- The coverage needed in the quartic application: every center is either
on the specified order-four part, or descends from a specified center with
order at most two. The latter bounds can be supplied by the actual quartic
transform formulas. Coverage is an additional geometric obligation, not a
consequence of the existence of a finite list of centers. -/
theorem no_entry_three_of_frontier_cover
    (spine frontier : Finset (Fin N))
    (hcover : ∀ q, q ∈ spine ∨ ∃ p ∈ frontier, c.Ancestor p q)
    (hspine : ∀ p ∈ spine, c.multiplicity p = 4)
    (hfrontier : ∀ p ∈ frontier, c.germ p ∉ Germ.maximalIdeal 2 ^ 3) :
    ∀ q, c.multiplicity q ≠ 3 := by
  intro q
  rcases hcover q with hq | ⟨p, hp, hpath⟩
  · rw [hspine q hq]
    decide
  · have hle := c.descendant_multiplicity_le_of_not_mem_pow
      (k := 2) hpath (hfrontier p hp)
    omega

end AnalyticPointBasis

end OnLeConjecture.Analytic
