/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectiveWeakIdealFiniteColength

/-!
# Trees of unmodified projective weak transforms

The generators at a child are exactly the analytically constructed weak
generators of its parent's projective chart. No subsequent coordinate
change or unit multiplication enters this definition. All common weak
zeros in both projective charts are recorded as children.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

universe u

variable {ι : Type u} [Fintype ι]

inductive RawProjectiveWeakBlowupTree : (ι → Germ 2) → Type u where
  | node (F : ι → Germ 2) (multiplicity : ℕ)
      (multiplicity_pos : 0 < multiplicity)
      (generator_mem : ∀ i, F i ∈ maximalIdeal 2 ^ multiplicity)
      (generator_exact : ∃ i, F i ∉ maximalIdeal 2 ^ (multiplicity + 1))
      (finite_colength : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F)))
      (points : Finset (Option ℂ)) (card_le : points.card ≤ multiplicity + 1)
      (complete : ∀ t, t ∈ points ↔
        t ∈ projectiveExceptionalBasepointSet multiplicity F generator_mem)
      (children : ∀ t : points, RawProjectiveWeakBlowupTree
        (projectiveWeakGenerators multiplicity F generator_mem t.val)) :
      RawProjectiveWeakBlowupTree F

end OnLeConjecture.Analytic
