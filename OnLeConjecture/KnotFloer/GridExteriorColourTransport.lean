/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationColourNatural
public import OnLeConjecture.KnotFloer.GridExteriorScissorSteps
public import OnLeConjecture.KnotFloer.GridCanonicalClass

/-!
# Colour-natural canonical maps along grid moves

This file states `ColourMovesToStatement`, the colour version of `MovesToCanonicalMapStatement`
(job J01). It is Lemma `movesToNativeMap` of the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 2): "After O markings are coloured constantly on each
component, the maps may be chosen to intertwine, on homology, the sums of the O derivatives of
every colour. A stabilization gives its new O the colour of its component." The statement is not
proved here.

A *colouring* of a grid diagram `G` of size `n` is a function `χ : Fin n → ℕ`, the colour of the
`O` marking of each column. Its colour classes are the column sets `colourClass χ v`. The colouring
is a *component colouring* (`ComponentColouring`) if it is constant on the components of `G`,
that is, on the cycles of `gridComponentPerm G` (see `GridExteriorScissorSteps`). It is *exact*
(`ExactColouring`) if two columns have the same colour exactly when they lie on the same
component.

`ColourCanonicalTransport G χ H χ'` asserts that, when both grids have size at least two, there is a
native chain map `laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2)` with
filtration shifts `(0, 0)` and canonical-class identity, whose underlying Laurent map `f`
intertwines the colour derivatives up to chain homotopy:
`f Φ_{χ⁻¹(v)} - Φ_{χ'⁻¹(v)} f` is null-homotopic for every colour `v`.

Ingredients already proved for the canonical move maps:

* column commutations: `commutationMap_oDerivative_homotopy` (`GridExteriorCommutationColour`), for
  the pentagon map `laurentCommutationMap` underlying `laurentMaslovCommutationHom`, for every
  colouring, with the colours exchanged by the column swap;
* cyclic row and column permutations: `laurentCyclicRowsEquiv_comp_oDerivative` and
  `laurentCyclicColumnsEquiv_comp_oDerivative` (`GridExteriorSymmetryColour`);
* the south-west corner `X` stabilization `G.stabilizeX s.castSucc (G.X s).castSucc s`:
  `isNullHomotopic_stabilization_inclusion_colour` for the canonical inclusion and every colouring,
  and `isNullHomotopic_stabilization_projection_colour` for the canonical projection when the new
  column `s.castSucc` and the column `s.succ` of the split `O` marking have the same colour
  (`GridStabilizationColourNatural`).

The remaining ingredients are the transposition and half-turn isomorphisms, the north-east corner
stabilization by half-turn conjugation, and the colour-tracked form of the corner reduction
`GridDiagram.IsStabilization.exists_commutationMovesTo` used in `GridStabilizationCornerMaps`.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n k : ℕ}

/-- The columns whose `O` marking has colour `v`. -/
def colourClass (χ : Fin n → ℕ) (v : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun c => χ c = v

/-- A colouring that is constant on every component of the grid. -/
def ComponentColouring (G : GridDiagram n) (χ : Fin n → ℕ) : Prop :=
  ∀ c, χ (gridComponentPerm G c) = χ c

/-- A colouring whose colour classes are exactly the components of the grid. -/
def ExactColouring (G : GridDiagram n) (χ : Fin n → ℕ) : Prop :=
  ∀ c d, χ c = χ d ↔ (gridComponentPerm G).SameCycle c d

/-- A native canonical map from `G` to `H` that intertwines the colour derivatives of the
colourings `χ` and `χ'` up to chain homotopy. -/
def ColourCanonicalTransport (G : GridDiagram n) (χ : Fin n → ℕ) (H : GridDiagram k)
    (χ' : Fin k → ℕ) : Prop :=
  ∀ (hn : 2 ≤ n) (hk : 2 ≤ k),
    ∃ (φ : laurentMaslovComplex G (ZMod 2) ⟶ laurentMaslovComplex H (ZMod 2))
      (f : LaurentChain (ZMod 2) n →ₗ[LaurentPolynomial (ZMod 2)] LaurentChain (ZMod 2) k),
      (∀ (m : ℤ) (x : (laurentMaslovComplex G (ZMod 2)).X m),
        (laurentMaslovChainEquiv H (ZMod 2) m (φ.f m x) : LaurentChain (ZMod 2) k) =
          f (laurentMaslovChainEquiv G (ZMod 2) m x)) ∧
      (laurentMaslovBifiltration G (ZMod 2)).Shifts (laurentMaslovBifiltration H (ZMod 2)) φ 0 0 ∧
      homologyMap φ 0 (gridCanonicalClass G hn) = gridCanonicalClass H hk ∧
      ∀ v : ℕ, IsNullHomotopic (laurentDifferential G (ZMod 2)) (laurentDifferential H (ZMod 2))
        (f ∘ₗ oDerivative (ZMod 2) G (colourClass χ v) -
          oDerivative (ZMod 2) H (colourClass χ' v) ∘ₗ f)

/-- **Colour-natural canonical maps along grid moves.** If `G` is related to `H` by grid moves,
then every component colouring of `H` comes from a component colouring of `G` with the same
colours, exact exactly when it is exact, and a colour-natural native canonical map from `G` to
`H`. -/
def ColourMovesToStatement : Prop :=
  ∀ {n k : ℕ} (G : GridDiagram n) (H : GridDiagram k), G.MovesTo H →
    ∀ χ' : Fin k → ℕ, ComponentColouring H χ' →
      ∃ χ : Fin n → ℕ, ComponentColouring G χ ∧
        (ExactColouring G χ ↔ ExactColouring H χ') ∧
        (∀ v, (∃ c, χ c = v) ↔ ∃ c, χ' c = v) ∧
        ColourCanonicalTransport G χ H χ'

end OnLeConjecture.KnotFloer.GridFull
