/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Chain.Complex
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Grading.Complex

/-!
# Rectangle-counting grid complexes

This entry module imports the concrete TauCeti grid-complex construction at the source commit
recorded in `External/TauCeti/grid-port-provenance.json`. Its proof counts pairs of actual empty
toroidal rectangles. Disjoint pairs commute, pairs sharing one side are recut, and the remaining
annular terms vanish because every row and column contains an X marking. The resulting
differentials square to zero without an assumed chain-complex certificate.

The imported declarations retain their original `TauCeti` namespaces:

* `GridDiagram.fullyBlockedComplex` is over `ZMod 2` and counts rectangles avoiding both kinds
  of marking.
* `GridDiagram.unblockedComplex` is over a polynomial ring in the O variables and counts
  rectangles avoiding the X markings.
* `OddComponentGridDiagram.gradedFullyBlockedComplex a` is a `ChainComplex` indexed by the
  integer Maslov degree at a fixed integer Alexander degree `a`.

The total modules are also packaged as one-object homological complexes. They are not silently
assigned a Maslov grading. The graded construction applies when the diagram has an odd number
of components, which includes knot grids.

The X-avoiding differential is the associated graded grid differential. The full filtered
complex needed for Upsilon also counts empty rectangles crossing X markings. The separate
`GridFullComplex` module proves square-zero for that differential, including cancellation of
the diagonal annular terms.
The imported results do not establish embedded-knot correspondence, filtered grid-move
invariance, or a smooth cobordism genus bound.
-/
