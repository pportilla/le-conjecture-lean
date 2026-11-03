/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorScissorCleanup
public import OnLeConjecture.Analytic.ResolutionSectionNativeFrontier

/-!
# The frontier after the scissor assembly

Combining `scissorCleanupStatement_of_endpointCleanup` (`GridExteriorScissorCleanup`) with
`leConjecture_of_rootFamily_frontier` (`ResolutionSectionNativeFrontier`) reduces Lê's conjecture
to two statements: `LevelRootFamilyStatement` (the root families of the levels, Section 3 of the
written proof of Statement E) and `ScissorEndpointCleanupStatement` (the cleanup of the scissor
endpoint by grid moves, Sections 8, 10 and 11).
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open OnLeConjecture.Analytic

/-- **Lê's conjecture from the root families of the levels and the cleanup of the scissor
endpoint.** -/
theorem leConjecture_of_rootFamily_endpointCleanup (hroot : LevelRootFamilyStatement)
    (h : ScissorEndpointCleanupStatement) : LeConjecture :=
  leConjecture_of_rootFamily_frontier hroot (scissorCleanupStatement_of_endpointCleanup h)

end OnLeConjecture.KnotFloer.GridFull
