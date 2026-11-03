/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteColength
public import OnLeConjecture.Analytic.PullbackEquivalence
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Coordinate colength of a finite analytic map germ

The coordinate colength is the complex dimension of the quotient by the
coordinate ideal. This file proves positivity and invariance under analytic
coordinate changes.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- An equivalence of analytic local algebras preserves the dimension of
quotients by corresponding ideals. -/
theorem quotient_finrank_eq_of_map_eq {n : ℕ}
    (I J : Ideal (Germ n)) (e : Germ n ≃ₐ[ℂ] Germ n)
    (hIJ : Ideal.map e.toRingEquiv.toRingHom I = J)
    [Module.Finite ℂ (Germ n ⧸ I)]
    [Module.Finite ℂ (Germ n ⧸ J)] :
    Module.finrank ℂ (Germ n ⧸ I) =
      Module.finrank ℂ (Germ n ⧸ J) := by
  let quotientEquiv : (Germ n ⧸ I) ≃ₐ[ℂ] Germ n ⧸ J :=
    Ideal.quotientEquivAlg I J e hIJ.symm
  exact quotientEquiv.toLinearEquiv.finrank_eq

end Germ

namespace PointedMapGerm

/-- The coordinate colength of a finite pointed analytic map germ is the complex
dimension of its coordinate quotient. -/
@[expose] noncomputable def coordinateColength {n m : ℕ}
    (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) : ℕ := by
  let _ : Module.Finite ℂ (Germ n ⧸ f.1.coordinateIdeal) :=
    f.coordinateQuotient_moduleFinite hfinite
  exact Module.finrank ℂ (Germ n ⧸ f.1.coordinateIdeal)

/-- The coordinate colength of a finite pointed analytic map germ is positive. -/
theorem coordinateColength_pos {n m : ℕ} (f : PointedMapGerm n m)
    (hfinite : f.IsFiniteAtOrigin) : 0 < f.coordinateColength hfinite := by
  let _ : Module.Finite ℂ (Germ n ⧸ f.1.coordinateIdeal) :=
    f.coordinateQuotient_moduleFinite hfinite
  have hproper : f.1.coordinateIdeal ≠ ⊤ := by
    intro htop
    have hmax : Germ.maximalIdeal n = ⊤ := by
      apply le_antisymm le_top
      rw [← htop]
      exact f.coordinateIdeal_le_maximalIdeal
    exact (Germ.maximalIdeal_isMaximal n).ne_top hmax
  let _ : Nontrivial (Germ n ⧸ f.1.coordinateIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  exact Module.finrank_pos

/-- Right left equivalent finite germs have the same coordinate colength. -/
theorem RightLeftEquivalent.coordinateColength_eq {n m : ℕ}
    {f g : PointedMapGerm n m} (hfg : f.RightLeftEquivalent g)
    (hf : f.IsFiniteAtOrigin) (hg : g.IsFiniteAtOrigin) :
    f.coordinateColength hf = g.coordinateColength hg := by
  let _ : Module.Finite ℂ (Germ n ⧸ f.1.coordinateIdeal) :=
    f.coordinateQuotient_moduleFinite hf
  let _ : Module.Finite ℂ (Germ n ⧸ g.1.coordinateIdeal) :=
    g.coordinateQuotient_moduleFinite hg
  rcases hfg.exists_map_coordinateIdeal with ⟨source, hsource⟩
  change Module.finrank ℂ (Germ n ⧸ f.1.coordinateIdeal) =
    Module.finrank ℂ (Germ n ⧸ g.1.coordinateIdeal)
  exact Germ.quotient_finrank_eq_of_map_eq
    f.1.coordinateIdeal g.1.coordinateIdeal source.pullbackAlgEquiv hsource

end PointedMapGerm

end OnLeConjecture.Analytic
