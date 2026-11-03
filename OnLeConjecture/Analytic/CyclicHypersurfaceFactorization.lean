/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CyclicHypersurfaceCoordinates
public import OnLeConjecture.Analytic.CyclicCoverUnitFactorization

/-!
# Unit factorization in the original hypersurface coordinates

The cyclic-cover factorization transports through an actual analytic
coordinate equivalence. Its hypotheses concern the zero set and an axis
restriction of a representative on the cover. No descent or factorization
of the given germ is assumed.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic.CyclicCover

/-- Transport a factorization modulo the cyclic relation to the original
hypersurface equation. -/
theorem exists_unit_factor_mod_equation_of_coordinate_factorization
    (r N : ℕ) (e : PointedEquivGerm 3) (H U a D : Germ 3)
    (hU : e.forward.pullbackRingHom (Germ.coordinate (0 : Fin 3)) = U)
    (hH : e.forward.pullbackRingHom (relationGerm r) = a * H)
    (u : Germ 3) (hu : IsUnit u)
    (hfactor : e.inverse.pullbackRingHom D -
      Germ.coordinate (0 : Fin 3) ^ N * u ∈ Ideal.span {relationGerm r}) :
    ∃ v : Germ 3, IsUnit v ∧ D - U ^ N * v ∈ Ideal.span {H} := by
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hfactor
  have hmap := congrArg e.forward.pullbackRingHom hq
  have hinv : e.forward.pullbackRingHom (e.inverse.pullbackRingHom D) = D :=
    e.pullbackRingEquiv.apply_symm_apply D
  rw [map_sub, map_mul, map_pow, hinv, hU, map_mul, hH] at hmap
  refine ⟨e.forward.pullbackRingHom u, hu.map e.forward.pullbackRingHom,
    Ideal.mem_span_singleton.mpr ⟨a * e.forward.pullbackRingHom q, ?_⟩⟩
  rw [hmap]
  ring

/-- Zero-set support and the axis restriction on the transported cyclic
cover give a unit factorization modulo the original equation. -/
theorem exists_unit_factor_mod_equation_of_axes_support
    (r N : ℕ) (hr : 0 < r) (e : PointedEquivGerm 3)
    (H U a D : Germ 3)
    (hU : e.forward.pullbackRingHom (Germ.coordinate (0 : Fin 3)) = U)
    (hH : e.forward.pullbackRingHom (relationGerm r) = a * H)
    (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0)
    (hrepresentative : Germ.ofFunction F hF =
      (e.inverse.comp (coverGerm r hr)).pullbackRingHom D)
    (c : ℂ) (hc : c ≠ 0)
    (hsupport : ∀ᶠ z in 𝓝 (0 : Source 2), F z = 0 → z 0 = 0 ∨ z 1 = 0)
    (haxis : Germ.lineRestriction (![1, 0] : Source 2) (Germ.ofFunction F hF) =
      Germ.constRingHom 1 c * Germ.coordinate (0 : Fin 1) ^ (r * N)) :
    ∃ v : Germ 3, IsUnit v ∧ D - U ^ N * v ∈ Ideal.span {H} := by
  rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply] at hrepresentative
  obtain ⟨u, hu, hfactor⟩ := exists_unit_factor_mod_relation_of_axes_support
    r N hr (e.inverse.pullbackRingHom D) F hF hrepresentative c hc hsupport haxis
  exact exists_unit_factor_mod_equation_of_coordinate_factorization
    r N e H U a D hU hH u hu hfactor

end OnLeConjecture.Analytic.CyclicCover
