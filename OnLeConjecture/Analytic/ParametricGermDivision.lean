/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Hyperplane

/-!
# Parametric division of an analytic germ

An analytic germ is the extension of its restriction to the first
coordinate hyperplane plus the first coordinate times an analytic germ.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem exists_eq_hyperplaneExtension_add_coordinate_mul
    {n : ℕ} (f : Germ (n + 1)) :
    ∃ q : Germ (n + 1), f = hyperplaneExtension n (hyperplaneRestriction n f) +
      coordinate (0 : Fin (n + 1)) * q := by
  have hres : hyperplaneRestriction n
      (hyperplaneExtension n (hyperplaneRestriction n f)) = hyperplaneRestriction n f :=
    DFunLike.congr_fun (hyperplaneRestriction_comp_extension n) (hyperplaneRestriction n f)
  have hmem : f - hyperplaneExtension n (hyperplaneRestriction n f) ∈
      RingHom.ker (hyperplaneRestriction n) := by
    rw [RingHom.mem_ker, map_sub, hres, sub_self]
  rw [ker_hyperplaneRestriction_eq_span_coordinate_zero] at hmem
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
  exact ⟨q, (sub_eq_iff_eq_add.mp hq).trans (add_comm _ _)⟩

end OnLeConjecture.Analytic.Germ
