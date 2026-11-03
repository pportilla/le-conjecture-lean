/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.Algebra.Homology.Contraction.Linear

/-!
# Transfer of chain maps along a special contraction

Let `(incl, proj, h)` be a special contraction of `(M, d_M)` onto `(N, d_N)` and let `Φ` be an
endomorphism of `M` commuting with `d_M`. The transferred operator `Φ_N = proj Φ incl` commutes
with `d_N` (`contractionTransfer_comm`), and the inclusion and the projection intertwine `Φ` with
`Φ_N` up to the explicit homotopies `h Φ incl` and `proj Φ h` (`comp_incl_sub_incl_comp_transfer`,
`proj_comp_sub_transfer_comp_proj`):

  `Φ incl - incl Φ_N = d_M (h Φ incl) + (h Φ incl) d_N`,
  `proj Φ - Φ_N proj = d_N (proj Φ h) + (proj Φ h) d_M`.

In the written proof of Statement E (`statement_E_complete_proof.tex`, Lemma `movesToNativeMap`)
the colour derivatives must be natural under the stabilization maps. The project's stabilization
maps come from a special contraction onto two copies of the old complex, so by these identities
their colour naturality on homology reduces to identifying the transferred derivative.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer

open TauCeti

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {dM : Module.End R M} {dN : Module.End R N}

/-- The operator transferred to the retract of a special contraction. -/
def contractionTransfer (c : LinearSpecialContraction dM dN) (Φ : Module.End R M) :
    Module.End R N :=
  c.proj ∘ₗ Φ ∘ₗ c.incl

variable (c : LinearSpecialContraction dM dN) {Φ : Module.End R M}

/-- The transferred operator of a chain map is a chain map. -/
theorem contractionTransfer_comm (hΦ : dM ∘ₗ Φ = Φ ∘ₗ dM) :
    dN ∘ₗ contractionTransfer c Φ = contractionTransfer c Φ ∘ₗ dN := by
  apply LinearMap.ext
  intro x
  have h1 := LinearMap.congr_fun c.proj_comp_dM (Φ (c.incl x))
  have h2 := LinearMap.congr_fun hΦ (c.incl x)
  have h3 := LinearMap.congr_fun c.dM_comp_incl x
  simp only [LinearMap.comp_apply] at h1 h2 h3 ⊢
  simp only [contractionTransfer, LinearMap.comp_apply]
  rw [← h1, h2, h3]

/-- The inclusion intertwines a chain map with its transfer up to an explicit homotopy. -/
theorem comp_incl_sub_incl_comp_transfer (hΦ : dM ∘ₗ Φ = Φ ∘ₗ dM) :
    Φ ∘ₗ c.incl - c.incl ∘ₗ contractionTransfer c Φ =
      dM ∘ₗ (c.homotopy ∘ₗ Φ ∘ₗ c.incl) + (c.homotopy ∘ₗ Φ ∘ₗ c.incl) ∘ₗ dN := by
  apply LinearMap.ext
  intro x
  have hid := LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM (Φ (c.incl x))
  have h2 := LinearMap.congr_fun hΦ (c.incl x)
  have h3 := LinearMap.congr_fun c.dM_comp_incl x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.id_apply] at hid h2 h3 ⊢
  simp only [contractionTransfer, LinearMap.comp_apply]
  rw [← h3, ← h2, hid]

/-- The projection intertwines a chain map with its transfer up to an explicit homotopy. -/
theorem proj_comp_sub_transfer_comp_proj (hΦ : dM ∘ₗ Φ = Φ ∘ₗ dM) :
    c.proj ∘ₗ Φ - contractionTransfer c Φ ∘ₗ c.proj =
      dN ∘ₗ (c.proj ∘ₗ Φ ∘ₗ c.homotopy) + (c.proj ∘ₗ Φ ∘ₗ c.homotopy) ∘ₗ dM := by
  apply LinearMap.ext
  intro x
  have hid := LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM x
  have h1 := LinearMap.congr_fun c.proj_comp_dM (Φ (c.homotopy x))
  have h2 := LinearMap.congr_fun hΦ (c.homotopy x)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.id_apply] at hid h1 h2 ⊢
  simp only [contractionTransfer, LinearMap.comp_apply]
  rw [← h1, h2, ← map_add, ← map_add, hid, map_sub, map_sub]

end OnLeConjecture.KnotFloer
