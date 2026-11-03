/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorContractionTransfer
public import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel

/-!
# Null-homotopic maps, transfer along a special contraction, and block homotopies

Let `(M, d_M)` and `(N, d_N)` be modules with endomorphisms. A linear map `f : M → N` is
null-homotopic (`IsNullHomotopic d_M d_N f`) when `f = d_N K + K d_M` for some linear map
`K : M → N`. This file collects the closure properties of this notion and the following
consequences for a special contraction `(incl, proj, h)` of `(M, d_M)` onto `(N, d_N)`, where
`Φ_N = proj Φ incl` is the transfer of a chain map `Φ` (`contractionTransfer`).

* `contractionTransfer_comp_sub_comp`: the transfer of `Φ Ψ` differs from `Φ_N Ψ_N` by the explicit
  null-homotopic map `d_N (proj Φ h Ψ incl) + (proj Φ h Ψ incl) d_N`.
* `isNullHomotopic_contractionTransfer`: the transfer of a null-homotopic endomorphism is
  null-homotopic.

For `N × N` with the diagonal endomorphism `d ⊕ d`, every block of a null-homotopic endomorphism
is null-homotopic (`IsNullHomotopic.block`). The two block identities
`isNullHomotopic_snd_comp_inl_of_anticomm` and `isNullHomotopic_fst_comp_inr_of_anticomm` read off
blocks of an endomorphism `T` from the vanishing up to homotopy of its anticommutator with
`inl ∘ snd`, respectively with an endomorphism `X` satisfying `fst ∘ X = 0` and `X ∘ inl = inr`.

These identities are used in `GridStabilizationColourNatural` to compute the transferred colour
derivative of a stabilization.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer

open TauCeti

variable {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P]

/-- A linear map between two modules with endomorphisms is null-homotopic. -/
def IsNullHomotopic (dM : Module.End R M) (dN : Module.End R N) (f : M →ₗ[R] N) : Prop :=
  ∃ K : M →ₗ[R] N, f = dN ∘ₗ K + K ∘ₗ dM

namespace IsNullHomotopic

variable {dM : Module.End R M} {dN : Module.End R N} {dP : Module.End R P} {f g : M →ₗ[R] N}

theorem zero : IsNullHomotopic dM dN (0 : M →ₗ[R] N) :=
  ⟨0, by simp⟩

theorem of_eq_zero (h : f = 0) : IsNullHomotopic dM dN f :=
  h ▸ zero

theorem add (hf : IsNullHomotopic dM dN f) (hg : IsNullHomotopic dM dN g) :
    IsNullHomotopic dM dN (f + g) := by
  obtain ⟨K, rfl⟩ := hf
  obtain ⟨L, rfl⟩ := hg
  exact ⟨K + L, by simp only [LinearMap.comp_add, LinearMap.add_comp]; abel⟩

theorem neg (hf : IsNullHomotopic dM dN f) : IsNullHomotopic dM dN (-f) := by
  obtain ⟨K, rfl⟩ := hf
  exact ⟨-K, by simp only [LinearMap.comp_neg, LinearMap.neg_comp, neg_add]⟩

theorem sub (hf : IsNullHomotopic dM dN f) (hg : IsNullHomotopic dM dN g) :
    IsNullHomotopic dM dN (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem smul (a : R) (hf : IsNullHomotopic dM dN f) : IsNullHomotopic dM dN (a • f) := by
  obtain ⟨K, rfl⟩ := hf
  exact ⟨a • K, by simp only [LinearMap.comp_smul, LinearMap.smul_comp, smul_add]⟩

theorem finsetSum {ι : Type*} (s : Finset ι) {F : ι → M →ₗ[R] N}
    (hF : ∀ i ∈ s, IsNullHomotopic dM dN (F i)) : IsNullHomotopic dM dN (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IsNullHomotopic dM dN (0 : M →ₗ[R] N))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

/-- Composition on the left with a chain map preserves null-homotopy. -/
theorem comp_left {g : N →ₗ[R] P} (hg : g ∘ₗ dN = dP ∘ₗ g) (hf : IsNullHomotopic dM dN f) :
    IsNullHomotopic dM dP (g ∘ₗ f) := by
  obtain ⟨K, rfl⟩ := hf
  refine ⟨g ∘ₗ K, ?_⟩
  rw [LinearMap.comp_add, ← LinearMap.comp_assoc, hg, LinearMap.comp_assoc,
    LinearMap.comp_assoc]

/-- Composition on the right with a chain map preserves null-homotopy. -/
theorem comp_right {g : P →ₗ[R] M} (hg : dM ∘ₗ g = g ∘ₗ dP) (hf : IsNullHomotopic dM dN f) :
    IsNullHomotopic dP dN (f ∘ₗ g) := by
  obtain ⟨K, rfl⟩ := hf
  refine ⟨K ∘ₗ g, ?_⟩
  rw [LinearMap.add_comp, LinearMap.comp_assoc, LinearMap.comp_assoc, hg,
    LinearMap.comp_assoc]

end IsNullHomotopic

/-! ### Transfer along a special contraction -/

section Transfer

variable {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
  {Φ Ψ : Module.End R M}

theorem contractionTransfer_add (Φ Ψ : Module.End R M) :
    contractionTransfer c (Φ + Ψ) = contractionTransfer c Φ + contractionTransfer c Ψ := by
  simp only [contractionTransfer, LinearMap.add_comp, LinearMap.comp_add]

theorem contractionTransfer_smul (a : R) (Φ : Module.End R M) :
    contractionTransfer c (a • Φ) = a • contractionTransfer c Φ := by
  simp only [contractionTransfer, LinearMap.smul_comp, LinearMap.comp_smul]

theorem contractionTransfer_finsetSum {ι : Type*} (s : Finset ι) (F : ι → Module.End R M) :
    contractionTransfer c (∑ i ∈ s, F i) = ∑ i ∈ s, contractionTransfer c (F i) := by
  apply LinearMap.ext
  intro x
  simp only [contractionTransfer, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]

/-- The transfer of a composite of chain maps is the composite of the transfers, up to an explicit
homotopy. -/
theorem contractionTransfer_comp_sub_comp (hΦ : dM ∘ₗ Φ = Φ ∘ₗ dM) (hΨ : dM ∘ₗ Ψ = Ψ ∘ₗ dM) :
    contractionTransfer c (Φ ∘ₗ Ψ) - contractionTransfer c Φ ∘ₗ contractionTransfer c Ψ =
      dN ∘ₗ (c.proj ∘ₗ Φ ∘ₗ c.homotopy ∘ₗ Ψ ∘ₗ c.incl) +
        (c.proj ∘ₗ Φ ∘ₗ c.homotopy ∘ₗ Ψ ∘ₗ c.incl) ∘ₗ dN := by
  apply LinearMap.ext
  intro x
  have hid := LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM (Ψ (c.incl x))
  have h1 := LinearMap.congr_fun c.proj_comp_dM (Φ (c.homotopy (Ψ (c.incl x))))
  have h2 := LinearMap.congr_fun hΦ (c.homotopy (Ψ (c.incl x)))
  have h3 := LinearMap.congr_fun hΨ (c.incl x)
  have h4 := LinearMap.congr_fun c.dM_comp_incl x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.id_apply] at hid h1 h2 h3 h4
  simp only [contractionTransfer, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.add_apply]
  rw [← h1, h2, ← h4, ← h3, ← map_add, ← map_add, hid, map_sub, map_sub]

theorem isNullHomotopic_contractionTransfer_comp_sub_comp (hΦ : dM ∘ₗ Φ = Φ ∘ₗ dM)
    (hΨ : dM ∘ₗ Ψ = Ψ ∘ₗ dM) :
    IsNullHomotopic dN dN
      (contractionTransfer c (Φ ∘ₗ Ψ) - contractionTransfer c Φ ∘ₗ contractionTransfer c Ψ) :=
  ⟨_, contractionTransfer_comp_sub_comp c hΦ hΨ⟩

/-- The transfer of a null-homotopic endomorphism is null-homotopic. -/
theorem isNullHomotopic_contractionTransfer (hΦ : IsNullHomotopic dM dM Φ) :
    IsNullHomotopic dN dN (contractionTransfer c Φ) := by
  obtain ⟨K, hK⟩ := hΦ
  refine ⟨c.proj ∘ₗ K ∘ₗ c.incl, ?_⟩
  apply LinearMap.ext
  intro x
  have h1 := LinearMap.congr_fun c.proj_comp_dM (K (c.incl x))
  have h2 := LinearMap.congr_fun c.dM_comp_incl x
  simp only [LinearMap.comp_apply] at h1 h2
  simp only [contractionTransfer, hK, LinearMap.comp_apply, LinearMap.add_apply, map_add, h1, h2]

/-- The inclusion intertwines a chain map with its transfer up to homotopy. -/
theorem isNullHomotopic_comp_incl_sub (hΦ : dM ∘ₗ Φ = Φ ∘ₗ dM) :
    IsNullHomotopic dN dM (Φ ∘ₗ c.incl - c.incl ∘ₗ contractionTransfer c Φ) :=
  ⟨_, comp_incl_sub_incl_comp_transfer c hΦ⟩

/-- The projection intertwines a chain map with its transfer up to homotopy. -/
theorem isNullHomotopic_proj_comp_sub (hΦ : dM ∘ₗ Φ = Φ ∘ₗ dM) :
    IsNullHomotopic dM dN (c.proj ∘ₗ Φ - contractionTransfer c Φ ∘ₗ c.proj) :=
  ⟨_, proj_comp_sub_transfer_comp_proj c hΦ⟩

/-- The transfer of an anticommutator of chain maps is the anticommutator of the transfers, up
to homotopy. -/
theorem isNullHomotopic_contractionTransfer_anticomm_sub (hΦ : dM ∘ₗ Φ = Φ ∘ₗ dM)
    (hΨ : dM ∘ₗ Ψ = Ψ ∘ₗ dM) :
    IsNullHomotopic dN dN
      (contractionTransfer c (Φ ∘ₗ Ψ + Ψ ∘ₗ Φ) -
        (contractionTransfer c Φ ∘ₗ contractionTransfer c Ψ +
          contractionTransfer c Ψ ∘ₗ contractionTransfer c Φ)) := by
  have h := (isNullHomotopic_contractionTransfer_comp_sub_comp c hΦ hΨ).add
    (isNullHomotopic_contractionTransfer_comp_sub_comp c hΨ hΦ)
  rw [contractionTransfer_add]
  convert h using 1
  abel

end Transfer

/-! ### Blocks on a product with a diagonal endomorphism -/

section Blocks

variable (d : Module.End R N)

theorem prodMap_comp_inl :
    d.prodMap d ∘ₗ LinearMap.inl R N N = LinearMap.inl R N N ∘ₗ d := by
  apply LinearMap.ext
  intro x
  simp

theorem prodMap_comp_inr :
    d.prodMap d ∘ₗ LinearMap.inr R N N = LinearMap.inr R N N ∘ₗ d := by
  apply LinearMap.ext
  intro x
  simp

theorem fst_comp_prodMap :
    LinearMap.fst R N N ∘ₗ d.prodMap d = d ∘ₗ LinearMap.fst R N N := by
  apply LinearMap.ext
  intro x
  simp

theorem snd_comp_prodMap :
    LinearMap.snd R N N ∘ₗ d.prodMap d = d ∘ₗ LinearMap.snd R N N := by
  apply LinearMap.ext
  intro x
  simp

variable {d}

namespace IsNullHomotopic

variable {F : Module.End R (N × N)}

theorem fst_inl (hF : IsNullHomotopic (d.prodMap d) (d.prodMap d) F) :
    IsNullHomotopic d d (LinearMap.fst R N N ∘ₗ F ∘ₗ LinearMap.inl R N N) := by
  rw [← LinearMap.comp_assoc]
  exact ((hF.comp_left (fst_comp_prodMap d)).comp_right (prodMap_comp_inl d))

theorem fst_inr (hF : IsNullHomotopic (d.prodMap d) (d.prodMap d) F) :
    IsNullHomotopic d d (LinearMap.fst R N N ∘ₗ F ∘ₗ LinearMap.inr R N N) := by
  rw [← LinearMap.comp_assoc]
  exact ((hF.comp_left (fst_comp_prodMap d)).comp_right (prodMap_comp_inr d))

theorem snd_inl (hF : IsNullHomotopic (d.prodMap d) (d.prodMap d) F) :
    IsNullHomotopic d d (LinearMap.snd R N N ∘ₗ F ∘ₗ LinearMap.inl R N N) := by
  rw [← LinearMap.comp_assoc]
  exact ((hF.comp_left (snd_comp_prodMap d)).comp_right (prodMap_comp_inl d))

theorem snd_inr (hF : IsNullHomotopic (d.prodMap d) (d.prodMap d) F) :
    IsNullHomotopic d d (LinearMap.snd R N N ∘ₗ F ∘ₗ LinearMap.inr R N N) := by
  rw [← LinearMap.comp_assoc]
  exact ((hF.comp_left (snd_comp_prodMap d)).comp_right (prodMap_comp_inr d))

end IsNullHomotopic

variable {T X : Module.End R (N × N)}

/-- The anticommutator with `inl ∘ snd` has the second-from-first block of `T` in its
first-from-first entry. -/
theorem isNullHomotopic_snd_comp_inl_of_anticomm
    (h : IsNullHomotopic (d.prodMap d) (d.prodMap d)
      ((LinearMap.inl R N N ∘ₗ LinearMap.snd R N N) ∘ₗ T +
        T ∘ₗ (LinearMap.inl R N N ∘ₗ LinearMap.snd R N N))) :
    IsNullHomotopic d d (LinearMap.snd R N N ∘ₗ T ∘ₗ LinearMap.inl R N N) := by
  have hb := h.fst_inl
  convert hb using 1
  apply LinearMap.ext
  intro x
  simp [Prod.mk_zero_zero, map_zero]

/-- The anticommutator with `inl ∘ snd` relates the two diagonal blocks of `T`. -/
theorem isNullHomotopic_diagonal_of_anticomm
    (h : IsNullHomotopic (d.prodMap d) (d.prodMap d)
      ((LinearMap.inl R N N ∘ₗ LinearMap.snd R N N) ∘ₗ T +
        T ∘ₗ (LinearMap.inl R N N ∘ₗ LinearMap.snd R N N))) :
    IsNullHomotopic d d (LinearMap.snd R N N ∘ₗ T ∘ₗ LinearMap.inr R N N +
      LinearMap.fst R N N ∘ₗ T ∘ₗ LinearMap.inl R N N) := by
  have hb := h.fst_inr
  convert hb using 1
  apply LinearMap.ext
  intro x
  simp

/-- An endomorphism `X` with `fst ∘ X = 0` and `X ∘ inl = inr` exposes the first-from-second
block of `T` in the first-from-second entry of the anticommutator. -/
theorem isNullHomotopic_fst_comp_inr_of_anticomm
    (hX1 : LinearMap.fst R N N ∘ₗ X = 0) (hX2 : X ∘ₗ LinearMap.inl R N N = LinearMap.inr R N N)
    (h : IsNullHomotopic (d.prodMap d) (d.prodMap d) (X ∘ₗ T + T ∘ₗ X)) :
    IsNullHomotopic d d (LinearMap.fst R N N ∘ₗ T ∘ₗ LinearMap.inr R N N) := by
  have hb := h.fst_inl
  convert hb using 1
  apply LinearMap.ext
  intro x
  have h1 := LinearMap.congr_fun hX1 (T (x, 0))
  have h2 := LinearMap.congr_fun hX2 x
  simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
    LinearMap.fst_apply, LinearMap.zero_apply] at h1 h2
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.inl_apply, LinearMap.inr_apply,
    LinearMap.fst_apply, Prod.fst_add, h1, h2, zero_add]

end Blocks

end OnLeConjecture.KnotFloer
