/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyRootFamily
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Root families of proper local homeomorphisms

This module proves the topological part of the paragraph "Over `|h| = ρ` the source sheets vary by
the implicit function theorem without collision" of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`). Let `Φ : E → F` be continuous on a closed ball `B̄_R` of a
proper normed group `E`, with values in a Hausdorff space `F`.

* `IsLocalInverse Φ V T ψ`: `Φ` maps the open set `V` bijectively onto the open set `T`, with
  continuous inverse `ψ` on `T`. `HasStrictFDerivAt.exists_isLocalInverse` is the inverse function
  theorem in this form; `IsLocalInverse.shrink` restricts a local inverse to an open subset.
* `exists_local_sections`: if no point of the fibre `Φ⁻¹(p) ∩ B̄_R` lies on the sphere and `Φ` has
  a local inverse at every point of the fibre, the fibre is finite, and over a neighbourhood `N`
  of `p` the fibres of `Φ` in `B̄_R` are the values of continuous pairwise distinct local sections
  through the points of `Φ⁻¹(p)`.
* `isRootFamily_of_fibration`: for a continuous family `γ` of base points over a preconnected open
  set `U ⊆ ℂ` with these properties at every `γ w`, and for a function `ψ` injective on every fibre,
  the images `ψ (Φ⁻¹(γ w) ∩ B_R)` form a root family of `S` points over `U`, where `S` is the
  number of points of one fibre. The number of points of the fibres is locally constant, hence
  constant on `U`.
-/

@[expose] public noncomputable section

open Set Function Filter Metric
open scoped Topology

namespace OnLeConjecture.Analytic

/-! ### Local inverses -/

/-- `Φ` maps the open set `V` bijectively onto the open set `T`, with continuous inverse `ψ` on
`T`. -/
structure IsLocalInverse {E F : Type*} [TopologicalSpace E] [TopologicalSpace F] (Φ : E → F)
    (V : Set E) (T : Set F) (ψ : F → E) : Prop where
  isOpen_source : IsOpen V
  isOpen_target : IsOpen T
  continuousOn : ContinuousOn ψ T
  mapsTo : MapsTo ψ T V
  right_inv : ∀ q ∈ T, Φ (ψ q) = q
  map_source : MapsTo Φ V T
  left_inv : ∀ y ∈ V, ψ (Φ y) = y

namespace IsLocalInverse

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F] {Φ : E → F} {V : Set E}
  {T : Set F} {ψ : F → E}

/-- Restriction of a local inverse to an open subset of its source. -/
theorem shrink (h : IsLocalInverse Φ V T ψ) {W : Set E} (hW : IsOpen W) :
    IsLocalInverse Φ (V ∩ W) (T ∩ ψ ⁻¹' W) ψ where
  isOpen_source := h.isOpen_source.inter hW
  isOpen_target := h.continuousOn.isOpen_inter_preimage h.isOpen_target hW
  continuousOn := h.continuousOn.mono inter_subset_left
  mapsTo q hq := ⟨h.mapsTo hq.1, hq.2⟩
  right_inv q hq := h.right_inv q hq.1
  map_source y hy := by
    refine ⟨h.map_source hy.1, ?_⟩
    change ψ (Φ y) ∈ W
    rw [h.left_inv y hy.1]
    exact hy.2
  left_inv y hy := h.left_inv y hy.1

/-- Two points of the source with the same image coincide. -/
theorem eq_of_eq (h : IsLocalInverse Φ V T ψ) {x y : E} (hx : x ∈ V) (hy : y ∈ V)
    (hxy : Φ x = Φ y) : x = y := by
  rw [← h.left_inv x hx, ← h.left_inv y hy, hxy]

end IsLocalInverse

/-- **The inverse function theorem**, in the form of a local inverse. -/
theorem HasStrictFDerivAt.exists_isLocalInverse {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace E] {Φ : E → F} {f' : E ≃L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt Φ (f' : E →L[𝕜] F) a) :
    ∃ (V : Set E) (T : Set F) (ψ : F → E), IsLocalInverse Φ V T ψ ∧ a ∈ V := by
  set e := hf.toOpenPartialHomeomorph Φ
  have he : ∀ y, e y = Φ y := fun y => rfl
  refine ⟨e.source, e.target, e.symm, ⟨e.open_source, e.open_target, e.continuousOn_symm,
    fun q hq => e.map_target hq, fun q hq => ?_, fun y hy => ?_, fun y hy => e.left_inv hy⟩,
    hf.mem_toOpenPartialHomeomorph_source⟩
  · rw [← he]
    exact e.right_inv hq
  · rw [← he]
    exact e.map_source hy

/-! ### Local sections of a proper local homeomorphism -/

variable {E F : Type*} [NormedAddCommGroup E] [ProperSpace E] [TopologicalSpace F] [T2Space F]

/-- **Local sections.** If the fibre `Φ⁻¹(p) ∩ B̄_R` does not meet the sphere and `Φ` has a local
inverse at each of its points, the fibre is a finite set `F₀`, and there are a neighbourhood `N`
of `p` and continuous sections `σ x` on `N`, `x ∈ F₀`, with pairwise distinct values in `B_R`,
whose values over `q ∈ N` are the points of `Φ⁻¹(q) ∩ B̄_R`. -/
theorem exists_local_sections {Φ : E → F} {R : ℝ} {p : F}
    (hΦ : ContinuousOn Φ (closedBall 0 R))
    (hint : ∀ x ∈ closedBall (0 : E) R, Φ x = p → x ∈ ball (0 : E) R)
    (hloc : ∀ x ∈ ball (0 : E) R, Φ x = p →
      ∃ (V : Set E) (T : Set F) (ψ : F → E), IsLocalInverse Φ V T ψ ∧ x ∈ V) :
    ∃ (F₀ : Finset E) (N : Set F) (σ : E → F → E),
      (∀ x, x ∈ F₀ ↔ x ∈ ball (0 : E) R ∧ Φ x = p) ∧ N ∈ 𝓝 p ∧
      (∀ x ∈ F₀, ContinuousOn (σ x) N) ∧
      (∀ x ∈ F₀, ∀ q ∈ N, σ x q ∈ ball (0 : E) R ∧ Φ (σ x q) = q) ∧
      (∀ q ∈ N, ∀ y ∈ closedBall (0 : E) R, Φ y = q → ∃ x ∈ F₀, σ x q = y) ∧
      (∀ x ∈ F₀, ∀ x' ∈ F₀, ∀ q ∈ N, σ x q = σ x' q → x = x') := by
  classical
  set Fb : Set E := {x | x ∈ ball (0 : E) R ∧ Φ x = p} with hFb
  have hFb_eq : Fb = closedBall (0 : E) R ∩ Φ ⁻¹' {p} := by
    ext x
    constructor
    · rintro ⟨hx, hxp⟩
      exact ⟨ball_subset_closedBall hx, hxp⟩
    · rintro ⟨hx, hxp⟩
      exact ⟨hint x hx hxp, hxp⟩
  have hcomp : IsCompact Fb := by
    rw [hFb_eq]
    exact (isCompact_closedBall (0 : E) R).of_isClosed_subset
      (hΦ.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton)
      inter_subset_left
  choose! V T ψ hVTψ hxV using hloc
  -- the fibre is finite
  have hfin : Fb.Finite := by
    obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover (fun x : Fb => V x)
      (fun x => (hVTψ x x.2.1 x.2.2).isOpen_source)
      (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hxV y hy.1 hy.2⟩)
    refine ((t.finite_toSet).image Subtype.val).subset ?_
    intro y hy
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hy)
    refine ⟨x, hxt, ?_⟩
    exact ((hVTψ x x.2.1 x.2.2).eq_of_eq hyx (hxV x x.2.1 x.2.2)
      (hy.2.trans x.2.2.symm)).symm
  obtain ⟨Usep, hUsep, hdisj⟩ := hfin.t2_separation
  set F₀ := hfin.toFinset with hF₀
  have hmemF₀ : ∀ x, x ∈ F₀ ↔ x ∈ ball (0 : E) R ∧ Φ x = p := fun x => by
    rw [hF₀, Set.Finite.mem_toFinset]
    rfl
  -- the shrunk local inverses
  set V' : E → Set E := fun x => V x ∩ (Usep x ∩ ball (0 : E) R) with hV'
  set T' : E → Set F := fun x => T x ∩ ψ x ⁻¹' (Usep x ∩ ball (0 : E) R) with hT'
  have hloc' : ∀ x ∈ F₀, IsLocalInverse Φ (V' x) (T' x) (ψ x) ∧ x ∈ V' x ∧ p ∈ T' x := by
    intro x hx
    obtain ⟨hxb, hxp⟩ := (hmemF₀ x).mp hx
    have h := (hVTψ x hxb hxp).shrink ((hUsep x).2.inter (isOpen_ball (x := (0 : E)) (ε := R)))
    have hxV' : x ∈ V' x := ⟨hxV x hxb hxp, (hUsep x).1, hxb⟩
    refine ⟨h, hxV', ?_⟩
    rw [← hxp]
    exact h.map_source hxV'
  -- properness: away from the shrunk sources there is no point over a neighbourhood of `p`
  set C : Set E := closedBall (0 : E) R \ ⋃ x ∈ F₀, V' x with hC
  have hCc : IsCompact C :=
    (isCompact_closedBall (0 : E) R).diff
      (isOpen_biUnion fun x hx => (hloc' x hx).1.isOpen_source)
  have hpC : p ∉ Φ '' C := by
    rintro ⟨y, ⟨hyb, hyV⟩, hyp⟩
    have hyF : y ∈ F₀ := (hmemF₀ y).mpr ⟨hint y hyb hyp, hyp⟩
    exact hyV (mem_iUnion₂.mpr ⟨y, hyF, (hloc' y hyF).2.1⟩)
  have hN₁ : (Φ '' C)ᶜ ∈ 𝓝 p :=
    (hCc.image_of_continuousOn (hΦ.mono sdiff_subset)).isClosed.isOpen_compl.mem_nhds hpC
  set N : Set F := (Φ '' C)ᶜ ∩ ⋂ x ∈ F₀, T' x with hN
  have hNmem : N ∈ 𝓝 p := inter_mem hN₁ ((biInter_finset_mem F₀).mpr fun x hx =>
    (hloc' x hx).1.isOpen_target.mem_nhds (hloc' x hx).2.2)
  have hNT : ∀ x ∈ F₀, ∀ q ∈ N, q ∈ T' x := fun x hx q hq =>
    mem_iInter₂.mp hq.2 x hx
  refine ⟨F₀, N, ψ, hmemF₀, hNmem, fun x hx => ?_, fun x hx q hq => ?_, fun q hq y hy hyq => ?_,
    fun x hx x' hx' q hq hxx' => ?_⟩
  · exact (hloc' x hx).1.continuousOn.mono fun q hq => hNT x hx q hq
  · have hmem := (hloc' x hx).1.mapsTo (hNT x hx q hq)
    exact ⟨hmem.2.2, (hloc' x hx).1.right_inv q (hNT x hx q hq)⟩
  · have hyC : y ∉ C := fun hyC => hq.1 ⟨y, hyC, hyq⟩
    have hyU : y ∈ ⋃ x ∈ F₀, V' x := by
      by_contra hyU
      exact hyC ⟨hy, hyU⟩
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hyU
    refine ⟨x, hx, ?_⟩
    rw [← hyq]
    exact (hloc' x hx).1.left_inv y hyx
  · by_contra hne
    have h1 := (hloc' x hx).1.mapsTo (hNT x hx q hq)
    have h2 := (hloc' x' hx').1.mapsTo (hNT x' hx' q hq)
    have hxF : x ∈ Fb := (hmemF₀ x).mp hx
    have hx'F : x' ∈ Fb := (hmemF₀ x').mp hx'
    have hd := hdisj hxF hx'F hne
    rw [hxx'] at h1
    exact Set.disjoint_left.mp hd h1.2.1 h2.2.1

/-! ### Root families from proper local homeomorphisms -/

/-- **Root family of a proper local homeomorphism.** Let `γ` be continuous on a preconnected open
set `U ⊆ ℂ`. If for every `w ∈ U` no point of `Φ⁻¹(γ w) ∩ B̄_R` lies on the sphere, `Φ` has a
local inverse at each point of `Φ⁻¹(γ w) ∩ B_R`, and `ψ` is injective on `Φ⁻¹(γ w) ∩ B_R`, then the
images `ψ (Φ⁻¹(γ w) ∩ B_R)` form a root family over `U`, whose number of points is the number of
points of any one fibre. -/
theorem isRootFamily_of_fibration {Φ : E → F} {ψ : E → ℂ} {R : ℝ} {γ : ℂ → F} {U : Set ℂ}
    {S : ℕ} (hU : IsOpen U) (hUc : IsPreconnected U) (hγ : ContinuousOn γ U)
    (hΦ : ContinuousOn Φ (closedBall 0 R)) (hψ : ContinuousOn ψ (ball 0 R))
    (hint : ∀ w ∈ U, ∀ x ∈ closedBall (0 : E) R, Φ x = γ w → x ∈ ball (0 : E) R)
    (hloc : ∀ w ∈ U, ∀ x ∈ ball (0 : E) R, Φ x = γ w →
      ∃ (V : Set E) (T : Set F) (ψ' : F → E), IsLocalInverse Φ V T ψ' ∧ x ∈ V)
    (hinj : ∀ w ∈ U, ∀ x ∈ ball (0 : E) R, ∀ y ∈ ball (0 : E) R, Φ x = γ w → Φ y = γ w →
      ψ x = ψ y → x = y)
    {w₀ : ℂ} (hw₀ : w₀ ∈ U) (hcount : {x | x ∈ ball (0 : E) R ∧ Φ x = γ w₀}.ncard = S) :
    IsRootFamily (fun w => ψ '' {x | x ∈ ball (0 : E) R ∧ Φ x = γ w}) S U := by
  classical
  set fib : ℂ → Set E := fun w => {x | x ∈ ball (0 : E) R ∧ Φ x = γ w} with hfib
  -- the local structure of the fibres
  have hlocal : ∀ w ∈ U, ∃ r > 0, ball w r ⊆ U ∧ ∃ (F₀ : Finset E) (σ : E → ℂ → E),
      (∀ x ∈ F₀, ContinuousOn (σ x) (ball w r)) ∧
      ∀ w' ∈ ball w r, fib w' = (fun x => σ x w') '' ↑F₀ ∧ InjOn (fun x => σ x w') ↑F₀ ∧
        ∀ x ∈ F₀, σ x w' ∈ ball (0 : E) R := by
    intro w hw
    obtain ⟨F₀, N, σ₀, -, hN, hσc, hσmem, hσcov, hσinj⟩ :=
      exists_local_sections hΦ (hint w hw) (hloc w hw)
    have hγw : ContinuousAt γ w := hγ.continuousAt (hU.mem_nhds hw)
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
      (inter_mem (hU.mem_nhds hw) (hγw.preimage_mem_nhds hN))
    have hrU : ball w r ⊆ U := fun w' hw' => (hrsub hw').1
    have hrN : ∀ w' ∈ ball w r, γ w' ∈ N := fun w' hw' => (hrsub hw').2
    refine ⟨r, hr, hrU, F₀, fun x w' => σ₀ x (γ w'), fun x hx => ?_, fun w' hw' => ?_⟩
    · exact (hσc x hx).comp (hγ.mono hrU) fun w' hw' => hrN w' hw'
    · refine ⟨?_, fun x hx x' hx' hxx' => hσinj x hx x' hx' _ (hrN w' hw') hxx',
        fun x hx => (hσmem x hx _ (hrN w' hw')).1⟩
      ext y
      constructor
      · rintro ⟨hyb, hyγ⟩
        obtain ⟨x, hx, hxy⟩ := hσcov _ (hrN w' hw') y (ball_subset_closedBall hyb) hyγ
        exact ⟨x, hx, hxy⟩
      · rintro ⟨x, hx, rfl⟩
        exact hσmem x hx _ (hrN w' hw')
  -- the number of points of the fibres is locally constant, hence constant
  have hcard : ∀ w ∈ U, ∃ r > 0, ∀ w' ∈ ball w r, (fib w').ncard = (fib w).ncard := by
    intro w hw
    obtain ⟨r, hr, -, F₀, σ, -, hσ⟩ := hlocal w hw
    have hc : ∀ w' ∈ ball w r, (fib w').ncard = F₀.card := fun w' hw' => by
      rw [(hσ w' hw').1, (hσ w' hw').2.1.ncard_image, Set.ncard_coe_finset]
    exact ⟨r, hr, fun w' hw' => (hc w' hw').trans (hc w (mem_ball_self hr)).symm⟩
  have hcont : ContinuousOn (fun w => (fib w).ncard) U := by
    intro w hw
    obtain ⟨r, hr, hr'⟩ := hcard w hw
    refine ((continuousAt_const (y := (fib w).ncard)).congr ?_).continuousWithinAt
    filter_upwards [ball_mem_nhds w hr] with w' hw'
    exact (hr' w' hw').symm
  have hconst : ∀ w ∈ U, (fib w).ncard = S := fun w hw =>
    (hUc.constant hcont hw hw₀).trans hcount
  refine ⟨hU, fun w hw => ?_⟩
  obtain ⟨r, hr, hrU, F₀, σ, hσc, hσ⟩ := hlocal w hw
  have hF₀ : F₀.card = S := by
    rw [← hconst w hw, (hσ w (mem_ball_self hr)).1,
      (hσ w (mem_ball_self hr)).2.1.ncard_image, Set.ncard_coe_finset]
  set e : F₀ ≃ Fin S := F₀.equivFinOfCardEq hF₀
  refine ⟨r, hr, hrU, fun k w' => ψ (σ (e.symm k) w'), fun k => ?_, fun w' hw' => ⟨?_, ?_⟩⟩
  · exact hψ.comp (hσc _ (e.symm k).2) fun w' hw' => (hσ w' hw').2.2 _ (e.symm k).2
  · intro k l hkl
    have hk := (hσ w' hw').2.2 _ (e.symm k).2
    have hl := (hσ w' hw').2.2 _ (e.symm l).2
    have hkf : σ (e.symm k) w' ∈ fib w' := by
      rw [(hσ w' hw').1]
      exact ⟨_, (e.symm k).2, rfl⟩
    have hlf : σ (e.symm l) w' ∈ fib w' := by
      rw [(hσ w' hw').1]
      exact ⟨_, (e.symm l).2, rfl⟩
    have h1 := hinj w' (hrU hw') _ hk _ hl hkf.2 hlf.2 hkl
    have h2 := (hσ w' hw').2.1 (e.symm k).2 (e.symm l).2 h1
    exact e.symm.injective (Subtype.ext h2)
  · change ψ '' fib w' = _
    rw [(hσ w' hw').1]
    ext z
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨e ⟨x, hx⟩, by simp⟩
    · rintro ⟨k, rfl⟩
      exact ⟨σ (e.symm k) w', ⟨_, (e.symm k).2, rfl⟩, rfl⟩

end OnLeConjecture.Analytic
