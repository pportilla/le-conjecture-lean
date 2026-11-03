/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyReverse
public import OnLeConjecture.Analytic.BraidMonodromyHomotopy
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Root families and continuation of labels

In the finite projection of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`) the roots over a base point `c` form a finite set `Z c` of `S`
points of `ℂ`, without a preferred labelling. This module continues labels of such set-valued
families along paths and over squares, and attaches path words to them.

* `IsRootLabellingOn Z P A K`: the labelled points `K · x`, continuous on `A`, are pairwise
  distinct and form the set `Z (P x)` for every `x ∈ A`.
* `IsRootLabellingOn.exists_perm`: on a preconnected set two labellings of the same set-valued
  family differ by a constant permutation of the labels.
* `IsRootFamily Z S U`: `U` is open and every point of `U` has a ball in `U` on which `Z` is the
  set of values of `S` continuous, pairwise distinct labelled points. These are the local labels
  given by the implicit function theorem away from the critical values.
* `IsRootFamily.isCoveringMap`: the projection of the total space
  `{(c, z) | c ∈ U, z ∈ Z c}` to `U` is a covering map.
* `IsRootFamily.exists_square_labelling`, `IsRootFamily.exists_path_labelling`: labels continue
  over every square and along every path in `U`. The proof uses the homotopy lifting property of
  covering maps (`IsCoveringMap.liftHomotopy`) and the uniqueness of lifts.
* `IsRootPathWord Z γ u v W`: `W` is a path word of some labelling of `Z ∘ γ` on `[u, v]`. It is a
  path word of every labelling (`IsRootPathWord.isPathWord`), unique up to `SignedBraidEquiv`,
  exists along every path in `U`, and is compatible with concatenation, reversal and increasing
  affine reparametrization.
* `IsRootFamily.square_relation`: the root path words of the four sides of a square in `U`
  satisfy `bottom · right ≡ left · top` (`isPathWord_homotopy`).
-/

@[expose] public noncomputable section

open Set Function Filter Metric
open scoped Topology unitInterval

namespace OnLeConjecture.Analytic

open KnotTheory SignedAdjacentWord

variable {S : ℕ}

/-! ### Labellings of set-valued families -/

/-- `K` labels the set-valued family `Z ∘ P` on `A`: the labelled points are continuous on `A`,
pairwise distinct, and form the set `Z (P x)` at every `x ∈ A`. -/
structure IsRootLabellingOn {X : Type*} [TopologicalSpace X] (Z : ℂ → Set ℂ) (P : X → ℂ)
    (A : Set X) (K : Fin S → X → ℂ) : Prop where
  continuousOn : ∀ k, ContinuousOn (K k) A
  injective : ∀ x ∈ A, Injective fun k => K k x
  range_eq : ∀ x ∈ A, range (fun k => K k x) = Z (P x)

namespace IsRootLabellingOn

variable {X : Type*} [TopologicalSpace X] {Z : ℂ → Set ℂ} {P : X → ℂ} {A : Set X}
  {K K' : Fin S → X → ℂ}

theorem mono (h : IsRootLabellingOn Z P A K) {B : Set X} (hB : B ⊆ A) :
    IsRootLabellingOn Z P B K :=
  ⟨fun k => (h.continuousOn k).mono hB, fun x hx => h.injective x (hB hx),
    fun x hx => h.range_eq x (hB hx)⟩

theorem relabel (h : IsRootLabellingOn Z P A K) (τ : Equiv.Perm (Fin S)) :
    IsRootLabellingOn Z P A (fun k => K (τ k)) := by
  refine ⟨fun k => h.continuousOn (τ k), fun x hx => (h.injective x hx).comp τ.injective,
    fun x hx => ?_⟩
  rw [← h.range_eq x hx]
  exact (τ.surjective.range_comp fun k => K k x)

theorem mem (h : IsRootLabellingOn Z P A K) {x : X} (hx : x ∈ A) (k : Fin S) :
    K k x ∈ Z (P x) := by
  rw [← h.range_eq x hx]
  exact ⟨k, rfl⟩

/-- **Two labellings differ by a constant permutation.** On a preconnected set, two labellings of
the same set-valued family differ by a permutation of the labels which does not depend on the
point. -/
theorem exists_perm (hA : IsPreconnected A) (h : IsRootLabellingOn Z P A K)
    (h' : IsRootLabellingOn Z P A K') :
    ∃ τ : Equiv.Perm (Fin S), ∀ k, ∀ x ∈ A, K' k x = K (τ k) x := by
  classical
  rcases A.eq_empty_or_nonempty with hAe | ⟨x₀, hx₀⟩
  · exact ⟨1, fun k x hx => by rw [hAe] at hx; exact hx.elim⟩
  -- The label of `K` carrying the point `K' k x`.
  have hex : ∀ k x, x ∈ A → ∃ j, K j x = K' k x := fun k x hx => by
    have : K' k x ∈ range fun j => K j x := by
      rw [h.range_eq x hx, ← h'.range_eq x hx]
      exact ⟨k, rfl⟩
    exact this
  let ι : Fin S → X → Fin S := fun k x =>
    if hx : x ∈ A then (hex k x hx).choose else (hex k x₀ hx₀).choose
  have hι : ∀ k, ∀ x ∈ A, K (ι k x) x = K' k x := fun k x hx => by
    simp only [ι, dif_pos hx]
    exact (hex k x hx).choose_spec
  -- `ι k` is locally constant on `A`.
  have hloc : ∀ k, ContinuousOn (ι k) A := by
    intro k x hx
    obtain ⟨m, hm, hmμ⟩ := exists_pos_le_of_finite
      (fun j : Fin S => if j = ι k x then 1 else ‖K j x - K (ι k x) x‖) fun j => by
        by_cases hj : j = ι k x
        · simp [hj]
        · simp only [if_neg hj]
          exact norm_pos_iff.mpr (sub_ne_zero.mpr fun he => hj (h.injective x hx he))
    have hev : ∀ᶠ y in 𝓝[A] x, (∀ j, ‖K j y - K j x‖ < m / 2) ∧ ‖K' k y - K' k x‖ < m / 2 := by
      refine (eventually_all.mpr fun j => ?_).and ?_
      · have := (h.continuousOn j x hx).tendsto
        exact this.eventually (Metric.ball_mem_nhds (K j x) (half_pos hm)) |>.mono fun y hy =>
          by simpa [dist_eq_norm] using hy
      · have := (h'.continuousOn k x hx).tendsto
        exact this.eventually (Metric.ball_mem_nhds (K' k x) (half_pos hm)) |>.mono fun y hy =>
          by simpa [dist_eq_norm] using hy
    have hconst : ∀ᶠ y in 𝓝[A] x, ι k y = ι k x := by
      filter_upwards [hev, self_mem_nhdsWithin] with y ⟨hy1, hy2⟩ hyA
      by_contra hne
      have h1 := hmμ (ι k y)
      rw [if_neg hne] at h1
      have e1 := hι k y hyA
      have e2 := hι k x hx
      have : ‖K (ι k y) x - K (ι k x) x‖ < m := by
        calc ‖K (ι k y) x - K (ι k x) x‖
            = ‖(K (ι k y) x - K (ι k y) y) + (K' k y - K' k x)‖ := by rw [e1, e2]; ring_nf
          _ ≤ ‖K (ι k y) x - K (ι k y) y‖ + ‖K' k y - K' k x‖ := norm_add_le _ _
          _ < m / 2 + m / 2 := by
            refine add_lt_add ?_ hy2
            rw [norm_sub_rev]; exact hy1 _
          _ = m := by ring
      linarith
    exact tendsto_nhds_of_eventually_eq hconst
  have hconst : ∀ k, ∀ x ∈ A, ι k x = ι k x₀ := fun k x hx =>
    hA.constant (hloc k) hx hx₀
  -- The constant labels form a permutation.
  have hinj : Injective fun k => ι k x₀ := by
    intro k l hkl
    apply h'.injective x₀ hx₀
    simp only at hkl ⊢
    rw [← hι k x₀ hx₀, ← hι l x₀ hx₀, hkl]
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj), fun k x hx => ?_⟩
  simp only [Equiv.ofBijective_apply]
  rw [← hconst k x hx, hι k x hx]

end IsRootLabellingOn

/-- An injective map from `Fin S` into the set of values of another injective map from `Fin S`
has the same set of values. -/
theorem range_eq_of_injective_of_subset {g h : Fin S → ℂ} (hh : Injective h)
    (hsub : range h ⊆ range g) : range h = range g := by
  choose φ hφ using fun k => hsub ⟨k, rfl⟩
  have hφi : Injective φ := fun k l hkl => hh (by rw [← hφ k, ← hφ l, hkl])
  refine (hsub).antisymm ?_
  rintro _ ⟨j, rfl⟩
  obtain ⟨k, rfl⟩ := Finite.surjective_of_injective hφi j
  exact ⟨k, (hφ k).symm⟩

/-! ### Root families -/

/-- **A root family** of `S` points over the open set `U`: every point of `U` has a ball in `U` on
which `Z` is the set of values of `S` continuous, pairwise distinct labelled points. -/
def IsRootFamily (Z : ℂ → Set ℂ) (S : ℕ) (U : Set ℂ) : Prop :=
  IsOpen U ∧ ∀ c ∈ U, ∃ r > 0, ball c r ⊆ U ∧ ∃ f : Fin S → ℂ → ℂ,
    (∀ k, ContinuousOn (f k) (ball c r)) ∧
      ∀ c' ∈ ball c r, Injective (fun k => f k c') ∧ Z c' = range fun k => f k c'

namespace IsRootFamily

variable {Z : ℂ → Set ℂ} {U : Set ℂ}

/-- Over every point of `U` the family consists of `S` distinct points. -/
theorem exists_labels_at (hZ : IsRootFamily Z S U) {c : ℂ} (hc : c ∈ U) :
    ∃ g : Fin S → ℂ, Injective g ∧ Z c = range g := by
  obtain ⟨r, hr, -, f, -, hf⟩ := hZ.2 c hc
  exact ⟨fun k => f k c, (hf c (mem_ball_self hr)).1, (hf c (mem_ball_self hr)).2⟩

/-- An injective labelling by points of the family over a point of `U` exhausts it. -/
theorem range_eq_of_injective (hZ : IsRootFamily Z S U) {c : ℂ} (hc : c ∈ U)
    {h : Fin S → ℂ} (hh : Injective h) (hmem : ∀ k, h k ∈ Z c) : range h = Z c := by
  obtain ⟨g, -, hg⟩ := hZ.exists_labels_at hc
  rw [hg]
  refine range_eq_of_injective_of_subset hh ?_
  rintro _ ⟨k, rfl⟩
  rw [← hg]
  exact hmem k

end IsRootFamily

/-- The total space `{(c, z) | c ∈ U, z ∈ Z c}` of a set-valued family. -/
def RootSpace (Z : ℂ → Set ℂ) (U : Set ℂ) : Set (ℂ × ℂ) := {q | q.1 ∈ U ∧ q.2 ∈ Z q.1}

/-- The projection of the total space to the base. -/
def rootProj (Z : ℂ → Set ℂ) (U : Set ℂ) : RootSpace Z U → U := fun q => ⟨q.1.1, q.2.1⟩

theorem continuous_rootProj (Z : ℂ → Set ℂ) (U : Set ℂ) : Continuous (rootProj Z U) :=
  (continuous_fst.comp continuous_subtype_val).subtype_mk _

namespace IsRootFamily

variable {Z : ℂ → Set ℂ} {U : Set ℂ}

/-- **Root families are coverings.** The projection of the total space of a root family to the
base is a covering map. -/
theorem isCoveringMap (hZ : IsRootFamily Z S U) : IsCoveringMap (rootProj Z U) := by
  classical
  intro x
  obtain ⟨r, hr, -, f, hf, hfZ⟩ := hZ.2 x.1 x.2
  set V : Set U := Subtype.val ⁻¹' ball x.1 r with hVdef
  have hV : IsOpen V := isOpen_ball.preimage continuous_subtype_val
  have hxV : x ∈ V := mem_ball_self hr
  suffices hev : IsEvenlyCovered (rootProj Z U) x (Fin S) from
    hev.to_isEvenlyCovered_preimage
  refine ⟨inferInstance, V, hxV, hV, hV.preimage (continuous_rootProj Z U), ?_⟩
  have hmem : ∀ q : rootProj Z U ⁻¹' V, q.1.1.2 ∈ range fun k => f k q.1.1.1 := fun q => by
    have hq : q.1.1.1 ∈ ball x.1 r := q.2
    rw [← (hfZ _ hq).2]
    exact q.1.2.2
  let idx : rootProj Z U ⁻¹' V → Fin S := fun q => (hmem q).choose
  have hidx : ∀ q, f (idx q) q.1.1.1 = q.1.1.2 := fun q => (hmem q).choose_spec
  have hfmem : ∀ (y : V) (k : Fin S), f k y.1.1 ∈ Z y.1.1 := fun y k => by
    rw [(hfZ _ y.2).2]
    exact ⟨k, rfl⟩
  -- `idx` is locally constant.
  have hidxc : Continuous idx := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq idx).mpr ?_)
    intro q₀
    have hc₀ : q₀.1.1.1 ∈ ball x.1 r := q₀.2
    obtain ⟨m, hm, hmμ⟩ := exists_pos_le_of_finite
      (fun j : Fin S => if j = idx q₀ then 1 else ‖f j q₀.1.1.1 - q₀.1.1.2‖) fun j => by
        by_cases hj : j = idx q₀
        · simp [hj]
        · simp only [if_neg hj]
          refine norm_pos_iff.mpr (sub_ne_zero.mpr fun he => hj ?_)
          exact (hfZ _ hc₀).1 (he.trans (hidx q₀).symm)
    have hcont1 : Continuous fun q : rootProj Z U ⁻¹' V => q.1.1.1 :=
      continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hcont2 : Continuous fun q : rootProj Z U ⁻¹' V => q.1.1.2 :=
      continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hev1 : ∀ᶠ c in 𝓝 q₀.1.1.1, ∀ j, ‖f j c - f j q₀.1.1.1‖ < m / 2 := by
      refine eventually_all.mpr fun j => ?_
      have := ((hf j).continuousAt (isOpen_ball.mem_nhds hc₀)).tendsto
      exact this.eventually (Metric.ball_mem_nhds _ (half_pos hm)) |>.mono fun c hc => by
        simpa [dist_eq_norm] using hc
    have hev2 : ∀ᶠ z in 𝓝 q₀.1.1.2, ‖z - q₀.1.1.2‖ < m / 2 :=
      (Metric.ball_mem_nhds _ (half_pos hm)) |> Filter.mem_of_superset <| fun z hz => by
        simpa [dist_eq_norm] using hz
    filter_upwards [hcont1.continuousAt.eventually hev1, hcont2.continuousAt.eventually hev2]
      with q hq1 hq2
    by_contra hne
    have h1 := hmμ (idx q)
    rw [if_neg hne] at h1
    have e1 := hidx q
    have : ‖f (idx q) q₀.1.1.1 - q₀.1.1.2‖ < m := by
      calc ‖f (idx q) q₀.1.1.1 - q₀.1.1.2‖
          = ‖(f (idx q) q₀.1.1.1 - f (idx q) q.1.1.1) + (q.1.1.2 - q₀.1.1.2)‖ := by
            rw [← e1]; ring_nf
        _ ≤ ‖f (idx q) q₀.1.1.1 - f (idx q) q.1.1.1‖ + ‖q.1.1.2 - q₀.1.1.2‖ := norm_add_le _ _
        _ < m / 2 + m / 2 := by
          refine add_lt_add ?_ hq2
          rw [norm_sub_rev]; exact hq1 _
        _ = m := by ring
    linarith
  refine ⟨{
    toFun := fun q => (⟨rootProj Z U q.1, q.2⟩, idx q)
    invFun := fun yk => ⟨⟨(yk.1.1.1, f yk.2 yk.1.1.1), yk.1.1.2, hfmem yk.1 yk.2⟩, yk.1.2⟩
    left_inv := fun q => by
      apply Subtype.ext; apply Subtype.ext
      change (q.1.1.1, f (idx q) q.1.1.1) = q.1.1
      rw [hidx q]
    right_inv := fun yk => by
      refine Prod.ext rfl ?_
      simp only
      apply (hfZ _ yk.1.2).1
      exact hidx _
    continuous_toFun := by
      refine Continuous.prodMk ?_ hidxc
      exact ((continuous_rootProj Z U).comp continuous_subtype_val).subtype_mk _
    continuous_invFun := by
      refine continuous_prod_of_discrete_right.mpr fun k => ?_
      refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
      refine Continuous.prodMk (continuous_subtype_val.comp continuous_subtype_val) ?_
      exact (hf k).comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
        fun y => y.2 }, fun q => rfl⟩

/-- **Continuation of labels over the square.** For a map `P` from the unit square to `U`,
continuous on the square, the family `Z ∘ P` has a continuous labelling. -/
theorem exists_square_labelling (hZ : IsRootFamily Z S U) {P : ℝ × ℝ → ℂ}
    (hP : ContinuousOn P (Icc 0 1 ×ˢ Icc 0 1)) (hPU : MapsTo P (Icc 0 1 ×ˢ Icc 0 1) U) :
    ∃ L : Fin S → ℝ × ℝ → ℂ, (∀ k, Continuous (L k)) ∧
      IsRootLabellingOn Z P (Icc 0 1 ×ˢ Icc 0 1) L := by
  classical
  have cov := hZ.isCoveringMap
  let H : C(I × I, U) := ⟨fun st => ⟨P (st.1.1, st.2.1), hPU ⟨st.1.2, st.2.2⟩⟩, by
    refine Continuous.subtype_mk ?_ _
    exact hP.comp_continuous (by fun_prop) fun st => ⟨st.1.2, st.2.2⟩⟩
  obtain ⟨g, hg, hgZ⟩ := hZ.exists_labels_at (H (0, 0)).2
  let e : Fin S → RootSpace Z U := fun k =>
    ⟨((H (0, 0)).1, g k), (H (0, 0)).2, by rw [hgZ]; exact ⟨k, rfl⟩⟩
  let γ₀ : C(I, U) := H.comp ⟨fun t => (0, t), by fun_prop⟩
  have hγ₀ : ∀ k, γ₀ 0 = rootProj Z U (e k) := fun k => rfl
  let Γ : Fin S → C(I, RootSpace Z U) := fun k => cov.liftPath γ₀ (e k) (hγ₀ k)
  have hΓ0 : ∀ k a, H (0, a) = rootProj Z U (Γ k a) := fun k a => by
    have := congrFun (cov.liftPath_lifts γ₀ (e k) (hγ₀ k)) a
    exact this.symm
  let G : Fin S → C(I × I, RootSpace Z U) := fun k => cov.liftHomotopy H (Γ k) (hΓ0 k)
  have hGl : ∀ k, rootProj Z U ∘ G k = H := fun k => cov.liftHomotopy_lifts H (Γ k) (hΓ0 k)
  have hG00 : ∀ k, G k (0, 0) = e k := fun k => by
    rw [cov.liftHomotopy_zero H (Γ k) (hΓ0 k) 0]
    exact cov.liftPath_zero γ₀ (e k) (hγ₀ k)
  -- Distinct starting points give distinct lifts at every point.
  have hGinj : ∀ st : I × I, Injective fun k => (G k st).1.2 := by
    intro st k l hkl
    have hst : G k st = G l st := by
      apply Subtype.ext
      refine Prod.ext ?_ hkl
      have h1 := congrArg Subtype.val (congrFun (hGl k) st)
      have h2 := congrArg Subtype.val (congrFun (hGl l) st)
      exact h1.trans h2.symm
    have hGG := cov.eq_of_comp_eq (G k).continuous (G l).continuous
      ((hGl k).trans (hGl l).symm) st hst
    have h00 := congrFun hGG (0, 0)
    rw [hG00, hG00] at h00
    exact hg (congrArg (fun q : RootSpace Z U => q.1.2) h00)
  let π : ℝ × ℝ → I × I := fun x =>
    (projIcc 0 1 zero_le_one x.1, projIcc 0 1 zero_le_one x.2)
  have hπ : Continuous π := by fun_prop
  have hπmem : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, (H (π x)).1 = P x := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    simp only [π, H, ContinuousMap.coe_mk, projIcc_of_mem _ hs, projIcc_of_mem _ ht]
  refine ⟨fun k x => (G k (π x)).1.2, fun k => ?_, ⟨fun k => ?_, fun x _ => hGinj (π x), ?_⟩⟩
  · exact continuous_snd.comp (continuous_subtype_val.comp ((G k).continuous.comp hπ))
  · exact (continuous_snd.comp (continuous_subtype_val.comp
      ((G k).continuous.comp hπ))).continuousOn
  · intro x hx
    have hbase : ∀ k, (G k (π x)).1.1 = P x := fun k => by
      have := congrArg Subtype.val (congrFun (hGl k) (π x))
      exact this.trans (hπmem x hx)
    refine hZ.range_eq_of_injective (hPU hx) (hGinj (π x)) fun k => ?_
    have := (G k (π x)).2.2
    rwa [hbase k] at this

/-- **Continuation of labels along a path.** For a path `γ` in `U`, continuous on `[u, v]`, the
family `Z ∘ γ` has a continuous labelling on `[u, v]`. -/
theorem exists_path_labelling (hZ : IsRootFamily Z S U) {γ : ℝ → ℂ} {u v : ℝ} (huv : u < v)
    (hγ : ContinuousOn γ (Icc u v)) (hγU : MapsTo γ (Icc u v) U) :
    ∃ K : Fin S → ℝ → ℂ, IsRootLabellingOn Z γ (Icc u v) K := by
  have hd : 0 < v - u := sub_pos.mpr huv
  set φ : ℝ → ℝ := fun t => u + t * (v - u) with hφ
  have hφm : MapsTo φ (Icc 0 1) (Icc u v) := fun t ht =>
    ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  set P : ℝ × ℝ → ℂ := fun x => γ (φ x.2) with hPdef
  have hP : ContinuousOn P (Icc 0 1 ×ˢ Icc 0 1) :=
    hγ.comp (by fun_prop) fun x hx => hφm hx.2
  have hPU : MapsTo P (Icc 0 1 ×ˢ Icc 0 1) U := fun x hx => hγU (hφm hx.2)
  obtain ⟨L, hLc, hL⟩ := hZ.exists_square_labelling hP hPU
  set ψ : ℝ → ℝ × ℝ := fun t => (0, (t - u) / (v - u)) with hψ
  have hψm : MapsTo ψ (Icc u v) (Icc 0 1 ×ˢ Icc 0 1) := fun t ht =>
    ⟨⟨le_rfl, zero_le_one⟩, div_nonneg (by linarith [ht.1]) hd.le,
      (div_le_one hd).mpr (by linarith [ht.2])⟩
  have hPψ : ∀ t, P (ψ t) = γ t := fun t => by
    simp only [hPdef, hψ, hφ]
    congr 1
    field_simp
    ring
  refine ⟨fun k t => L k (ψ t), fun k => ((hLc k).comp (by fun_prop)).continuousOn,
    fun t ht => hL.injective _ (hψm ht), fun t ht => ?_⟩
  rw [hL.range_eq _ (hψm ht), hPψ]

end IsRootFamily

/-! ### Path words of root families -/

/-- `W` is a path word of some labelling of the family `Z ∘ γ` on `[u, v]`. -/
def IsRootPathWord (Z : ℂ → Set ℂ) (γ : ℝ → ℂ) (u v : ℝ) (W : SignedAdjacentWord S) : Prop :=
  ∃ K : Fin S → ℝ → ℂ, IsRootLabellingOn Z γ (Icc u v) K ∧ IsPathWord K u v W

namespace IsRootPathWord

variable {Z : ℂ → Set ℂ} {γ γ' : ℝ → ℂ} {u v w : ℝ} {W W₁ W₂ : SignedAdjacentWord S}

/-- A root path word is a path word of every labelling. -/
theorem isPathWord (h : IsRootPathWord Z γ u v W) {K : Fin S → ℝ → ℂ}
    (hK : IsRootLabellingOn Z γ (Icc u v) K) : IsPathWord K u v W := by
  obtain ⟨K₀, hK₀, hW⟩ := h
  obtain ⟨τ, hτ⟩ := hK₀.exists_perm isPreconnected_Icc hK
  have h1 := (IsPathWord.relabel (K := K₀) hK₀.injective τ).mpr hW
  exact h1.of_eqOn fun k t ht => (hτ k t ht).symm

/-- Root path words are unique up to `SignedBraidEquiv`. -/
theorem unique (huv : u < v) (h : IsRootPathWord Z γ u v W)
    (h' : IsRootPathWord Z γ u v W₁) : SignedBraidEquiv W W₁ := by
  obtain ⟨K, hK, hW⟩ := h
  exact hW.unique huv (h'.isPathWord hK)

theorem congr_equiv (h : IsRootPathWord Z γ u v W) (hW : SignedBraidEquiv W W₁) :
    IsRootPathWord Z γ u v W₁ := by
  obtain ⟨K, hK, hW'⟩ := h
  exact ⟨K, hK, hW'.congr_equiv hW⟩

theorem of_eqOn (h : IsRootPathWord Z γ u v W) (hγ : EqOn γ γ' (Icc u v)) :
    IsRootPathWord Z γ' u v W := by
  obtain ⟨K, hK, hW⟩ := h
  exact ⟨K, ⟨hK.continuousOn, hK.injective, fun t ht => by rw [hK.range_eq t ht, hγ ht]⟩, hW⟩

/-- Every labelling of a root family has a path word. -/
theorem of_labelling (huv : u < v) {K : Fin S → ℝ → ℂ} (hK : IsRootLabellingOn Z γ (Icc u v) K) :
    ∃ W : SignedAdjacentWord S, IsRootPathWord Z γ u v W := by
  obtain ⟨W, hW⟩ := exists_isPathWord huv hK.continuousOn hK.injective
  exact ⟨W, K, hK, hW⟩

/-- The path word of a labelling over `[u, w]` is the concatenation of the root path words over
`[u, v]` and `[v, w]`. -/
theorem isPathWord_append (huv : u < v) (hvw : v < w) {K : Fin S → ℝ → ℂ}
    (hK : IsRootLabellingOn Z γ (Icc u w) K) (h₁ : IsRootPathWord Z γ u v W₁)
    (h₂ : IsRootPathWord Z γ v w W₂) : IsPathWord K u w (W₁ ++ W₂) := by
  have k₁ := h₁.isPathWord (hK.mono (Icc_subset_Icc le_rfl hvw.le))
  have k₂ := h₂.isPathWord (hK.mono (Icc_subset_Icc huv.le le_rfl))
  exact k₁.append huv hvw hK.continuousOn hK.injective k₂

/-- **Concatenation** of root path words along a labelled path. -/
theorem append_of_labelling (huv : u < v) (hvw : v < w) {K : Fin S → ℝ → ℂ}
    (hK : IsRootLabellingOn Z γ (Icc u w) K) (h₁ : IsRootPathWord Z γ u v W₁)
    (h₂ : IsRootPathWord Z γ v w W₂) : IsRootPathWord Z γ u w (W₁ ++ W₂) :=
  ⟨K, hK, isPathWord_append huv hvw hK h₁ h₂⟩

/-- **Reversal** of root path words. -/
theorem reverse (h : IsRootPathWord Z γ u v W) :
    IsRootPathWord Z (fun t => γ (u + v - t)) u v (inv W) := by
  obtain ⟨K, hK, hW⟩ := h
  have hmaps : MapsTo (fun t : ℝ => u + v - t) (Icc u v) (Icc u v) := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨fun k t => K k (u + v - t), ⟨fun k => (hK.continuousOn k).comp (by fun_prop) hmaps,
    fun t ht => hK.injective _ (hmaps ht), fun t ht => hK.range_eq _ (hmaps ht)⟩,
    hW.reverse hK.continuousOn hK.injective⟩

/-- **Increasing affine reparametrization** of root path words. -/
theorem comp_affine {φ : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hφ : ∀ t, φ t = α * t + β)
    (h : IsRootPathWord Z γ (φ u) (φ v) W) : IsRootPathWord Z (fun t => γ (φ t)) u v W := by
  obtain ⟨K, hK, hW⟩ := h
  have hmaps : MapsTo φ (Icc u v) (Icc (φ u) (φ v)) := fun t ht => by
    rw [hφ, hφ, hφ]
    exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hφc : Continuous φ := by
    rw [show φ = fun t => α * t + β from funext hφ]; fun_prop
  refine ⟨fun k t => K k (φ t), ⟨fun k => (hK.continuousOn k).comp hφc.continuousOn hmaps,
    fun t ht => hK.injective _ (hmaps ht), fun t ht => hK.range_eq _ (hmaps ht)⟩,
    hW.comp_affine hα hφ⟩

end IsRootPathWord

namespace IsRootFamily

variable {Z : ℂ → Set ℂ} {U : Set ℂ}

/-- **Existence of root path words** along every path in `U`. -/
theorem exists_isRootPathWord (hZ : IsRootFamily Z S U) {γ : ℝ → ℂ} {u v : ℝ} (huv : u < v)
    (hγ : ContinuousOn γ (Icc u v)) (hγU : MapsTo γ (Icc u v) U) :
    ∃ W : SignedAdjacentWord S, IsRootPathWord Z γ u v W := by
  obtain ⟨K, hK⟩ := hZ.exists_path_labelling huv hγ hγU
  exact IsRootPathWord.of_labelling huv hK

/-- **Concatenation** of root path words along a path in `U`. -/
theorem isRootPathWord_append (hZ : IsRootFamily Z S U) {γ : ℝ → ℂ} {u v w : ℝ} (huv : u < v)
    (hvw : v < w) (hγ : ContinuousOn γ (Icc u w)) (hγU : MapsTo γ (Icc u w) U)
    {W₁ W₂ : SignedAdjacentWord S} (h₁ : IsRootPathWord Z γ u v W₁)
    (h₂ : IsRootPathWord Z γ v w W₂) : IsRootPathWord Z γ u w (W₁ ++ W₂) := by
  obtain ⟨K, hK⟩ := hZ.exists_path_labelling (huv.trans hvw) hγ hγU
  exact IsRootPathWord.append_of_labelling huv hvw hK h₁ h₂

/-- **The square relation.** For a map `P` from the unit square to `U`, continuous on the square,
the root path words of its four sides (bottom `t ↦ P (0, t)`, top `t ↦ P (1, t)`, left
`s ↦ P (s, 0)`, right `s ↦ P (s, 1)`) satisfy `bottom · right ≡ left · top`. -/
theorem square_relation (hZ : IsRootFamily Z S U) {P : ℝ × ℝ → ℂ}
    (hP : ContinuousOn P (Icc 0 1 ×ˢ Icc 0 1)) (hPU : MapsTo P (Icc 0 1 ×ˢ Icc 0 1) U)
    {bottom top left right : SignedAdjacentWord S}
    (hb : IsRootPathWord Z (fun t => P (0, t)) 0 1 bottom)
    (ht : IsRootPathWord Z (fun t => P (1, t)) 0 1 top)
    (hl : IsRootPathWord Z (fun s => P (s, 0)) 0 1 left)
    (hr : IsRootPathWord Z (fun s => P (s, 1)) 0 1 right) :
    SignedBraidEquiv (bottom ++ right) (left ++ top) := by
  obtain ⟨L, hLc, hL⟩ := hZ.exists_square_labelling hP hPU
  have hside : ∀ (ψ : ℝ → ℝ × ℝ), Continuous ψ → MapsTo ψ (Icc 0 1) (Icc 0 1 ×ˢ Icc 0 1) →
      IsRootLabellingOn Z (fun t => P (ψ t)) (Icc 0 1) (fun k t => L k (ψ t)) :=
    fun ψ hψ hψm => ⟨fun k => ((hLc k).comp hψ).continuousOn,
      fun t ht => hL.injective _ (hψm ht), fun t ht => hL.range_eq _ (hψm ht)⟩
  have hI : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hI1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have kb := hb.isPathWord (hside (fun t => (0, t)) (by fun_prop) fun t ht => ⟨hI, ht⟩)
  have kt := ht.isPathWord (hside (fun t => (1, t)) (by fun_prop) fun t ht => ⟨hI1, ht⟩)
  have kl := hl.isPathWord (hside (fun s => (s, 0)) (by fun_prop) fun s hs => ⟨hs, hI⟩)
  have kr := hr.isPathWord (hside (fun s => (s, 1)) (by fun_prop) fun s hs => ⟨hs, hI1⟩)
  exact isPathWord_homotopy (H := fun s k t => L k (s, t)) zero_lt_one
    (fun k => (hLc k).continuousOn) (fun s hs t ht => hL.injective _ ⟨hs, ht⟩) kb kt kl kr

end IsRootFamily

end OnLeConjecture.Analytic
