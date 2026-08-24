/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.IsFiberBundle
import Mathlib.Topology.Algebra.Group.Torsor
import Mathlib.Topology.Algebra.ProperAction.Basic

/-! # Locally trivial `G`-spaces
In this file we define locally trivial `G`-spaces: a `G`-space is called locally trivial if its
projection to is orbit space locally admits equivariant trivialisations. In this sense locally
trivial `G`-spaces are just `G`-principal bundles, represented by the `G`-action on their orbit
space.

## Main definitions & results
* `LocallyTrivialSMul G X`: typeclass stating that a `G`-space `X` is locally trivial in the sense
  that `Quotient.mk _ : X → Quotient (MulAction.orbitRel G X)` admits `G`-equivariant
  trivializations around each point
* Every locally trivial action is continuous and free
* Any free and proper action is locally trivial if and only if the projection to its orbit space
  admits sections around each point.

## TODO
* Prove that locally trivial `G`-spaces are proper if and only if their orbit spaces are Hausdorff
-/

open Bundle Topology

/-- A `G`-space `X` is called locally trivial if its projection to its orbit space
locally admits `G`-equivariant trivialisations. -/
class LocallyTrivialSMul (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type*) [TopologicalSpace X] [MulAction G X] : Prop where
  exists_equivariant_trivialization b :
    ∃ e : Trivialization G (Quotient.mk (MulAction.orbitRel G X)), b ∈ e.baseSet ∧ e.IsEquivariant G

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X : Type*} [TopologicalSpace X] [MulAction G X]

lemma LocallyTrivialSMul.isFiberBundleMap_quotientMk [LocallyTrivialSMul G X] :
    IsFiberBundleMap G (Quotient.mk (MulAction.orbitRel G X)) where
  exists_trivialization' b := by
    have ⟨e, he, he'⟩ := LocallyTrivialSMul.exists_equivariant_trivialization b
    exact ⟨e, he⟩

/-- Every locally trivial `G`-action is in particular free. -/
instance LocallyTrivialSMul.isCancelSMul [LocallyTrivialSMul G X] : IsCancelSMul G X where
  right_cancel' g g' x h := by
    have ⟨e, hx, he⟩ := LocallyTrivialSMul.exists_equivariant_trivialization (G := G) ⟦x⟧
    replace hx : x ∈ e.source := by simpa [e.source_eq] using hx
    simpa [he.map_smul hx] using congrArg (fun x ↦ (e x).2) h

/-- TODO: move -/
@[fun_prop]
lemma continuous_quotientMk {X : Type*} [TopologicalSpace X] {s : Setoid X} :
    Continuous (Quotient.mk s) :=
  continuous_quotient_mk'

/-- TODO: move -/
@[fun_prop]
lemma isQuotientMap_quotientMk {X : Type*} [TopologicalSpace X] {s : Setoid X} :
    IsQuotientMap (Quotient.mk s) :=
  isQuotientMap_quotient_mk'

/-- Every locally trivial `G`-action is in particular continuous. -/
instance [LocallyTrivialSMul G X] : ContinuousSMul G X where
  continuous_smul := by
    choose e he he' using LocallyTrivialSMul.exists_equivariant_trivialization (G := G) (X := X)
    suffices h : ∀ b, ContinuousOn (fun x : G × X ↦ x.1 • x.2)
        (.univ ×ˢ (Quotient.mk _ ⁻¹' (e b).baseSet)) from
      continuous_iff_continuousAt.2 fun ⟨g, x⟩ ↦ (h ⟦x⟧).continuousAt <| prod_mem_nhds
        Filter.univ_mem <| ((e ⟦x⟧).open_baseSet.preimage <| by fun_prop).mem_nhds <| he ⟦x⟧
    refine fun b ↦ ?_
    have := (e b).toOpenPartialHomeomorph.symm
    refine .congr (f := fun x ↦ (e b).toOpenPartialHomeomorph.symm ⟨⟦x.2⟧, x.1 • (e b x.2).2⟩)
        ?_ fun ⟨g, x⟩ ⟨_, hx⟩ ↦ by
      simp [(e b).isEquivariant_iff_symm.1 (he' b) ⟦x⟧ (by simpa using hx),
        show x ∈ (e b).source by simpa [(e b).source_eq] using hx, -smul_eq_mul]
    refine (e b).toOpenPartialHomeomorph.continuousOn_symm.comp ?_ ?_
    · refine (continuous_quotientMk.comp continuous_snd).continuousOn.prodMk ?_
      refine continuous_smul.comp_continuousOn ?_
        (f := fun x : G × X ↦ (x.1, (e b x.2).2))
      refine continuousOn_id.prodMap (g := fun x ↦ (e b x).2) ?_
      refine continuous_snd.comp_continuousOn ?_
      rw [← (e b).source_eq]
      exact (e b).toOpenPartialHomeomorph.continuousOn
    · exact fun ⟨g, x⟩ ⟨_, hx⟩ ↦ by simpa [(e b).target_eq] using hx

/-- TODO: remove next time mathlib is bumped -/
@[to_additive (attr := simp)]
lemma MulAction.orbitRel.Quotient.quotient_smul_eq {G α : Type*} [Group G] [MulAction G α]
    {g : G} {a : α} : ⟦g • a⟧ = (⟦a⟧ : orbitRel.Quotient G α) :=
  Quotient.eq.mpr ⟨g, rfl⟩

lemma IsCancelSMul.smul_pair_injective {G X : Type*} [Group G] [MulAction G X] [IsCancelSMul G X] :
    Function.Injective (fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) := by
  simp_rw [Function.Injective, Prod.ext_iff]
  rintro ⟨g, x⟩ ⟨g', x'⟩ ⟨h, rfl⟩
  simpa using IsCancelSMul.right_cancel _ _ _ h

/-- For any free and proper group action, the shear map `G × X → X × X` is a closed embedding.

TODO: move -/
lemma ProperSMul.isClosedEmbedding_smul_pair {G X : Type*} [TopologicalSpace G] [TopologicalSpace X]
    [Group G] [MulAction G X] [IsCancelSMul G X] [ProperSMul G X] :
    IsClosedEmbedding (fun gx : G × X ↦ (gx.1 • gx.2, gx.2)) :=
  .of_continuous_injective_isClosedMap (by fun_prop) IsCancelSMul.smul_pair_injective
    ProperSMul.isProperMap_smul_pair.isClosedMap

/-- TODO: move -/
lemma continuousOn_prodMk {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} {g : X → Z} {s : Set X} :
    ContinuousOn (fun x ↦ (f x, g x)) s ↔ ContinuousOn f s ∧ ContinuousOn g s :=
  ⟨fun h ↦ ⟨continuous_fst.comp_continuousOn h, continuous_snd.comp_continuousOn h⟩,
    fun h ↦ h.1.prodMk h.2⟩

/-- A free and proper `G`-space is locally trivial if and only if the projection to its orbit space
locally admits sections. -/
lemma locallyTrivialSMul_iff_exists_section [IsCancelSMul G X] [ProperSMul G X] :
    LocallyTrivialSMul G X ↔ ∀ b : Quotient (MulAction.orbitRel G X), ∃ u, IsOpen u ∧ b ∈ u ∧
      ∃ s : _ → X, u.EqOn (Quotient.mk'' ∘ s) id ∧ ContinuousOn s u := by
  refine ⟨fun h b ↦ ?_, fun h ↦ ⟨fun b ↦ ?_⟩⟩
  · have ⟨e, he⟩ := h.isFiberBundleMap_quotientMk.exists_trivialization b
    refine ⟨e.baseSet, e.open_baseSet, he, fun x' ↦ e.toOpenPartialHomeomorph.symm (x', 1),
      fun x' hx' ↦ ?_, e.continuousOn_symm_prodMk_left⟩
    simp [Quotient.mk'', e.proj_symm_apply' hx']
  · have ⟨u, hu, hbu, s, hs, hs'⟩ := h b
    classical
    refine ⟨{
      toFun x := ⟨⟦x⟧, if hx : ⟦x⟧ ∈ u then
          (MulAction.mem_orbit_iff.1 (MulAction.orbitRel.Quotient.mem_orbit.2 (hs hx).symm)).choose
        else 1⟩
      invFun x := x.2 • s x.1
      source := Quotient.mk _ ⁻¹' u
      target := u ×ˢ Set.univ
      map_source' x hx := by simpa using hx
      map_target' x hx := by simp [show ⟦s x.1⟧ = x.1 by simpa using hs hx.1, hx.1]
      left_inv' x hx := by
        simpa [Set.mem_preimage.1 hx] using Exists.choose_spec (p := fun g ↦ g • s ⟦x⟧ = x) _
      right_inv' x hx := by
        simp only [show ⟦s x.1⟧ = x.1 by simpa using hs hx.1, hx.1,
          MulAction.orbitRel.Quotient.quotient_smul_eq, ↓reduceDIte]
        exact Prod.ext rfl <| IsCancelSMul.right_cancel _ _ (s x.1) <|
          Exists.choose_spec (p := fun g : G ↦ g • s x.1 = x.2 • s x.1) _
      open_source := hu.preimage <| by fun_prop
      open_target := hu.prod isOpen_univ
      continuousOn_toFun := by
        refine .prodMk (by fun_prop) ?_
        rw [← continuousOn_prodMk.trans <| and_iff_left <|
            hs'.comp continuous_quotientMk.continuousOn <| Set.mapsTo_preimage _ _,
          ProperSMul.isClosedEmbedding_smul_pair.continuousOn_iff]
        refine (continuousOn_id.congr fun x hx ↦ ?_).prodMk <| hs'.comp (by fun_prop) fun _ hx ↦ hx
        simpa [Set.mem_preimage.1 hx] using Exists.choose_spec (p := fun g : G ↦ g • s ⟦x⟧ = x) _
      continuousOn_invFun := continuousOn_snd.smul <| hs'.comp continuousOn_fst fun x hx ↦ hx.1
      baseSet := u
      open_baseSet := hu
      source_eq := rfl
      target_eq := rfl
      proj_toFun := by simp }, ?_, ?_⟩
    · simp [hbu]
    · simp [Trivialization.isEquivariant_iff_symm, smul_smul]
