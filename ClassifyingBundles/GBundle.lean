/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.InducingSMul
import ClassifyingBundles.PrincipalBundle

/-! # `G`-structures on fibre bundles
In this file we define `G`-structures on fibre bundles.

Our first main example are vector bundles: every vector bundle with standard fibre `F` is a
`(F →L[𝕜] F)ˣ`-bundle.
-/

open Bundle FiberBundle

variable (G : Type*) [Group G] [TopologicalSpace G]
  (F : Type*) [TopologicalSpace F] {B : Type*} [TopologicalSpace B]
  (E : B → Type*) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (Bundle.TotalSpace F E)]
  [FiberBundle F E] [MulAction G F]

namespace FiberBundle

/-- A (left) `G`-structure on a fibre bundle, given by a system of `G`-valued transition functions.
Note that while this can be though of as a property when `G` acts effectively on the standard fiber
`F`, in general it is data-carrying.
TODO: find better names. -/
class GStructure where
  /-- The `G`-valued transition function on the overlap of two trivialisations `e` and `e'`.
  Takes on junk values outside of `e.baseSet ∩ e'.baseSet`. -/
  g (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e]
    [MemTrivializationAtlas e'] (b : B) : G
  g_mul_g (e e' e'' : Trivialization F (π F E)) [MemTrivializationAtlas e]
    [MemTrivializationAtlas e'] [MemTrivializationAtlas e''] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet ∩ e''.baseSet) : g e e' b * g e' e'' b = g e e'' b
  continuousOn_g : ∀ (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e]
    [MemTrivializationAtlas e'], ContinuousOn (g e e') (e.baseSet ∩ e'.baseSet)
  coordChange_apply_eq_smul (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e]
    [MemTrivializationAtlas e'] {b : B} (hb : b ∈ e.baseSet ∩ e'.baseSet) (x : F) :
    e'.coordChange e b x = g e e' b • x

/-- A typeclass stating that the fibre bundle given by `F` and `E` admits a `G`-structure without
carrying one as data. For faithful / effective actions this distinction does not matter since there
is at most one `G`-structure anyway (at least up to differing junk values), but for e.g. spin
structures that is not the case. -/
class IsGBundle where
  out : Nonempty (GStructure G F E)

protected lemma GStructure.g_eq_one [GStructure G F E] (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {b : B} (hb : b ∈ e.baseSet) : g e e b (G := G) = 1 := by
  simpa using g_mul_g e e e (G := G) ⟨⟨hb, hb⟩, hb⟩

/-- Given a local trivialization `e` of a pullback bundle, `e.unpullback` is a local
trivialization of the original bundle that `e` is the pullback of. -/
noncomputable def _root_.Bundle.Trivialization.unpullback [∀ b, Zero (E b)] {B' : Type*}
    [TopologicalSpace B'] {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B] {f : K}
    (e : Trivialization F (π F (f *ᵖ E))) [MemTrivializationAtlas e] : Trivialization F (π F E) :=
  ‹MemTrivializationAtlas e›.out.choose

instance [∀ b, Zero (E b)] {B' : Type*} [TopologicalSpace B'] {K : Type*} [FunLike K B' B]
    [ContinuousMapClass K B' B] {f : K} (e : Trivialization F (π F (f *ᵖ E)))
    [MemTrivializationAtlas e] : MemTrivializationAtlas e.unpullback :=
  ‹MemTrivializationAtlas e›.out.choose_spec.choose

@[simp]
lemma _root_.Bundle.Trivialization.pullback_unpullback [∀ b, Zero (E b)] {B' : Type*}
    [TopologicalSpace B'] {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B] {f : K}
    (e : Trivialization F (π F (f *ᵖ E))) [MemTrivializationAtlas e] :
    e.unpullback.pullback f = e :=
  ‹MemTrivializationAtlas e›.out.choose_spec.choose_spec.symm

/-- The pullback of a `G`-structure to the pullback bundle along a continuous map. -/
noncomputable instance GStructure.pullback [GStructure G F E] [∀ b, Zero (E b)] {B' : Type*}
    [TopologicalSpace B'] {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B] (f : K) :
    GStructure G F (f *ᵖ E) where
  g e e' he he' b' := g e.unpullback e'.unpullback (G := G) (f b')
  g_mul_g := by sorry
  continuousOn_g := by sorry
  coordChange_apply_eq_smul := by sorry

/-- Every group `G` is a right `G`-torsor under right multiplication. See `Group.toTorsor` for
the analogous instance for left multiplication.
Note: this is currently a bad instance, because the acting group is an `outParam` of `Torsor` and so
`G` shouldn't be a `G`-torsor and `Gᵐᵒᵖ`-torsor at the same time - should it maybe not be
an `outParam`? -/
instance _root_.Group.toOppositeTorsor (G : Type*) [Group G] : Torsor Gᵐᵒᵖ G where
  sdiv g g' := .op (g'⁻¹ * g)
  sdiv_smul' := by simp
  smul_sdiv' := by simp

/-- TODO: figure out how to best connect the APIs for `G`-bundles and `G`-principal bundles.
In textbooks this would be "a `G`-principal bundle is the same thing as a `G`-bundle with standard
fibre `G`", but here the two carry technically different data. -/
@[implicit_reducible]
noncomputable def _root_.PrincipalBundle.toGStructure [TopologicalSpace (Bundle.TotalSpace G E)]
    [FiberBundle G E] [∀ b, Torsor Gᵐᵒᵖ (E b)] [IsPrincipalBundle Gᵐᵒᵖ G E] :
    GStructure G G E where
  g e e' _ _ b := (e (Torsor.nonempty.some : E b)).2 / (e' (Torsor.nonempty.some : E b)).2
  g_mul_g e e' e'' _ _ _ b hb := by simp
  continuousOn_g := by sorry
  coordChange_apply_eq_smul := by sorry

section Faithful

variable [FaithfulSMul G F]

/-- When `G` acts faithfully, every set of continuous `G`-valued transition functions can be
assembled into a `G`-structure: compatibility on triple intersections follows automatically. -/
@[implicit_reducible] def GStructure.mkOfFaithful (g : ∀ (e e' : Trivialization F (π F E))
      [MemTrivializationAtlas e] [MemTrivializationAtlas e'], B → G)
    (hg : ∀ (e e' : _) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ContinuousOn (g e e') (e.baseSet ∩ e'.baseSet))
    (hg' : ∀ (e e' : _) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ∀ b ∈ e.baseSet ∩ e'.baseSet, ∀ x : F, e'.coordChange e b x = g e e' b • x) :
    GStructure G F E where
  g := g
  g_mul_g e e' e'' _ _ _ b hb := by
    refine FaithfulSMul.eq_of_smul_eq_smul fun x : F ↦ ?_
    rw [mul_smul, ← hg' e' e'' b ⟨hb.1.2, hb.2⟩, ← hg' e e' b hb.1, ← hg' e e'' b ⟨hb.1.1, hb.2⟩]
    exact Trivialization.coordChange_coordChange _ _ _ hb.2 hb.1.2 x
  continuousOn_g := hg
  coordChange_apply_eq_smul := hg'

/-- When `G` acts faithfully, `E` admits a `G`-structure iff between any two local trivialisations
there exists a continuous `G`-valued transition map. -/
lemma isGBundle_iff_of_faithful : IsGBundle G F E ↔
    ∀ (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ∃ g : B → G, ContinuousOn g (e.baseSet ∩ e'.baseSet) ∧
        ∀ b ∈ e.baseSet ∩ e'.baseSet, ∀ x : F, e'.coordChange e b x = g b • x := by
  refine ⟨fun ⟨⟨_⟩⟩ e e' _ _ ↦ ⟨GStructure.g e e', GStructure.continuousOn_g e e',
    fun b hb x ↦ GStructure.coordChange_apply_eq_smul e e' hb x⟩, fun h ↦ ⟨⟨?_⟩⟩⟩
  exact .mkOfFaithful G F E (fun e e' _ _ ↦ (h e e').choose)
    (fun e e' _ _ ↦ (h e e').choose_spec.1) (fun e e' _ _ ↦ (h e e').choose_spec.2)

lemma _root_.Bundle.Trivialization.continuousOn_coordChange {B : Type*} {F : Type*}
    {Z : Type*} [TopologicalSpace B] [TopologicalSpace F] {proj : Z → B} [TopologicalSpace Z]
    (e e' : Trivialization F proj) :
    ContinuousOn (fun x : B × F ↦ e.coordChange e' x.1 x.2)
      ((e.baseSet ∩ e'.baseSet) ×ˢ .univ) := by
  unfold Trivialization.coordChange
  apply continuous_snd.comp_continuousOn ?_
  refine e'.toOpenPartialHomeomorph.continuousOn.comp ?_ fun x hx ↦ by
    rw [Set.inter_prod] at hx
    rw [e'.source_eq, Set.mem_preimage, e.proj_symm_apply (e.target_eq ▸ hx).1]
    exact hx.2.1
  refine e.toOpenPartialHomeomorph.symm.continuousOn.mono ?_
  rw [e.symm_source, e.target_eq]
  exact Set.prod_mono_left <| Set.inter_subset_left

/-- When `G` acts faithfully and the topology on it is induced by the action map to `C(F, F)`,
every set of `G`-valued transition functions can be assembled into a `G`-structure:
continuity and compatibility on triple intersections follows automatically. -/
@[implicit_reducible] def GStructure.mkOfInducing [InducingSMul G F] [LocallyCompactSpace F]
    (g : ∀ (e e' : Trivialization F (π F E))
      [MemTrivializationAtlas e] [MemTrivializationAtlas e'], B → G)
    (hg : ∀ (e e' : _) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ∀ b ∈ e.baseSet ∩ e'.baseSet, ∀ x : F, e'.coordChange e b x = g e e' b • x) :
    GStructure G F E where
  g := g
  g_mul_g e e' e'' _ _ _ b hb := by
    refine FaithfulSMul.eq_of_smul_eq_smul fun x : F ↦ ?_
    rw [mul_smul, ← hg e' e'' b ⟨hb.1.2, hb.2⟩, ← hg e e' b hb.1, ← hg e e'' b ⟨hb.1.1, hb.2⟩]
    exact Trivialization.coordChange_coordChange _ _ _ hb.2 hb.1.2 x
  continuousOn_g e e' _ _ := by
    rw [InducingSMul.continuousOn_iff (X := F)]
    refine .congr (f := fun x ↦ e'.coordChange e x.1 x.2) ?_ fun x hx ↦ (hg e e' x.1 hx.1 _).symm
    rw [Set.inter_comm]
    exact e'.continuousOn_coordChange e
  coordChange_apply_eq_smul := hg

/-- When `G` acts faithfully and the topology on it is induced by the action map to `C(F, F)`,
`E` admits a `G`-structure iff the transition map between any two local trivializations can at any
point be written as the action of some `g : G`. -/
lemma isGBundle_iff_of_inducing [InducingSMul G F] [LocallyCompactSpace F] : IsGBundle G F E ↔
    ∀ (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ∀ b ∈ e.baseSet ∩ e'.baseSet, ∃ g : G, ∀ x : F, e'.coordChange e b x = g • x := by
  refine ⟨fun ⟨⟨_⟩⟩ e e' _ _ b hb ↦
    ⟨GStructure.g e e' b, GStructure.coordChange_apply_eq_smul e e' hb⟩, fun h ↦ ⟨⟨?_⟩⟩⟩
  classical
  refine .mkOfInducing G F E
    (fun e e' _ _ b ↦ if hb : b ∈ e.baseSet ∩ e'.baseSet then (h e e' b hb).choose else 1)
    fun e e' _ _ b hb x ↦ ?_
  simpa [hb] using (h e e' b hb).choose_spec x

/-- Every vector bundle is a `(F →L[𝕜] F)ˣ`-bundle.

The converse is true mathematically, but can't usefully be stated here for technical reasons:
`IsGBundle (F →L[𝕜] F)ˣ F E` only requires a vector space structure on `F`, while
`VectorBundle 𝕜 F E` also requires compatible vector space structures on all fibres `E b`.
The assumption of these being compatible with the vector space structure on `F` already implies
that the bundle is a vector bundle, so there is not point in assuming that and then stating that
`IsGBundle (F →L[𝕜] F)ˣ F E` implies `VectorBundle 𝕜 F E`. -/
instance {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [LocallyCompactSpace 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace 𝕜 (E b)]
    [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E] :
    IsGBundle (F →L[𝕜] F)ˣ F E := by
  have := LocallyCompactSpace.of_finiteDimensional_of_complete 𝕜 F
  refine (isGBundle_iff_of_inducing _ F E).2 fun e e' _ _ b hb ↦
    ⟨(e'.coordChangeL 𝕜 e b).toUnit, fun x ↦ ?_⟩
  simp [Units.smul_def, ContinuousLinearEquiv.toUnit, e'.coordChangeL_apply' e ⟨hb.2, hb.1⟩ x,
    Trivialization.coordChange]

end Faithful

end FiberBundle
