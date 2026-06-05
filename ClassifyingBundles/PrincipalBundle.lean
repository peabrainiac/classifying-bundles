/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.ContinuousSection
import ClassifyingBundles.ContinuousBundleActionHom
import ClassifyingBundles.MulActionEquiv
import Mathlib.Topology.ContinuousMap.Algebra

/-! # `G`-principal bundles

Mathematically, a `G`-principal bundle for a topological group `G` is a fiber bundle `p : E → B`
with generic fiber `G` and a continuous `G`-action on `E` that preserves the fibers of `p` and turns
them into topological `G`-torsors. Equivalently, `G`-principal bundles can also be defined as
fiber bundles with generic fiber a `G`-torsor `F` and a bundle atlas for which all changes of charts
are `G`-equivariant. In this sense, `G`-principal bundles are to `G`-torsors as vector bundles are
to vector spaces.

In this file, we formalize `G`-principal bundles using the second definition: to avoid the
type-theoretical difficulties that come from restricting a global `G`-action to individual fibers,
we instead start with a bundle `E : B → Type*` whose fibers `E b` are `G`-torsors and assemble a
`G`-action on the total space from that. Hence, for our purposes a `G`-principal bundle is a
bundle of `G`-torsors equipped with a bundle atlas with `G`-equivariant changes of charts.
-/

open Bundle FiberBundle

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (F : Type*) [TopologicalSpace F] {B : Type*} [TopologicalSpace B]
  (E : B → Type*) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (Bundle.TotalSpace F E)]

variable {F E}

/-- Typeclass stating that a local trivialization of a bundle is equivariant with respect
to actions on its fibers and the model fiber. -/
class Bundle.Trivialization.IsEquivariant [SMul G F] [∀ b, SMul G (E b)]
    (e : Trivialization F (π F E)) where
  map_smul {b : B} (hb : b ∈ e.baseSet) {g : G} {x : E b} : (e ⟨_, g • x⟩).2 = g • (e ⟨_, x⟩).2

variable {G}

-- TODO: get rid of unnecessary `∀ b, Zero (E b)` condition imposed by `Trivialization.symm`
variable [∀ b, Zero (E b)]

/-- The bijection between `E b` and the model fiber `F` as an isomorphism of torsors. -/
noncomputable def Bundle.Trivialization.mulActionEquivAt (e : Trivialization F (π F E))
    [SMul G F] [∀ b, SMul G (E b)] [e.IsEquivariant G] {b : B} (hb : b ∈ e.baseSet) :
    E b ≃[G] F where
  toFun x := (e ⟨_, x⟩).2
  invFun := e.symm b
  left_inv := e.symm_apply_apply_mk hb
  right_inv x := by simp_rw [e.apply_mk_symm hb x]
  map_smul' g x := IsEquivariant.map_smul hb

open Classical in
/-- The coordinate change function between two trivialisations, as an equivariant automorphism of
the model fiber `F`. Defined to be the identity when `b` does not lie in both trivializations. -/
noncomputable def Bundle.Trivialization.coordChangeₑ (e e' : Trivialization F (π F E))
    [SMul G F] [∀ b, SMul G (E b)] [e.IsEquivariant G] [e'.IsEquivariant G] (b : B) :
    F ≃[G] F :=
  if hb : b ∈ e.baseSet ∩ e'.baseSet then
    (e.mulActionEquivAt hb.1).symm.trans (e'.mulActionEquivAt hb.2) else .refl G F

variable [FiberBundle F E] [Torsor G F] [IsTopologicalTorsor F]
    [∀ b, Torsor G (E b)] [∀ b, IsTopologicalTorsor (E b)]

variable (G F E) in
/-- A (left) `G`-principal bundle is a fiber bundle whose standard fiber `F` and fibers `E b` are
`G`-torsors, and whose bundle atlas has the property that changes of charts are `G`-equivariant.

Note that in this definition we have `G` acting on the left; under the usual convention that
`G`-principal bundles are acted on from the right, this is really a `Gᵐᵒᵖ`-principal bundle.
`G`-principal bundles are instead captured by `IsPrincipalBundle Gᵐᵒᵖ F E`. -/
class IsPrincipalBundle : Prop where
  trivialization_equivariant (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    e.IsEquivariant G

attribute [instance] IsPrincipalBundle.trivialization_equivariant

omit [IsTopologicalGroup G] [∀ (b : B), IsTopologicalTorsor (E b)] in
lemma Bundle.Trivialization.continuousOn_coordChangeₑ [IsPrincipalBundle G F E]
    (e : Trivialization F (π F E)) (e' : Trivialization F (π F E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
      ContinuousOn (coordChangeₑ (G := G) e e') (e.baseSet ∩ e'.baseSet) := by
  have z : F := Torsor.nonempty.some
  refine ((MulActionEquiv.evalHomeo z).comp_continuousOn_iff _ _).1 ?_
  refine .congr (f := fun x ↦ (e' ⟨x, e.symm x z⟩).2) ?_ fun x hx ↦ by
    simp [coordChangeₑ, hx, mulActionEquivAt]; rfl
  refine continuous_snd.comp_continuousOn ?_
  refine e'.continuousOn.comp ?_ fun x ↦ by simp [e'.source_eq]
  refine .mono ?_ Set.inter_subset_left
  exact e.continuousOn_symm.comp (f := fun x ↦ (x, z)) (by fun_prop) (by intro; simp)

/-- The action of `G` on the total space on any `G`-principal bundle is continuous. -/
instance [IsPrincipalBundle G F E] : ContinuousSMul G (TotalSpace F E) where
  continuous_smul := by
    suffices h : ∀ b, ContinuousOn (fun x : G × TotalSpace F E ↦ x.1 • x.2)
        (.univ ×ˢ (π F E ⁻¹' (trivializationAt F E b).baseSet)) from
      continuous_iff_continuousAt.2 fun ⟨g, x⟩ ↦ (h x.1).continuousAt <|
        prod_mem_nhds Filter.univ_mem <| ((trivializationAt F E x.1).open_baseSet.preimage <|
          continuous_proj F E).mem_nhds <| mem_baseSet_trivializationAt F E _
    refine fun b ↦ .congr (f := fun x ↦ ⟨_, (trivializationAt F E b).symm x.2.1
        (x.1 • (trivializationAt F E b x.2).2)⟩) ?_ fun ⟨g, x⟩ ⟨_, hx⟩ ↦ by
      ext
      · rfl
      · simp only [heq_eq_eq, ← Trivialization.IsEquivariant.map_smul hx]
        exact ((trivializationAt F E b).symm_proj_apply ⟨x.1, g • x.2⟩ hx).symm
    refine (trivializationAt F E b).continuousOn_symm.comp
      (f := (fun x : G × TotalSpace F E ↦ ⟨x.2.1, x.1 • (trivializationAt F E b x.2).2⟩)) ?_ ?_
    · refine ((continuous_proj F E).comp continuous_snd).continuousOn.prodMk ?_
      refine continuous_smul.comp_continuousOn ?_
        (f := fun x : G × TotalSpace F E ↦ (x.1, (trivializationAt F E b x.2).2))
      refine continuousOn_id.prodMap (g := fun x ↦ (trivializationAt F E b x).2) ?_
      refine continuous_snd.comp_continuousOn ?_
      rw [← (trivializationAt F E b).source_eq]
      exact (trivializationAt F E b).continuousOn
    · exact fun ⟨g, x⟩ ⟨_, hx⟩ ↦ ⟨hx, trivial⟩

namespace Bundle.ContinuousSection

/-- For any `G`-principal bundle `E`, `G` acts on the type `Cₛ⟮F, E⟯` of continuous sections of `E`.
TODO: show this more generally for fibre bundles with a continuous fiberwise `G`-action. -/
@[simps]
instance [IsPrincipalBundle G F E] : SMul G Cₛ⟮F, E⟯ where
  smul g s := ⟨fun b ↦ g • s b, s.continuous.const_smul g⟩

/-- For any `G`-principal bundle `E` over `B`, `B → G` acts on the type `Cₛ⟮F, E⟯` of continuous
sections of `E`.
TODO: show this more generally for fibre bundles with a continuous fiberwise `G`-action. -/
instance [IsPrincipalBundle G F E] : SMul C(B, G) Cₛ⟮F, E⟯ where
  smul f s := ⟨fun b ↦ f b • s b, f.continuous.smul s.continuous⟩

omit [IsTopologicalGroup G] [∀ (b : B), IsTopologicalTorsor (E b)] in
/-- Note: this should be an `@[simps]`-lemma, but couldn't because the auto-generated name
`smul_toFun` was already taken. -/
@[simp]
lemma smul_toFun' [IsPrincipalBundle G F E] (f : C(B, G)) (s : Cₛ⟮F, E⟯) (b : B) :
    (f • s) b = f b • s b := rfl

instance [IsPrincipalBundle G F E] : IsScalarTower G C(B, G) Cₛ⟮F, E⟯ where
  smul_assoc g f s := by ext; simp [smul_smul]

@[simps]
instance [IsPrincipalBundle G F E] : SDiv C(B, G) Cₛ⟮F, E⟯ where
  sdiv s t := ⟨fun b ↦ s b /ₛ t b, by
    suffices h : ∀ b, ContinuousOn (fun b' ↦ s b' /ₛ t b') (trivializationAt F E b).baseSet from
      continuous_iff_continuousAt.2 fun b ↦ (h b).continuousAt <|
        (trivializationAt F E b).open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E b
    refine fun b ↦ .congr (f := fun b' ↦ (trivializationAt F E b ⟨_, s b'⟩).2 /ₛ
      (trivializationAt F E b ⟨_, t b'⟩).2) ?_ fun b' hb' ↦
        trivializationAt F E b|>.mulActionEquivAt hb'|>.map_sdiv_map (s b') (t b')|>.symm
    refine .sdiv (continuous_snd.comp_continuousOn ?_) (continuous_snd.comp_continuousOn ?_)
    · exact (trivializationAt F E b).continuousOn.comp s.continuous.continuousOn fun b' ↦ by
        simp [Bundle.Trivialization.mem_source]
    · exact (trivializationAt F E b).continuousOn.comp t.continuous.continuousOn fun b' ↦ by
        simp [Bundle.Trivialization.mem_source]⟩

/-- For any `G`-principal bundle `E` over `B`, the type `Cₛ⟮F, E⟯` of continuous sections of `E` is
a `(B → G)`-torsor if it isn't empty.
TODO: define a class `Pretorsor` for not necessarily empty torsors, and show that this is one? -/
instance [IsPrincipalBundle G F E] [Nonempty Cₛ⟮F, E⟯] : Torsor C(B, G) Cₛ⟮F, E⟯ where
  mul_smul f f' s := by ext; simp [smul_smul]
  one_smul s := by ext; simp
  sdiv_smul' s t := by ext; simp
  smul_sdiv' f s := by ext; simp

end Bundle.ContinuousSection

section Pullback

instance Bundle.Trivialization.IsEquivariant.pullback {B' : Type*} [TopologicalSpace B']
    {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B] {f : K} (e : Trivialization F (π F E))
    [e.IsEquivariant G] : (e.pullback f).IsEquivariant G where
  map_smul {b} hb {g x} :=
    Trivialization.IsEquivariant.map_smul (by simpa using hb : f b ∈ e.baseSet)

instance {B' : Type*} {f : B' → B} {b' : B'} [Torsor G (E (f b'))] : Torsor G ((f *ᵖ E) b') :=
  inferInstanceAs (Torsor G (E (f b')))

/-- Pullbacks of `G`-principal bundles along continuous maps are `G`-principal bundles. -/
instance IsPrincipalBundle.pullback [IsPrincipalBundle G F E] {B' : Type*} [TopologicalSpace B']
    {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B] {f : K} :
    IsPrincipalBundle G F (f *ᵖ E) where
  trivialization_equivariant e he := by
    obtain ⟨⟨e, he, rfl⟩⟩ := he
    exact (trivialization_equivariant e).pullback

end Pullback
