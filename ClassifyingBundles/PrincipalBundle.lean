/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.ContinuousBundleActionHom
import ClassifyingBundles.MulActionEquiv
import ClassifyingBundles.NumerableBundle

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

open Bundle FiberBundle unitInterval

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

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [(b : B) → TopologicalSpace (E b)]
  [(b : B) → Zero (E b)] in
lemma Bundle.Trivialization.map_smul (e : Trivialization F (π F E))
    [SMul G F] [∀ b, SMul G (E b)] [e.IsEquivariant G] {b : B} (hb : b ∈ e.baseSet)
    {g : G} {x : E b} : (e ⟨_, g • x⟩).2 = g • (e ⟨_, x⟩).2 :=
  IsEquivariant.map_smul hb

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [(b : B) → TopologicalSpace (E b)] in
lemma Bundle.Trivialization.symm_map_smul (e : Trivialization F (π F E))
    [SMul G F] [∀ b, SMul G (E b)] [e.IsEquivariant G] {b : B} (hb : b ∈ e.baseSet)
    {g : G} {x : F} : e.symm b (g • x) = g • e.symm b x :=
  (e.mulActionEquivAt hb).symm.map_smul g x

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

/-- For any `G`-principal bundle `E` over `B`, `C(B, G)` acts on the type `Cₛ⟮F, E⟯` of continuous
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

omit [IsTopologicalGroup G] [∀ b, IsTopologicalTorsor (E b)] in
attribute [local simp] Trivialization.source_eq mem_baseSet_trivializationAt in
lemma _root_.ContinuousWithinAt.section_sdiv [IsPrincipalBundle G F E] {s t : ∀ b, E b} {u : Set B}
    {b : B} (hs : ContinuousWithinAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u b)
    (ht : ContinuousWithinAt (fun b ↦ (⟨b, t b⟩ : TotalSpace F E)) u b) :
    ContinuousWithinAt (fun b ↦ s b /ₛ t b) u b := by
  refine .mono_of_mem_nhdsWithin ?_ <| inter_mem_nhdsWithin _ <|
    (trivializationAt F E b).open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F E b
  refine .congr (f := fun b' ↦ (trivializationAt F E b ⟨_, s b'⟩).2 /ₛ
    (trivializationAt F E b ⟨_, t b'⟩).2) ?_ (fun b' hb' ↦ ?_) ?_
  · refine .sdiv (continuous_snd.continuousAt.comp_continuousWithinAt ?_)
      (continuous_snd.continuousAt.comp_continuousWithinAt ?_)
    · exact (trivializationAt F E b).continuousOn _ (by simp)
        |>.comp (hs.mono Set.inter_subset_left) fun x hx ↦ by simp [hx.2]
    · exact (trivializationAt F E b).continuousOn _ (by simp)
        |>.comp (ht.mono Set.inter_subset_left) fun x hx ↦ by simp [hx.2]
  · exact trivializationAt F E b |>.mulActionEquivAt hb'.2 |>.map_sdiv_map (s _) (t _) |>.symm
  · exact trivializationAt F E b |>.mulActionEquivAt (by simp) |>.map_sdiv_map (s b) (t b) |>.symm

omit [IsTopologicalGroup G] [∀ b, IsTopologicalTorsor (E b)] in
lemma _root_.ContinuousAt.section_sdiv [IsPrincipalBundle G F E] {s t : ∀ b, E b} {b : B}
    (hs : ContinuousAt (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) b)
    (ht : ContinuousAt (fun b ↦ (⟨b, t b⟩ : TotalSpace F E)) b) :
    ContinuousAt (fun b ↦ s b /ₛ t b) b := by
  rw [← continuousWithinAt_univ] at hs ht ⊢
  exact hs.section_sdiv ht

omit [IsTopologicalGroup G] [∀ b, IsTopologicalTorsor (E b)] in
lemma _root_.ContinuousOn.section_sdiv [IsPrincipalBundle G F E] {s t : ∀ b, E b} {u : Set B}
    (hs : ContinuousOn (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) u)
    (ht : ContinuousOn (fun b ↦ (⟨b, t b⟩ : TotalSpace F E)) u) :
    ContinuousOn (fun b ↦ s b /ₛ t b) u :=
  fun b hb ↦ (hs b hb).section_sdiv (ht b hb)

omit [IsTopologicalGroup G] [∀ b, IsTopologicalTorsor (E b)] in
lemma _root_.Continuous.section_sdiv [IsPrincipalBundle G F E] {s t : ∀ b, E b}
    (hs : Continuous (fun b ↦ (⟨b, s b⟩ : TotalSpace F E)))
    (ht : Continuous (fun b ↦ (⟨b, t b⟩ : TotalSpace F E))) :
    Continuous (fun b ↦ s b /ₛ t b) := by
  rw [← continuousOn_univ] at hs ht ⊢
  exact hs.section_sdiv ht

@[simps]
instance [IsPrincipalBundle G F E] : SDiv C(B, G) Cₛ⟮F, E⟯ where
  sdiv s t := ⟨fun b ↦ s b /ₛ t b, s.continuous.section_sdiv t.continuous⟩

/-- For any `G`-principal bundle `E` over `B`, the type `Cₛ⟮F, E⟯` of continuous sections of `E` is
a `C(B, G)`-torsor if it isn't empty.
TODO: define a class `Pretorsor` for not necessarily empty torsors, and show that this is one? -/
instance [IsPrincipalBundle G F E] [Nonempty Cₛ⟮F, E⟯] : Torsor C(B, G) Cₛ⟮F, E⟯ where
  mul_smul f f' s := by ext; simp [smul_smul]
  one_smul s := by ext; simp
  sdiv_smul' s t := by ext; simp
  smul_sdiv' f s := by ext; simp

end Bundle.ContinuousSection

namespace ContinuousBundleHom

variable (F' : Type*) [TopologicalSpace F'] {B' : Type*} [TopologicalSpace B']
  (E' : B' → Type*) [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (Bundle.TotalSpace F' E')]
  [FiberBundle F' E'] (f : C(B', B))

/-- For any `G`-principal bundle `E` and any other fibre bundle `E'`, `G` acts on the type
`Cᶠ⟮F', E'; F, E⟯` of continuous fibrewise maps from `E'` to `E`.
TODO: show this more generally for fibre bundles with a continuous fiberwise `G`-action. -/
@[simps]
instance [IsPrincipalBundle G F E] : SMul G Cᶠ[f]⟮F', E'; F, E⟯ where
  smul g f' := ⟨fun b x ↦ g • f' b x, f'.continuous_toFun.const_smul g⟩

/-- For any `G`-principal bundle `E` over `B` and any other fibre bundle `E'`,
`C(B', G)` acts on the type `Cᶠ[f]⟮F', E'; F, E⟯` of continuous fibrewise maps from `E'` to `E`.
TODO: show this more generally for fibre bundles with a continuous fiberwise `G`-action. -/
instance [IsPrincipalBundle G F E] : SMul C(B', G) Cᶠ[f]⟮F', E'; F, E⟯ where
  smul f' f'' := ⟨fun b x ↦ f' b • f'' b x,
    f'.continuous.comp (continuous_proj F' E') |>.smul f''.continuous_toFun⟩

/-- For any `G`-principal bundle `E` over `B` and any other fibre bundle `E'`,
`C(TotalSpace B' E', G)` acts on the type `Cᶠ[f]⟮F', E'; F, E⟯` of continuous fibrewise maps from
`E'` to `E`.
TODO: show this more generally for fibre bundles with a continuous fiberwise `G`-action. -/
instance [IsPrincipalBundle G F E] : SMul C(TotalSpace F' E', G) Cᶠ[f]⟮F', E'; F, E⟯ where
  smul f' f'' := ⟨fun b x ↦ f' ⟨b, x⟩ • f'' b x, f'.continuous.smul f''.continuous_toFun⟩

omit [IsTopologicalGroup G] [∀ (b : B), IsTopologicalTorsor (E b)] in
/-- Note: this should be an `@[simps]`-lemma, but couldn't because the auto-generated name
`smul_toFun` was already taken. -/
@[simp]
lemma smul_toFun' [IsPrincipalBundle G F E] (f' : C(B', G)) (f'' : Cᶠ[f]⟮F', E'; F, E⟯) (b : B') :
    (f' • f'') b = f' b • f'' b := rfl

omit [IsTopologicalGroup G] [∀ (b : B), IsTopologicalTorsor (E b)] [TopologicalSpace F']
  [(b : B') → TopologicalSpace (E' b)] [FiberBundle F' E'] in
/-- Note: this should be an `@[simps]`-lemma, but couldn't because the auto-generated name
`smul_toFun` was already taken. -/
@[simp]
lemma smul_toFun'' [IsPrincipalBundle G F E] (f' : C(TotalSpace F' E', G))
    (f'' : Cᶠ[f]⟮F', E'; F, E⟯) (b : B') (x : E' b) :
    (f' • f'') b x = f' ⟨b, x⟩ • f'' b x := rfl

instance [IsPrincipalBundle G F E] : IsScalarTower G C(B', G) Cᶠ[f]⟮F', E'; F, E⟯ where
  smul_assoc g f' f'' := by ext; simp [smul_smul]

instance [IsPrincipalBundle G F E] :
    IsScalarTower G C(TotalSpace F' E', G) Cᶠ[f]⟮F', E'; F, E⟯ where
  smul_assoc g f' f'' := by ext; simp [smul_smul]

omit [IsTopologicalGroup G] [∀ b, IsTopologicalTorsor (E b)] in
attribute [local fun_prop] FiberBundle.continuous_proj in
attribute [local simp] Trivialization.source_eq mem_baseSet_trivializationAt in
lemma _root_.ContinuousWithinAt.bundleHom_sdiv [IsPrincipalBundle G F E]
    {g g' : ∀ b, E' b → E (f b)} {u : Set (TotalSpace F' E')} {x : TotalSpace F' E'}
    (hg : ContinuousWithinAt (TotalSpace.map F' F g) u x)
    (hg' : ContinuousWithinAt (TotalSpace.map F' F g') u x) :
    ContinuousWithinAt (fun x : TotalSpace F' E' ↦ g x.1 x.2 /ₛ g' x.1 x.2) u x := by
  refine .mono_of_mem_nhdsWithin ?_ <| inter_mem_nhdsWithin _ <|
    ((trivializationAt F E (f x.1)).open_baseSet.preimage (map_continuous f)
    |>.preimage (f := π F' E') (by fun_prop)).mem_nhds <| mem_baseSet_trivializationAt F E _
  refine .congr (f := fun x' ↦ (trivializationAt F E (f x.1) ⟨_, g x'.1 x'.2⟩).2 /ₛ
    (trivializationAt F E (f x.1) ⟨_, g' x'.1 x'.2⟩).2) ?_ (fun x' hx' ↦ ?_) ?_
  · refine .sdiv (continuous_snd.continuousAt.comp_continuousWithinAt ?_)
      (continuous_snd.continuousAt.comp_continuousWithinAt ?_)
    · exact (trivializationAt F E (f x.1)).continuousOn _ (by simp)
        |>.comp (hg.mono Set.inter_subset_left) fun x hx ↦ by simpa using hx.2
    · exact (trivializationAt F E (f x.1)).continuousOn _ (by simp)
        |>.comp (hg'.mono Set.inter_subset_left) fun x hx ↦ by simpa using hx.2
  · exact trivializationAt F E (f x.1) |>.mulActionEquivAt hx'.2
      |>.map_sdiv_map (g x'.1 x'.2) (g' x'.1 x'.2) |>.symm
  · exact trivializationAt F E (f x.1) |>.mulActionEquivAt (by simp)
      |>.map_sdiv_map (g x.1 x.2) (g' x.1 x.2) |>.symm

omit [IsTopologicalGroup G] [∀ b, IsTopologicalTorsor (E b)] in
lemma _root_.ContinuousAt.bundleHom_sdiv [IsPrincipalBundle G F E]
    {g g' : ∀ b, E' b → E (f b)} {x : TotalSpace F' E'}
    (hg : ContinuousAt (TotalSpace.map F' F g) x)
    (hg' : ContinuousAt (TotalSpace.map F' F g') x) :
    ContinuousAt (fun x : TotalSpace F' E' ↦ g x.1 x.2 /ₛ g' x.1 x.2) x := by
  rw [← continuousWithinAt_univ] at hg hg' ⊢
  exact hg.bundleHom_sdiv _ _ _ hg'

omit [IsTopologicalGroup G] [∀ b, IsTopologicalTorsor (E b)] in
lemma _root_.ContinuousOn.bundleHom_sdiv [IsPrincipalBundle G F E]
    {g g' : ∀ b, E' b → E (f b)} {u : Set (TotalSpace F' E')}
    (hg : ContinuousOn (TotalSpace.map F' F g) u)
    (hg' : ContinuousOn (TotalSpace.map F' F g') u) :
    ContinuousOn (fun x : TotalSpace F' E' ↦ g x.1 x.2 /ₛ g' x.1 x.2) u :=
  fun b hb ↦ (hg b hb).bundleHom_sdiv _ _ _ (hg' b hb)

omit [IsTopologicalGroup G] [∀ b, IsTopologicalTorsor (E b)] in
lemma _root_.Continuous.bundleHom_sdiv [IsPrincipalBundle G F E] {g g' : ∀ b, E' b → E (f b)}
    (hg : Continuous (TotalSpace.map F' F g))
    (hg' : Continuous (TotalSpace.map F' F g')) :
    Continuous (fun x : TotalSpace F' E' ↦ g x.1 x.2 /ₛ g' x.1 x.2) := by
  rw [← continuousOn_univ] at hg hg' ⊢
  exact hg.bundleHom_sdiv _ _ _ hg'

@[simps]
instance [IsPrincipalBundle G F E] : SDiv C(TotalSpace F' E', G) Cᶠ[f]⟮F', E'; F, E⟯ where
  sdiv f' f'' := ⟨fun x ↦ f' x.1 x.2 /ₛ f'' x.1 x.2,
    f'.continuous_toFun.bundleHom_sdiv _ _ _ f''.continuous_toFun⟩

/-- For any `G`-principal bundle `E` over `B` and any other bundle `E'`, the type
`Cᶠ[f]⟮F', E'; F, E⟯` of continuous fibrewise maps from `E'` to `E` is
a `C(TotalSpace F' E', G)`-torsor if it isn't empty.
TODO: define a class `Pretorsor` for not necessarily empty torsors, and show that this is one? -/
instance [IsPrincipalBundle G F E] [Nonempty Cᶠ[f]⟮F', E'; F, E⟯] :
    Torsor C(TotalSpace F' E', G) Cᶠ[f]⟮F', E'; F, E⟯ where
  mul_smul f f' s := by ext; simp [smul_smul]
  one_smul s := by ext; simp
  sdiv_smul' s t := by ext; simp
  smul_sdiv' f s := by ext; simp

end ContinuousBundleHom

omit [IsTopologicalGroup G] [∀ (b : B), IsTopologicalTorsor (E b)] in
/-- For a principal bundle `E`, the following are equivalent:
* `E` is trivial as a fibre bundle, i.e. it admits a global not necessarily equivariant
  trivialisation
* `E` admits a global equivariant trivialisation
* `E` admits an equivariant isomorphism to a trivial bundle
* `E` admits a global section.

These are only the characterisations of `IsTrivial` that are specific to principal
bundles; see the API around `IsTrivial` for more general ones. -/
lemma IsPrincipalBundle.isTrivial_tfae [IsPrincipalBundle G F E] :
    [IsTrivial F E,
      Nonempty (E ≃ₜᶠₑ[G; F, G] Trivial B G),
      ∃ e : Trivialization F (π F E), e.IsEquivariant G ∧ e.baseSet = .univ,
      Nonempty Cₛ⟮F, E⟯].TFAE := by
  tfae_have 1 → 4 := fun ⟨e⟩ ↦ by
    rw [show Equiv.refl B = Homeomorph.refl B from rfl] at e
    exact ⟨e.continuousSectionEquiv.symm <|
      ContinuousSection.equivContinuousMap.symm <| .const _ <| Classical.arbitrary _⟩
  tfae_have 4 → 2 := fun ⟨s⟩ ↦ ⟨{
      toFun b x := x /ₛ s b
      invFun b g := g • s b
      left_inv' b g := smul_sdiv _ _
      right_inv' b x := sdiv_smul _ _
      continuous_toFun := by
        refine (Trivial.continuous_iff _).2 ⟨continuous_proj _ _, ?_⟩
        let f₁ : Cᶠ[ContinuousMap.id B]⟮F, E; F, E⟯ := ⟨fun _ ↦ id, continuous_id⟩
        let f₂ : Cᶠ[ContinuousMap.id B]⟮F, E; F, E⟯ := .ofContinuousSection F E (.refl _) s
        exact (f₁ /ₛ f₂).continuous
      continuous_invFun := by
        let f₁ : C(TotalSpace G (Trivial B G), G) := ⟨TotalSpace.trivialSnd B G, by fun_prop⟩
        let f₂ : Cᶠ[ContinuousMap.id B]⟮G, Trivial B G; F, E⟯ :=
          .ofContinuousSection _ _ (.refl _) s
        exact (f₁ • f₂).continuous_toFun
      map_smul' g b x := by simp [smul_sdiv_assoc] }⟩
  tfae_have 2 → 3 := fun ⟨e⟩ ↦ by
    refine ⟨{
      __ := (e.toHomeomorph.trans (Trivial.homeomorphProd B G) |>.trans
        (.prodCongr (.refl _) (.smulConst (Classical.arbitrary F)))).toOpenPartialHomeomorph
      baseSet := .univ
      open_baseSet := isOpen_univ
      source_eq := by simp
      target_eq := by simp
      proj_toFun := by simp [ContinuousBundleIso.toHomeomorph] }, ⟨?_⟩, ?_⟩
    · simp [ContinuousBundleIso.toHomeomorph, mul_smul]
    · simp
  tfae_have 3 → 1 := fun ⟨e, he⟩ ↦ (isTrivial_iff_exists_trivialization _ _).2 ⟨e, he.2⟩
  tfae_finish

omit [IsTopologicalGroup G] [∀ (b : B), IsTopologicalTorsor (E b)] in
/-- A principal bundle is trivial if and only if it admits a continuous global section. -/
lemma Bundle.isTrivial_iff_nonempty_continuousSection [IsPrincipalBundle G F E] :
    IsTrivial F E ↔ Nonempty Cₛ⟮F, E⟯ :=
  IsPrincipalBundle.isTrivial_tfae.out 0 3

omit [IsTopologicalGroup G] [∀ (b : B), IsTopologicalTorsor (E b)] in
attribute [local fun_prop] FiberBundle.continuous_proj in
/-- A `G`-principal bundle is trivial on an open set `u` if and only if it admits a `G`-equivariant
trivialisation on `u`. -/
lemma isTrivialOn_iff_exists_equivariant_trivialization [IsPrincipalBundle G F E]
    {u : Set B} (hu : IsOpen u) :
    IsTrivialOn F E u ↔ ∃ e : Trivialization F (π F E), e.baseSet = u ∧ e.IsEquivariant G := by
  rw [isTrivialOn_iff_exists_trivialization _ _ hu]
  refine ⟨fun ⟨e, he⟩ ↦ ?_, fun ⟨e, he, _⟩ ↦ ⟨e, he⟩⟩
  use {
    toFun x := ⟨x.proj, (x.snd /ₛ e.symm x.proj (Classical.arbitrary F)) • Classical.arbitrary F⟩
    invFun x := (x.2 /ₛ Classical.arbitrary F) • e.symm x.1 (Classical.arbitrary F)
    source := e.source
    target := e.target
    map_source' := by simp [e.source_eq, e.target_eq]
    map_target' := by simp [e.source_eq, e.target_eq]
    left_inv' := by simp
    right_inv' := by simp
    open_source := e.open_source
    open_target := e.open_target
    continuousOn_toFun := by
      refine .prodMk (by fun_prop) <| .smul ?_ (by fun_prop)
      refine .bundleHom_sdiv (F := F) (G := G) (E := E) F E (.id B) (g := fun b x ↦ x)
        (g' := fun b x ↦ e.symm b (Classical.arbitrary F)) continuousOn_id ?_
      refine e.continuousOn_symm.comp
        (f := fun x : TotalSpace F E ↦ (x.1, Classical.arbitrary F)) (by fun_prop) fun x hx ↦ ?_
      simpa [e.source_eq] using hx
    continuousOn_invFun := by
      refine .smul (by fun_prop) <| e.continuousOn_symm.comp
        (f := fun x : B × F ↦ (x.1, Classical.arbitrary F)) (by fun_prop) fun x hx ↦ ?_
      simpa [e.target_eq] using hx
    baseSet := e.baseSet
    open_baseSet := e.open_baseSet
    source_eq := e.source_eq
    target_eq := e.target_eq
    proj_toFun := by simp }
  refine ⟨he, ⟨fun {b} hb g {x} ↦ ?_⟩⟩
  simp [smul_sdiv_assoc, mul_smul]

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

omit [IsTopologicalGroup G] in
/-- The covering homotopy theorem for principal bundles: every numerable principal bundle over
`B × I` is isomorphic to the pullback of itself along the map `B × I → B × I` sending `(b, t)` to
`(b, 1)`.

TODO: rename, get rid of unnecessary `[(b : B) → Zero (E b)]`-assumption -/
lemma IsPrincipalBundle.coveringHomotopyLemma (E : B × I → Type*)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [∀ b, Zero (E b)] [NumerableBundle F E] [∀ b, Torsor G (E b)] [IsPrincipalBundle G F E] :
    Nonempty (E ≃ₜᶠₑ[G; F, F] (ContinuousMap.prodMap (.id B) (.const I 1)) *ᵖ E) := by
  have ⟨u, hu⟩ := NumerableBundle.exists_countable_isTrivialOn_cover_prod_unitInterval F E
  choose e he he' using fun n ↦ (isTrivialOn_iff_exists_equivariant_trivialization
      <| (hu.2.2 n).1.prod isOpen_univ).1 (hu.2.2 n).2
  have ⟨e, he⟩ := coveringHomotopyLemma_of_prop F E (fun _ _ f ↦ ∀ (g : G) x, f (g • x) = g • f x)
    (by grind) hu.2.1 e he fun n m x hx x' hx' g x'' ↦ by
      simp [(e n).map_smul hx, (e m).symm_map_smul hx']
  exact ⟨⟨e, fun g x ↦ he x g⟩⟩

end Pullback
