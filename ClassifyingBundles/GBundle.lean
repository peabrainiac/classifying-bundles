import ClassifyingBundles.PrincipalBundle

open Bundle FiberBundle

variable (G : Type*) [Group G] [TopologicalSpace G]
  (F : Type*) [TopologicalSpace F] {B : Type*} [TopologicalSpace B]
  (E : B → Type*) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (Bundle.TotalSpace F E)]
  [FiberBundle F E] [SMul G F]

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
    e.coordChange e' b x = g e e' b • x

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

end FiberBundle
