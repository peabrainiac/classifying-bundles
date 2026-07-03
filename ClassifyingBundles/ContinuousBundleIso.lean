/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.ContinuousBundleHom
import Mathlib.Logic.Function.CompTypeclasses

/-! # Bundled continuous fibrewise homeomorphisms between fibre bundles -/

open Bundle FiberBundle Function

variable (F : Type*) {B : Type*} (E : B → Type*) [TopologicalSpace (Bundle.TotalSpace F E)]
  (F' : Type*) {B' : Type*} (E' : B' → Type*) [TopologicalSpace (Bundle.TotalSpace F' E')]
  (F'' : Type*) {B'' : Type*} (E'' : B'' → Type*) [TopologicalSpace (Bundle.TotalSpace F'' E'')]

/-- A continuous fibrewise homeomorphism between bundles, relative to a given map of the base
spaces. -/
structure ContinuousBundleIso (e : B ≃ B') where
  toFun (b : B) (x : E b) : E' (e b)
  invFun (b' : B') (x : E' b') : E (e.symm b')
  left_inv' (b' : B') (x : E' b') : toFun _ (invFun _ x) = cast (congrArg E' (by simp)) x
  right_inv' (b : B) (x : E b) : invFun _ (toFun _ x) = cast (congrArg E (by simp)) x
  continuous_toFun : Continuous (TotalSpace.map F F' toFun)
  continuous_invFun : Continuous (TotalSpace.map F' F invFun)

@[inherit_doc] scoped[Bundle] notation E " ≃ₜᶠ[" e "; " F ", "F'"] " E' =>
  ContinuousBundleIso F E F' E' e

/-- A continuous fibrewise map between bundles over the same base space. -/
scoped[Bundle] notation E " ≃ₜᶠ[" F ", "F'"] " E' =>
  ContinuousBundleIso F E F' E' (Equiv.refl _)

namespace ContinuousBundleIso

variable {e : B ≃ B'}

variable {F E F' E' F'' E''}

instance instDFunLike : DFunLike (E ≃ₜᶠ[e; F, F'] E') B (fun b ↦ (E b → E' (e b))) where
  coe f := f.toFun
  coe_injective := by
    rintro ⟨toFun, invFun, left_inv, right_inv, _⟩ ⟨toFun', invFun', _, right_inv', _⟩
      (h : toFun = toFun')
    congr; ext b' x
    obtain ⟨b, rfl⟩ := e.surjective b'
    suffices h' : (toFun b).Surjective by
      obtain ⟨x, rfl⟩ := h' x
      rw [right_inv, h, right_inv']
    obtain ⟨b', rfl⟩ := e.symm.surjective b
    refine Surjective.of_comp (g := invFun b') ?_
    simpa [Function.comp_def, left_inv] using (cast_bijective _).surjective

@[ext]
theorem ext {e' e'' : E ≃ₜᶠ[e; F, F'] E'} (h : ∀ b x, e' b x = e'' b x) : e' = e'' :=
  DFunLike.ext _ _ fun b ↦ funext <| h b

lemma apply_bijective (e' : E ≃ₜᶠ[e; F, F'] E') (b : B) : (e' b).Bijective := by
  refine ⟨?_, ?_⟩
  · refine .of_comp (f := e'.invFun (e b)) (g := e'.toFun b) ?_
    simp only [Function.comp_def, e'.right_inv' b]
    exact (cast_bijective _).injective
  · rw [← e.symm_apply_apply b]
    refine .of_comp (f := e'.toFun _) (g := e'.invFun (e b)) ?_
    simp only [Function.comp_def, e'.left_inv' _]
    exact (cast_bijective _).surjective

/-- The forwards direction of a bundle isomorphism. -/
def toHom (e' : E ≃ₜᶠ[e; F, F'] E') : Cᶠ[e]⟮F, E; F', E'⟯ where
  toFun := e'
  continuous_toFun := e'.continuous_toFun

@[simp]
lemma toHom_apply (e' : E ≃ₜᶠ[e; F, F'] E') (b : B) (x : E b) : e'.toHom b x = e' b x := rfl

/-- Construct a bundle isomorphism from a pair of bundle morphisms. -/
def ofHoms (f : Cᶠ[e]⟮F, E; F', E'⟯) (g : Cᶠ[e.symm]⟮F', E'; F, E⟯)
    (h : Function.LeftInverse f.toContinuousMap g.toContinuousMap)
    (h' : Function.RightInverse f.toContinuousMap g.toContinuousMap) : E ≃ₜᶠ[e; F, F'] E' where
  toFun := f
  continuous_toFun := f.continuous_toFun
  invFun := g
  continuous_invFun := g.continuous_toFun
  left_inv' b' x := by
    simpa [ContinuousBundleHom.toContinuousMap, TotalSpace.map, eq_cast_iff_heq] using h ⟨b', x⟩
  right_inv' b x := by
    simpa [ContinuousBundleHom.toContinuousMap, TotalSpace.map, eq_cast_iff_heq] using h' ⟨b, x⟩

/-- The homeomorphism of total spaces induced by an isomorphism of bundles. -/
def toHomeomorph (e' : E ≃ₜᶠ[e; F, F'] E') : TotalSpace F E ≃ₜ TotalSpace F' E' where
  toFun := TotalSpace.map _ _ e'.toFun
  invFun := TotalSpace.map _ _ e'.invFun
  left_inv := by
    intro ⟨b, x⟩
    simpa [TotalSpace.map, eq_cast_iff_heq] using e'.right_inv' b x
  right_inv := by
    intro ⟨b, x⟩
    simpa [TotalSpace.map, eq_cast_iff_heq] using e'.left_inv' b x
  continuous_toFun := e'.continuous_toFun
  continuous_invFun := e'.continuous_invFun

/-- Construct a fibre bundle isomorphism out of a homeomorpism that respects the fibres.
This construction has really bad defeq properties, so it should be used only when
absolutely necessary. -/
def ofHomeomorph (e' : TotalSpace F E ≃ₜ TotalSpace F' E') (he' : ∀ x, (e' x).proj = e x.proj) :
    E ≃ₜᶠ[e; F, F'] E' := by
  refine ofHoms (.ofContinuousMap e' he') (.ofContinuousMap e'.symm fun x ↦ ?_) ?_ ?_
  · obtain ⟨x, rfl⟩ := e'.surjective x
    simp [he']
  · simpa using e'.symm.left_inv
  · simpa using e'.symm.right_inv

variable (F E) in
/-- The identity isomorphism of a bundle `E`. -/
def refl : E ≃ₜᶠ[F, F] E where
  toFun _ := id
  invFun _ := id
  left_inv' _ := by simp
  right_inv' _ := by simp
  continuous_toFun := by simp [continuous_id]
  continuous_invFun := by simp [continuous_id]

@[simp]
lemma refl_apply {b : B} : (refl F E b : E b → E b) = id := rfl

@[simp]
lemma refl_apply' {b : B} {x : E b} : refl F E b x = x :=
  rfl

/-- The inverse of a bundle isomorphism. -/
def symm (e' : E ≃ₜᶠ[e; F, F'] E') : E' ≃ₜᶠ[e.symm; F', F] E where
  toFun := e'.invFun
  invFun := e'.toFun
  left_inv' := e'.right_inv'
  right_inv' := e'.left_inv'
  continuous_toFun := e'.continuous_invFun
  continuous_invFun := e'.continuous_toFun

@[simp]
lemma left_inv (e' : E ≃ₜᶠ[e; F, F'] E') (b : B') (x : E' b) :
    e' _ (e'.symm b x) = cast (by simp) x :=
  e'.left_inv' b x

@[simp]
lemma right_inv (e' : E ≃ₜᶠ[e; F, F'] E') (b : B) (x : E b) :
    e'.symm _ (e' b x) = cast (by simp) x :=
  e'.right_inv' b x

-- TODO: find home
local instance {e₁ : B ≃ B'} {e₂ : B' ≃ B''} {e₃ : B ≃ B''} [CompTriple e₁ e₂ e₃] :
    CompTriple e₂.symm e₁.symm e₃.symm where
  comp_eq := by
    suffices h : e₃ = e₁.trans e₂ by simp [h]
    ext x
    simp [CompTriple.comp_apply]

/-- The composition of two bundle isomorphisms along two homeomorphisms of the base spaces,
as a bundle isomorphism along a third homeomorphism of base spaces that propositionally equals the
composition of the first two. -/
def trans {e₁ : B ≃ B'} {e₂ : B' ≃ B''} {e₃ : B ≃ B''} [CompTriple e₁ e₂ e₃]
    (e₁' : E ≃ₜᶠ[e₁; F, F'] E') (e₂' : E' ≃ₜᶠ[e₂; F', F''] E'') : E ≃ₜᶠ[e₃; F, F''] E'' where
  toFun b x := cast (congrArg _ (CompTriple.comp_apply ‹_› _)) (e₂' _ (e₁' b x))
  invFun b' x := cast (congrArg _ (CompTriple.comp_apply inferInstance _))
    (e₁'.symm _ (e₂'.symm b' x))
  left_inv' b x := by
    obtain rfl : e₃ = e₁.trans e₂ := by ext _; simp [CompTriple.comp_apply]
    simp only [Equiv.symm_trans, Equiv.trans_apply, cast_eq, left_inv]
    suffices h : ∀ (b b' : B') (h : b = b') (x : E' b),
        e₂' _ (cast (congrArg E' h) x) = cast (by rw [h]) (e₂' _ x) by
      rw [h _ _ (by simp)]; simp
    intro b b' rfl x
    simp
  right_inv' b x := by
    obtain rfl : e₃ = e₁.trans e₂ := by ext _; simp [CompTriple.comp_apply]
    simp only [Equiv.symm_trans, Equiv.trans_apply, cast_eq, right_inv]
    suffices h : ∀ (b b' : B') (h : b = b') (x : E' b),
        e₁'.symm _ (cast (congrArg E' h) x) = cast (by rw [h]) (e₁'.symm _ x) by
      rw [h _ _ (by simp)]; simp
    intro b b' rfl x
    simp
  continuous_toFun := by
    refine (e₂'.continuous_toFun.comp (e₁'.continuous_toFun)).congr fun ⟨b, x⟩ ↦ ?_
    ext
    · simp [CompTriple.comp_apply]
    · simp only [comp_apply, TotalSpace.map, heq_cast_iff_heq, heq_eq_eq]
      rfl
  continuous_invFun := by
    refine (e₁'.symm.continuous_toFun.comp (e₂'.symm.continuous_toFun)).congr fun ⟨b, x⟩ ↦ ?_
    ext
    · simp [CompTriple.comp_apply]
    · simp only [comp_apply, TotalSpace.map, heq_cast_iff_heq, heq_eq_eq]
      rfl

variable [TopologicalSpace F] [TopologicalSpace B] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [TopologicalSpace F'] [TopologicalSpace B'] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E']
  [TopologicalSpace F''] [TopologicalSpace B''] [∀ b, TopologicalSpace (E'' b)]
  [FiberBundle F'' E'']

set_option backward.defeqAttrib.useBackward true in
/-- The restriction of a fibrewise bundle homeomorphism to a single fibre. -/
def homeomorphAt (e' : E ≃ₜᶠ[e; F, F'] E') (b : B) : E b ≃ₜ E' (e b) where
  toFun := e'.toHom.continuousMapAt b
  invFun := cast (by simp) ∘ e'.symm.toHom.continuousMapAt (e b)
  left_inv x := by simp
  right_inv := Function.LeftInverse.rightInverse_of_surjective
    (fun x ↦ by simp) (e'.apply_bijective b).surjective
  continuous_toFun := map_continuous _
  continuous_invFun := by
    refine .comp ?_ (map_continuous _)
    suffices h : ∀ (b' : B) (hb : b' = b), Continuous (cast (congrArg E hb)) from h _ (by simp)
    rintro b rfl
    exact continuous_id.congr fun x ↦ by simp

-- TODO: find home
@[simp]
lemma _root_.Homeomorph.coe_symm_toEquiv' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : ⇑(h : Equiv X Y).symm = ⇑h.symm := by
  rfl

/-- The homeomorphism between trivial bundles given by a homeomorphism of the bases and a
homeomorphism of the standard fibres. -/
def trivialCongr (e : B ≃ₜ B') (e' : F ≃ₜ F') : Trivial B F ≃ₜᶠ[e; F, F'] Trivial B' F' where
  toFun b x := e' x
  invFun b' x := e'.symm x
  left_inv' := by simp
  right_inv' := by simp
  continuous_toFun := by
    rw [← (Trivial.homeomorphProd B F).symm.comp_continuous_iff',
      ← (Trivial.homeomorphProd B' F').comp_continuous_iff]
    simp only [Function.comp_def, Trivial.homeomorphProd_apply,
      TotalSpace.map_proj, Trivial.homeomorphProd_symm_apply_proj, TotalSpace.map_snd,
      Trivial.homeomorphProd_symm_apply_snd]
    simp only [EquivLike.coe_coe]
    fun_prop
  continuous_invFun := by
    rw [← (Trivial.homeomorphProd B F).comp_continuous_iff,
      ← (Trivial.homeomorphProd B' F').symm.comp_continuous_iff']
    rw [Function.comp_def]
    simp only [comp_apply, Trivial.homeomorphProd_apply, TotalSpace.map_proj,
      Trivial.homeomorphProd_symm_apply_proj, Homeomorph.coe_symm_toEquiv', TotalSpace.map_snd,
      Trivial.homeomorphProd_symm_apply_snd]
    fun_prop

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pull back an isomorphism `e'` of bundles along a homeomorphism `e` of the bases to an
isomorphism of pullback bundles along a homeomorphism `e''` that forms a commutative square with `e`
and the maps the bundles are pulled back along. -/
def pullbackCongr {e : B ≃ₜ B'} (e' : E ≃ₜᶠ[e; F, F'] E') {B'' B''' : Type*} [TopologicalSpace B'']
    [TopologicalSpace B'''] (f : C(B'', B)) (f' : C(B''', B')) (e'' : B'' ≃ₜ B''')
    (h : e ∘ f = f' ∘ e'') : (f *ᵖ E) ≃ₜᶠ[e''; F, F'] (f' *ᵖ E') where
  toFun b x := cast (congrArg E' <| by simpa using congrFun h b) (e' _ x)
  invFun b x := cast (congrArg E <| by have := congrFun h (e''.symm b); simp_all [e.symm_apply_eq])
    (e'.symm _ x)
  left_inv' b x := by
    suffices h' : ∀ (b b' : B) (h : b = b') (x : E b),
        e' _ (cast (congrArg E h) x) = cast (by rw [h]) (e' _ x) by
      erw [h' _ _ (by
        have := congrFun h (e''.symm b)
        simp_all [e.symm_apply_eq]), e'.left_inv]
      simp
    intro b b' rfl x
    simp
  right_inv' b x := by
    suffices h' : ∀ (b b' : B') (h : b = b') (x : E' b),
        e'.symm _ (cast (congrArg E' h) x) = cast (by rw [h]) (e'.symm _ x) by
      erw [h' _ _ (congrFun h _), e'.right_inv]
      simp
    intro b b' rfl x
    simp
  continuous_toFun := by
    refine (Pullback.TotalSpace.continuous_iff _).2
      ⟨e''.continuous.comp <| Pullback.continuous_proj _ _ _, ?_⟩
    refine (e'.continuous_toFun.comp <| Pullback.continuous_lift _ _ f).congr fun ⟨b, x⟩ ↦ ?_
    ext
    · simpa using congrFun h b
    · simp; rfl
  continuous_invFun := by
    refine (Pullback.TotalSpace.continuous_iff _).2
      ⟨e''.symm.continuous.comp <| Pullback.continuous_proj _ _ _, ?_⟩
    refine (e'.continuous_invFun.comp <| Pullback.continuous_lift _ _ f').congr fun ⟨b, x⟩ ↦ ?_
    ext
    · have := congrFun h (e''.symm b)
      simp_all [e.symm_apply_eq]
    · simp; rfl

/-- The pullback of a trivial bundle is isomorphic to a trivial bundle. -/
def pullbackTrivialIso (f : C(B', B)) : f *ᵖ (Trivial B F) ≃ₜᶠ[F, F] Trivial B' F where
  toFun _ x := x
  invFun _ x := x
  left_inv' := by simp
  right_inv' := by simp
  continuous_toFun :=
    (Trivial.continuous_iff _).2 ⟨Pullback.continuous_proj _ _ _,
      (TotalSpace.continuous_trivialSnd.comp <| Pullback.continuous_lift F (Trivial B F) f:)⟩
  continuous_invFun :=
    (Pullback.TotalSpace.continuous_iff _).2 ⟨continuous_proj _ _, (Trivial.continuous_iff _).2
      ⟨(map_continuous f).comp <| continuous_proj _ _, TotalSpace.continuous_trivialSnd⟩⟩

/-- The pullback of a pullback bundle is isomorphic to the pullback of the original bundle along the
composition. -/
def pullbackPullbackIso (f : C(B', B)) (g : C(B'', B')) :
    g *ᵖ (f *ᵖ E) ≃ₜᶠ[F, F] (f.comp g) *ᵖ E where
  toFun _ x := x
  invFun _ x := x
  left_inv' := by simp
  right_inv' := by simp
  continuous_toFun := by
    refine (Pullback.TotalSpace.continuous_iff _).2 ⟨Pullback.continuous_proj _ _ _, ?_⟩
    refine ((Pullback.continuous_lift F E f).comp <| Pullback.continuous_lift F (f *ᵖ E) g).congr ?_
    simp [Function.comp_def, Pullback.lift, TotalSpace.map]
  continuous_invFun := by
    refine (Pullback.TotalSpace.continuous_iff _).2 ⟨Pullback.continuous_proj _ _ _, ?_⟩
    refine (Pullback.TotalSpace.continuous_iff _).2
      ⟨(map_continuous g).comp <| Pullback.continuous_proj _ _ _, ?_⟩
    refine (Pullback.continuous_lift F E (f.comp g)).congr ?_
    simp [Function.comp_def, Pullback.lift, TotalSpace.map]


end ContinuousBundleIso
