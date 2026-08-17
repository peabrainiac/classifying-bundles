/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.ContinuousBundleIso
import ClassifyingBundles.MulActionEquiv
import Mathlib.Logic.Lemmas

/-! # Bundled continuous fibrewise equivariant maps between fibre bundles-/

open Bundle FiberBundle Function

-- TODO: generalise from groups to monoids or plain types where possible
variable (G : Type*) (F : Type*) {B : Type*} (E : B → Type*)
  [TopologicalSpace (Bundle.TotalSpace F E)]
  (H : Type*) (F' : Type*) {B' : Type*} (E' : B' → Type*)
  [TopologicalSpace (Bundle.TotalSpace F' E')]
  (H' : Type*) (F'' : Type*) {B'' : Type*} (E'' : B'' → Type*)
  [TopologicalSpace (Bundle.TotalSpace F'' E'')]
  [∀ b, SMul G (E b)] [∀ b', SMul H (E' b')] [∀ b'', SMul H' (E'' b'')] {φ : G → H} {f : B → B'}

variable {G H} in
/-- A continuous fibrewise equivariant map between bundles, relative to given maps of the base
spaces and groups/monoids. -/
structure ContinuousBundleActionHom (φ : G → H) (f : B → B') extends Cᶠ[f]⟮F, E; F', E'⟯ where
  map_smul' (g : G) {b : B} (x : E b) : toFun b (g • x) = φ g • toFun b x

@[inherit_doc] scoped[Bundle] notation "Cᶠₑ[" φ ", " f "]⟮" F ", " E "; " F' ", " E' "⟯" =>
  ContinuousBundleActionHom F E F' E' φ f

/-- A continuous fibrewise equivariant map between bundles over the same base space, relative to a
given map of the action groups/monoids. -/
scoped[Bundle] notation "Cᶠₑ[" φ "]⟮" F ", " E "; " F' ", " E' "⟯" =>
  ContinuousBundleActionHom F E F' E' φ id

/-- A continuous fibrewise equivariant map between bundles over the same base space. -/
scoped[Bundle] notation "Cᶠ[" G "]⟮" F ", " E "; " F' ", " E' "⟯" =>
  ContinuousBundleActionHom F E F' E' (@id G) id

/-- When `G` acts on every fibre of a bundle `E`, we equip `Bundle.TotalSpace F E` with the
corresponding `G`-action as well.
TODO: find a more permanent home for this. -/
@[simps]
instance : SMul G (TotalSpace F E) where
  smul g x := ⟨_, g • x.2⟩

omit [TopologicalSpace (TotalSpace F E)] in
@[simp]
lemma Bundle.TotalSpace.smul_mk {g : G} {b : B} {x : E b} :
    g • (⟨b, x⟩ : TotalSpace F E) = ⟨b, g • x⟩ := by rfl

namespace ContinuousBundleActionHom

variable {G F E H F' E' H' F'' E''}

instance instDFunLike : DFunLike Cᶠₑ[φ, f]⟮F, E; F', E'⟯ B (fun b ↦ (E b → E' (f b))) where
  coe f := f.toFun
  coe_injective := by rintro ⟨⟨⟩⟩ ⟨⟩ _; congr

@[simp]
lemma toContinuousBundleHom_coe (f' : Cᶠₑ[φ, f]⟮F, E; F', E'⟯) : ⇑f'.toContinuousBundleHom = f' :=
  rfl

@[ext]
theorem ext {g g' : Cᶠₑ[φ, f]⟮F, E; F', E'⟯} (h : ∀ b x, g b x = g' b x) : g = g' :=
  DFunLike.ext _ _ fun b ↦ funext <| h b

@[simp]
lemma map_smul (f' : Cᶠₑ[φ, f]⟮F, E; F', E'⟯) (g : G) {b : B} (x : E b) :
    f' b (g • x) = φ g • f' b x :=
  f'.map_smul' g x

/-- The equivariant map between total spaces corresponding to a continuous fibrewise equivariant
map.
TODO: upgrade this to a `ContinuousMulActionHom` once that is defined. -/
@[simps]
def toMulActionHom (f' : Cᶠₑ[φ, f]⟮F, E; F', E'⟯) : TotalSpace F E →ₑ[φ] TotalSpace F' E' where
  toFun := TotalSpace.map F F' f'
  map_smul' g x := by ext <;> simp; rfl

lemma toMulActionHom_injective :
    Injective (toMulActionHom : Cᶠₑ[φ, f]⟮F, E; F', E'⟯ → _) := by
  intro g g' h
  ext b x
  simpa [toMulActionHom, TotalSpace.map] using congrFun (congrArg MulActionHom.toFun h) ⟨_, x⟩

/-- The restriction of a continuous fibrewise equivariant map to a single fibre.
TODO: upgrade this to a `ContinuousMulActionHom` once that is defined. -/
@[simps]
def mulActionHomAt (f' : Cᶠₑ[φ, f]⟮F, E; F', E'⟯) (b : B) : E b →ₑ[φ] E' (f b) where
  toFun := f' b
  map_smul' g x := f'.map_smul g x

variable [TopologicalSpace F] [TopologicalSpace B] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [TopologicalSpace F'] [TopologicalSpace B'] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E']
  [TopologicalSpace F''] [TopologicalSpace B''] [∀ b, TopologicalSpace (E'' b)]
  [FiberBundle F'' E'']

instance {f : B' → B} {b' : B'} [SMul G (E (f b'))] : SMul G ((f *ᵖ E) b') :=
  inferInstanceAs (SMul G (E (f b')))

/-- Continuous fibrewise equivariant maps from a bundle `E` over `B` to a bundle `E'` over `B'`
relative to a map `B → B'` are equivalently continuous fibrewise equivariant maps from `E` to the
pullback `f *ᵖ E'` of `E'` to `B`. -/
@[simps!]
def pullbackEquiv : Cᶠₑ[φ, f]⟮F, E; F', E'⟯ ≃ Cᶠₑ[φ]⟮F, E; F', f *ᵖ E'⟯ where
  toFun f' := ⟨ContinuousBundleHom.pullbackEquiv f'.toContinuousBundleHom,
    fun g _ x ↦ f'.map_smul g x⟩
  invFun f' := ⟨ContinuousBundleHom.pullbackEquiv.invFun f'.toContinuousBundleHom,
    fun g _ x ↦ f'.map_smul g x⟩
  left_inv _ := rfl
  right_inv _ := rfl

end ContinuousBundleActionHom

variable [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace B''] (φ : G ≃ H) (e : B ≃ₜ B')

variable {G H} in
/-- A continuous fibrewise equivariant isomorphism between bundles, relative to given maps of the
base spaces and groups/monoids. -/
structure ContinuousBundleActionEquiv (φ : G ≃ H) (e : B ≃ₜ B') extends
    E ≃ₜᶠ[e; F, F'] E', Cᶠₑ[φ, e]⟮F, E; F', E'⟯ where

@[inherit_doc] scoped[Bundle] notation E " ≃ₜᶠₑ[" φ ", " e "; " F ", " F' "] " E' =>
  ContinuousBundleActionEquiv F E F' E' φ e

/-- A continuous fibrewise equivariant isomorphism between bundles over the same base space. -/
scoped[Bundle] notation E " ≃ₜᶠₑ["G "; " F ", " F' "] " E' =>
  ContinuousBundleActionEquiv F E F' E' (Equiv.refl G) (Homeomorph.refl _)

namespace ContinuousBundleActionEquiv

variable {G F E H F' E' H' F'' E'' φ e}

instance instDFunLike : DFunLike (E ≃ₜᶠₑ[φ, e; F, F'] E') B (fun b ↦ (E b → E' (e b))) where
  coe f := f.toFun
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; congr; exact DFunLike.coe_injective h

@[simp]
lemma toFun_eq_coe (e' : E ≃ₜᶠₑ[φ, e; F, F'] E') : e'.toFun = e' := rfl

@[simp]
lemma coe_toContinuousBundleIso (e' : E ≃ₜᶠₑ[φ, e; F, F'] E') :
    ⇑e'.toContinuousBundleIso = e' := rfl

@[simp]
lemma map_smul (e' : E ≃ₜᶠₑ[φ, e; F, F'] E') (g : G) {b : B} (x : E b) :
    e' b (g • x) = φ g • e' b x :=
  e'.map_smul' g x

variable [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [TopologicalSpace F'] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] in
/-- The restriction of a continuous fibrewise equivariant map to a single fibre.
TODO: upgrade this to a `ContinuousMulActionEquiv` once that is defined. -/
@[simps]
def mulActionEquivAt (e' : E ≃ₜᶠₑ[φ, e; F, F'] E') (b : B) : E b ≃ₑ[φ] E' (e b) where
  toEquiv := (e'.homeomorphAt b).toEquiv
  __ := e'.mulActionHomAt b

set_option backward.isDefEq.respectTransparency false in
variable [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [TopologicalSpace F'] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] in
/-- The inverse of an equivariant bundle isomorphism. -/
nonrec def symm (e' : E ≃ₜᶠₑ[φ, e; F, F'] E') : E' ≃ₜᶠₑ[φ.symm, e.symm; F', F] E where
  toContinuousBundleIso := e'.toContinuousBundleIso.symm
  map_smul' g b x := by
    have h := (e'.mulActionEquivAt (e.symm b)).symm.map_smul'' g (Equiv.congrArg _ (by simp) x)
    simp only [Equiv.smul_congrArg, MulActionEquiv.symm_toFun, mulActionEquivAt_invFun,
      ContinuousBundleIso.homeomorphAt] at h
    simp only [EquivLike.coe_coe, ContinuousBundleHom.continuousMapAt, ContinuousMap.coe_mk,
      comp_apply, Equiv.apply_congrArg, ContinuousBundleIso.toHom_apply, Equiv.smul_congrArg,
      Equiv.eq_congrArg_iff_heq, Equiv.congrArg_heq_iff_heq, heq_eq_eq,
      EmbeddingLike.apply_eq_iff_eq] at h
    exact h

set_option backward.isDefEq.respectTransparency false in
/-- The composition of two equivariant bundle isomorphisms along two group isomorphisms and two
homeomorphisms of the base spaces,
as an equivariant bundle isomorphism along a third isomorphism and homeomorphism that
propositionally equal the composition of the first two. -/
def trans {φ₁ : G ≃ H} {φ₂ : H ≃ H'} {φ₃ : G ≃ H'} [CompTriple φ₁ φ₂ φ₃]
    {e₁ : B ≃ₜ B'} {e₂ : B' ≃ₜ B''} {e₃ : B ≃ₜ B''} [CompTriple e₁ e₂ e₃]
    (e₁' : E ≃ₜᶠₑ[φ₁, e₁; F, F'] E') (e₂' : E' ≃ₜᶠₑ[φ₂, e₂; F', F''] E'') :
    E ≃ₜᶠₑ[φ₃, e₃; F, F''] E'' where
  toContinuousBundleIso :=
    haveI : CompTriple (EquivLike.toEquiv e₁) (EquivLike.toEquiv e₂) (EquivLike.toEquiv e₃) :=
      ⟨CompTriple.comp_eq (φ := e₁) (ψ := e₂)⟩
    e₁'.toContinuousBundleIso.trans e₂'.toContinuousBundleIso
  map_smul' g b x := by
    change Equiv.congrArg _ _ (e₂' _ (e₁' _ _)) = _ • Equiv.congrArg _ _ (e₂' _ (e₁' _ _))
    simp [‹CompTriple φ₁ φ₂ φ₃›.comp_apply _]

section Pullback

/-- Pull back an equivariant isomorphism `e'` of bundles along a group isomorphism `φ` and a
homeomorphism `e` of the bases to an equivariant isomorphism of pullback bundles along a
homeomorphism `e''` that forms a commutative square with `e`
and the maps the bundles are pulled back along. -/
def pullbackCongr {φ : G ≃ H} {e : B ≃ₜ B'} (e' : E ≃ₜᶠₑ[φ, e; F, F'] E') {B'' B''' : Type*}
    [TopologicalSpace B''] [TopologicalSpace B'''] (f : C(B'', B)) (f' : C(B''', B'))
    (e'' : B'' ≃ₜ B''') (h : e ∘ f = f' ∘ e'') :
    (f *ᵖ E) ≃ₜᶠₑ[φ, e''; F, F'] (f' *ᵖ E') where
  toContinuousBundleIso := e'.toContinuousBundleIso.pullbackCongr f f' e'' h
  map_smul' g {b} x := by
    refine cast_eq_iff_heq.2 <| (e'.map_smul g x).heq.trans ?_
    have h' b b' (h : b = b') (g : H) x :
        cast (congrArg E' h) (g • x) = g • cast (congrArg E' h) x := by
      obtain rfl := h; rfl
    refine .trans ?_ (h' (e (f b)) (f' (e'' b)) (congrFun h b) (φ g) _).heq
    simp; rfl

/-- The pullback of a pullback bundle is isomorphic to the pullback of the original bundle along the
composition. -/
def pullbackPullbackIso (f : C(B', B)) (g : C(B'', B')) :
    g *ᵖ (f *ᵖ E) ≃ₜᶠₑ[G; F, F] (f.comp g) *ᵖ E where
  toContinuousBundleIso := ContinuousBundleIso.pullbackPullbackIso f g
  map_smul' _ _ _ := rfl

end Pullback

end ContinuousBundleActionEquiv
