/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Topology.FiberBundle.Constructions

/-! # Bundled continuous fibrewise maps between fibre bundles -/

open Bundle FiberBundle Function

variable (F : Type*) {B : Type*} (E : B → Type*) [TopologicalSpace (Bundle.TotalSpace F E)]
  (F' : Type*) {B' : Type*} (E' : B' → Type*) [TopologicalSpace (Bundle.TotalSpace F' E')]
  {f : B → B'}

variable {E E'} in
/-- The map `TotalSpace F E → TotalSpace F' E'` given by a map `f : B → B'` and a map
`f' b : E b → E' (f b)` for each `b`. -/
@[simps]
def Bundle.TotalSpace.map (f' : ∀ b, E b → E' (f b)) (x : TotalSpace F E) :
    TotalSpace F' E' := ⟨_, f' _ x.2⟩

omit [TopologicalSpace (Bundle.TotalSpace F E)] in
@[simp]
lemma Bundle.TotalSpace.map_id : map F F (f := @id B) (fun b ↦ @id (E b)) = id :=
  rfl

omit [TopologicalSpace (Bundle.TotalSpace F E)] [TopologicalSpace (Bundle.TotalSpace F' E')] in
lemma Bundle.TotalSpace.map_injective : Injective (map F F' : (∀ b, E b → E' (f b)) → _) := by
  intro f' f'' h
  ext b x
  simpa [map] using congrFun h ⟨_, x⟩

/-- A continuous fibrewise map between bundles, relative to a given map of the base spaces. -/
structure ContinuousBundleHom (f : B → B') where
  toFun (b : B) (x : E b) : E' (f b)
  continuous_toFun : Continuous (TotalSpace.map F F' toFun)

@[inherit_doc] scoped[Bundle] notation "Cᶠ[" f "]⟮" F ", " E "; " F' ", " E' "⟯" =>
  ContinuousBundleHom F E F' E' f

/-- A continuous fibrewise map between bundles over the same base space. -/
scoped[Bundle] notation "Cᶠ⟮" F ", " E "; " F' ", " E' "⟯" =>
  ContinuousBundleHom F E F' E' id

namespace ContinuousBundleHom

variable {F E F' E'}

instance instDFunLike : DFunLike Cᶠ[f]⟮F, E; F', E'⟯ B (fun b ↦ (E b → E' (f b))) where
  coe f := f.toFun
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; congr

@[simp]
theorem coeFn_mk (f' : ∀ b, E b → E' (f b)) (hf : Continuous (TotalSpace.map F F' f')) :
    (mk f' hf : ∀ _, _) = f' := rfl

@[ext]
theorem ext {g g' : Cᶠ[f]⟮F, E; F', E'⟯} (h : ∀ b x, g b x = g' b x) : g = g' :=
  DFunLike.ext _ _ fun b ↦ funext <| h b

/-- The continuous map between total spaces underlying a continuous fibrewise map. -/
@[simps!]
def toContinuousMap (g : Cᶠ[f]⟮F, E; F', E'⟯) : C(TotalSpace F E, TotalSpace F' E') where
  toFun := TotalSpace.map F F' g
  continuous_toFun := g.continuous_toFun

lemma toContinuousMap_injective : Injective (toContinuousMap : Cᶠ[f]⟮F, E; F', E'⟯ → _) := by
  intro g g' h
  ext b x
  simpa [toContinuousMap, TotalSpace.map] using congrFun (congrArg ContinuousMap.toFun h) ⟨_, x⟩

set_option backward.defeqAttrib.useBackward true in
/-- Construct a bundle morphism out of a continuous map of the total spaces that respects the
fibres. This construction has really bad defeq properties, so it should be used only when
absolutely necessary. -/
def ofContinuousMap (g : C(TotalSpace F E, TotalSpace F' E')) (hg : ∀ x, (g x).proj = f x.proj) :
    Cᶠ[f]⟮F, E; F', E'⟯ where
  toFun b x := cast (congrArg E' <| hg ⟨b, x⟩) (g ⟨b, x⟩).2
  continuous_toFun := by
    refine (map_continuous g).congr fun ⟨b, x⟩ ↦ ?_
    ext
    · simp [hg]
    · simp

@[simp]
lemma ofContinuousMap_toContinuousMap (g : Cᶠ[f]⟮F, E; F', E'⟯) :
    ofContinuousMap (g.toContinuousMap) (fun _ ↦ rfl) = g := by
  ext b x
  rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma toContinuousMap_ofContinuousMap (g : C(TotalSpace F E, TotalSpace F' E'))
    (hg : ∀ x, (g x).proj = f x.proj) :
    (ofContinuousMap g hg).toContinuousMap = g := by
  ext ⟨b, x⟩
  · simp [hg]
  · simp [ofContinuousMap]

variable [TopologicalSpace F] [TopologicalSpace B] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [TopologicalSpace F'] [TopologicalSpace B'] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E']

/-- The restriction of a continuous fibrewise map to a single fibre. -/
@[simps]
def continuousMapAt (g : Cᶠ[f]⟮F, E; F', E'⟯) (b : B) : C(E b, E' (f b)) where
  toFun := g b
  continuous_toFun := by
    rw [(FiberBundle.totalSpaceMk_isInducing F' E' (f b)).continuous_iff]
    exact g.continuous_toFun.comp (FiberBundle.totalSpaceMk_isInducing F E b).continuous

/-- TODO: find home -/
@[fun_prop]
lemma _root_.Bundle.TotalSpace.continuous_trivialSnd : Continuous (TotalSpace.trivialSnd B F) := by
  simp [continuous_iff_le_induced, Trivial.topologicalSpace]

/-- TODO: find home -/
lemma _root_.Bundle.Trivial.continuous_iff {X : Type*} [TopologicalSpace X]
    (g : X → TotalSpace F (Trivial B F)) :
    Continuous g ↔
      Continuous (TotalSpace.proj ∘ g) ∧ Continuous (TotalSpace.trivialSnd _ _ ∘ g) := by
  simp [continuous_iff_le_induced, Trivial.topologicalSpace, induced_compose]

/-- Continuous fibrewise maps into a trivial bundle correspond to continuous maps into the standard
fibre of the model. -/
def trivialEquiv {f : C(B, B')} : Cᶠ[f]⟮F, E; F', Trivial B' F'⟯ ≃ C(TotalSpace F E, F') where
  toFun g := .comp ⟨TotalSpace.trivialSnd _ _, by fun_prop⟩ g.toContinuousMap
  invFun g := ⟨fun b x ↦ g ⟨b, x⟩,
    (Trivial.continuous_iff _).2 ⟨(map_continuous f).comp (continuous_proj _ _), map_continuous g⟩⟩
  left_inv _ := by ext; simp [TotalSpace.trivialSnd]
  right_inv _ := by ext; simp [TotalSpace.trivialSnd]

/-- `Bundle.Pullback.lift` as a continuous fibrewise map. -/
@[simps]
def pullbackLift {f : B' → B} : Cᶠ[f]⟮F, f *ᵖ E; F, E⟯ where
  toFun _ x := x
  continuous_toFun := Pullback.continuous_lift F E f

omit [TopologicalSpace F] [TopologicalSpace B] [(b : B) → TopologicalSpace (E b)]
  [FiberBundle F E] in
/-- TODO: find home -/
lemma _root_.Pullback.TotalSpace.continuous_iff {X : Type*} [TopologicalSpace X] {f : B' → B}
    (g : X → TotalSpace F (f *ᵖ E)) :
    Continuous g ↔ Continuous (TotalSpace.proj ∘ g) ∧ Continuous (Pullback.lift f ∘ g):= by
  simp [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace,
    pullbackTopology_def, induced_compose]

/-- Continuous fibrewise maps from a bundle `E` over `B` to a bundle `E'` over `B'` relative to a
map `B → B'` are equivalently continuous fibrewise maps from `E` to the pullback `f *ᵖ E'` of `E'`
to `B`. -/
@[simps]
def pullbackEquiv : Cᶠ[f]⟮F, E; F', E'⟯ ≃ Cᶠ⟮F, E; F', f *ᵖ E'⟯ where
  toFun f' :=
    ⟨f', (Pullback.TotalSpace.continuous_iff _).2 ⟨continuous_proj F E, f'.continuous_toFun⟩⟩
  invFun f' := ⟨f', (Pullback.continuous_lift F' E' f).comp f'.continuous_toFun⟩
  left_inv _ := rfl
  right_inv _ := rfl

end ContinuousBundleHom
