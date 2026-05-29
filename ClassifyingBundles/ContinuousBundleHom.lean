import Mathlib.Topology.FiberBundle.Basic

/-! # Bundled continuous fibrewise maps between fibre bundles -/

open Bundle FiberBundle Function

variable (F : Type*) {B : Type*} (E : B → Type*) [TopologicalSpace (Bundle.TotalSpace F E)]
  (F' : Type*) {B' : Type*} (E' : B' → Type*) [TopologicalSpace (Bundle.TotalSpace F' E')]

variable {E E'} in
/-- The map `TotalSpace F E → TotalSpace F' E'` given by a map `f : B → B'` and a map
`f' b : E b → E' (f b)` for each `b`. -/
@[simps]
def Bundle.TotalSpace.map {f : B → B'} (f' : ∀ b, E b → E' (f b)) (x : TotalSpace F E) :
    TotalSpace F' E' := ⟨_, f' _ x.2⟩

omit [TopologicalSpace (Bundle.TotalSpace F E)] [TopologicalSpace (Bundle.TotalSpace F' E')] in
lemma Bundle.TotalSpace.map_injective {f : B → B'} :
    Injective (map F F' : (∀ b, E b → E' (f b)) → _) := by
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

instance instDFunLike {f : B → B'} : DFunLike Cᶠ[f]⟮F, E; F', E'⟯ B (fun b ↦ (E b → E' (f b))) where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h; congr

@[simp]
theorem coeFn_mk {f : B → B'} (f' : ∀ b, E b → E' (f b))
    (hf : Continuous (TotalSpace.map F F' f')) :
    (mk f' hf : ∀ _, _) = f' := rfl

@[ext]
theorem ext {f : B → B'} {g g' : Cᶠ[f]⟮F, E; F', E'⟯} (h : ∀ b x, g b x = g' b x) : g = g' :=
  DFunLike.ext _ _ fun b ↦ funext <| h b

/-- The continuous map between total spaces underlying a continuous fibrewise map. -/
@[simps!]
def toContinuousMap {f : B → B'} (g : Cᶠ[f]⟮F, E; F', E'⟯) :
    C(TotalSpace F E, TotalSpace F' E') where
  toFun := TotalSpace.map F F' g
  continuous_toFun := g.continuous_toFun

lemma toContinuousMap_injective {f : B → B'} :
    Injective (toContinuousMap : Cᶠ[f]⟮F, E; F', E'⟯ → _) := by
  intro g g' h
  ext b x
  simpa [toContinuousMap, TotalSpace.map] using congrFun (congrArg ContinuousMap.toFun h) ⟨_, x⟩

variable [TopologicalSpace F] [TopologicalSpace B] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [TopologicalSpace F'] [TopologicalSpace B'] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E']

/-- The restriction of a continuous fibrewise map to a single fibre. -/
@[simps]
def continuousMapAt {f : B → B'} (g : Cᶠ[f]⟮F, E; F', E'⟯) (b : B) : C(E b, E' (f b)) where
  toFun := g b
  continuous_toFun := by
    rw [(FiberBundle.totalSpaceMk_isInducing F' E' (f b)).continuous_iff]
    exact g.continuous_toFun.comp (FiberBundle.totalSpaceMk_isInducing F E b).continuous

end ContinuousBundleHom
