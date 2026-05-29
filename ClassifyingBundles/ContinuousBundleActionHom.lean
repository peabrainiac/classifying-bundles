import ClassifyingBundles.ContinuousBundleHom
import ClassifyingBundles.TopologicalTorsor

/-! # Bundled continuous fibrewise equivariant maps between fibre bundles-/

open Bundle FiberBundle Function

-- TODO: generalise from groups to monoids or plain types where possible
variable (G : Type*) (F : Type*) {B : Type*} (E : B → Type*)
  [TopologicalSpace (Bundle.TotalSpace F E)]
  (H : Type*) (F' : Type*) {B' : Type*} (E' : B' → Type*)
  [TopologicalSpace (Bundle.TotalSpace F' E')]
  [∀ b, SMul G (E b)] [∀ b', SMul H (E' b')] {φ : G → H} {f : B → B'}

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
scoped[Bundle] notation "Cᶠₑ[" G "]⟮" F ", " E "; " F' ", " E' "⟯" =>
  ContinuousBundleActionHom F E F' E' (@id G) id


/-- When `G` acts on every fibre of a bundle `E`, we equip `Bundle.TotalSpace F E` with the
corresponding `G`-action as well.
TODO: find a more permanent home for this. -/
@[simps]
instance : SMul G (TotalSpace F E) where
  smul g x := ⟨_, g • x.2⟩

namespace ContinuousBundleActionHom

variable {G F E H F' E'}

instance instDFunLike : DFunLike Cᶠₑ[φ, f]⟮F, E; F', E'⟯ B (fun b ↦ (E b → E' (f b))) where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟩⟩ ⟨⟩ _; congr

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

end ContinuousBundleActionHom
