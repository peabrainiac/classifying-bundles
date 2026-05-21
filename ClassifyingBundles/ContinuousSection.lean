import Mathlib.Topology.FiberBundle.Basic

/-! # Continuous sections of fibre bundles
API for bundled continuous sections of topological fibre bundles. Adapted from the API for Cⁿ
sections of Cⁿ fibre bundles at `Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection`.
-/

open Function

namespace Bundle

variable (F : Type*) [TopologicalSpace F] {B : Type*} [TopologicalSpace B]
  (E : B → Type*) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E]

/-- The type of continuous sections of a topological `FiberBundle F E`, written `Cₛ(F, E)` in
the `Bundle` namespace. -/
structure ContinuousSection (F : Type*) [TopologicalSpace F] {B : Type*} [TopologicalSpace B]
    (E : B → Type*) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] where
  toFun : ∀ b, E b
  continuous_toFun : Continuous fun b ↦ (⟨b, toFun b⟩ : TotalSpace F E)

@[inherit_doc] scoped[Bundle] notation "Cₛ⟮" F ", " E "⟯" => ContinuousSection F E

namespace ContinuousSection

variable {F E}

instance : DFunLike Cₛ⟮F, E⟯ B E where
  coe := ContinuousSection.toFun
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h; congr

variable {s t : Cₛ⟮F, E⟯}

@[simp]
theorem coeFn_mk (s : ∀ b, E b) (hs : Continuous fun b ↦ (⟨b, s b⟩ : TotalSpace F E)) :
    (mk s hs : ∀ b, E b) = s := rfl

protected theorem continuous (s : Cₛ⟮F, E⟯) : Continuous fun b ↦ (⟨b, s b⟩ : TotalSpace F E) :=
  s.continuous_toFun

theorem coe_inj ⦃s t : Cₛ⟮F, E⟯⦄ (h : (s : ∀ b, E b) = t) : s = t :=
  DFunLike.ext' h

theorem coe_injective : Injective ((↑) : Cₛ⟮F, E⟯ → ∀ b, E b) :=
  coe_inj

@[ext]
theorem ext (h : ∀ x, s x = t x) : s = t := DFunLike.ext _ _ h

end ContinuousSection

end Bundle
