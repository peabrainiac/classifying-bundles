/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Topology.ContinuousMap.Basic

/-! # Equivariant continuous maps

In this file we define a type `ContinuousMulActionHom` of equivariant continuous maps.
-/

/-- A continuous `φ`-equivariant map. -/
structure ContinuousMulActionHom {M N : Type*} (φ : M → N)
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [SMul M X] [SMul N Y] extends
  C(X, Y), X →ₑ[φ] Y

/-- `φ`-equivariant continuous maps `X → Y`. -/
notation "Cₑ[" φ "](" X ", " Y ")" => ContinuousMulActionHom φ X Y

/-- `M`-equivariant continuous maps `X → Y`. -/
notation "C[" M "](" X ", " Y ")" => ContinuousMulActionHom (@id M) X Y

namespace ContinuousMulActionHom

variable {M N : Type*} {φ : M → N}
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SMul M X] [SMul N Y]

instance : FunLike (Cₑ[φ](X, Y)) X Y where
  coe f := f.toFun
  coe_injective f g := by cases f; cases g; simp

instance : ContinuousMapClass Cₑ[φ](X, Y) X Y where
  map_continuous f := map_continuous f.toContinuousMap

instance : MulActionSemiHomClass Cₑ[φ](X, Y) φ X Y where
  map_smulₛₗ f m x := f.toMulActionHom.map_smul' m x

@[ext]
protected lemma ext {f f' : Cₑ[φ](X, Y)} (h : ∀ x, f x = f' x) : f = f' :=
  DFunLike.ext _ _ h

lemma map_smul'' (f : Cₑ[φ](X, Y)) (m : M) (x : X) :
    f (m • x) = φ m • f x :=
  f.map_smul' m x

lemma map_smul [SMul M Y] (f : C[M](X, Y)) (m : M) (x : X) :
    f (m • x) = m • f x :=
  f.toMulActionHom.map_smul m x

@[simp]
lemma coe_mk (f : C(X, Y)) (hf : ∀ m x, f.toFun (m • x) = φ m • f.toFun x) :
    ⇑(mk f hf) = f :=
  rfl

@[simp]
lemma toFun_eq_coe {f : Cₑ[φ](X, Y)} : f.toFun = f := rfl

initialize_simps_projections ContinuousMulActionHom (toFun → apply)

variable (M) (X) in
@[simps!]
protected def id : C[M](X, X) := ⟨.id X, by simp⟩

end ContinuousMulActionHom
