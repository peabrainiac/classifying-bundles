/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Topology.Homotopy.Basic

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

@[simp]
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

@[simp]
lemma coe_toContinuousMap {f : Cₑ[φ](X, Y)} : ⇑f.toContinuousMap = f := rfl

@[simp]
lemma coe_toMulActionHom {f : Cₑ[φ](X, Y)} : ⇑f.toMulActionHom = f := rfl

initialize_simps_projections ContinuousMulActionHom (toFun → apply)

variable (M) (X) in
/-- The identity on `X` as a continuous equivariant map. -/
@[simps!]
protected def id : C[M](X, X) := ⟨.id X, by simp⟩

/-- The composition of two continuous equivariant maps.

TODO: generalise this to maps that are equivariant along maps of the groups -/
@[simps!]
protected def comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [SMul M X] [SMul M Y] [SMul M Z] (f : C[M](Y, Z)) (g : C[M](X, Y)) : C[M](X, Z) where
  toContinuousMap := (toContinuousMap f).comp (toContinuousMap g)
  map_smul' := by simp

/-- We equip `Cₑ[φ](X, Y)` with the topology induced by the compact-open topology on `C(X, Y)`. -/
instance : TopologicalSpace Cₑ[φ](X, Y) := .induced (fun f ↦ toContinuousMap f) inferInstance

lemma isInducing_toContinuousMap :
    Topology.IsInducing fun f : Cₑ[φ](X, Y) ↦ toContinuousMap f :=
  ⟨rfl⟩

/-- Homotopies of continuous equivariant maps. -/
abbrev Homotopy (f g : Cₑ[φ](X, Y)) :=
  ContinuousMap.HomotopyWith (toContinuousMap f) (toContinuousMap g)
    (fun f ↦ ∀ (m : M) x, f (m • x) = φ m • f x)

namespace Homotopy

/-- The constant homotopy from any continuous equivariant map to itself. -/
def refl (f : Cₑ[φ](X, Y)) : f.Homotopy f :=
  ContinuousMap.HomotopyWith.refl _ (by simp)

/-- The homotopy from `g` to `f` given by reversing a homotopy of equivariant maps
from `f` to `g`. -/
def symm {f g : Cₑ[φ](X, Y)} (F : f.Homotopy g) : g.Homotopy f :=
  ContinuousMap.HomotopyWith.symm F

/-- The concatenation of two homotopies of equivariant maps. -/
noncomputable def trans {f f' f'' : Cₑ[φ](X, Y)} (F : f.Homotopy f') (F' : f'.Homotopy f'') :
    f.Homotopy f'' :=
  ContinuousMap.HomotopyWith.trans F F'

/-- The composition of two homotopies of equivariant maps. -/
def comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [SMul M X] [SMul M Y] [SMul M Z] {f f' : C[M](Y, Z)} (F : f.Homotopy f')
    {f'' f''' : C[M](X, Y)} (F' : f''.Homotopy f''') : (f.comp f'').Homotopy (f'.comp f''') where
  toHomotopy := F.toHomotopy.comp F'.toHomotopy
  prop' t m x := by
    simp only [ContinuousMap.Homotopy.comp, id_eq, ContinuousMap.HomotopyWith.coe_toHomotopy,
      ContinuousMap.toFun_eq_coe, ContinuousMap.coe_mk]
    have h := F.prop t m; have h' := F'.prop t m
    simp only [id_eq, ContinuousMap.Homotopy.curry_apply,
      ContinuousMap.HomotopyWith.coe_toHomotopy] at h h'
    simp [h, h']

/-- Every homotopy of equivariant maps defines a continuous map from the unit interval to
the space of continuous equivariant maps. None that while the converse requires additional
topological assumptions, this does not. -/
def curry {f f' : Cₑ[φ](X, Y)} (F : f.Homotopy f') : C(unitInterval, Cₑ[φ](X, Y)) where
  toFun t := ⟨F.toHomotopy.curry t, F.prop t⟩
  continuous_toFun :=
    isInducing_toContinuousMap.continuous_iff.2 <| map_continuous F.toHomotopy.curry

end Homotopy

/-- Two continuous equivariant maps are homotopic if there exists a homotopy of continuous
equivariant maps between them. -/
def Homotopic (f g : Cₑ[φ](X, Y)) := Nonempty (Homotopy f g)

namespace Homotopic

lemma refl (f : Cₑ[φ](X, Y)) : f.Homotopic f := ⟨.refl f⟩

lemma symm {f f' : Cₑ[φ](X, Y)} (h : f.Homotopic f') : f'.Homotopic f := ⟨h.some.symm⟩

lemma trans {f f' f'' : Cₑ[φ](X, Y)} (h : f.Homotopic f') (h' : f'.Homotopic f'') :
    f.Homotopic f'' := ⟨h.some.trans h'.some⟩

lemma comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [SMul M X] [SMul M Y] [SMul M Z] {f f' : C[M](Y, Z)} (h : f.Homotopic f')
    {f'' f''' : C[M](X, Y)} (h' : f''.Homotopic f''') : (f.comp f'').Homotopic (f'.comp f''') :=
  ⟨h.some.comp h'.some⟩

end Homotopic

end ContinuousMulActionHom
