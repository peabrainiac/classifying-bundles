/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.CountableTrans
import ClassifyingBundles.MulActionEquiv
import ClassifyingBundles.TrivialSMul
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Topology.Homotopy.Equiv

/-! # Equivariant continuous maps

In this file we define a type `ContinuousMulActionHom` of equivariant continuous maps,
and a type `ContinuousMulActionEquiv` of equivariant homeomorphisms.
-/

open scoped ContinuousMap

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

@[simp]
lemma comp_id {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SMul M X] [SMul M Y]
    {f : C[M](X, Y)} : f.comp (.id _ _) = f := by
  ext; simp

@[simp]
lemma id_comp {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SMul M X] [SMul M Y]
    {f : C[M](X, Y)} : .comp (.id _ _) f = f := by
  ext; simp

lemma comp_assoc {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [TopologicalSpace W] [SMul M X] [SMul M Y] [SMul M Z] [SMul M W]
    (f : C[M](Z, W)) (f' : C[M](Y, Z)) (f'' : C[M](X, Y)) :
    (f.comp f').comp f'' = f.comp (f'.comp f'') :=
  rfl

/-- We equip `Cₑ[φ](X, Y)` with the topology induced by the compact-open topology on `C(X, Y)`. -/
instance : TopologicalSpace Cₑ[φ](X, Y) := .induced (fun f ↦ toContinuousMap f) inferInstance

lemma isInducing_toContinuousMap :
    Topology.IsInducing fun f : Cₑ[φ](X, Y) ↦ toContinuousMap f :=
  ⟨rfl⟩

/-- When `M` acts trivially on `X`, `M`-equivariant functions out of `X × M` are equivalently just
continuous functions out of `X`. -/
@[simps!]
def equivContinuousMap [TopologicalSpace M] [TopologicalSpace N] [Monoid M] [Monoid N] {φ : M →ₜ* N}
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SMul M X] [TrivialSMul M X]
    [MulAction N Y] [ContinuousSMul N Y] :
    Cₑ[φ](X × M, Y) ≃ C(X, Y) where
  toFun f := (toContinuousMap f).comp <| .prodMk (.id _) (.const _ 1)
  invFun f := {
    toFun x := φ x.2 • f x.1
    map_smul' := by simp [mul_smul] }
  left_inv _ := by ext; simp [← ContinuousMulActionHom.map_smul'']
  right_inv _ := by ext; simp

/-- Homotopies of continuous equivariant maps. -/
abbrev Homotopy (f g : Cₑ[φ](X, Y)) :=
  ContinuousMap.HomotopyWith (toContinuousMap f) (toContinuousMap g)
    (fun f ↦ ∀ (m : M) x, f (m • x) = φ m • f x)

namespace Homotopy

@[simp]
lemma map_smul {f g : Cₑ[φ](X, Y)} {F : f.Homotopy g} {t : unitInterval} {m : M} {x : X} :
    F (t, m • x) = (φ m) • F (t, x) := by
  simpa using F.prop t m x

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

@[simp]
lemma curry_apply {f f' : Cₑ[φ](X, Y)} {F : f.Homotopy f'} {t : unitInterval} {x : X} :
    F.curry t x = F (t, x) := rfl

@[simp]
lemma curry_zero {f f' : Cₑ[φ](X, Y)} {F : f.Homotopy f'} : F.curry 0 = f := by
  simp [curry]

@[simp]
lemma curry_one {f f' : Cₑ[φ](X, Y)} {F : f.Homotopy f'} : F.curry 1 = f' := by
  simp [curry]

open Filter unitInterval Topology in
/-- The concatenation of countably many equivariant homotopies `F n : (f n).Homotopy (f (n + 1))`
leading up to a single equivariant map `g`. -/
noncomputable def countableTrans {f : ℕ → Cₑ[φ](X, Y)} (F : (n : ℕ) → (f n).Homotopy (f (n + 1)))
    (g : Cₑ[φ](X, Y))
    (hFg : ∀ x, Tendsto (fun x : ℕ × I × X ↦ F x.1 x.2) (atTop ×ˢ ⊤ ×ˢ 𝓝 x) (𝓝 (g x))) :
    (f 0).Homotopy g where
  toHomotopy := .countableTrans (fun n ↦ (F n).toHomotopy) g hFg
  prop' t g x := by
    simp [ContinuousMap.Homotopy.countableTrans, ContinuousMap.Homotopy.countableTransFun]

end Homotopy

/-- Two continuous equivariant maps are homotopic if there exists a homotopy of continuous
equivariant maps between them. -/
def Homotopic (f g : Cₑ[φ](X, Y)) := Nonempty (Homotopy f g)

lemma Homotopy.homotopic {f f' : Cₑ[φ](X, Y)} (F : f.Homotopy f') : f.Homotopic f' := ⟨F⟩

namespace Homotopic

lemma toContinuousMap {f g : Cₑ[φ](X, Y)} (h : f.Homotopic g) :
    (toContinuousMap f).Homotopic (toContinuousMap g) :=
  ⟨h.some.toHomotopy⟩

@[refl]
lemma refl (f : Cₑ[φ](X, Y)) : f.Homotopic f := ⟨.refl f⟩

@[symm]
lemma symm {f f' : Cₑ[φ](X, Y)} (h : f.Homotopic f') : f'.Homotopic f := ⟨h.some.symm⟩

lemma trans {f f' f'' : Cₑ[φ](X, Y)} (h : f.Homotopic f') (h' : f'.Homotopic f'') :
    f.Homotopic f'' := ⟨h.some.trans h'.some⟩

/-- Transitivity of `Homotopic`, in the form needed for `gcongr` and `grw` to be able to rewrite
in both arguments of a `Homotopic` goal. -/
instance : IsTrans Cₑ[φ](X, Y) Homotopic := ⟨fun _ _ _ ↦ trans⟩

@[gcongr]
lemma comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [SMul M X] [SMul M Y] [SMul M Z] {f f' : C[M](Y, Z)} {f'' f''' : C[M](X, Y)}
    (h : f.Homotopic f') (h' : f''.Homotopic f''') : (f.comp f'').Homotopic (f'.comp f''') :=
  ⟨h.some.comp h'.some⟩

/-- The bijection between equivariant maps `Cₑ[φ](X × M, Y)` and continuous maps `C(X, Y)` when `M`
acts trivially on `X`, as an isomorphism of the equivalence relations
`ContinuousMulActionHom.Homotopic` and `ContinuousMap.Homotopic`. -/
def relIsoContinuousMap [TopologicalSpace M] [TopologicalSpace N] [Monoid M] [Monoid N]
    {φ : M →ₜ* N} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SMul M X]
    [TrivialSMul M X] [MulAction N Y] [ContinuousSMul N Y] :
    (Homotopic (φ := φ) (X := X × M) (Y := Y)) ≃r
      (ContinuousMap.Homotopic (X := X) (Y := Y)) where
  toEquiv := equivContinuousMap
  map_rel_iff' {f f'} := by
    refine ⟨fun ⟨F⟩ ↦ ⟨?_⟩, fun h ↦ h.toContinuousMap.comp <| .refl _⟩
    exact {
      toFun x := φ x.2.2 • F (x.1, x.2.1)
      map_zero_left := by simp [← f.map_smul'']
      map_one_left := by simp [← f'.map_smul'']
      prop' _ _ _ := by simp [mul_smul] }

end Homotopic

end ContinuousMulActionHom

structure ContinuousMulActionEquiv {M N : Type*} (φ : M ≃ N)
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [SMul M X] [SMul N Y] extends
  X ≃ₜ Y, X ≃ₑ[φ] Y

/-- Equivariant homeomorphisms `X ≃ₜ Y` along a bijection `M ≃ N`. -/
notation:25 X " ≃ₜₑ[" φ:25 "] " Y:0 => ContinuousMulActionEquiv φ X Y

/-- `M`-equivariant homeomorphisms `X ≃ₜ Y`. This is the same as `X ≃ₜₑ[Equiv.refl M] Y`. -/
notation:25 X " ≃ₜ[" M:25 "] " Y:0 => ContinuousMulActionEquiv (Equiv.refl M) X Y

namespace ContinuousMulActionEquiv

variable {M N : Type*} {φ : M ≃ N} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SMul M X] [SMul N Y]

lemma toHomeomorph_injective : (toHomeomorph : (X ≃ₜₑ[φ] Y) → X ≃ₜ Y).Injective
  | ⟨_, _⟩, ⟨_, _⟩, h => by grind

instance : EquivLike (X ≃ₜₑ[φ] Y) X Y where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' _ _ h h' := toHomeomorph_injective <| EquivLike.coe_injective' _ _ h h'

instance : MulActionSemiHomClass (X ≃ₜₑ[φ] Y) φ X Y where
  map_smulₛₗ e m x := e.map_smul' m x

instance : HomeomorphClass (X ≃ₜₑ[φ] Y) X Y where
  map_continuous e := e.continuous_toFun
  inv_continuous e := e.continuous_invFun

@[simp]
lemma coe_toHomeomorph {e : X ≃ₜₑ[φ] Y} : ⇑e.toHomeomorph = e := rfl

/-- The continuous equivariant map underlying a continuous equivariant homeomorphism. -/
def toContinuousMulActionHom (e : X ≃ₜₑ[φ] Y) : Cₑ[φ](X, Y) where
  __ := e

@[simp]
lemma coe_toContinuousMulActionHom {e : X ≃ₜₑ[φ] Y} : ⇑e.toContinuousMulActionHom = e := rfl

@[simp]
lemma coe_mk {toHomeomorph : X ≃ₜ Y}
    {map_smul' : ∀ m x, toHomeomorph.toFun (m • x) = φ m • toHomeomorph.toFun x} :
    ⇑(ContinuousMulActionEquiv.mk toHomeomorph map_smul') = toHomeomorph := rfl

@[ext]
lemma ext {e e' : X ≃ₜₑ[φ] Y} (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

lemma map_smul'' (e : X ≃ₜₑ[φ] Y) (m : M) (x : X) : e (m • x) = φ m • e x :=
  e.map_smul' m x

lemma map_smul {M : Type*} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SMul M X] [SMul M Y] (e : X ≃ₜ[M] Y) (m : M) (x : X) : e (m • x) = m • e x := by
  simp

variable (M) (X) in
/-- The identity map on `X` as an equivariant homeomorphism. -/
def refl : X ≃ₜ[M] X where
  toHomeomorph := .refl _
  map_smul' := by simp

@[simp]
lemma coe_refl : ⇑(refl M X) = id := rfl

@[simp]
lemma toContinuousMulActionHom_refl : (refl M X).toContinuousMulActionHom = .id M X := rfl

/-- The inverse of an equivariant homeomorphism.

TODO: generalise this to homeomorphisms that are equivariant along isomorphisms of the groups -/
def symm {M : Type*} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SMul M X] [SMul M Y] (e : X ≃ₜ[M] Y) : Y ≃ₜ[M] X where
  toHomeomorph := .symm e
  map_smul' := e.toMulActionEquiv.symm.map_smul

@[simp]
lemma apply_symm_apply {M : Type*} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SMul M X] [SMul M Y] {e : X ≃ₜ[M] Y} {y : Y} : e (e.symm y) = y :=
  e.toHomeomorph.apply_symm_apply y

@[simp]
lemma symm_apply_apply {M : Type*} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SMul M X] [SMul M Y] {e : X ≃ₜ[M] Y} {x : X} : e.symm (e x) = x :=
  e.toHomeomorph.symm_apply_apply x

/-- The composition of equivariant homeomorphisms.

TODO: generalise this to homeomorphisms that are equivariant along isomorphisms of the groups -/
def trans {M : Type*} {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [SMul M X] [SMul M Y] [SMul M Z] (e : X ≃ₜ[M] Y) (e' : Y ≃ₜ[M] Z) : X ≃ₜ[M] Z where
  toHomeomorph := .trans e e'.toHomeomorph
  map_smul' := by simp

@[simp]
lemma coe_trans {M : Type*} {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [SMul M X] [SMul M Y] [SMul M Z] {e : X ≃ₜ[M] Y} {e' : Y ≃ₜ[M] Z} :
    ⇑(e.trans e') = e' ∘ e :=
  rfl

@[simp]
lemma toContinuousMulActionHom_trans {M : Type*} {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [SMul M X] [SMul M Y] [SMul M Z]
    {e : X ≃ₜ[M] Y} {e' : Y ≃ₜ[M] Z} :
    (e.trans e').toContinuousMulActionHom =
      e'.toContinuousMulActionHom.comp e.toContinuousMulActionHom :=
  rfl

@[simp]
lemma symm_trans_self {M : Type*} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SMul M X] [SMul M Y] {e : X ≃ₜ[M] Y} : e.symm.trans e = .refl _ _ := by
  ext; simp

@[simp]
lemma self_trans_symm {M : Type*} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SMul M X] [SMul M Y] {e : X ≃ₜ[M] Y} : e.trans e.symm = .refl _ _ := by
  ext; simp

end ContinuousMulActionEquiv

@[simp]
lemma ContinuousMulActionHom.Homotopic.comp_continuousMulActionEquiv_iff {M : Type*} {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [SMul M X] [SMul M Y] [SMul M Z] {f f' : C[M](Y, Z)} (e : X ≃ₜ[M] Y) :
    (f.comp e.toContinuousMulActionHom).Homotopic (f'.comp e.toContinuousMulActionHom) ↔
      f.Homotopic f' := by
  refine ⟨fun ⟨F⟩ ↦ ?_, fun h ↦ h.comp (.refl _)⟩
  rw [← f.comp_id, ← f'.comp_id, ← ContinuousMulActionEquiv.toContinuousMulActionHom_refl,
    ← e.symm_trans_self, ContinuousMulActionEquiv.toContinuousMulActionHom_trans]
  exact ⟨F.comp (.refl _)⟩

@[simp]
lemma ContinuousMulActionHom.Homotopic.continuousMulActionEquiv_comp_iff {M : Type*} {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [SMul M X] [SMul M Y] [SMul M Z] {f f' : C[M](X, Y)} (e : Y ≃ₜ[M] Z) :
    (e.toContinuousMulActionHom.comp f).Homotopic (e.toContinuousMulActionHom.comp f') ↔
      f.Homotopic f' := by
  refine ⟨fun ⟨F⟩ ↦ ?_, fun h ↦ .comp (.refl _) h⟩
  rw [← f.id_comp, ← f'.id_comp, ← ContinuousMulActionEquiv.toContinuousMulActionHom_refl,
    ← e.self_trans_symm, ContinuousMulActionEquiv.toContinuousMulActionHom_trans]
  exact ⟨.comp (.refl e.symm.toContinuousMulActionHom) F⟩

namespace ContinuousMulActionHom

/-- A `G`-homotopy equivalence between `G`-spaces `X` and `Y` is a pair of `G`-equivariant functions
`C[G](X, Y)`, `C[M](Y, X)` such that the two compositions of the two are both `G`-equivariantly
homotopic to the identity. -/
structure HomotopyEquiv (M : Type*) (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] [SMul M X] [SMul M Y] where
  toFun : C[M](X, Y)
  invFun : C[M](Y, X)
  left_inv : (invFun.comp toFun).Homotopic (.id M X)
  right_inv : (toFun.comp invFun).Homotopic (.id M Y)

@[inherit_doc]
notation:25 X " ≃ₕ[" G:25 "] " Y:0 => HomotopyEquiv G X Y

namespace HomotopyEquiv

variable {M : Type*} {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [SMul M X] [SMul M Y] [SMul M Z]

instance : CoeFun (X ≃ₕ[M] Y) fun _ ↦ (X → Y) where
  coe h := h.toFun

@[simp]
lemma coe_toFun (h : X ≃ₕ[M] Y) : ⇑h.toFun = h := rfl

/-- Convert an equivariant homotopy equivalence to simply a homotopy equivalence. -/
def toHomotopyEquiv (h : X ≃ₕ[M] Y) : X ≃ₕ Y where
  toFun := h.toFun.toContinuousMap
  invFun := h.invFun.toContinuousMap
  left_inv := h.left_inv.toContinuousMap
  right_inv := h.right_inv.toContinuousMap

@[simp]
lemma coe_toHomotopyEquiv (h : X ≃ₕ[M] Y) : ⇑h.toHomotopyEquiv = h := rfl

/-- Convert an equivariant homeomorphism to an equivariant homotopy equivalence. -/
def _root_.ContinuousMulActionEquiv.toHomotopyEquiv (e : X ≃ₜ[M] Y) : X ≃ₕ[M] Y where
  toFun := e.toContinuousMulActionHom
  invFun := e.symm.toContinuousMulActionHom
  left_inv := by simp [← e.toContinuousMulActionHom_trans, Homotopic.refl]
  right_inv := by simp [← e.symm.toContinuousMulActionHom_trans, Homotopic.refl]

@[simp]
lemma _root_.ContinuousMulActionEquiv.coe_toHomotopyEquiv (e : X ≃ₜ[M] Y) :
    ⇑e.toHomotopyEquiv = e := rfl

variable (M X) in
/-- The identity as an equivariant homotopy equivalence. -/
def refl : X ≃ₕ[M] X := (ContinuousMulActionEquiv.refl M X).toHomotopyEquiv

@[simp]
lemma coe_refl : ⇑(refl M X) = id := rfl

/-- The inverse of an equivariant homotopy equivalence. -/
def symm (h : X ≃ₕ[M] Y) : Y ≃ₕ[M] X where
  toFun := h.invFun
  invFun := h.toFun
  left_inv := h.right_inv
  right_inv := h.left_inv

@[simp]
lemma coe_invFun (h : X ≃ₕ[M] Y) : ⇑h.invFun = h.symm := rfl

/-- The composition of two equivariant homotopy equivalences. -/
def trans (h : X ≃ₕ[M] Y) (h' : Y ≃ₕ[M] Z) : X ≃ₕ[M] Z where
  toFun := h'.toFun.comp h.toFun
  invFun := h.invFun.comp h'.invFun
  left_inv := .trans (by exact .comp (.refl _) (.comp h'.left_inv (.refl _))) h.left_inv
  right_inv := .trans (by exact .comp (.refl _) (.comp h.right_inv (.refl _))) h'.right_inv

@[simp]
lemma coe_trans (h : X ≃ₕ[M] Y) (h' : Y ≃ₕ[M] Z) : ⇑(h.trans h') = h' ∘ h := rfl

end HomotopyEquiv

end ContinuousMulActionHom

@[simp]
lemma ContinuousMulActionHom.Homotopic.comp_homotopyEquiv_iff {M : Type*} {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [SMul M X] [SMul M Y] [SMul M Z] {f f' : C[M](Y, Z)} (e : X ≃ₕ[M] Y) :
    (f.comp e.toFun).Homotopic (f'.comp e.toFun) ↔
      f.Homotopic f' := by
  refine ⟨fun ⟨F⟩ ↦ ?_, fun h ↦ h.comp (.refl _)⟩
  grw [← f.comp_id, ← f'.comp_id, ← e.right_inv, ← comp_assoc, ← comp_assoc, F.homotopic]

@[simp]
lemma ContinuousMulActionHom.Homotopic.homotopyEquiv_comp_iff {M : Type*} {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [SMul M X] [SMul M Y] [SMul M Z] {f f' : C[M](X, Y)} (e : Y ≃ₕ[M] Z) :
    (e.toFun.comp f).Homotopic (e.toFun.comp f') ↔
      f.Homotopic f' := by
  refine ⟨fun ⟨F⟩ ↦ ?_, fun h ↦ .comp (.refl _) h⟩
  grw [← f.id_comp, ← f'.id_comp, ← e.left_inv, comp_assoc, comp_assoc, F.homotopic]
