/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.CompactOpen

/-! # Topologically inducing group actions
In this file we define what we call "inducing" group actions, group actions `SMul G X` for which
multiplication by each `g : G` is a continuous map `X → X`  and the resulting map `G → C(X, X)` is
topologically inducing. In other words (assuming local compactness of `Y`), a map `Y → G` is
continuous iff the corresponding map `Y × X → X` is.
-/

/-- Left multiplication by `g` as a continuous map. -/
@[simps]
def ContinuousMap.constSMul {G X : Type*} [TopologicalSpace X] [SMul G X]
    [ContinuousConstSMul G X] (g : G) : C(X, X) where
  toFun x := g • x
  continuous_toFun := by fun_prop

/-- We call an action "inducing" if `fun x ↦ g • x` is a continuous map for each `g` and the
resulting map `G → C(X, X)` is topologically inducing. -/
class InducingSMul (G X : Type*) [TopologicalSpace G] [TopologicalSpace X] [SMul G X] extends
    ContinuousConstSMul G X where
  isInducing_constSMul : Topology.IsInducing (ContinuousMap.constSMul : G → C(X, X))

instance InducingSMul.continuousSMul {G X : Type*} [TopologicalSpace G] [TopologicalSpace X]
    [LocallyCompactSpace X] [SMul G X] [InducingSMul G X] : ContinuousSMul G X where
  continuous_smul :=
    ContinuousMap.continuous_uncurry_of_continuous ⟨_, isInducing_constSMul.continuous⟩

lemma continuous_uncurry_iff {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [LocallyCompactSpace Y] {f : X → C(Y, Z)} :
    Continuous (Function.uncurry fun x y ↦ f x y) ↔ Continuous f := by
  exact ⟨ContinuousMap.continuous_of_continuous_uncurry f,
    fun h ↦ ContinuousMap.continuous_uncurry_of_continuous ⟨_, h⟩⟩

lemma continuousOn_uncurry_iff {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [LocallyCompactSpace Y] {f : X → C(Y, Z)} {s : Set X} :
    ContinuousOn (Function.uncurry fun x y ↦ f x y) (s ×ˢ .univ) ↔ ContinuousOn f s := by
  refine ⟨fun h ↦ ContinuousMap.continuousOn_of_continuousOn_uncurry f h, fun h ↦ ?_⟩
  rw [continuousOn_iff_continuous_restrict] at h ⊢
  exact (continuous_uncurry_iff.2 h).comp ((Homeomorph.Set.prod s (Set.univ : Set Y)).trans
    (.prodCongr (.refl _) (Homeomorph.Set.univ _))).continuous

/-- When the action of `G` on `X` is inducing, a map `f : Y → G` is continuous iff the map
`Y × X → X` corresponding to the resulting action of `Ỳ` on `X` is. -/
lemma InducingSMul.continuous_iff {G X Y : Type*} [TopologicalSpace G] [TopologicalSpace X]
    [TopologicalSpace Y] [LocallyCompactSpace X] [SMul G X] [InducingSMul G X] {f : Y → G} :
    Continuous f ↔ Continuous (fun x : Y × X ↦ f x.1 • x.2) := by
  rw [(isInducing_constSMul (G := G) (X := X)).continuous_iff]
  exact continuous_uncurry_iff.symm

/-- When the action of `G` on `X` is inducing, a map `f : Y → G` is continuous iff the map
`Y × X → X` corresponding to the resulting action of `Ỳ` on `X` is. -/
lemma InducingSMul.continuousOn_iff {G X Y : Type*} [TopologicalSpace G] [TopologicalSpace X]
    [TopologicalSpace Y] [LocallyCompactSpace X] [SMul G X] [InducingSMul G X] {f : Y → G}
    {s : Set Y} : ContinuousOn f s ↔ ContinuousOn (fun x : Y × X ↦ f x.1 • x.2) (s ×ˢ .univ) := by
  rw [(isInducing_constSMul (G := G) (X := X)).continuousOn_iff]
  exact continuousOn_uncurry_iff.symm
