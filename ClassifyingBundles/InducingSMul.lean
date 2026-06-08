/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Topologically inducing group actions
In this file we define what we call "inducing" group actions, group actions `SMul G X` for which
multiplication by each `g : G` is a continuous map `X → X`  and the resulting map `G → C(X, X)` is
topologically inducing. In other words (assuming local compactness of `Y`), a map `Y → G` is
continuous iff the corresponding map `Y × X → X` is.

The most important example of this for our purposes is the action of the general linear group
of any finite-dimensional TVS on that space, since it being inducing means that the action of any
subgroup of it is inducing too, which lets us construct bundle structures with these structure
groups without explicitly checking continuity.

## Main definitions / results
* `InducingSMul G X`: typeclass stating that the action of `G` on `X` is inducing in the sense that
  it is continuous and the resulting map `G → C(X, X)` is topologically inducing.
* `inducingSMul_iff`: when `X` is locally compact, an action of `G` on `X` is inducing iff for
  every space `Y`, maps `Y → G` are continuous iff the induced action of `Y` on `X` is.
* `IsInducing.inducingSMul`: inducing actions can be pulled back along inducing maps `G → G'`
  and equivariant homeomorphisms `X ≃ₜ X'`.
* For every finite-dimensional Hausdorff topological vector space `E` over a sufficiently nice
  field `𝕜`, the action of the general linear group `E →L[𝕜] E` on `E` is inducing.
-/

universe u

open Topology

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
  isInducing_constSMul : IsInducing (ContinuousMap.constSMul : G → C(X, X))

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

/-- A function `f : X → Y` is inducing iff for every other space `Z`, maps `g : Z → X` are
continuous iff their compositions `f ∘ g : Z → Y` with `f` are. -/
lemma Topology.isInducing_iff_continuous_iff {X : Type u} {Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} :
    IsInducing f ↔ ∀ {Z : Type u} [TopologicalSpace Z] {g : Z → X},
      Continuous g ↔ Continuous (f ∘ g) := by
  refine ⟨fun h ↦ h.continuous_iff, fun h ↦
    (isInducing_iff _).2 <| le_antisymm (continuous_iff_le_induced.1 <| h.1 continuous_id) ?_⟩
  simpa [induced_id, continuous_iff_le_induced] using
    (@h X (.induced f ‹_›) id).2 continuous_induced_dom

/-- Assuming `X` is locally compact, a `G`-action on `X` is inducing iff for every space `Y`,
maps `f : Y → G` are continuous iff the corresponding maps `Y × X → X` are. -/
lemma inducingSMul_iff {G : Type u} {X : Type*} [TopologicalSpace G] [TopologicalSpace X]
    [LocallyCompactSpace X] [SMul G X] :
    InducingSMul G X ↔ ∀ {Y : Type u} [TopologicalSpace Y] {f : Y → G},
      Continuous f ↔ Continuous (fun x : Y × X ↦ f x.1 • x.2) := by
  refine ⟨fun h ↦ h.continuous_iff, fun h ↦ ?_⟩
  have : ContinuousSMul G X := ⟨h.1 continuous_id⟩
  refine ⟨isInducing_iff_continuous_iff.2 ?_⟩
  intro Y _ f
  rw [h, ← continuous_uncurry_iff]
  rfl

/-- Given an inducing map `φ : G → G'` and a `φ`-equivariant homeomorphism `f : X ≃ₜ X'`,
the action of `G` on `X` is inducing if the action of `G'` on `X'` is.

Note that `f` being just an inducing map or even an embedding would not be enough: for example,
the restriction of any `G`-action to its space of fixed points is only inducing if `G` is
indiscrete, even though the inclusion is a `G`-equivariant embedding. -/
lemma Topology.IsInducing.inducingSMul {G G' X X' : Type*} [TopologicalSpace G]
    [TopologicalSpace G'] [TopologicalSpace X] [TopologicalSpace X']
    [SMul G X] [SMul G' X'] {φ : G → G'} (hφ : IsInducing φ) (f : X ≃ₜ X')
    (h : ∀ {g : G} {x : X}, f (g • x) = φ g • f x)
    [InducingSMul G' X'] : InducingSMul G X where
  continuous_const_smul := (f.isInducing.continuousConstSMul φ h).continuous_const_smul
  isInducing_constSMul := by
    rw [← (f.arrowCongr f).isInducing.of_comp_iff]
    convert InducingSMul.isInducing_constSMul (X := X') |>.comp hφ
    ext g x
    simp [Homeomorph.arrowCongr, h]

/-- For every finite-dimensional Hausdorff topological vector space `E` over a sufficiently nice
field `𝕜` the canonical action of `E →L[𝕜] E` on `E` is inducing. -/
instance {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [LocallyCompactSpace 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] :
    InducingSMul (E →L[𝕜] E) E := by
  -- it suffices to show this for `Fin n → 𝕜`
  revert E
  suffices ∀ n, InducingSMul ((Fin n → 𝕜) →L[𝕜] (Fin n → 𝕜)) (Fin n → 𝕜) by
    intro E _ _ _ _ _ _ _
    let e := (Module.finBasis 𝕜 E).equivFunL
    exact (e.arrowCongr e).toHomeomorph.isInducing.inducingSMul e.toHomeomorph (by simp)
  refine fun n ↦ ⟨?_⟩
  /- this follows because the map `((Fin n → 𝕜) →L[𝕜] Fin n → 𝕜) → C(Fin n → 𝕜, Fin n → 𝕜)` has a
  continuous left inverse, given by the map that sends each `f : C(Fin n → 𝕜, Fin n → 𝕜)` to
  the linear map taking the same value as `f` on all standard basis vectors. -/
  refine (Function.LeftInverse.isEmbedding
    (f := fun f ↦ ∑ i, .smulRight (.proj i) (f <| Pi.basisFun 𝕜 (Fin n) i)) ?_ ?_ ?_).isInducing
  · intro f; ext1 x
    exact .trans (by simp) (congr_arg f <| (Pi.basisFun 𝕜 (Fin n)).sum_repr x)
  · fun_prop
  · rw [← continuous_uncurry_iff]
    simp only [ContinuousMap.constSMul_apply, ContinuousLinearMap.smul_def]
    fun_prop
