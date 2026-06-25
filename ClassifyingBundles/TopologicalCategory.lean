/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Action
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homeomorph.TransferInstance

/-! # Topological categories and groupoids
In this file we define topological categories and groupoids, i.e. categories / groupoids whose
type of objects `C` and type of arrows `Arrow C` are topological spaces and whose structure maps
(the source and target maps `Arrow C → C`, the identity map `C → Arrow C`, the composition map
`ComposableArrows C 2 → Arrow C` and in the case of groupoids the inverse map `Arrow C → Arrow C`)
are continuous. Mathematically this is a special case of internal categories and groupoids
(topological categories/groupoids are categories/groupoids internal to `TopCat`), but
for actually working with them it is more convenient to define them in an unbundled manner as done
here instead of working abstractly with category/groupoid objects in `TopCat`.

## Main definitions & results
* `IsTopologicalCategory C`: `Prop`-valued typeclass stating that the source, target, identity and
  composition maps of `C` are continuous with respect to given topologies on `C` and `Arrow C`.
* `IsTopologicalGroupoid C`: `Prop`-valued typeclass stating that a category is both a groupoid and
  a topological category for which the inverse map `Arrow C → Arrow C` is also continuous.
* `topologicalNerve C`: the nerve of a topological category as a simplicial topological space.
* For every topological space `X`, `Discrete X` is a topological groupoid.
* For every topological monoid `M`, `SingleObj M` is a topological category.
* For every topological group `G`, `SingleObj G` is a topological groupoid.
* For every continuous action of a monoid `M` on a topological space `X`, `ActionCategory M X` is
  a topological category.
* For every continuous action of a group `G` on a topological space `X`, `ActionCategory G X` is
  a topological groupoid.
-/

universe u

open Topology

namespace CategoryTheory

protected abbrev Arrow.id {C : Type*} [Category* C] (X : C) : Arrow C := 𝟙 X

namespace ComposableArrows

variable {C : Type*} [Category* C] [TopologicalSpace C] [TopologicalSpace (Arrow C)] {n : ℕ}

/-- Given a topology on `Arrow C`, we equip `ComposableArrows C n` with the coarsest topology making
the `ǹ + 1` projections to `C` as well as the `n` projections to `Arrow C` selecting one of the `n`
arrows continuous. In the case of topological categories also implies continuity of the
projections to `Arrow C` given by partial compositions. -/
instance instTopologicalSpace (C : Type*) [Category* C] [TopologicalSpace C]
    [TopologicalSpace (Arrow C)] {n : ℕ} : TopologicalSpace (ComposableArrows C n) :=
  (⨅ i ≤ n, .induced (fun F ↦ F.obj' i) ‹_›) ⊓
    ⨅ i < n, .induced (fun F ↦ F.map' i (i + 1) : _ → Arrow C) ‹_›

variable {C : Type*} [Category* C] [TopologicalSpace C] [TopologicalSpace (Arrow C)]

lemma continuous_obj' {n : ℕ} {i : ℕ} (h : i ≤ n := by valid) :
    Continuous (fun F ↦ F.obj' i : ComposableArrows C n → C) :=
  continuous_iff_le_induced.2 <| inf_le_of_left_le <| iInf₂_le _ _

lemma continuous_map'_add_one {C : Type*} [Category* C] [TopologicalSpace C]
    [TopologicalSpace (Arrow C)] {n : ℕ} {i : ℕ} (h : i < n := by valid) :
    Continuous (fun F ↦ F.map' i (i + 1) : ComposableArrows C n → Arrow C) :=
  continuous_iff_le_induced.2 <| inf_le_of_right_le <| iInf₂_le i h

lemma continuous_iff {n : ℕ} {X : Type*} [TopologicalSpace X] {f : X → ComposableArrows C n} :
    Continuous f ↔ (∀ (i : ℕ) (_ : i ≤ n), Continuous fun x ↦ (f x).obj' i) ∧
      ∀ (i : ℕ) (_ : i < n), Continuous (fun x ↦ (f x).map' i (i + 1) : _ → Arrow C) := by
  simp_rw [continuous_iff_le_induced, ← le_iInf₂_iff, ← le_inf_iff, instTopologicalSpace,
    induced_inf, induced_iInf, induced_compose]
  rfl

end ComposableArrows

/-- We say that a category `C` is a topological category if both its type of objects `C` and
its type of arrows `Arrow C` are equipped with topologies, that make the source and target maps
`Arrow C → C`, the identity map `C → Arrow C` and the composition map
`ComposableArrows C 2 → Arrow C` continuous. In addition to that, we assume that each hom-type
`X ⟶ Y` is already equipped with the topology induced by the inclusion into `Arrow C`. -/
class IsTopologicalCategory (C : Type*) [Category* C] [TopologicalSpace C]
    [TopologicalSpace (Arrow C)] [∀ X Y : C, TopologicalSpace (X ⟶ Y)] where
  /-- The source map `Arrow C → C` is continuous. -/
  continuous_arrowLeft : Continuous (Arrow.left : Arrow C → C)
  /-- The target map `Arrow C → C` is continuous. -/
  continuous_arrowRight : Continuous (Arrow.right : Arrow C → C)
  /-- The identity map `C → Arrow C` is continuous. -/
  continuous_arrowId : Continuous (Arrow.id : C → Arrow C)
  /-- The composition map `ComposableArrows C 2 → Arrow C` is continuous. -/
  continuous_composableArrowsHom : Continuous (fun F ↦ F.hom : ComposableArrows C 2 → Arrow C)
  /-- The topology on each hom-type `X → Y` is induced by the inclusion into `Arrow C`. -/
  isInducing_arrowMk (X Y : C) : IsInducing (Arrow.mk : (X ⟶ Y) → Arrow C)

namespace Arrow

variable {C : Type*} [Category* C] [TopologicalSpace C] [TopologicalSpace (Arrow C)]
  [∀ X Y : C, TopologicalSpace (X ⟶ Y)] [IsTopologicalCategory C]

lemma continuous_left : Continuous (left : Arrow C → C) :=
  IsTopologicalCategory.continuous_arrowLeft

lemma continuous_right : Continuous (right : Arrow C → C) :=
  IsTopologicalCategory.continuous_arrowRight

protected lemma continuous_id : Continuous (Arrow.id : C → Arrow C) :=
  IsTopologicalCategory.continuous_arrowId

lemma continuous_mk (X Y : C) : Continuous (mk : (X ⟶ Y) → Arrow C) :=
  (IsTopologicalCategory.isInducing_arrowMk _ _).continuous

@[fun_prop]
lemma isQuotientMap_left : IsQuotientMap (left : Arrow C → C) :=
  .of_inverse Arrow.continuous_id continuous_left fun _ ↦ rfl

@[fun_prop]
lemma isQuotientMap_right : IsQuotientMap (right : Arrow C → C) :=
  .of_inverse Arrow.continuous_id continuous_right fun _ ↦ rfl

@[fun_prop]
protected lemma isEmbedding_id : IsEmbedding (Arrow.id : C → Arrow C) :=
  .of_leftInverse (fun _ ↦ rfl) continuous_right Arrow.continuous_id

@[fun_prop]
lemma isEmbedding_mk (X Y : C) : IsEmbedding (mk : (X ⟶ Y) → Arrow C) :=
  ⟨IsTopologicalCategory.isInducing_arrowMk _ _, mk_injective _ _⟩

end Arrow

lemma ComposableArrows.continuous_iff' {C : Type*} [Category* C] [TopologicalSpace C]
    [TopologicalSpace (Arrow C)] [∀ X Y : C, TopologicalSpace (X ⟶ Y)] [IsTopologicalCategory C]
    {n : ℕ} (hn : 0 < n := by valid) {X : Type*} [TopologicalSpace X]
    {f : X → ComposableArrows C n} : Continuous f ↔
      ∀ (i : ℕ) (_ : i < n), Continuous (fun x ↦ (f x).map' i (i + 1) : _ → Arrow C) := by
  rw [continuous_iff, iff_comm, iff_and_self]
  intro h i hi
  cases i
  · exact Arrow.continuous_left.comp (h 0 hn)
  · exact Arrow.continuous_right.comp (h _ <| by valid)

set_option backward.isDefEq.respectTransparency false in
/-- For any three objects `X Y Z` in a topological category, the composition map
`(X ⟶ Y) × (Y ⟶ Z) → (X ⟶ Z)` is continuous. This means that every topological category is in
particular `TopCat`-enriched. -/
lemma continuous_comp {C : Type*} [Category* C] [TopologicalSpace C] [TopologicalSpace (Arrow C)]
    [∀ X Y : C, TopologicalSpace (X ⟶ Y)] [IsTopologicalCategory C] {X Y Z : C} :
    Continuous (fun fg : (X ⟶ Y) × (Y ⟶ Z) ↦ fg.1 ≫ fg.2) := by
  suffices h : Continuous (fun fg : (X ⟶ Y) × (Y ⟶ Z) ↦ ComposableArrows.mk₂ fg.1 fg.2) by
    rw [(Arrow.isEmbedding_mk X Z).continuous_iff]
    exact IsTopologicalCategory.continuous_composableArrowsHom.comp h
  refine (ComposableArrows.continuous_iff').2 fun i hi ↦ ?_
  interval_cases i
  · exact (Arrow.continuous_mk _ _).comp continuous_fst
  · exact (Arrow.continuous_mk _ _).comp continuous_snd

namespace ComposableArrows

/-- When `C` is a topological groupoid, all projections of `ComposableArrows C` to `Arrow C`
are continuous, including the ones given by identities or compositions. -/
lemma continuous_map' {C : Type*} [Category* C] [TopologicalSpace C] [TopologicalSpace (Arrow C)]
    [∀ X Y : C, TopologicalSpace (X ⟶ Y)] [IsTopologicalCategory C]
    {n : ℕ} {i j : ℕ} (h : i ≤ j := by valid) (h' : j ≤ n := by valid) :
    Continuous (fun F ↦ F.map' i j : ComposableArrows C n → Arrow C) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero =>
    simp only [Nat.add_zero, map', homOfLE_refl, Functor.map_id]
    exact Arrow.continuous_id.comp continuous_obj'
  | succ k hk =>
    specialize hk (by lia) (by lia)
    simp_rw [fun F : ComposableArrows C n ↦ map'_comp F i (i + k) (i + (k + 1))]
    suffices h : Continuous
        (fun F : ComposableArrows C n ↦ mk₂ (F.map' i (i + k)) (F.map' (i + k) (i + (k + 1)))) from
      IsTopologicalCategory.continuous_composableArrowsHom.comp h
    refine (continuous_iff').2 fun l hl ↦ ?_
    interval_cases l
    · exact hk
    · exact continuous_map'_add_one

/-- Composing `n` composable arrows is continuous. -/
lemma continuous_hom {C : Type*} [Category* C] [TopologicalSpace C] [TopologicalSpace (Arrow C)]
    [∀ X Y : C, TopologicalSpace (X ⟶ Y)] [IsTopologicalCategory C] {n : ℕ} :
    Continuous (fun F ↦ F.hom : ComposableArrows C n → Arrow C) :=
  continuous_map'

lemma continuous_map {C : Type*} [Category* C] [TopologicalSpace C] [TopologicalSpace (Arrow C)]
    [∀ X Y : C, TopologicalSpace (X ⟶ Y)] [IsTopologicalCategory C]
    {n : ℕ} {i j} {f : i ⟶ j} : Continuous (fun F ↦ F.map f : ComposableArrows C n → Arrow C) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  rw [Subsingleton.elim f (homOfLE (leOfHom f))]
  exact continuous_map' (h := leOfHom f)

lemma continuous_whiskerLeft {C : Type*} [Category* C] [TopologicalSpace C]
    [TopologicalSpace (Arrow C)] [∀ X Y : C, TopologicalSpace (X ⟶ Y)] [IsTopologicalCategory C]
    {n m : ℕ} (Φ : Fin (n + 1) ⥤ Fin (m + 1)) :
    Continuous (fun F : ComposableArrows C m ↦ F.whiskerLeft Φ) :=
  continuous_iff.2 ⟨fun i hi ↦ continuous_obj', fun i hi ↦ continuous_map⟩

end ComposableArrows

/-- We say that a category is a topological groupoid if it is both a groupoid and a topological
category, and the inverse map `Arrow C → Arrow C` is continuous. -/
class IsTopologicalGroupoid (C : Type*) [Category* C] [TopologicalSpace C]
    [TopologicalSpace (Arrow C)] [∀ X Y : C, TopologicalSpace (X ⟶ Y)] extends
    IsGroupoid C, IsTopologicalCategory C where
  /-- The inversion map `Arrow C → Arrow C` is continuous. -/
  continuous_inv : Continuous (fun f ↦ inv f.hom : Arrow C → Arrow C)

namespace IsTopologicalGroupoid

lemma continuous_groupoidInv (C : Type*) [Groupoid C] [TopologicalSpace C]
    [TopologicalSpace (Arrow C)] [∀ X Y : C, TopologicalSpace (X ⟶ Y)] [IsTopologicalGroupoid C] :
    Continuous (fun f ↦ Groupoid.inv f.hom : Arrow C → Arrow C) := by
  simpa using continuous_inv

end IsTopologicalGroupoid

section End

variable {C : Type*} [Category* C] [TopologicalSpace C] [TopologicalSpace (Arrow C)]
    [∀ X Y : C, TopologicalSpace (X ⟶ Y)] [IsTopologicalCategory C] (X : C)

instance : TopologicalSpace (End X) := inferInstanceAs (TopologicalSpace (X ⟶ X))

instance : ContinuousMul (End X) where
  continuous_mul := continuous_comp.comp continuous_swap

instance {C : Type*} [Groupoid C] [TopologicalSpace C] [TopologicalSpace (Arrow C)]
    [∀ X Y : C, TopologicalSpace (X ⟶ Y)] [IsTopologicalGroupoid C] (X : C) :
    IsTopologicalGroup (End X) where
  continuous_inv :=
    (Arrow.isEmbedding_mk X X).continuous_iff.2 <|
      (IsTopologicalGroupoid.continuous_groupoidInv C).comp <| Arrow.continuous_mk X X

end End

section Discrete

variable (X : Type*) [TopologicalSpace X]

instance : TopologicalSpace (Discrete X) :=
  discreteEquiv.topologicalSpace

/-- Any topological space is homeomorphic to the trivial topological groupoid on it. Note that
while this groupoid is often called discrete because it has no arrows except identities, it is
not discrete topologically, so this is not a contradiction. -/
def discreteHomeomorph : Discrete X ≃ₜ X where
  __ := discreteEquiv
  continuous_invFun := discreteEquiv.homeomorph.symm.continuous

instance : TopologicalSpace (Arrow (Discrete X)) :=
  (Arrow.discreteEquiv X).topologicalSpace

/-- Any topological space is homeomorphic to the space of morphisms of the trivial topological
groupoid on it. Note that while this groupoid is often called discrete because it has no arrows
except identities, it is not discrete topologically, so this is not a contradiction. -/
def Arrow.discreteHomeomorph : Arrow (Discrete X) ≃ₜ X where
  __ := discreteEquiv X
  continuous_invFun := (discreteEquiv X).homeomorph.symm.continuous

instance {x x' : Discrete X} : TopologicalSpace (x ⟶ x') := ⊥

/-- Every linear order is preconnected as a category. Of course this can be vastly generalised,
but I wasn't sure what the correct typeclass for "total order" or "preconnected order" is. -/
instance {α : Type*} [LinearOrder α] : IsPreconnected α :=
  zigzag_isPreconnected fun a b ↦ (le_total a b).rec
    (fun h ↦ .of_hom (homOfLE h)) (fun h ↦ .of_inv (homOfLE h))

/-- The bijection between composable arrows in `Discrete α` and `α`. -/
def ComposableArrows.discreteEquiv (α : Type*) {n : ℕ} : ComposableArrows (Discrete α) n ≃ α where
  toFun F := (F.obj' 0).as
  invFun X := (Functor.const _).obj ⟨X⟩
  left_inv F :=
    Functor.ext (fun i ↦ any_functor_const_on_obj F _ _) fun _ _ _ ↦ Subsingleton.elim _ _
  right_inv X := rfl

/-- Any topological space is homeomorphic to the space of `n` composable arrows in the trivial
topological groupoid on it. Note that while this groupoid is often called discrete because it has
no arrows except identities, it is not discrete topologically, so this is not a contradiction. -/
def ComposableArrows.discreteHomeomorph {n : ℕ} : ComposableArrows (Discrete X) n ≃ₜ X where
  __ := discreteEquiv X
  continuous_toFun := (CategoryTheory.discreteHomeomorph X).continuous.comp continuous_obj'
  continuous_invFun :=
    continuous_iff.2 ⟨fun i _ ↦ (CategoryTheory.discreteHomeomorph X).symm.continuous,
      fun _ _ ↦ (Arrow.discreteHomeomorph X).symm.continuous⟩

instance : IsTopologicalGroupoid (Discrete X) where
  continuous_arrowLeft :=
    (discreteHomeomorph X).symm.continuous.comp (Arrow.discreteHomeomorph X).continuous
  continuous_arrowRight := by
    refine ((discreteHomeomorph X).symm.continuous.comp
      (Arrow.discreteHomeomorph X).continuous).congr fun f ↦ ?_
    obtain ⟨⟨x⟩, ⟨x'⟩, ⟨⟨⟨⟩⟩⟩⟩ := f
    rfl
  continuous_arrowId :=
    (Arrow.discreteHomeomorph X).symm.continuous.comp (discreteHomeomorph X).continuous
  continuous_composableArrowsHom := by
    rw [← (ComposableArrows.discreteHomeomorph X).symm.comp_continuous_iff']
    exact (Arrow.discreteHomeomorph X).symm.continuous
  isInducing_arrowMk x x' := .of_subsingleton _
  continuous_inv := by
    rw [← (Arrow.discreteHomeomorph X).symm.comp_continuous_iff']
    exact (Arrow.discreteHomeomorph X).symm.continuous

end Discrete

section SingleObj

instance {M : Type*} : TopologicalSpace (SingleObj M) := ⊥

set_option backward.isDefEq.respectTransparency false in
/-- `Arrow.mk` as a bijection whenever `C` has at most one object. -/
@[simps]
def Arrow.mkEquiv {C : Type*} [Category* C] [Subsingleton C] (X Y : C) : (X ⟶ Y) ≃ Arrow C where
  toFun f := f
  invFun f := eqToHom (Subsingleton.elim _ _) ≫ f.hom ≫ eqToHom (Subsingleton.elim _ _)
  left_inv f := by simp
  right_inv f := by simp

set_option backward.isDefEq.respectTransparency false in
/-- The bijection `ComposableArrows C 2 ≃ (X ⟶ X) × (X ⟶ X)` in any category with only a single
object `X`. -/
@[simps]
def ComposableArrows.equivProd {C : Type*} [Category* C] [Subsingleton C] (X : C) :
    ComposableArrows C 2 ≃ (X ⟶ X) × (X ⟶ X) where
  toFun F := (eqToHom (Subsingleton.elim _ _) ≫ F.map' 0 1 ≫ eqToHom (Subsingleton.elim _ _),
    eqToHom (Subsingleton.elim _ _) ≫ F.map' 1 2 ≫ eqToHom (Subsingleton.elim _ _))
  invFun f := mk₂ f.1 f.2
  left_inv F := by refine ComposableArrows.ext₂ ?_ ?_ ?_ rfl rfl <;> apply Subsingleton.elim
  right_inv f := by ext <;> simp [Precomp.map]

instance {M : Type*} [Monoid M] [TopologicalSpace M] : TopologicalSpace (Arrow (SingleObj M)) :=
  (Arrow.mkEquiv (SingleObj.star M) (SingleObj.star M)).symm.topologicalSpace

set_option backward.isDefEq.respectTransparency false in
attribute [local fun_prop] continuous_of_indiscreteTopology in
/-- For every topological monoid `M`, `SingleObj M` is a topological category. -/
instance {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M] :
    IsTopologicalCategory (SingleObj M) where
  continuous_arrowLeft := by fun_prop
  continuous_arrowRight := by fun_prop
  continuous_arrowId := by fun_prop
  continuous_composableArrowsHom := by
    have h : Continuous (ComposableArrows.equivProd (SingleObj.star M)) := by
      refine continuous_prodMk.2 ⟨?_, ?_⟩
      <;> exact (Arrow.mkEquiv _ _).symm.homeomorph.continuous.comp <|
        ComposableArrows.continuous_map'_add_one (C := SingleObj M)
    convert! (Arrow.mkEquiv _ _).symm.homeomorph.symm.continuous.comp
      (continuous_mul.comp <| continuous_swap.comp h) with F
    obtain ⟨f, rfl⟩ := (ComposableArrows.equivProd (SingleObj.star M)).symm.surjective F
    simp [Equiv.homeomorph, ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj,
      SingleObj.comp_as_mul, ComposableArrows.equivProd]
  isInducing_arrowMk X Y := by
    rw [Subsingleton.elim X (SingleObj.star M), Subsingleton.elim Y (SingleObj.star M)]
    exact (Arrow.mkEquiv (SingleObj.star M) (SingleObj.star M)).symm.homeomorph.symm.isInducing

/-- For every topological group `G`, `SingleObj G` is a topological groupoid. -/
instance {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    IsTopologicalGroupoid (SingleObj G) where
  continuous_inv := by
    have h := (Arrow.mkEquiv (SingleObj.star G) _).symm.homeomorph.symm.continuous.comp <|
      continuous_inv.comp <| (Arrow.mkEquiv (SingleObj.star G) _).symm.homeomorph.continuous
    convert! h with ⟨X, Y, f⟩
    obtain rfl := Subsingleton.elim X (SingleObj.star G)
    obtain rfl := Subsingleton.elim Y (SingleObj.star G)
    simp [Equiv.homeomorph, SingleObj.inv_as_inv]

/-- The isomorphism `SingleObj.toEnd : M ≃* End (star M)` between `M` and the unique endomorphism
monoid in `SingleObj M` as an isomorphism of topological monoids. -/
def SingleObj.toEndHomeomorph (M : Type*) [Monoid M] [TopologicalSpace M] [ContinuousMul M] :
    M ≃ₜ* End (star M) where
  __ := toEnd M
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

end SingleObj

section Action

instance {M : Type*} [Monoid M] {X : Type*} [MulAction M X] [TopologicalSpace X] :
    TopologicalSpace (ActionCategory M X) :=
  (ActionCategory.objEquiv M X).symm.topologicalSpace

def ActionCategory.objHomeomorph (M : Type*) [Monoid M] (X : Type*) [MulAction M X]
    [TopologicalSpace X] : X ≃ₜ ActionCategory M X where
  __ := ActionCategory.objEquiv M X
  continuous_toFun := (objEquiv M X).symm.homeomorph.symm.continuous
  continuous_invFun := (objEquiv M X).symm.homeomorph.continuous

--set_option allowUnsafeReducibility true in
--attribute [reducible] actionAsFunctor

set_option backward.isDefEq.respectTransparency false in
def ActionCategory.arrowEquiv (M : Type*) [Monoid M] (X : Type*) [MulAction M X] :
    Arrow (ActionCategory M X) ≃ M × X where
  toFun f := (f.hom.1, f.left.2)
  invFun f := Arrow.mk <|
    CategoryOfElements.homMk (F := actionAsFunctor M X) ⟨(), f.2⟩ ⟨(), f.1 • f.2⟩ f.1 rfl
  left_inv f := by
    obtain ⟨⟨⟨⟩, x⟩, ⟨⟨⟩, y⟩, ⟨f, hf⟩⟩ := f
    dsimp [actionAsFunctor] at f hf ⊢
    subst hf
    refine Arrow.ext rfl rfl ?_
    simp
    rfl
  right_inv f := rfl

instance {M : Type*} [Monoid M] [TopologicalSpace M] {X : Type*} [MulAction M X]
    [TopologicalSpace X] : TopologicalSpace (Arrow (ActionCategory M X)) :=
  (ActionCategory.arrowEquiv M X).topologicalSpace

def ActionCategory.arrowHomeomorph (M : Type*) [Monoid M] [TopologicalSpace M] (X : Type*)
    [MulAction M X] [TopologicalSpace X] : Arrow (ActionCategory M X) ≃ₜ M × X where
  __ := arrowEquiv M X
  continuous_toFun := (arrowEquiv M X).homeomorph.continuous
  continuous_invFun := (arrowEquiv M X).homeomorph.symm.continuous

instance {M : Type*} [Monoid M] [TopologicalSpace M] {X : Type*} [MulAction M X]
    [TopologicalSpace X] {Y Z : ActionCategory M X} : TopologicalSpace (Y ⟶ Z) :=
  .induced Arrow.mk inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The action category of a continuous action is a topological category. -/
instance {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M] {X : Type*} [MulAction M X]
    [TopologicalSpace X] [ContinuousSMul M X] : IsTopologicalCategory (ActionCategory M X) where
  continuous_arrowLeft :=
    (ActionCategory.objHomeomorph M X).continuous.comp <|
      continuous_snd.comp (ActionCategory.arrowHomeomorph M X).continuous
  continuous_arrowRight := by
    refine ((ActionCategory.objHomeomorph M X).continuous.comp <| continuous_smul.comp <|
      (ActionCategory.arrowHomeomorph M X).continuous).congr fun x ↦ ?_
    simp only [ActionCategory.objHomeomorph, ActionCategory.objEquiv,
      Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, ActionCategory.arrowHomeomorph,
      ActionCategory.arrowEquiv, Function.comp_apply]
    refine Sigma.ext rfl <| Eq.heq ?_
    simp_rw [← x.hom.2]
    rfl
  continuous_arrowId := by
    refine ((ActionCategory.arrowHomeomorph M X).symm.continuous.comp <|
      (Continuous.prodMk_right 1).comp
        (ActionCategory.objHomeomorph M X).symm.continuous).congr fun x ↦ ?_
    simp only [ActionCategory.arrowHomeomorph, ActionCategory.arrowEquiv,
      Homeomorph.homeomorph_mk_coe_symm, Equiv.symm_mk,
      Equiv.coe_fn_mk, ActionCategory.objHomeomorph, ActionCategory.objEquiv, Function.comp_apply]
    rw! [one_smul M x.back]
    exact Arrow.ext rfl rfl <| Subtype.ext (by simp)
  continuous_composableArrowsHom := by
    refine .congr ?_ (fun F ↦ ?_) (f := fun F ↦ (ActionCategory.arrowHomeomorph M X).symm <|
      ⟨(F.map' 1 2).1 * (F.map' 0 1).1, (ActionCategory.objHomeomorph M X).symm <| F.obj' 0⟩)
    · refine (ActionCategory.arrowHomeomorph M X).symm.continuous.comp <| .prodMk
        (.mul ?_ ?_)
        ((ActionCategory.objHomeomorph M X).symm.continuous.comp
          (ComposableArrows.continuous_obj' (i := 0)))
      · exact continuous_fst.comp <| (ActionCategory.arrowHomeomorph M X).continuous.comp <|
          ComposableArrows.continuous_map'_add_one
      · exact continuous_fst.comp <| (ActionCategory.arrowHomeomorph M X).continuous.comp <|
          ComposableArrows.continuous_map'_add_one
    · obtain ⟨⟨⟨⟩, x⟩, ⟨⟨⟩, y⟩, ⟨⟨⟩, z⟩, ⟨f, hf⟩, ⟨g, hg⟩, rfl⟩ := F.mk₂_surjective
      dsimp [actionAsFunctor] at x y z g hg f hf
      subst hg hf
      refine Arrow.ext rfl ?_ <| Subtype.ext ?_
      · simp [ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj,
          ActionCategory.arrowHomeomorph, ActionCategory.arrowEquiv, ActionCategory.objHomeomorph,
          ActionCategory.objEquiv, mul_smul]
      · simp [ComposableArrows.Precomp.map, ComposableArrows.Precomp.obj,
          ActionCategory.arrowHomeomorph, ActionCategory.arrowEquiv, ActionCategory.objHomeomorph,
          ActionCategory.objEquiv,
          show ∀ i j : ActionCategory M X, ∀ h : i = j, (eqToHom h).1 = (1 : M) by
            rintro i j rfl; simp]
  isInducing_arrowMk _ _ := ⟨rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The action category of a continuous group action is a topological groupoid. -/
instance {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {X : Type*} [MulAction G X] [TopologicalSpace X] [ContinuousSMul G X] :
    IsTopologicalGroupoid (ActionCategory G X) where
  continuous_inv := by
    refine ((ActionCategory.arrowHomeomorph G X).symm.continuous.comp <|
      (by fun_prop : Continuous fun gx ↦ (gx.1⁻¹, gx.1 • gx.2)).comp
        (ActionCategory.arrowHomeomorph G X).continuous).congr fun f ↦ ?_
    obtain ⟨⟨⟨⟩, x⟩, ⟨⟨⟩, y⟩, ⟨f, hf⟩⟩ := f
    dsimp [actionAsFunctor] at x y f hf
    subst hf
    refine Arrow.ext rfl ?_ <| Subtype.ext ?_
    · simp [ActionCategory.arrowHomeomorph, ActionCategory.arrowEquiv]
    · simpa [ActionCategory.arrowHomeomorph, ActionCategory.arrowEquiv,
        show ∀ i j : ActionCategory G X, ∀ h : i = j, (eqToHom h).1 = (1 : G) by
            rintro i j rfl; simp, ← Groupoid.inv_eq_inv]
        using (SingleObj.inv_as_inv _ _).symm.trans (Groupoid.inv_eq_inv _).symm

end Action

section Nerve

open ConcreteCategory in
/-- The *topological nerve* of a topological category is the simplicial topological space whose
underlying simplicial set is the nerve of the underlying category, equipped with the appropriate
topologies. -/
@[simps -isSimp]
def topologicalNerve (C : Type*) [Category* C] [TopologicalSpace C] [TopologicalSpace (Arrow C)]
    [∀ X Y : C, TopologicalSpace (X ⟶ Y)] [IsTopologicalCategory C] : SimplicialObject TopCat where
  obj Δ := .of (ComposableArrows C (Δ.unop.len))
  map f := ofHom ⟨↾fun x ↦ x.whiskerLeft (SimplexCategory.toCat.map f.unop).toFunctor,
    ComposableArrows.continuous_whiskerLeft _⟩
  map_id _ := rfl
  map_comp _ _ := rfl

attribute [simp] topologicalNerve_obj_carrier

end Nerve

end CategoryTheory
