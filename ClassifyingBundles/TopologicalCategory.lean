/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Constructions.SumProd

/-! # Topological categories and groupoids
In this file we define topological categories and groupoids, i.e. categories / groupoids whose
type of objects `C` and type of arrows `Arrow C` are topological spaces and whose structure maps
(the source and target maps `Arrow C → C`, the identity map `C → Arrow C`, the composition map
`ComposableArrows C 2 → Arrow C` and in the case of groupoids the inverse map `Arrow C → Arrow C`)
are continuous. Mathematically this is a special case of internal categories and groupoids
(topological categories/groupoids are categories/groupoids internal to `TopCat`), but
for actually working with them it is more convenient to define them in an unbundled manner as done
here instead of working abstractly with category/groupoid objects in `TopCat`.

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
  · dsimp; fun_prop
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
  | zero => simpa using (Arrow.continuous_id (C := C)).comp continuous_obj'
  | succ k hk =>
    specialize hk (by lia) (by lia)
    simp_rw [fun F : ComposableArrows C n ↦ map'_comp F i (i + k) (i + (k + 1))]
    suffices h : Continuous
        (fun F : ComposableArrows C n ↦ mk₂ (F.map' i (i + k)) (F.map' (i + k) (i + (k + 1)))) from
      IsTopologicalCategory.continuous_composableArrowsHom.comp h
    refine (continuous_iff').2 fun l hl ↦ ?_
    interval_cases l
    · exact hk
    · exact continuous_iff_le_induced.2 <| inf_le_of_right_le <| iInf_le_of_le (i + k) <|
        iInf_le_of_le (by lia) <| by rfl

/-- Composing `n` composable arrows is continuous. -/
lemma continuous_hom {C : Type*} [Category* C] [TopologicalSpace C] [TopologicalSpace (Arrow C)]
    [∀ X Y : C, TopologicalSpace (X ⟶ Y)] [IsTopologicalCategory C] {n : ℕ} :
    Continuous (fun F ↦ F.hom : ComposableArrows C n → Arrow C) :=
  continuous_map'

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

end CategoryTheory
