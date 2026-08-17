/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Topology.Continuous

/-! # `Equiv.congrArg`
This file contains some additional API on basic `Equiv`s, in particularly a new `Equiv.congrArg`
designed to replace `Equiv.cast` in some places while allowing for more automation. -/

variable {ι κ : Type*} {α : ι → Type*} {β : ι → Type*}

namespace Equiv

variable (α) in
/-- The identity equivalence `α i ≃ α j` given a family of types `α` and two equal indices `i`, `j`.

This is defined to be just `Equiv.cast (congrArg α h)`, but offers some technical advantages over
it: since due to proof irrelevance `Equiv.cast` "forgets" which proof of `α i = α j` was fed into
it, there is no way to write e.g. simp lemmas that match `Equiv.cast (congrArg α h)` without being
explicitly given `h`, while for simp lemmas involving `Equiv.congrArg α h` `h` can easily be
inferred from the goal state.

The reason that keeping available the information that an equality `α i = α j` came from an equality
`i = j` is relevant is that many properties hold in this context that do not hold true for
`Equiv.cast` in general: for example, `Equiv.congrArg` is continuous when applied to a family of
topological spaces, linear when applied to a family of vector spaces, equivariant when applied to a
family of `G`-sets and so on, while `Equiv.cast` could be generally none of those.

Since this means that it is usually better to have `Equiv.congrArg` in a goal than `Equiv.cast` or
`cast`, we do not make lemmas like `coe_congrArg` that replace `Equiv.congrArg` with a `cast` simp
lemmas. For lemmas that merely move an `Equiv.congrArg` around, we let the simp normal form be the
form that has `Equiv.congrArg` further on the outside, in the hope that this will let `simp` move
casts to the outside where they can hopefully cancel out or merge with an existing `Heq`. -/
protected def congrArg {i j : ι} (h : i = j) : α i ≃ α j :=
  Equiv.cast (congrArg α h)

lemma coe_congrArg {i j : ι} (h : i = j) : ⇑(Equiv.congrArg α h) = cast (congrArg α h) := rfl

@[simp]
lemma congrArg_refl {i : ι} : (Equiv.congrArg α (rfl : i = i)) = Equiv.refl (α i) := rfl

@[simp]
lemma congrArg_symm {i j : ι} (h : i = j) : (Equiv.congrArg α h).symm = .congrArg α h.symm := rfl

@[simp]
lemma congrArg_trans {i j k : ι} (h : i = j) (h' : j = k) :
    (Equiv.congrArg α h).trans (Equiv.congrArg α h') = Equiv.congrArg α (h.trans h') := by
  simp [Equiv.congrArg, ← Equiv.cast_trans]

@[simp]
lemma congrArg_congrArg {i j k : ι} (h : i = j) (h' : j = k) {x : α i} :
    (Equiv.congrArg α h') (Equiv.congrArg α h x) = Equiv.congrArg α (h.trans h') x := by
  simp [Equiv.congrArg]

/-- `Equiv.congrArg` commutes with application of dependent functions. This can not be registered
as a simp lemma because the left hand side is not of a form that simp can deal with well, but can
often be useful to pass to a simp call manually. -/
lemma apply_congrArg {f : (i : ι) → α i → β i} {i j : ι} (h : i = j) {x : α i} :
    f j (Equiv.congrArg α h x) = Equiv.congrArg β h (f i x) := by
  obtain rfl := h
  rfl

@[simp]
lemma congrArg_heq_iff_heq {i j k : ι} (h : i = j) {x : α i} {y : α k} :
    Equiv.congrArg α h x ≍ y ↔ x ≍ y := by
  subst h; simp

@[simp]
lemma heq_congrArg_iff_heq {i j k : ι} (h : i = j) {x : α k} {y : α i} :
    x ≍ Equiv.congrArg α h y ↔ x ≍ y := by
  subst h; simp

@[simp]
lemma congrArg_eq_iff_heq {i j : ι} (h : i = j) {x : α i} {y : α j} :
    Equiv.congrArg α h x = y ↔ x ≍ y := by
  subst h; simp

@[simp]
lemma eq_congrArg_iff_heq {i j : ι} (h : i = j) {x : α j} {y : α i} :
    x = Equiv.congrArg α h y ↔ x ≍ y := by
  subst h; simp

@[simp]
lemma congrArg_comp {f : κ → ι} {i j : κ} (h : i = j) :
    Equiv.congrArg (α ∘ f) h = Equiv.congrArg α (congrArg f h) := by
  subst h; simp

lemma congrArg_comp_apply {f : κ → ι} {i j : κ} (h : i = j) :
    Equiv.congrArg (fun i ↦ α (f i)) h = Equiv.congrArg α (congrArg f h) := by
  subst h; simp

/-- When applied to a family of topological spaces, `Equiv.congrArg` is continuous
(and a homeomorphism). This is one of the main technical advantages over `Equiv.cast`: it is not
generally true that `Equiv.cast` applied to two topological spaces is continuous because the two
`TopologicalSpace`-instances could be entirely unrelated, and there is no convenient way to state
that they are compatible with `Equiv.cast`, but for `Equiv.congrArg` applied to a family of spaces
the compatibility is automatic.

In principle it could also make sense to make this a definition `Homeomorph.congrArg` instead of a
lemma, but since there are so many variants of `Equiv.congrArg` that one could add
(it is an isomorphism for every structure that the types in the family carry), we haven chosen to
just make it a lemma for now. -/
@[fun_prop]
lemma continuous_congrArg [∀ i, TopologicalSpace (α i)] {i j : ι} (h : i = j) :
    Continuous (Equiv.congrArg α h) := by
  subst h
  simp [continuous_id]

/-- `Equiv.congrArg` is equivariant. We state backwards compared to how equivariance is usually
stated to make sure that simp pushes `Equiv.congrArg` further out instead of in, where it
can hopefully be merged with e.g. existing `HEq`s. -/
@[simp]
lemma smul_congrArg {G : Type*} [∀ i, SMul G (α i)] {i j : ι} (h : i = j) {g : G} {x : α i} :
    g • Equiv.congrArg α h x = Equiv.congrArg α h (g • x) := by
  subst h
  simp

end Equiv
