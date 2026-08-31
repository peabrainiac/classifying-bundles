/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Homeomorph.TransferInstance

/-! # Trivial group actions

In this file we define a typeclass `TrivialSMul G X` stating that the action of `G` on `X` is
trivial, and a type synonym `WithTrivialSMul G X` for equipping any type `X` with a trivial
`G`-action.

One motivating use case for this is working with group actions on products that are induced by
actions on only one of the factors: by default, `X × Y` is only equipped with a `G`-action when
both `X` and `Y` are, and adding an instance of `SMul G (X × Y)` for the case where `G` acts only
on `X` or only on `Y` would lead to a conflict in the case where `G` acts on both.
`WithTrivialSMul` solves this because when e.g. `X` carries a `G`-action but `Y` does not, the
product action on `X × WithTrivialSMul G Y` is the action induced only by the action on `X`.
-/

/-- `G` acts trivially on `X` if `g • x = x` for all `g` and `x`. -/
class TrivialSMul (G X : Type*) [SMul G X] where
  smul_eq_self (g : G) (x : X) : g • x = x

/- TODO: check if this slows down `simp` too much and remove it again if it does. It is potentially
costly because it means `simp` has to try to synthesise `TrivialSMul` whenever it encounters an
expression containing scalar multiplication. -/
attribute [simp] TrivialSMul.smul_eq_self

set_option linter.unusedVariables false in
/-- A type synonym for `X` equipped with the trivial action by `G`. -/
def _root_.WithTrivialSMul (G X : Type*) := X

instance {G X : Type*} : SMul G (WithTrivialSMul G X) where
  smul _ x := x

instance {G X : Type*} : TrivialSMul G (WithTrivialSMul G X) where
  smul_eq_self _ _ := rfl

/- TODO: similarly check for the performance impact of this and the following instances, and
specialise them to `WithTrivialSMul G X` if it is too high. -/
instance {G X : Type*} [Monoid G] [SMul G X] [TrivialSMul G X] : MulAction G X where
  mul_smul := by simp
  one_smul := by simp

instance {G X : Type*} [TopologicalSpace G] [TopologicalSpace X] [SMul G X] [TrivialSMul G X] :
    ContinuousSMul G X where
  continuous_smul := by simp [continuous_snd]

/-- The identity equivalence between `WithTrivialSMul G X` and `X`. -/
def WithTrivialSMul.equiv (G X : Type*) : WithTrivialSMul G X ≃ X where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

instance {G X : Type*} [TopologicalSpace X] : TopologicalSpace (WithTrivialSMul G X) :=
  (WithTrivialSMul.equiv G X).topologicalSpace

/-- The identity homeomorphism between `WithTrivialSMul G X` and `X`. -/
def WithTrivialSMul.homeomorph (G X : Type*) [TopologicalSpace X] : WithTrivialSMul G X ≃ₜ X :=
  (WithTrivialSMul.equiv G X).homeomorph
