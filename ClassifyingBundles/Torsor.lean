/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.End

/-! # Multiplicative torsors
Basic API on multiplicative torsors. I already directly submitted this to mathlib in
https://github.com/leanprover-community/mathlib4/pull/38896/, since the code is not an addition
but a refactor of existing files; but since we won't have access to these changes in this repository
for a while, I'm also copying the code here for now.
-/

/-- Type class for the `/ₛ` notation. -/
class SDiv (G : outParam Type*) (P : Type*) where
  /-- `a /ₛ b` computes the quotient of `a` and `b`. The meaning of this notation is
  type-dependent, but it is intended to be used for multiplicative torsors. -/
  sdiv : P → P → G

@[inherit_doc] infixl:65 " /ₛ " => SDiv.sdiv

recommended_spelling "sdiv" for "/ₛ" in [SDiv.sdiv, «term_/ₛ_»]

-- code analogous to that in `Mathlib.Algebra.AddTorsor.Defs`
section Defs

/-- A `Torsor G P` gives a structure to the nonempty type `P`,
acted on by a `Group G` with a transitive and free action given
by the `•` operation and a corresponding division given by the
`/ₛ` operation. -/
class Torsor (G : outParam Type*) (P : Type*) [Group G] extends MulAction G P, SDiv G P where
  [nonempty : Nonempty P]
  /-- Scalar division and multiplication with the same element cancels out. -/
  sdiv_smul' : ∀ p₁ p₂ : P, (p₁ /ₛ p₂ : G) • p₂ = p₁
  /-- Scalar multiplication and division with the same element cancels out. -/
  smul_sdiv' : ∀ (g : G) (p : P), (g • p) /ₛ p = g

attribute [instance 100] Torsor.nonempty

/-- A `Group G` is a torsor for itself. -/
instance Group.toTorsor (G : Type*) [Group G] : Torsor G G where
  sdiv := Div.div
  sdiv_smul' := div_mul_cancel
  smul_sdiv' := mul_div_cancel_right

/-- Simplify division for a torsor for a `Group G` over itself. -/
@[simp]
theorem sdiv_eq_div {G : Type*} [Group G] (g₁ g₂ : G) : g₁ /ₛ g₂ = g₁ / g₂ :=
  rfl

section General

variable {G : Type*} {P : Type*} [Group G] [T : Torsor G P]

/-- Scalar multiplying the result of dividing another point produces that point. -/
@[simp]
theorem sdiv_smul (p₁ p₂ : P) : (p₁ /ₛ p₂) • p₂ = p₁ :=
  Torsor.sdiv_smul' p₁ p₂

/-- Multiplying by a group element then dividing by the original point
produces that group element. -/
@[simp]
theorem smul_sdiv (g : G) (p : P) : (g • p) /ₛ p = g :=
  Torsor.smul_sdiv' g p

/-- If the same point multiplied with two group elements produces equal
results, those group elements are equal. -/
theorem smul_right_cancel {g₁ g₂ : G} (p : P) (h : g₁ • p = g₂ • p) : g₁ = g₂ := by
  rw [← smul_sdiv g₁ p, h, smul_sdiv]

@[simp]
theorem smul_right_cancel_iff {g₁ g₂ : G} (p : P) : g₁ • p = g₂ • p ↔ g₁ = g₂ :=
  ⟨smul_right_cancel p, fun h => h ▸ rfl⟩

/-- Multiplying a group element with the point `p` is an injective function. -/
theorem smul_right_injective' (p : P) : Function.Injective ((· • p) : G → P) := fun _ _ =>
  smul_right_cancel p

/-- Multiplying a group element with a point, then dividing by another point,
produces the same result as dividing the points then multiplying the group element. -/
theorem smul_sdiv_assoc (g : G) (p₁ p₂ : P) : (g • p₁) /ₛ p₂ = g * (p₁ /ₛ p₂) := by
  apply smul_right_cancel p₂
  rw [sdiv_smul, mul_smul, sdiv_smul]

/-- Dividing a point by itself produces 1. -/
@[simp]
theorem sdiv_self (p : P) : p /ₛ p = (1 : G) := by
  rw [← one_mul (p /ₛ p), ← smul_sdiv_assoc, smul_sdiv]

/-- If dividing two points produces 1, they are equal. -/
theorem eq_of_sdiv_eq_one {p₁ p₂ : P} (h : p₁ /ₛ p₂ = (1 : G)) : p₁ = p₂ := by
  rw [← sdiv_smul p₁ p₂, h, one_smul]

/-- Dividing two points produces 1 if and only if they are equal. -/
@[simp]
theorem sdiv_eq_one_iff_eq {p₁ p₂ : P} : p₁ /ₛ p₂ = (1 : G) ↔ p₁ = p₂ :=
  Iff.intro eq_of_sdiv_eq_one fun h => h ▸ sdiv_self _

theorem sdiv_ne_one {p q : P} : p /ₛ q ≠ (1 : G) ↔ p ≠ q :=
  not_congr sdiv_eq_one_iff_eq

/-- Cancellation multiplying the results of two divisions. -/
@[simp]
theorem sdiv_mul_sdiv_cancel (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂) * (p₂ /ₛ p₃) = p₁ /ₛ p₃ := by
  apply smul_right_cancel p₃
  rw [mul_smul, sdiv_smul, sdiv_smul, sdiv_smul]

/-- Dividing two points in the reverse order produces the inverse of dividing them. -/
@[simp]
theorem inv_sdiv_eq_sdiv_rev (p₁ p₂ : P) : (p₁ /ₛ p₂)⁻¹ = p₂ /ₛ p₁ := by
  refine inv_eq_of_mul_eq_one_right (smul_right_cancel p₁ ?_)
  rw [sdiv_mul_sdiv_cancel, sdiv_self]

theorem smul_sdiv_eq_div_sdiv (g : G) (p q : P) : (g • p) /ₛ q = g / (q /ₛ p) := by
  rw [smul_sdiv_assoc, div_eq_mul_inv, inv_sdiv_eq_sdiv_rev]

/-- Dividing by the result of multiplying with a group element produces the same result
as dividing the points and dividing by that group element. -/
theorem sdiv_smul_eq_sdiv_div (p₁ p₂ : P) (g : G) : p₁ /ₛ (g • p₂) = (p₁ /ₛ p₂) / g := by
  rw [← mul_right_inj (p₂ /ₛ p₁ : G), sdiv_mul_sdiv_cancel, ← inv_sdiv_eq_sdiv_rev, smul_sdiv, ←
    mul_div_assoc, ← inv_sdiv_eq_sdiv_rev, inv_mul_cancel, one_div]

/-- Cancellation dividing the results of two divisions. -/
@[simp]
theorem sdiv_div_sdiv_cancel_right (p₁ p₂ p₃ : P) : (p₁ /ₛ p₃) / (p₂ /ₛ p₃) = p₁ /ₛ p₂ := by
  rw [← sdiv_smul_eq_sdiv_div, sdiv_smul]

/-- Convert between an equality with multiplying a group element with a point
and an equality of a division of two points with a group element. -/
theorem eq_smul_iff_sdiv_eq (p₁ : P) (g : G) (p₂ : P) : p₁ = g • p₂ ↔ p₁ /ₛ p₂ = g :=
  ⟨fun h => h.symm ▸ smul_sdiv _ _, fun h => h ▸ (sdiv_smul _ _).symm⟩

theorem smul_eq_smul_iff_inv_mul_eq_sdiv {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ • p₁ = v₂ • p₂ ↔ v₁⁻¹ * v₂ = p₁ /ₛ p₂ := by
  rw [eq_smul_iff_sdiv_eq, smul_sdiv_assoc, ← mul_right_inj v₁⁻¹, inv_mul_cancel_left, eq_comm]

@[simp]
theorem smul_sdiv_smul_cancel_right (v₁ v₂ : G) (p : P) : (v₁ • p) /ₛ (v₂ • p) = v₁ / v₂ := by
  rw [sdiv_smul_eq_sdiv_div, smul_sdiv_assoc, sdiv_self, mul_one]

end General

namespace Equiv

variable {G : Type*} {P : Type*} [Group G] [Torsor G P]

/-- `v ↦ v • p` as an equivalence. -/
def smulConst (p : P) : G ≃ P where
  toFun v := v • p
  invFun p' := p' /ₛ p
  left_inv _ := smul_sdiv _ _
  right_inv _ := sdiv_smul _ _

@[simp]
theorem coe_smulConst (p : P) : ⇑(smulConst p) = fun v => v • p :=
  rfl

@[simp]
theorem coe_smulConst_symm (p : P) : ⇑(smulConst p).symm = fun p' => p' /ₛ p :=
  rfl

/-- `p' ↦ p /ₛ p'` as an equivalence. -/
def constSDiv (p : P) : P ≃ G where
  toFun := (p /ₛ ·)
  invFun := (·⁻¹ • p)
  left_inv p' := by simp
  right_inv v := by simp [sdiv_smul_eq_sdiv_div]

@[simp]
lemma coe_constSDiv (p : P) : ⇑(constSDiv p) = (p /ₛ ·) := rfl

@[simp]
theorem coe_constSDiv_symm (p : P) : ⇑(constSDiv p).symm = fun (v : G) => v⁻¹ • p :=
  rfl

variable (P)

/-- The permutation given by `p ↦ v • p`. -/
def constSMul (v : G) : Equiv.Perm P where
  toFun := (v • ·)
  invFun := (v⁻¹ • ·)
  left_inv p := by simp [smul_smul]
  right_inv p := by simp [smul_smul]

@[simp]
lemma coe_constSMul (v : G) : ⇑(constSMul P v) = (v • ·) := rfl

end Equiv

theorem Torsor.subsingleton_iff (G P : Type*) [Group G] [Torsor G P] :
    Subsingleton G ↔ Subsingleton P := by
  inhabit P
  exact (Equiv.smulConst default).subsingleton_congr

end Defs

-- code analogous to that in `Mathlib.Algebra.AddTorsor.Basic`
section Basic

section General

variable {G : Type*} {P : Type*} [Group G] [T : Torsor G P]

/-- If dividing two points by the same point produces equal results, those points are equal. -/
theorem sdiv_left_cancel {p₁ p₂ p : P} (h : p₁ /ₛ p = p₂ /ₛ p) : p₁ = p₂ := by
  rwa [← div_eq_one, sdiv_div_sdiv_cancel_right, sdiv_eq_one_iff_eq] at h

/-- Dividing two points by the same point produces equal results
if and only if those points are equal. -/
@[simp]
theorem sdiv_left_cancel_iff {p₁ p₂ p : P} : p₁ /ₛ p = p₂ /ₛ p ↔ p₁ = p₂ :=
  ⟨sdiv_left_cancel, fun h => h ▸ rfl⟩

/-- Dividing by the point `p` is an injective function. -/
theorem sdiv_left_injective (p : P) : Function.Injective ((· /ₛ p) : P → G) := fun _ _ =>
  sdiv_left_cancel

/-- If dividing the same point by two points produces equal results, those points are equal. -/
theorem sdiv_right_cancel {p₁ p₂ p : P} (h : p /ₛ p₁ = p /ₛ p₂) : p₁ = p₂ := by
  refine smul_left_cancel (p /ₛ p₂) ?_
  rw [sdiv_smul, ← h, sdiv_smul]

/-- Subtracting two points from the same point produces equal results
if and only if those points are equal. -/
@[simp]
theorem sdiv_right_cancel_iff {p₁ p₂ p : P} : p /ₛ p₁ = p /ₛ p₂ ↔ p₁ = p₂ :=
  ⟨sdiv_right_cancel, fun h => h ▸ rfl⟩

/-- Dividing the point `p` by other points is an injective function. -/
theorem sdiv_right_injective (p : P) : Function.Injective ((p /ₛ ·) : P → G) := fun _ _ =>
  sdiv_right_cancel

end General

section comm

variable {G : Type*} {P : Type*} [CommGroup G] [Torsor G P]

/-- Cancellation dividing the results of two divisions. -/
@[simp]
theorem sdiv_div_sdiv_cancel_left (p₁ p₂ p₃ : P) : (p₃ /ₛ p₂) / (p₃ /ₛ p₁) = p₁ /ₛ p₂ := by
  rw [div_eq_mul_inv, inv_sdiv_eq_sdiv_rev, mul_comm, sdiv_mul_sdiv_cancel]

@[simp]
theorem smul_sdiv_smul_cancel_left (v : G) (p₁ p₂ : P) : (v • p₁) /ₛ (v • p₂) = p₁ /ₛ p₂ := by
  rw [sdiv_smul_eq_sdiv_div, smul_sdiv_assoc, mul_div_cancel_left]

theorem smul_sdiv_smul_comm (v₁ v₂ : G) (p₁ p₂ : P) :
    (v₁ • p₁) /ₛ (v₂ • p₂) = (v₁ / v₂) * (p₁ /ₛ p₂) := by
  rw [sdiv_smul_eq_sdiv_div, smul_sdiv_assoc, mul_div_assoc, ← mul_comm_div]

theorem div_mul_sdiv_comm (v₁ v₂ : G) (p₁ p₂ : P) :
    (v₁ / v₂) * (p₁ /ₛ p₂) = (v₁ • p₁) /ₛ (v₂ • p₂) :=
  smul_sdiv_smul_comm _ _ _ _ |>.symm

theorem sdiv_smul_comm (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂ : G) • p₃ = (p₃ /ₛ p₂) • p₁ := by
  rw [← @sdiv_eq_one_iff_eq G, smul_sdiv_assoc, sdiv_smul_eq_sdiv_div]
  simp

theorem smul_eq_smul_iff_div_eq_sdiv {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ • p₁ = v₂ • p₂ ↔ v₂ / v₁ = p₁ /ₛ p₂ := by
  rw [smul_eq_smul_iff_inv_mul_eq_sdiv, inv_mul_eq_div]

theorem sdiv_div_sdiv_comm (p₁ p₂ p₃ p₄ : P) :
    (p₁ /ₛ p₂) / (p₃ /ₛ p₄) = (p₁ /ₛ p₃) / (p₂ /ₛ p₄) := by
  rw [← sdiv_smul_eq_sdiv_div, sdiv_smul_comm, sdiv_smul_eq_sdiv_div]

end comm

namespace Prod

variable {G G' P P' : Type*} [Group G] [Group G'] [Torsor G P] [Torsor G' P']

instance instTorsor : Torsor (G × G') (P × P') where
  smul v p := (v.1 • p.1, v.2 • p.2)
  one_smul _ := Prod.ext (one_smul _ _) (one_smul _ _)
  mul_smul _ _ _ := Prod.ext (mul_smul _ _ _) (mul_smul _ _ _)
  sdiv p₁ p₂ := (p₁.1 /ₛ p₂.1, p₁.2 /ₛ p₂.2)
  sdiv_smul' _ _ := Prod.ext (sdiv_smul _ _) (sdiv_smul _ _)
  smul_sdiv' _ _ := Prod.ext (smul_sdiv _ _) (smul_sdiv _ _)

@[simp]
theorem fst_smul (v : G × G') (p : P × P') : (v • p).1 = v.1 • p.1 :=
  rfl

@[simp]
theorem snd_smul (v : G × G') (p : P × P') : (v • p).2 = v.2 • p.2 :=
  rfl

@[simp]
theorem mk_smul_mk (v : G) (v' : G') (p : P) (p' : P') : (v, v') • (p, p') = (v • p, v' • p') :=
  rfl

@[simp]
theorem fst_sdiv (p₁ p₂ : P × P') : (p₁ /ₛ p₂ : G × G').1 = p₁.1 /ₛ p₂.1 :=
  rfl

@[simp]
theorem snd_sdiv (p₁ p₂ : P × P') : (p₁ /ₛ p₂ : G × G').2 = p₁.2 /ₛ p₂.2 :=
  rfl

@[simp]
theorem mk_sdiv_mk (p₁ p₂ : P) (p₁' p₂' : P') :
    ((p₁, p₁') /ₛ (p₂, p₂') : G × G') = (p₁ /ₛ p₂, p₁' /ₛ p₂') :=
  rfl

end Prod

namespace Pi

universe u v w

variable {I : Type u} {fg : I → Type v} [∀ i, Group (fg i)] {fp : I → Type w}
  [∀ i, Torsor (fg i) (fp i)]

/-- A product of `Torsor`s is a `Torsor`. -/
instance instTorsor : Torsor (∀ i, fg i) (∀ i, fp i) where
  sdiv p₁ p₂ i := p₁ i /ₛ p₂ i
  sdiv_smul' p₁ p₂ := funext fun i => sdiv_smul (p₁ i) (p₂ i)
  smul_sdiv' g p := funext fun i => smul_sdiv (g i) (p i)

@[simp]
theorem sdiv_apply (p q : ∀ i, fp i) (i : I) : (p /ₛ q) i = p i /ₛ q i :=
  rfl

@[push ←]
theorem sdiv_def (p q : ∀ i, fp i) : p /ₛ q = fun i => p i /ₛ q i :=
  rfl

end Pi

namespace Equiv

variable (G : Type*) (P : Type*) [Group G] [Torsor G P]

@[simp]
theorem constSMul_one : constSMul P (1 : G) = 1 :=
  ext <| one_smul G

variable {G}

@[simp]
theorem constSMul_mul (v₁ v₂ : G) : constSMul P (v₁ * v₂) = constSMul P v₁ * constSMul P v₂ :=
  ext <| mul_smul v₁ v₂

/-- `Equiv.constSMul` as a homomorphism from `G` to `Equiv.perm P` -/
def constSMulHom : G →* Equiv.Perm P where
  toFun v := constSMul P v
  map_one' := constSMul_one G P
  map_mul' := constSMul_mul P

end Equiv

/-- Pullback of a torsor along an injective map. -/
abbrev Function.Injective.torsor {G P Q : Type*}
    [Group G] [Torsor G P] [SMul G Q] [SDiv G Q] [Nonempty Q] (f : Q → P)
    (hf : Function.Injective f)
    (smul : ∀ (c : G) (x : Q), f (c • x) = c • f x)
    (sdiv : ∀ (x y : Q), x /ₛ y = f x /ₛ f y) : Torsor G Q where
  __ := hf.mulAction f smul
  sdiv_smul' x y := hf <| by simp only [sdiv, smul, sdiv_smul]
  smul_sdiv' c x := by simp [sdiv, smul]

/-- Pushforward of a torsor along a surjective map. -/
abbrev Function.Surjective.torsor {G P Q : Type*}
    [Group G] [Torsor G P] [SMul G Q] [SDiv G Q]
    (f : P → Q) (hf : Surjective f)
    (smul : ∀ (c : G) (x : P), f (c • x) = c • f x)
    (sdiv : ∀ (x y : P), x /ₛ y = f x /ₛ f y) : Torsor G Q where
  __ := hf.mulAction f smul
  nonempty := Torsor.nonempty.map f
  sdiv_smul' := by simp [hf.forall, ← smul, ← sdiv]
  smul_sdiv' := by simp [hf.forall, ← smul, ← sdiv]

end Basic
