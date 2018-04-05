/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl

Modules over a ring.
-/

import algebra.ring algebra.big_operators data.set.lattice
open function

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

lemma set.sInter_eq_Inter {s : set (set α)} : (⋂₀ s) = (⋂i ∈ s, i) :=
set.ext $ by simp

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (α : out_param $ Type u) (γ : Type v) := (smul : α → γ → γ)

infixr ` • `:73 := has_scalar.smul

/-- A module is a generalization of vector spaces to a scalar ring.
  It consists of a scalar ring `α` and an additive group of "vectors" `β`,
  connected by a "scalar multiplication" operation `r • x : β`
  (where `r : α` and `x : β`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
class module (α : out_param $ Type u) (β : Type v) [out_param $ ring α]
  extends has_scalar α β, add_comm_group β :=
(smul_add : ∀r (x y : β), r • (x + y) = r • x + r • y)
(add_smul : ∀r s (x : β), (r + s) • x = r • x + s • x)
(mul_smul : ∀r s (x : β), (r * s) • x = r • s • x)
(one_smul : ∀x : β, (1 : α) • x = x)

section module
variables [ring α] [module α β] {r s : α} {x y : β}

theorem smul_add : r • (x + y) = r • x + r • y := module.smul_add r x y
theorem add_smul : (r + s) • x = r • x + s • x := module.add_smul r s x
theorem mul_smul : (r * s) • x = r • s • x :=  module.mul_smul r s x
@[simp] theorem one_smul : (1 : α) • x = x := module.one_smul x

@[simp] theorem zero_smul : (0 : α) • x = 0 :=
have (0 : α) • x + 0 • x = 0 • x + 0, by rw ← add_smul; simp,
add_left_cancel this

@[simp] theorem smul_zero : r • (0 : β) = 0 :=
have r • (0:β) + r • 0 = r • 0 + 0, by rw ← smul_add; simp,
add_left_cancel this

@[simp] theorem neg_smul : -r • x = - (r • x) :=
eq_neg_of_add_eq_zero (by rw [← add_smul, add_left_neg, zero_smul])

theorem neg_one_smul (x : β) : (-1 : α) • x = -x := by simp

@[simp] theorem smul_neg : r • (-x) = -(r • x) :=
by rw [← neg_one_smul x, ← mul_smul, mul_neg_one, neg_smul]

theorem smul_sub (r : α) (x y : β) : r • (x - y) = r • x - r • y :=
by simp [smul_add]

theorem sub_smul (r s : α) (y : β) : (r - s) • y = r • y - s • y :=
by simp [add_smul]

lemma smul_smul : r • s • x = (r * s) • x := mul_smul.symm

lemma smul_smul : a • (b • u) = (a * b) • u := mul_smul.symm

end module

instance ring.to_module {α : Type u} [r : ring α] : module α α :=
{ r with
  smul := λa b, a * b,
  smul_left_distrib := assume a b c, mul_add _ _ _,
  smul_right_distrib := assume a b c, add_mul _ _ _,
  mul_smul := assume a b c, mul_assoc _ _ _,
  one_smul := assume a, one_mul _ }

lemma eq_zero_of_add_self_eq {α : Type} [add_comm_group α]
{a : α} (H : a + a = a) : a = 0 :=
add_left_cancel (by {rw add_zero, exact H})


class submodule (R : Type) (M : Type) [ring R] [module R M] (p : set M) :=
(add : ∀ {u v}, u ∈ p → v ∈ p → u + v ∈ p)
(zero : (0:M) ∈ p)
(neg : ∀ {v}, v ∈ p → -v ∈ p)
(smul : ∀ c {v}, v ∈ p → c • v ∈ p)

namespace submodule

variables (R : Type) {M : Type} [ring R] [module R M]
variables {p : set M} [submodule R M p]
variables {c d : R} (u v w : {x : M // x ∈ p})

include R

protected def add' : {x : M // x ∈ p} → {x : M // x ∈ p} → {x : M // x ∈ p}
| ⟨v₁, p₁⟩ ⟨v₂, p₂⟩ := ⟨v₁ + v₂, add R p₁ p₂⟩

protected def neg' : {x : M // x ∈ p} → {x : M // x ∈ p}
| ⟨v, p⟩ := ⟨-v, neg R p⟩

protected def smul' : R → {x : M // x ∈ p} → {x : M // x ∈ p}
| c ⟨v, p⟩ := ⟨c • v, smul c p⟩

instance : has_add {x : M // x ∈ p} := ⟨submodule.add' R⟩
instance : has_zero {x : M // x ∈ p} := ⟨⟨0, zero R p⟩⟩
instance : has_neg {x : M // x ∈ p} := ⟨submodule.neg' R⟩
instance : has_scalar R {x : M // x ∈ p} := ⟨submodule.smul' R⟩

@[simp] lemma add_val : (u + v).val = u.val + v.val := by cases u; cases v; refl
@[simp] lemma zero_val : (0 : {x : M // x ∈ p}).val = 0 := rfl
@[simp] lemma neg_val : (-v).val = -v.val := by cases v; refl
@[simp] lemma smul_val : (c • v).val = c • v.val := by cases v; refl

lemma sub {u v : M} (HU : u ∈ p) (HV : v ∈ p) : u - v ∈ p := add R HU (neg R HV)

variables (R M p)

instance : module R {x : M // x ∈ p} :=
{ add                := (+),
  add_assoc          := λ u v w, subtype.eq (by simp [add_assoc]),
  zero               := 0,
  zero_add           := λ v, subtype.eq (by simp [zero_add]),
  add_zero           := λ v, subtype.eq (by simp [add_zero]),
  neg                := has_neg.neg,
  add_left_neg       := λ v, subtype.eq (by simp [add_left_neg]),
  add_comm           := λ u v, subtype.eq (by simp [add_comm]),
  smul               := (•),
  smul_left_distrib  := λ c u v, subtype.eq (by simp [smul_left_distrib]),
  smul_right_distrib := λ c u v, subtype.eq (by simp [smul_right_distrib]),
  mul_smul           := λ c d v, subtype.eq (by simp [mul_smul]),
  one_smul           := λ v, subtype.eq (by simp [one_smul]) }

instance : has_coe (submodule R M p) (module R {x : M // x ∈ p}) := ⟨λ s, submodule.module R M p⟩

end submodule


structure linear_map (R M N : Type) [ring R] [module R M] [module R N] :=
(T : M → N)
(map_add : ∀ u v, T (u+v) = T u + T v)
(map_smul : ∀ (c:R) v, T (c • v) = c • (T v))

namespace linear_map

variables {R M N : Type}

section basic

variables [ring R] [module R M] [module R N]
variables {c d : R} {A B C : linear_map R M N} {u v : M}

instance : has_coe_to_fun (linear_map R M N) := ⟨_, T⟩

@[simp] lemma map_add_app : A (u+v) = A u + A v := A.map_add u v
@[simp] lemma map_smul_app : A (c•v) = c • (A v) := A.map_smul c v

theorem ext (HAB : ∀ v, A v = B v) : A = B :=
by {cases A, cases B, congr, exact funext HAB}

@[simp] lemma map_zero : A 0 = 0 :=
begin
  have := eq.symm (map_add A 0 0),
  rw [add_zero] at this,
  exact eq_zero_of_add_self_eq this
end

@[simp] lemma map_neg : A (-v) = -(A v) :=
eq_neg_of_add_eq_zero (by {rw [←map_add_app], simp})

@[simp] lemma map_sub : A (u-v) = A u - A v := by simp

end basic


def ker [ring R] [module R M] [module R N]
  (A : linear_map R M N) : set M := {v | A v = 0}

namespace ker

variables [ring R] [module R M] [module R N]
variables {c d : R} {A : linear_map R M N} {u v : M}

@[simp] lemma mem_ker : v ∈ A.ker ↔ A v = 0 := iff.rfl

theorem ker_of_map_eq_map (Huv : A u = A v) : u-v ∈ A.ker :=
by {rw [mem_ker,map_sub], exact sub_eq_zero_of_eq Huv}

theorem inj_of_trivial_ker (H: ∀ v, A.ker v → v = 0) (Huv: A u = A v) : u = v :=
eq_of_sub_eq_zero (H _ (ker_of_map_eq_map Huv))

variables (R A)

instance : submodule R M A.ker :=
{ add  := λ u v HU HV, by {rw [mem_ker] at *, simp [HU,HV]},
  zero := map_zero,
  neg  := λ v HV, by {rw [mem_ker] at *, simp [HV]},
  smul := λ c v HV, by {rw [mem_ker] at *, simp [HV]} }

theorem sub_ker (HU : u ∈ A.ker) (HV : v ∈ A.ker) : u - v ∈ A.ker :=
submodule.sub R HU HV

end ker


def im [ring R] [module R M] [module R N]
  (A : linear_map R M N) : set N := {w | ∃ v, A v = w}

namespace im

variables [ring R] [module R M] [module R N]
variables {c d : R} {A : linear_map R M N} (u v w : N)

@[simp] lemma mem_im : w ∈ A.im ↔ ∃ v, A v = w := ⟨id, id⟩

theorem add_im (HU : u ∈ A.im) (HV : v ∈ A.im) : u + v ∈ A.im :=
begin
  unfold im at *,
  cases HU with x hx,
  cases HV with y hy,
  existsi (x + y),
  simp [hx, hy]
end

theorem zero_im : (0:N) ∈ A.im := ⟨0, map_zero⟩

theorem neg_im (HV : v ∈ A.im) : -v ∈ A.im :=
begin
  unfold im at *,
  cases HV with y hy,
  existsi (-y),
  simp [hy]
end

theorem smul_im (c : R) (v : N) (HV : v ∈ A.im) : c • v ∈ A.im :=
begin
  unfold im at *,
  cases HV with y hy,
  existsi (c • y),
  simp [hy]
end

variables (R A)

instance : submodule R N A.im :=
{ add  := add_im,
  zero := zero_im,
  neg  := neg_im,
  smul := smul_im }

end im


section add_comm_group

variables [ring R] [module R M] [module R N]
variables {c d : R} {A B C : linear_map R M N} {u v : M}

protected def add : linear_map R M N → linear_map R M N → linear_map R M N
| ⟨T₁, a₁, s₁⟩ ⟨T₂, a₂, s₂⟩ :=
{ T        := λ v, T₁ v + T₂ v,
  map_add  := λ u v, by simp [a₁, a₂],
  map_smul := λ c v, by simp [smul_left_distrib, s₁, s₂] }

protected def neg : linear_map R M N → linear_map R M N
| ⟨T, a, s⟩ :=
{ T        := (λ v, -(T v)),
  map_add  := λ u v, by simp [a],
  map_smul := λ c v, by simp [s] }

instance : has_add (linear_map R M N) := ⟨linear_map.add⟩

instance : has_zero (linear_map R M N) := ⟨
{ T        := λ v, 0,
  map_add  := λ u v, by simp,
  map_smul := λ c v, by simp }⟩

instance : has_neg (linear_map R M N) := ⟨linear_map.neg⟩

@[simp] lemma add_app : (A + B) v = A v + B v := by cases A; cases B; refl
@[simp] lemma zero_app : (0:linear_map R M N) v = 0 := rfl
@[simp] lemma neg_app : (-A) v = -(A v) := by cases A; refl

instance : add_comm_group (linear_map R M N) :=
{ add                 := (+),
  add_assoc           := λ A B C, ext (λ v, by simp [add_assoc]),
  zero                := 0,
  zero_add            := λ A, ext (λ v, by simp [zero_add]),
  add_zero            := λ A, ext (λ v, by simp [add_zero]),
  neg                 := has_neg.neg,
  add_left_neg        := λ A, ext (λ v, by simp [add_left_neg]),
  add_comm            := λ A B, ext (λ v, by simp [add_comm]) }

end add_comm_group


section Hom

variables [comm_ring R] [module R M] [module R N]
variables {c d : R} {A B C : linear_map R M N} {u v : M}

protected def smul : R → linear_map R M N → linear_map R M N
| c ⟨T, a, s⟩ :=
{ T        := λ v, c • T v,
  map_add  := λ u v, by simp [smul_left_distrib,a],
  map_smul := λ k v, by simp [smul_smul,s] }

instance : has_scalar R (linear_map R M N) := ⟨linear_map.smul⟩

@[simp] lemma smul_app : (c • A) v = c • (A v) := by cases A; refl

variables (R M N)

instance : module R (linear_map R M N) :=
{ linear_map.add_comm_group with
  smul               := (•),
  smul_left_distrib  := λ c A B, ext (λ v, by simp [module.smul_left_distrib]),
  smul_right_distrib := λ c d A, ext (λ v, by simp [module.smul_right_distrib]),
  mul_smul           := λ c d A, ext (λ v, by simp [module.mul_smul]),
  one_smul           := λ A, ext (λ v, by simp [module.one_smul]) }

end Hom

end linear_map


namespace module

variables (R M : Type)

def dual [comm_ring R] [module R M] := module R (linear_map R M R)

variables {R M}
variables [ring R] [module R M]
variables {A B C : linear_map R M M} {v : M}

protected def mul : linear_map R M M → linear_map R M M → linear_map R M M
| ⟨T₁, a₁, s₁⟩ ⟨T₂, a₂, s₂⟩ :=
{ T        := T₁ ∘ T₂,
  map_add  := λ u v, by simp [function.comp, a₂, a₁],
  map_smul := λ c v, by simp [function.comp, s₂, s₁] }

def id : linear_map R M M := ⟨id, λ u v, rfl, λ u v, rfl⟩

instance : has_mul (linear_map R M M) := ⟨module.mul⟩

@[simp] lemma id_app : (id : linear_map R M M) v = v := rfl
@[simp] lemma comp_app : (A * B) v = A (B v) := by cases A; cases B; refl

variables (A B C)

@[simp] lemma comp_id : A * id = A := linear_map.ext (λ v, by simp)
@[simp] lemma id_comp : id * A = A := linear_map.ext (λ v, by simp)
theorem comp_assoc : (A * B) * C = A * (B * C) := linear_map.ext (λ v, by simp)
theorem comp_add : A * (B + C) = A * B + A * C := linear_map.ext (λ v, by simp)
theorem add_comp : (A + B) * C = A * C + B * C := linear_map.ext (λ v, by simp)

variables (R M)

def endomorphism_ring : ring (linear_map R M M) :=
{ linear_map.add_comm_group with
  mul             := (*),
  mul_assoc       := comp_assoc,
  one             := id,
  one_mul         := id_comp,
  mul_one         := comp_id,
  left_distrib    := comp_add,
  right_distrib   := add_comp }

def general_linear_group [ring R] [module R M] :=
by have := endomorphism_ring R M; exact units (linear_map R M M)

end module
=======
instance ring.to_module [r : ring α] : module α α :=
{ smul := (*),
  smul_add := mul_add,
  add_smul := add_mul,
  mul_smul := mul_assoc,
  one_smul := one_mul, ..r }

@[simp] lemma smul_eq_mul [ring α] {a a' : α} : a • a' = a * a' := rfl

structure is_linear_map {α : Type u} {β : Type v} {γ : Type w} [ring α] [module α β] [module α γ]
  (f : β → γ) : Prop :=
(add  : ∀x y, f (x + y) = f x + f y)
(smul : ∀c x, f (c • x) = c • f x)

namespace is_linear_map
variables [ring α] [module α β] [module α γ] [module α δ]
variables {f g h : β → γ} {r : α} {x y : β}
include α

section
variable (hf : is_linear_map f)
include hf

@[simp] lemma zero : f 0 = 0 :=
calc f 0 = f (0 • 0 : β) : by rw [zero_smul]
     ... = 0 : by rw [hf.smul]; simp

@[simp] lemma neg (x : β) : f (- x) = - f x :=
eq_neg_of_add_eq_zero $ by rw [←hf.add]; simp [hf.zero]

@[simp] lemma sub (x y : β) : f (x - y) = f x - f y :=
by simp [hf.neg, hf.add]

@[simp] lemma sum {ι : Type x} {t : finset ι} {g : ι → β} : f (t.sum g) = t.sum (λi, f (g i)) :=
(finset.sum_hom f hf.zero hf.add).symm

end

lemma comp {g : δ → β} (hf : is_linear_map f) (hg : is_linear_map g) : is_linear_map (f ∘ g) :=
by refine {..}; simp [(∘), hg.add, hf.add, hg.smul, hf.smul]

lemma id : is_linear_map (id : β → β) :=
by refine {..}; simp

lemma inverse {f : γ → β} {g : β → γ}
  (hf : is_linear_map f) (h₁ : left_inverse g f) (h₂ : right_inverse g f): is_linear_map g :=
⟨assume x y,
  have g (f (g (x + y))) = g (f (g x + g y)),
    by rw [h₂ (x + y), hf.add, h₂ x, h₂ y],
  by rwa [h₁ (g (x + y)), h₁ (g x + g y)] at this,
assume a b,
  have g (f (g (a • b))) = g (f (a • g b)),
    by rw [h₂ (a • b), hf.smul, h₂ b],
  by rwa [h₁ (g (a • b)), h₁ (a • g b)] at this ⟩

lemma map_zero : is_linear_map (λb, 0 : β → γ) :=
by refine {..}; simp

lemma map_neg (hf : is_linear_map f) : is_linear_map (λb, - f b) :=
by refine {..}; simp [hf.add, hf.smul]

lemma map_add (hf : is_linear_map f) (hg : is_linear_map g) : is_linear_map (λb, f b + g b) :=
by refine {..}; simp [hg.add, hf.add, hg.smul, hf.smul, smul_add]

lemma map_sum [decidable_eq δ] {t : finset δ} {f : δ → β → γ} :
  (∀d∈t, is_linear_map (f d)) → is_linear_map (λb, t.sum $ λd, f d b) :=
finset.induction_on t (by simp [map_zero]) (by simp [map_add] {contextual := tt})

lemma map_sub (hf : is_linear_map f) (hg : is_linear_map g) : is_linear_map (λb, f b - g b) :=
by refine {..}; simp [hg.add, hf.add, hg.smul, hf.smul, smul_add]

lemma map_smul_right {α : Type u} {β : Type v} {γ : Type w} [comm_ring α] [module α β] [module α γ]
  {f : β → γ} {r : α} (hf : is_linear_map f) :
  is_linear_map (λb, r • f b) :=
by refine {..}; simp [hf.add, hf.smul, smul_add, smul_smul, mul_comm]

lemma map_smul_left {f : γ → α} (hf : is_linear_map f) : is_linear_map (λb, f b • x) :=
by refine {..}; simp [hf.add, hf.smul, add_smul, smul_smul]

end is_linear_map

/-- A submodule of a module is one which is closed under vector operations.
  This is a sufficient condition for the subset of vectors in the submodule
  to themselves form a module. -/
class is_submodule {α : Type u} {β : Type v} [ring α] [module α β] (p : set β) : Prop :=
(zero_ : (0:β) ∈ p)
(add_  : ∀ {x y}, x ∈ p → y ∈ p → x + y ∈ p)
(smul : ∀ c {x}, x ∈ p → c • x ∈ p)

namespace is_submodule
variables [ring α] [module α β] [module α γ]
variables {p p' : set β} [is_submodule p] [is_submodule p']
variables {r : α}
include α

section
variables {x y : β}

lemma zero : (0 : β) ∈ p := is_submodule.zero_ α p

lemma add : x ∈ p → y ∈ p → x + y ∈ p := is_submodule.add_ α

lemma neg (hx : x ∈ p) : -x ∈ p := by rw ← neg_one_smul x; exact smul _ hx

lemma sub (hx : x ∈ p) (hy : y ∈ p) : x - y ∈ p := add hx (neg hy)

lemma sum {ι : Type w} [decidable_eq ι] {t : finset ι} {f : ι → β} :
  (∀c∈t, f c ∈ p) → t.sum f ∈ p :=
finset.induction_on t (by simp [zero]) (by simp [add] {contextual := tt})

lemma smul_ne_0 {a : α} {b : β} (h : a ≠ 0 → b ∈ p) : a • b ∈ p :=
classical.by_cases
  (assume : a = 0, by simp [this, zero])
  (assume : a ≠ 0, by simp [h this, smul])

instance single_zero : is_submodule ({0} : set β) :=
by refine {..}; by simp {contextual := tt}

instance univ : is_submodule (set.univ : set β) :=
by refine {..}; by simp {contextual := tt}

instance image {f : β → γ} (hf : is_linear_map f) : is_submodule (f '' p) :=
{ is_submodule .
  zero_ := ⟨0, zero, hf.zero⟩,
  add_  := assume c₁ c₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
    ⟨b₁ + b₂, add hb₁ hb₂, by simp [eq₁, eq₂, hf.add]⟩,
  smul  := assume a c ⟨b, hb, eq⟩, ⟨a • b, smul a hb, by simp [hf.smul, eq]⟩ }

instance range {f : β → γ} (hf : is_linear_map f) : is_submodule (set.range f) :=
by rw [← set.image_univ]; exact is_submodule.image hf

instance preimage {f : γ → β} (hf : is_linear_map f) : is_submodule (f ⁻¹' p) :=
by refine {..}; simp [hf.zero, hf.add, hf.smul, zero, add, smul] {contextual:=tt}

instance add_submodule : is_submodule {z | ∃x∈p, ∃y∈p', z = x + y} :=
{ is_submodule .
  zero_ := ⟨0, zero, 0, zero, by simp⟩,
  add_  := assume b₁ b₂ ⟨x₁, hx₁, y₁, hy₁, eq₁⟩ ⟨x₂, hx₂, y₂, hy₂, eq₂⟩,
    ⟨x₁ + x₂, add hx₁ hx₂, y₁ + y₂, add hy₁ hy₂, by simp [eq₁, eq₂]⟩,
  smul  := assume a b ⟨x, hx, y, hy, eq⟩,
    ⟨a • x, smul _ hx, a • y, smul _ hy, by simp [eq, smul_add]⟩ }

lemma Inter_submodule {ι : Sort w} {s : ι → set β} (h : ∀i, is_submodule (s i)) :
  is_submodule (⋂i, s i) :=
by refine {..}; simp [zero, add, smul] {contextual := tt}

instance Inter_submodule' {ι : Sort w} {s : ι → set β} [h : ∀i, is_submodule (s i)] :
  is_submodule (⋂i, s i) :=
Inter_submodule h

instance sInter_submodule {s : set (set β)} [hs : ∀t∈s, is_submodule t] : is_submodule (⋂₀ s) :=
by rw [set.sInter_eq_Inter]; exact Inter_submodule (assume t, Inter_submodule $ hs t)

instance inter_submodule : is_submodule (p ∩ p') :=
suffices is_submodule (⋂₀ {p, p'} : set β), by simpa [set.inter_comm],
@is_submodule.sInter_submodule α β _ _ {p, p'} $
  by simp [or_imp_distrib, ‹is_submodule p›, ‹is_submodule p'›] {contextual := tt}

end

end is_submodule

section comm_ring

theorem is_submodule.eq_univ_of_contains_unit {α : Type u} [comm_ring α] (S : set α) [is_submodule S]
  (x y : α) (hx : x ∈ S) (h : y * x = 1) : S = set.univ :=
set.ext $ λ z, ⟨λ hz, trivial, λ hz, calc
    z = z * (y * x) : by simp [h]
  ... = (z * y) * x : eq.symm $ mul_assoc z y x
  ... ∈ S : is_submodule.smul (z * y) hx⟩

theorem is_submodule.univ_of_one_mem {α : Type u} [comm_ring α] (S : set α) [is_submodule S] :
  (1:α) ∈ S → S = set.univ :=
λ h, set.ext $ λ z, ⟨λ hz, trivial, λ hz, by simpa using (is_submodule.smul z h : z * 1 ∈ S)⟩

end comm_ring

/-- A vector space is the same as a module, except the scalar ring is actually
  a field. (This adds commutativity of the multiplication and existence of inverses.)
  This is the traditional generalization of spaces like `ℝ^n`, which have a natural
  addition operation and a way to multiply them by real numbers, but no multiplication
  operation between vectors. -/
class vector_space (α : out_param $ Type u) (β : Type v) [field α] extends module α β

/-- Subspace of a vector space. Defined to equal `is_submodule`. -/
@[reducible] def subspace {α : Type u} {β : Type v} [field α] [vector_space α β] (p : set β) :
  Prop :=
is_submodule p