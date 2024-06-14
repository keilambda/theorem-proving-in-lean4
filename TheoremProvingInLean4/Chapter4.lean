namespace UniversalQuantification

def Forall.{u} {α : Type u} {p : α → Prop} : Prop := ∀ x : α, p x

#print Forall

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from (h z).left

variable (α : Type) (r : α → α → Prop)
variable (refl_r : ∀ {x}, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check @trans_r a b c
#check @trans_r a b c hab
#check @trans_r a b c hab hbc
#check trans_r hab hbc

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

end UniversalQuantification

namespace Equality

universe u

#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

variable (α β : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  hab.trans (hcb.symm.trans hcd)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl (f a)
example (a : α) (b : β) : (a, b).1 = a := Eq.refl a
example : 2 + 3 = 5 := Eq.refl 5

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

example (α : Type) (a b : α) (p : α → Prop) (h₁ : a = b) (h₂ : p a) : p b :=
  h₁ ▸ h₂

example (α : Type) (a b : α) (p : α → Prop) (h₁ : a = b) (h₂ : p a) : p b :=
  Eq.subst h₁ h₂

variable (f g : α → Nat) (h₁ : a = b) (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = f b := congrArg _ h₁
example : f a = g a := congrFun h₂ a
example : f a = g a := congrFun h₂ _
example : f a = g b := congr h₂ h₁

section LeanStdlibIden

variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h₁ := Nat.mul_add (x + y) x y
  have h₂ := (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h₁
  h₂.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

end LeanStdlibIden

section CalculationalProofs

variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T : a = e :=
  calc
    a = b     := h1
    _ = c + 1 := h2
    _ = d + 1 := congrArg Nat.succ h3
    _ = 1 + d := Nat.add_comm d 1
    _ = e     := Eq.symm h4

example : a = e :=
  calc
    a = b     := by rw [h1]
    _ = c + 1 := by rw [h2]
    _ = d + 1 := by rw [h3]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e     := by rw [h4]

example : a = e :=
  calc
    _ = d + 1 := by rw [h1, h2, h3]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e     := by rw [h4]

example : a = e := by rw [h1, h2, h3, Nat.add_comm, h4]

example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d := h3

def Divides (x y : Nat) : Prop := ∃ k, k * x = y

def Divides_trans (h₁ : Divides x y) (h₂ : Divides y z) : Divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def Divides_mul (x : Nat) (k : Nat) : Divides x (k * x) := ⟨k, rfl⟩

instance : Trans Divides Divides Divides := ⟨Divides_trans⟩

example (h₁ : Divides x y) (h₂ : y = z) : Divides x (2*z) :=
  calc
    Divides x y := h₁
    _ = z := h₂
    Divides _ (2 * z) := Divides_mul ..

infix:50 " ∣∣ " => Divides

example (h₁ : x ∣∣ y) (h₂ : y = z) : x ∣∣ (2*z) :=
  calc
    x ∣∣ y := h₁
    _ = z := h₂
    _ ∣∣ (2 * z) := Divides_mul ..

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y := by rw [← Nat.add_assoc]

end CalculationalProofs
end Equality

namespace ExiststentialQuantification

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h
example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)
example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩

#check @Exists.intro

variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

-- set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4

variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h (fun w ⟨pw, qw⟩ => show ∃ x, q x ∧ p x from ⟨w, qw, pw⟩)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, ⟨pw, qw⟩⟩ => ⟨w, qw, pw⟩

def IsEven (a : Nat) := ∃ b, a = 2 * b

theorem Even_plus_Even (h₁ : IsEven a) (h₂ : IsEven b) : IsEven (a + b) :=
  match h₁, h₂ with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩

open Classical

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction fun h1 =>
    have h2 : ∀ x, ¬ p x :=
      fun x =>
      fun h3 =>
      have h4 : ∃ x, p x := ⟨x, h3⟩
      show False from h1 h4
    show False from h h2

end ExiststentialQuantification
