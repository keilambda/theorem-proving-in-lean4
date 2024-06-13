variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => And.intro h.right h.left)
    (fun h : q ∧ p => And.intro h.right h.left)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h => Or.elim h Or.inr Or.inl)
    (fun h => Or.elim h Or.inr Or.inl)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h => have hpq := h.left; ⟨hpq.left, hpq.right, h.right⟩)
    (fun h => have hqr := h.right; ⟨⟨h.left, hqr.left⟩, hqr.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hpqr => Or.elim hpqr
      (fun hpq => Or.elim hpq Or.inl (fun hq => Or.inr (Or.inl hq)))
      (fun hr => Or.inr (Or.inr hr)))
    (fun hpqr => Or.elim hpqr
      (fun hp => Or.inl (Or.inl hp))
      (fun hqr => Or.elim hqr (fun hq => Or.inl (Or.inr hq)) Or.inr))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun hpqr =>
      have hqr := hpqr.right
      Or.elim hqr
        (fun hq => Or.inl (And.intro hpqr.left hq))
        (fun hr => Or.inr (And.intro hpqr.left hr)))
    (fun hpqpr =>
      Or.elim hpqpr
        (fun hpq => And.intro hpq.left (Or.inl hpq.right))
        (fun hpr => And.intro hpr.left (Or.inr hpr.right)))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun hpqr =>
      Or.elim hpqr
        (fun hp => And.intro (Or.inl hp) (Or.inl hp))
        (fun hqr => And.intro (Or.inr hqr.left) (Or.inr hqr.right)))
    (fun hpqpr =>
      Or.elim hpqpr.left
        Or.inl
        (fun hq =>
          Or.elim hpqpr.right
            Or.inl
            (fun hr => Or.inr (And.intro hq hr))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
