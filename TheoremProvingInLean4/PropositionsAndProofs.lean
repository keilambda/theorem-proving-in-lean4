variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun ⟨p, q⟩ => And.intro q p)
    (fun ⟨q, p⟩ => And.intro p q)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h => Or.elim h Or.inr Or.inl)
    (fun h => Or.elim h Or.inr Or.inl)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun ⟨⟨p, q⟩, r⟩ => ⟨p, q, r⟩)
    (fun ⟨p, ⟨q, r⟩⟩ => ⟨⟨p, q⟩, r⟩)

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
    (fun ⟨p, qr⟩ =>
      Or.elim qr
        (fun hq => Or.inl (And.intro p hq))
        (fun hr => Or.inr (And.intro p hr)))
    (fun hpqpr =>
      Or.elim hpqpr
        (fun ⟨p, q⟩ => And.intro p (Or.inl q))
        (fun ⟨p, r⟩ => And.intro p (Or.inr r)))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun hpqr =>
      Or.elim hpqr
        (fun hp => And.intro (Or.inl hp) (Or.inl hp))
        (fun ⟨q, r⟩ => And.intro (Or.inr q) (Or.inr r)))
    (fun ⟨pq, pr⟩ =>
      Or.elim pq
        Or.inl
        (fun hq =>
          Or.elim pr
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
