open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun pqr => Or.elim (em (p → q))
    Or.inl
    (fun npq => Or.inr (fun hp =>
      Or.elim (pqr hp)
        (fun hq => False.elim (npq (fun _ => hq)))
        id))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun npq => Or.elim (em ¬p)
    Or.inl
    (fun nnp => Or.inr (fun hq => npq ⟨byContradiction nnp, hq⟩))

example : ¬(p → q) → p ∧ ¬q :=
  fun npq => And.intro
    (byContradiction (fun np => npq (fun hp => absurd hp np)))
    (fun hq => Or.elim (em q) (fun _ => False.elim (npq (fun _ => hq))) (fun hnq => absurd hq hnq))

example : (p → q) → (¬p ∨ q) :=
  fun h => Or.elim (em p) (fun hp => Or.inr (h hp)) Or.inl

example : (¬q → ¬p) → (p → q) :=
  fun h => Or.elim (em p)
    (fun hp => Or.elim (em q) (fun hq _ => hq) (fun nq => absurd hp (h nq)))
    (fun np hp => absurd hp np)

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
  fun pqp => Or.elim (em p) id (fun np => pqp (fun hp => absurd hp np))
