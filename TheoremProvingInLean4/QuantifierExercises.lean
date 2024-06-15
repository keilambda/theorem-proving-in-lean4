open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := fun ⟨_, hr⟩ => hr

example (a : α) : r → (∃ x : α, r) := fun hr => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun ⟨w, ⟨hp, hr⟩⟩ => And.intro ⟨w, hp⟩ hr)
    (fun ⟨⟨w, hp⟩, hr⟩ => ⟨w, And.intro hp hr⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨w, hpq⟩ => Or.elim hpq (fun hp => Or.inl ⟨w, hp⟩) (fun hq => Or.inr ⟨w, hq⟩))
    (fun h => Or.elim h (fun ⟨w, hp⟩ => ⟨w, Or.inl hp⟩) (fun ⟨w, hq⟩ => ⟨w, Or.inr hq⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun hxp ⟨w, np⟩ => absurd (hxp w) np)
    (fun hnxnp hx => byContradiction (fun npx => hnxnp ⟨hx, npx⟩))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun ⟨w, hp⟩ hxnp => absurd hp (hxnp w))
    (fun hnxnp => byContradiction
      (fun hnxp => hnxnp
        (fun hx => byContradiction
          (fun hnnp => hnnp (fun hp => absurd ⟨hx, hp⟩ hnxp)))))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun hnxp hx hp => hnxp ⟨hx, hp⟩)
    (fun hxnp ⟨hx, hp⟩ => absurd hp (hxnp hx))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun hnxp => byContradiction
      (fun hnxnp => hnxp
        (fun hx => byContradiction
          (fun hnp => hnxnp ⟨hx, hnp⟩))))
    (fun ⟨hx, hnp⟩ hxp => absurd (hxp hx) hnp)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun hxpr ⟨hx, hp⟩ => (hxpr hx) hp)
    (fun hxpr hx hp => hxpr ⟨hx, hp⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨hx, hpr⟩ hxp => hpr (hxp hx))
    (fun hxpr => byCases
      (fun hxp => ⟨a, fun _ => hxpr hxp⟩)
      (fun hnxp => byContradiction
        (fun hnxpr => hnxp (fun x => byContradiction (fun hnp => hnxpr ⟨x, (fun hp => absurd hp hnp)⟩)))))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun ⟨hx, hrp⟩ hr => ⟨hx, hrp hr⟩)
    (fun hrxp => ⟨a, fun hr => have ⟨hx, hp⟩ := hrxp hr; sorry⟩)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun hxpq => ⟨fun hx => (hxpq hx).left, fun hx => (hxpq hx).right⟩)
    (fun ⟨hxp, hxq⟩ hx => ⟨hxp hx, hxq hx⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hxpq hxp hx => (hxpq hx) (hxp hx)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun hxpxq hx => Or.elim hxpxq
    (fun hxp => Or.inl (hxp hx))
    (fun hxq => Or.inr (hxq hx))

example : α → ((∀ x : α, r) ↔ r) :=
  fun hx => Iff.intro
    (fun hxr => hxr hx)
    (fun hr _ => hr)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun hxpr => sorry)
    (fun hxpr hx => Or.elim hxpr (fun hxp => Or.inl (hxp hx)) Or.inr)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun hxrp hr hx => (hxrp hx) hr)
    (fun hrxp hx hr => (hrxp hr) hx)
