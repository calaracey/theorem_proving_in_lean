/-
Solutions to _Theorem Proving in Lean_ Chapter 5
https://leanprover.github.io/theorem_proving_in_lean4/Tactics/#Theorem-Proving-in-Lean-4--Tactics
-/
import Mathlib

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  constructor
  . intro hpq
    exact ⟨hpq.right, hpq.left⟩
  . intro hqp
    exact ⟨hqp.right, hqp.left⟩

example : p ∨ q ↔ q ∨ p := by
  constructor
  . intro hpq
    cases hpq with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  . intro hqp
    cases hqp with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  . intro h
    exact ⟨h.left.left, ⟨h.left.right, h.right⟩⟩
  . intro h
    exact ⟨⟨h.left, h.right.left⟩, h.right.right⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  . intro hpqr
    cases hpqr with
      | inl hpq => cases hpq with
        | inl hp => exact Or.inl hp
        | inr hq => exact Or.inr (Or.inl hq)
      | inr hr => exact Or.inr (Or.inr hr)
  . intro hpqr2
    cases hpqr2 with
      | inl hp => exact Or.inl (Or.inl hp)
      | inr hqr => cases hqr with
        | inl hq => exact Or.inl (Or.inr hq)
        | inr hr => exact Or.inr hr

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  sorry

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  · intro h
    rcases h with hp | hqr
    · exact ⟨Or.inl hp, Or.inl hp⟩
    · rcases hqr with ⟨hq, hr⟩
      exact ⟨Or.inr hq, Or.inr hr⟩
  · rintro ⟨hpq, hpr⟩
    rcases hpq with hp | hq
    · left;  exact hp
    · rcases hpr with hp | hr
      · left;  exact hp
      · right; exact ⟨hq, hr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  . intro h
    . intro hpq
      exact h hpq.left hpq.right
  . intro h
    intro hp
    intro hq
    exact h ⟨hp, hq⟩


example : (p → q → r) ↔ (p ∧ q → r) := by
  constructor
  · rintro h ⟨hp, hq⟩
    trace_state
    exact h hp hq
  · rintro h hp hq
    exact h ⟨hp, hq⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  . intro h
    constructor
    . intro hp
      exact h (Or.inl hp)
    . intro hq
      exact h (Or.inr hq)
  . rintro ⟨hpr, hqr⟩
    rintro (hp | hq)
    . exact hpr hp
    . exact hqr hq

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  . intro h
    constructor
    . intro hp; apply h; left; exact hp
    . intro hq; apply h; right; exact hq
  . rintro ⟨hnp, hnq⟩ (hp | hq)
    . exact hnp hp
    . exact hnq hq

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  rintro (hnp | hnq) ⟨hp, hq⟩
  . exact hnp hp
  . exact hnq hq

/- TODO -/

example : ¬(p ∧ ¬p) := fun h_pnp: p ∧ ¬p => absurd h_pnp.left h_pnp.right

example : p ∧ ¬q → ¬(p → q) :=
  fun h_pnq: p ∧ ¬q =>
  fun h_ptq: p → q => False.elim (h_pnq.right (h_ptq h_pnq.left))

example : ¬p → (p → q) := fun h_np: ¬p => fun hp: p => absurd hp h_np

example : (¬p ∨ q) → (p → q) := fun h_npq: ¬p ∨ q => fun hp: p =>
  Or.elim h_npq
    (fun hnp => absurd hp hnp)
    (fun hq => hq)

example : p ∨ False ↔ p := Iff.intro
  (fun h_pF => Or.elim h_pF
    (fun hp => hp)
    (fun hF => False.elim hF)
  )
  (fun hp => Or.inl hp)

example : p ∧ False ↔ False := Iff.intro
  (fun hpF => hpF.right)
  (fun hF => ⟨False.elim hF, hF⟩)

example : (p → q) → (¬q → ¬p) :=
  fun h_ptq: p → q => fun hnq: ¬q => fun hp: p => hnq (h_ptq hp) -- false

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h_ptqr =>
    Or.elim (Classical.em q)
      (fun hq => Or.inl (fun hp => hq))
      (fun hnq => Or.inr (fun hp => (h_ptqr hp).resolve_left hnq))

example : ¬(p ∧ q) → ¬p ∨ ¬q := fun hnpq: ¬(p ∧ q) =>
  Or.elim (Classical.em p)
    (fun hp =>  Or.inr fun hq => hnpq ⟨hp, hq⟩)
    (fun hnp => Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q := fun hnptq: (p → q) → False =>
  Or.elim (Classical.em p)
    (fun hp => ⟨hp, fun hq => hnptq fun hp: p => hq⟩)
    (fun hnp => False.elim (hnptq (fun hp: p => absurd hp hnp)))

example : (p → q) → (¬p ∨ q) := fun hptq: p → q =>
  Or.elim (Classical.em p)
    (fun hp => Or.inr (hptq hp))
    (fun hnp => Or.inl hnp)

example : (¬q → ¬p) → (p → q) := fun hnqtnp: (¬q → ¬p) =>
  Or.elim (Classical.em q)
    (fun hq => fun hp => hq)
    (fun hnq => fun hp => absurd hp (hnqtnp hnq))

example : p ∨ ¬p := Classical.em p

example : (((p → q) → p) → p) :=
fun hptqtp: (p → q) → p =>
  Or.elim (Classical.em p)
    (fun hp => hp)
    (fun hnp => hptqtp (fun hp => absurd hp hnp))


variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun h : (x : α) → p x ∧ q x =>
      ⟨(fun x : α => (h x).left), (fun x : α => (h x).right)⟩)
    (fun h : (∀ x, p x) ∧ (∀ x, q x) =>
      fun x : α => ⟨h.left x, h.right x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h => fun h2 => fun y => (h y) (h2 y)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h =>
    fun x =>
      Or.elim h
        (fun hpx => Or.inl (hpx x))
        (fun hqx => Or.inr (hqx x))

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun a =>
    Iff.intro
      (fun h => h a)
      (fun h2 => fun _ => h2)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Or.elim (Classical.em r)
    (fun hr =>
      Iff.intro
        (fun _ => Or.inr hr)
        (fun _ => fun _ => Or.inr hr))
    (fun hnr =>
      Iff.intro
        (fun h =>
          Or.inl fun x =>
            Or.elim (h x)
              (fun hpx => hpx)
              (fun hr => absurd hr hnr))
        (fun h2 =>
          fun x =>
            Or.elim h2
              (fun hpx => Or.inl (hpx x))
              (fun hr => absurd hr hnr)))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun h => fun hr => fun x => h x hr)
    (fun h2 => fun x => fun hr => h2 hr x)

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have h_barber := h barber
  have hn : ¬ shaves barber barber := by
    intro hp
    exact absurd hp (h_barber.mp hp)
  absurd (h_barber.mpr hn) hn

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

set_option linter.unusedVariables false

example : (∃ x : α, r) → r :=
  fun h => Exists.elim h (fun _ hw => hw)

example (a : α) : r → ∃ x : α, r :=
  fun hr => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun h1 =>
      Exists.elim h1 (fun w hw => ⟨⟨w, hw.left⟩, hw.right⟩))
    (fun h2 =>
      Exists.elim h2.left (fun w hw => ⟨w, ⟨hw, h2.right⟩⟩))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun h =>
      Exists.elim h (fun w hw =>
        Or.elim (Classical.em (p w))
          (fun hpw => Or.inl ⟨w, hpw⟩)
          (fun hnpw =>
            have hqw : q w := Or.resolve_left hw hnpw
            Or.inr ⟨w, hqw⟩)))
    (fun h2 =>
      Or.elim h2
        (fun h21 => Exists.elim h21 (fun w hw => ⟨w, Or.inl hw⟩))
        (fun h22 => Exists.elim h22 (fun w hw => ⟨w, Or.inr hw⟩)))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h1 => fun henpx : ∃ x, ¬ p x =>
      Exists.elim henpx (fun w hnpw => absurd (h1 w) hnpw))
    (fun h2 => fun x =>
      Or.elim (Classical.em (p x))
        (fun hp => hp)
        (fun hnp => False.elim (h2 ⟨x, hnp⟩)))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun h1 => fun hnpx : (∀ x, ¬ p x) =>
      Exists.elim h1 (fun w hw => absurd hw (hnpx w)))
    (fun h2 =>
      Or.elim (Classical.em (∃ x, p x))
        (fun hp => hp)
        (fun hnp =>
          False.elim (h2 (fun z hz => hnp ⟨z, hz⟩))))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun h1 => fun z hz => h1 ⟨z, hz⟩)
    (fun h2 =>
      Or.elim (Classical.em (∃ x, p x))
        (fun h11 => Exists.elim h11 (fun w hw => absurd hw (h2 w)))
        (fun h12 => h12))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h1 =>
      Or.elim (Classical.em (∃ x, ¬ p x))
        (fun h11 => h11)
        (fun h12 =>
          show ∃ x, ¬ p x from
            False.elim
              (h1 (fun x =>
                show p x from
                  Or.elim (Classical.em (p x))
                    (fun hpx => hpx)
                    (fun hnx => False.elim (h12 ⟨x, hnx⟩))))))
    (fun h2 =>
      fun h21 =>
        show False from
          Exists.elim
            (h2)
            (fun w =>
              fun hw =>
                absurd
                  (h21 w)
                  (hw)
            )
      )

example : (∀ x, (p x → r)) ↔ ((∃ x, p x) → r) :=
  Iff.intro
    (fun h1: ∀ x, (p x → r) => fun h11: ∃ x, p x =>
      show r from Exists.elim (h11) (fun w => fun hw => (h1 w) hw))
    (fun h2: (∃ x, p x) → r => fun z => fun hpz => h2 ⟨z, hpz⟩)

example (a : α) : (∃ x, (p x → r)) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun h1: ∃ x, (p x → r) => fun h12: ∀ x, p x => show r from Exists.elim (h1) (fun w => fun hw => hw (h12 w)))
    (fun h2: (∀ x, p x) → r =>
      show ∃ x, (p x → r) from Or.elim (Classical.em r)
      (fun hr => ⟨a, fun hpa => hr⟩)
      (fun hnr => Or.elim (Classical.em (∀ x, p x))
        (fun hpx => absurd (h2 hpx) hnr)
        (fun hnx => show ∃ x, (p x → r) from Or.elim (Classical.em (∃ x, ¬ p x))
          (fun hepx => Exists.elim (hepx) (fun w => fun hw => show ∃ x, (p x → r) from ⟨w, fun hpw => False.elim (hw hpw)⟩))
          (fun hnepx => False.elim (hnx (show ∀ x, p x from fun x => Or.elim (Classical.em (p x)) (fun h1 => h1) (fun h2 => False.elim (hnepx ⟨x, h2⟩))))))))

example (a : α) : (∃ x, (r → p x)) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun h2: ∃ x, (r → p x) => fun hr => Exists.elim (h2) (fun w => fun hw => show ∃ x, p x from ⟨w, hw hr⟩))
    (fun h1 => Or.elim (Classical.em (r)) (fun hr => Exists.elim (h1 hr) (fun w => fun hw => ⟨w, fun hz => hw⟩)) (fun hnr => ⟨a, show r → p a from fun hr => absurd hr hnr⟩))
