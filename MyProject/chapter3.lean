/-
Solutions to _Theorem Proving in Lean_ Chapter 3
https://leanprover.github.io/theorem_proving_in_lean4/Propositions-and-Proofs/#propositions-and-proofs
-/
import Mathlib

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
  (fun hpq: p ∧ q =>
    have hq: q := hpq.right
    have hp: p := hpq.left
    show q ∧ p from And.intro hq hp)
  (fun hqp: q ∧ p =>
    have hq: q := hqp.left
    have hp: p := hqp.right
    show p ∧ q from And.intro hp hq)

example : p ∨ q ↔ q ∨ p :=
 Iff.intro
  (fun hpq: p ∨ q =>
    Or.elim hpq (fun hp => Or.inr hp) (fun hq => Or.inl hq))
  (fun hqp: q ∨ p =>
    Or.elim hqp (fun hq => Or.inr hq) (fun hp => Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
 Iff.intro
  (fun h: ((p ∧ q) ∧ r) => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
  (fun h: (p ∧ (q ∧ r)) => ⟨⟨h.left, h.right.left⟩, h.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hpqr: ((p ∨ q) ∨ r) =>
      Or.elim hpqr
      -- goal here is to get p ∨ (q ∨ r)
        (fun hpq: p ∨ q =>
          Or.elim hpq (fun hp => Or.inl hp) (fun hq => Or.inr (Or.inl hq)))
        (fun hr => Or.inr (Or.inr hr)))
    (fun hpqr2: (p ∨ (q ∨ r)) =>
      Or.elim hpqr2
        (fun hp => Or.inl (Or.inl hp))
        (fun hqr => Or.elim hqr (fun hq => Or.inl (Or.inr hq)) (fun hr => Or.inr hr)
        )
    )

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h: (p ∧ (q ∨ r)) =>
      Or.elim h.right
        (fun hq => Or.inl ⟨h.left, hq⟩)
        (fun hr => Or.inr ⟨h.left, hr⟩))
    (fun h: ((p ∧ q) ∨ (p ∧ r)) =>
      Or.elim h
        (fun hpq => ⟨hpq.left, Or.inl hpq.right⟩)
        (fun hpr => ⟨hpr.left, Or.inr hpr.right⟩)
    )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h: p ∨ (q ∧ r) =>
      Or.elim h
        (fun hp => ⟨Or.inl hp, Or.inl hp⟩)
        (fun hqr => ⟨Or.inr hqr.left, Or.inr hqr.right⟩))
    (fun h: (p ∨ q) ∧ (p ∨ r) =>
      Or.elim h.left
        (fun hp => Or.inl hp)
        (fun hq =>
          Or.elim h.right
          (fun hp => Or.inl hp)
          (fun hr => Or.inr ⟨hq, hr⟩ )))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h: p → (q → r) => fun h_pq: p ∧ q => h h_pq.left h_pq.right)
    (fun h: p ∧ q → r => fun h_p: p => fun h_q: q => h ⟨h_p, h_q⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h: (p ∨ q) → r => ⟨fun hp: p => h (Or.inl hp), fun hq: q => h (Or.inr hq) ⟩)
    (fun h: (p → r) ∧ (q → r) => fun h_pq: p ∨ q =>
      Or.elim h_pq
        (fun hp => h.left hp)
        (fun hq => h.right hq)
    )

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    -- if p or q, then false
    -- if p then false and if q then false
    (fun h: ¬(p ∨ q) => ⟨fun hp: p => h (Or.inl hp), fun hq => h (Or.inr hq)⟩)
    (fun h: ¬p ∧ ¬q => fun h_pq: p ∨ q => Or.elim h_pq
      (fun hp => h.left hp)
      (fun hq => h.right hq)
    )
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    (fun h: ¬p ∨ ¬q => fun h_pq: p ∧ q =>
      Or.elim h
        (fun hnp => hnp h_pq.left)
        (fun hnq => hnq h_pq.right)
    )
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
