/-
Solutions to _Theorem Proving in Lean_ Chapter 4
https://leanprover.github.io/theorem_proving_in_lean4/Propositions-and-Proofs/#propositions-and-proofs
-/
import Mathlib

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

--  Remember that, without any parameters, an expression of type Prop is just an assertion.
--  Fill in the definitions of prime and Fermat_prime below, and construct each of the given assertions.

def even (n : Nat) : Prop := ∃ k, n = 2 * k

def odd (n : Nat) : Prop := ¬ even n

def prime (n : Nat) : Prop :=
  n >= 2 ∧ ∀ a b : Nat, n = a * b → a = 1 ∨ b = 1

-- For example, you can say that there are infinitely many primes by asserting that for every
-- natural number n, there is a prime number greater than n.
def infinitely_many_primes : Prop :=
  ∀ a : Nat, ∃ k : Nat, k > a ∧ prime k

def Fermat_prime (n : Nat) : Prop :=
  (∃ k : Nat, n = 2 ^ (2 ^ k) + 1) ∧ prime n

def infinitely_many_Fermat_primes : Prop :=
  ∀ a : Nat, ∃ k : Nat, k > a ∧ Fermat_prime k

-- Goldbach's weak conjecture states that every odd number greater than 5 is the sum of three primes.
-- Look up the definition of a Fermat prime or any of the other statements, if necessary.
def goldbach_conjecture : Prop :=
  ∀ n : Nat, even n ∧ n > 2 → ∃ k y : Nat, n = k + y ∧ prime k ∧ prime y

def Goldbach's_weak_conjecture : Prop :=
  ∀ n : Nat, odd n ∧ n > 5 →
    ∃ k y r : Nat, n = k + y + r ∧ prime k ∧ prime y ∧ prime r

def Fermat's_last_theorem : Prop :=
  ∀ n : Nat, n > 2 → ∀ a b c : Nat, (a > 0 ∧ b > 0 ∧ c > 0) → a ^ n + b ^ n ≠ c ^ n

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
