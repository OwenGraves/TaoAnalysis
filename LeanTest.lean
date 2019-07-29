set_option pp.width 60
section
/-
variables p q : Prop
variable hp : p
example (hq : q) : p ∧ q := and.intro hp hq

variable h : p ∨ q
example : q ∨ p :=
or.elim h
(assume hp : p, or.inr hp)
(assume hq : q, or.intro_left p hq)
check @or.intro_right q p hp
check @or.elim
check @or.intro_left
check @or.intro_right
-/

variables p q : Prop
theorem contra (hpq : p → q) : ¬q → ¬p :=
λ hnq : ¬q, λ hp : p, false.elim (hnq (hpq hp))

theorem aswap : p ∧ q ↔ q ∧ p :=
iff.intro
(assume h : p ∧ q, show q ∧ p, from and.intro (and.right h) (and.left h))
(assume h : q ∧ p, show p ∧ q, from and.intro (and.right h)(and.left h))

theorem aaswap : ∀ {p q : Prop}, p ∧ q ↔ q ∧ p :=
λ p q : Prop,
iff.intro
(λ h : p ∧ q, and.intro (and.right h) (and.left h))
(λ h : q ∧ p, and.intro (and.right h) (and.left h))

variables x y : Prop
variable z : y ∧ x
lemma a : x ∧ y := iff.mp (aaswap) z

lemma b : x ∧ y := and.intro
(and.right z)
(and.left z)

lemma c : x ∧ y := 
(λ (hx : x),
(λ (hy : y),
and.intro hx hy) (and.left z)) (and.right z)

lemma havelist : x ∧ y :=
have hx : x, from and.right z,
have hy : y, from and.left z,
show x ∧ y, from and.intro hx hy

lemma suff : x ∧ y :=
have hx : x, from and.right z,
suffices hy : y, from and.intro hx hy,
show y, from and.left z


open classical
theorem dner {p : Prop} : p → ¬¬p :=
assume hp : p,
    not.intro (assume np : ¬p, np hp)

theorem dne {p : Prop} : ¬¬p → p :=
--λ h : ¬¬p,
assume h : ¬¬p,
show p, from or.elim (em p)
(λ hp : p, hp)
(λ hnp : ¬p, absurd hnp h)

example (h : ¬¬p) : p :=
by_contradiction (assume h1: ¬p, show false, from h h1)

lemma demorg (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
--or.elim (em p)
by_cases
(assume hp : p, or.inr (show ¬q, from assume hq : q, h ⟨hp, hq⟩))
(assume hp : ¬p, or.inl hp)

end

section propositional_validities --Proofs of lots of propositions

variables p q r s : Prop

--commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
iff.intro
(assume x : p ∧ q,
show q ∧ p, from and.intro (and.right x) (and.left x))
(assume y : q ∧ p,
show p ∧ q, from and.intro (and.right y) (and.left y))
--cleaner(?) version
example : p ∧ q ↔ q ∧ p :=
have for : p ∧ q → q ∧ p, from (assume x : p ∧ q,
    have z : q, from and.right x,
    have c : p, from and.left x,
    and.intro z c),
have bac : q ∧ p → p ∧ q, from (assume y : q ∧ p, and.intro (and.right y) (and.left y)),
iff.intro for bac

example : p ∨ q ↔ q ∨ p :=
iff.intro
(assume x : p ∨ q,
show q ∨ p, from or.elim x
(assume hp : p, or.inr hp) (assume hq : q, or.inl hq))
(assume y : q ∨ p,
show p ∨ q, from or.elim y
(assume hq : q, or.inr hq) (assume hp : p, or.inl hp))
--associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
iff.intro
(assume x : (p ∧ q) ∧ r,
show p ∧ (q ∧ r), from and.intro (and.left (and.left x))
(and.intro (and.right (and.left x))
(and.right x)))
(assume y : p ∧ (q ∧ r),
show (p ∧ q) ∧ r, from and.intro (and.intro
(and.left y) (and.left (and.right y)))
(and.right (and.right y)))

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
have forward : (p ∨ q) ∨ r → p ∨ (q ∨ r), from (
assume x : (p ∨ q) ∨ r, show p ∨ (q ∨ r), from 
or.elim x (assume hpq : p ∨ q,
or.elim hpq (assume hp : p, or.inl hp)
(assume hq : q, or.inr (or.inl hq)))
(assume hr : r, or.inr (or.inr hr))),
have backward : p ∨ (q ∨ r) → (p ∨ q) ∨ r, from (
assume x : p ∨ (q ∨ r), show (p ∨ q) ∨ r, from
or.elim x (assume hp : p, or.inl (or.inl hp))
(assume hqr : q ∨ r, or.elim hqr
(assume hq : q, or.inl (or.inr hq))
(assume hr : r, or.inr hr))),
iff.intro forward backward
--distributivity of ∧ and ∨
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
iff.intro
    (assume h : p ∧ (q ∨ r),
        have hp : p, from h^.left,
        have hqr : q ∨ r, from h^.right,
        or.elim hqr
            (assume hq : q, or.inl ⟨hp,hq⟩)
            (assume hr : r, or.inr ⟨hp,hr⟩))
    (assume h : (p ∧ q) ∨ (p ∧ r),
        have hp : p, from
            or.elim h
                (assume hpq : p ∧ q, hpq^.left)
                (assume hpr : p ∧ r, hpr^.left),
        have hqr : q ∨ r, from
            or.elim h
                (assume hpq : p ∧ q, or.inl hpq^.right)
                (assume hpr : p ∧ r, or.inr hpr^.right),
        ⟨hp,hqr⟩)

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
iff.intro
    (assume h : p ∨ (q ∧ r),
        or.elim h
            (assume hp : p, ⟨or.inl hp,or.inl hp⟩)
            (assume hqr : q ∧ r, ⟨or.inr hqr^.left, or.inr hqr^.right⟩))
    (assume h : (p ∨ q) ∧ (p ∨ r),
        have hpq : p ∨ q, from h^.left,
        have hpr : p ∨ r, from h^.right,
         or.elim hpq
            (assume hp : p, or.inl hp)
            (assume hq : q,
                or.elim hpr
                    (assume hp : p, or.inl hp)
                    (assume hr : r, or.inr ⟨hq, hr⟩)
            )
    )
--other propositional proofs (non-classical)
example : (p → (q → r)) ↔ (p ∧ q → r) :=
iff.intro
    (assume h : p → (q → r),
        assume hpq : p ∧ q,
            h hpq^.left hpq^.right)
    (assume h : p ∧ q → r,
        assume hp : p,
            assume hq : q,
                h ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
iff.intro
    (assume h : (p ∨ q) → r,
        have hpr : p → r, from
            assume hp : p,
                h (or.inl hp),
        have hqr : q → r, from
            assume hq : q,
                h (or.inr hq),
        ⟨hpr, hqr⟩)
    (assume h : (p → r) ∧ (q → r),
        have hpr : p → r, from h^.left,
        have hqr : q → r, from h^.right,
        assume hpq : p ∨ q,
            show r, from or.elim hpq
                (assume hp : p, hpr hp)
                (assume hq : q, hqr hq))

lemma lem₁ {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
iff.intro
    (assume h : ¬(p ∨ q),
        have np : ¬p, from
            not.intro (show p → false, from (assume hp : p, h (or.inl hp))),
        have nq : ¬q, from
            not.intro (assume hq : q, h (or.inr hq)),
        ⟨np, nq⟩)
    (assume h : ¬p ∧ ¬q,
        show ¬(p ∨ q), from
            not.intro (assume hpq : p ∨ q, or.elim hpq
            (assume hp : p, h^.left hp)
            (assume hq : q, h^.right hq)))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
assume h : ¬p ∨ ¬q,
    or.elim h
        (assume np : ¬p, not.intro (assume hpq : p ∧ q, np hpq^.left))
        (assume nq : ¬q, not.intro (assume hpq : p ∧ q, nq hpq^.right))

example : ¬(p ∧ ¬p) :=
not.intro (assume h : p ∧ ¬p, h^.right h^.left)

example : p ∧ ¬q → ¬(p → q) :=
assume h : p ∧ ¬q,
    not.intro (assume hpq : p → q, h^.right (hpq h^.left))

example : ¬p → (p → q) :=
assume np : ¬p,
    assume hp : p,
        false.elim (np hp)

lemma lem₄ {p q : Prop} : (¬p ∨ q) → (p → q) :=
assume h : ¬p ∨ q,
    assume hp : p,
        or.elim h
            (assume np : ¬p, false.elim (np hp))
            (assume hq : q, hq)

example : p ∨ false ↔ p :=
iff.intro
    (assume h : p ∨ false, or.elim h
        (assume hp : p, hp)
        (assume fal, false.elim fal))
    (assume h : p, or.inl h)

example : p ∧ false ↔ false :=
iff.intro
    (assume h : p ∧ false, h^.right)
    (assume h : false, false.elim h)

example : ¬(p ↔ ¬p) :=
not.intro
    (assume h : p ↔ ¬p,
        have np : ¬p, from not.intro
            (assume hp : p,
                ((iff.elim_left h hp) hp)),
        (np (iff.elim_right h np)))

example : ¬(p ↔ ¬p) := --fully lambda???
not.intro (λ h : p ↔ ¬p, ((not.intro (λ hp : p, ((iff.elim_left h hp) hp))) (iff.elim_right h (not.intro (λ hp : p, ((iff.elim_left h hp) hp))))))

example : (p → q) → (¬q → ¬p) :=
assume h : p → q,
    assume nq : ¬q,
        not.intro
            (assume hp : p, nq (h hp))
--propositions that rely on classical logic
open classical

lemma lem₃ {p q : Prop} : ¬(p ∧ q) → ¬p ∨ ¬q :=
assume h : ¬(p ∧ q),
    or.elim (em (¬p ∨ ¬q))
        (assume h₁ : ¬p ∨ ¬q, h₁)
        (assume h₂ : ¬(¬p ∨ ¬q),
            have nnpq : (¬¬p ∧ ¬¬q),
                from iff.elim_left (@lem₁ (¬p) (¬q)) h₂,
            have hp : p, from dne nnpq^.left,
            have hq : q, from dne nnpq^.right,
            absurd (and.intro hp hq) h)

lemma lem₂ {p q : Prop} : ¬(p → q) → p ∧ ¬q :=
assume h : ¬(p → q),
    by_contradiction (assume h₂ : ¬(p ∧ ¬q),
        have nnpq : ¬p ∨ ¬¬q, from lem₃ h₂,
        have npq : ¬p ∨ q, from or.elim nnpq (assume np : ¬p, or.inl np) (assume nnq : ¬¬q, or.inr (dne nnq)),
        h (lem₄ npq))


example : (p → r ∨ s) → (p → r) ∨ (p → s) :=
assume h : p → r ∨ s,
    by_contradiction (assume h₂ : ¬((p → r) ∨ (p → s)),
        have h₃ : ¬(p → r) ∧ ¬(p → s), from iff.elim_left lem₁ h₂,
        have npr : ¬(p → r), from h₃^.left,
        have nps : ¬(p → s), from h₃^.right,
        have pnr : p ∧ ¬r, from lem₂ npr,
        have pns : p ∧ ¬s, from lem₂ nps,
        have hp : p, from pnr^.left,
        have nr : ¬r, from pnr^.right,
        have ns : ¬s, from pns^.right,
        or.elim (h hp)
            (assume hr : r, nr hr)
            (assume hs : s, ns hs)
    )

example : ¬(p ∧ q) → ¬p ∨ ¬q := --same as lem₃
assume h : ¬(p ∧ q),
    by_contradiction (assume h₂ : ¬(¬p ∨ ¬q),
        have nnpq : (¬¬p ∧ ¬¬q), from iff.elim_left (@lem₁ (¬p) (¬q)) h₂,
        h ⟨dne nnpq^.left, dne nnpq^.right⟩)

example : (p → q) → (¬p ∨ q) :=
assume h : p → q,
    or.elim (em (¬p ∨ q))
        (assume npq : ¬p ∨ q, npq)
        (assume nnpq : ¬(¬p ∨ q),
            have nh : ¬¬p ∧ ¬q, from (iff.elim_left lem₁) nnpq,
            have hp : p, from dne nh^.left,
            have hq : q, from h hp,
            or.inr hq)

example : (¬q → ¬p) → (p → q) :=
assume h : ¬q → ¬p,
    assume hp : p,
        or.elim (em q)
            (assume hq : q, hq)
            (assume nq : ¬q,
                have np : ¬p, from h nq,
                absurd hp np)

example : p ∨ ¬p := em p

lemma lem₆ : (((p → q) → p) → p) :=
assume h : (p → q) → p,
    show p, from or.elim (em (p → q))
        (assume h₂ : p → q, h h₂)
        (assume h₃ : ¬(p → q),
            have h₄ : p ∧ ¬q, from lem₂ h₃,
            h₄^.left)

end propositional_validities

section
open classical
lemma iffcontradiction {p : Prop} (h : p ↔ ¬p) : false :=
have h₁ : p → ¬p, from iff.elim_left h,
have h₂ : ¬p → p, from iff.elim_right h,
by_cases
    (assume h₃ : p, (h₁ h₃) h₃)
    (assume h₄ : ¬p, h₄ (h₂ h₄))
end

section

variables (α : Type) (p q : α → Prop)

example : (∀ x : α, p x ∧ q x) → ∀ z : α, p z :=
assume h : ∀ x : α, p x ∧ q x,
    take y : α,
        show p y, from (h y)^.left

    section
    variable (r : α → α → Prop)
    variable transr : ∀ {x y z}, r x y → r y z → r x z
    variable reflr : ∀ x, r x x
    variable symmr : ∀ {x y}, r x y → r y x

    lemma a1short (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
    transr (transr hab (symmr hcb)) hcd

    lemma a1full
    : Π α : Type, Π r : α → α → Prop, Π transr : Π {x y z}, r x y → r y z → r x z, Π symmr : Π x y, r x y → r y x, Π a b c d : α, r a b → r c b → r c d → r a d :=
    λ α : Type, λ r : α → α → Prop, λ transr : Π {x y z}, r x y → r y z → r x z, λ symmr : Π x y, r x y → r y x, λ a b c d : α, λ hab : r a b, λ hcb : r c b, λ (hcd : r c d), (transr (transr hab (symmr c b hcb)) hcd)
    end
--variables (α : Type) (p q : α → Prop) is above

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
    (assume h : ∀ x, p x ∧ q x,
        and.intro 
            (take z : α, show p z, from (h z)^.left)
            (take z : α, show q z, from (h z)^.right))
    (assume h : (∀ x, p x) ∧ (∀ x, q x),
        take z : α,
            show p z ∧ q z, from ⟨h^.left z, h^.right z⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
assume h : ∀ x, p x → q x,
    assume h₂ : ∀ x, p x,
        take z,
            show q z, from (h z) (h₂ z)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
assume h : (∀ x, p x) ∨ (∀ x, q x),
    take x : α,
        or.elim h
            (assume h₂ : ∀ x, p x,
                or.inl (h₂ x))
            (assume h₃ : ∀ x, q x,
                or.inr (h₃ x))

    section
    variable r : Prop
    open classical
    example : α → ((∀ x : α, r) ↔ r) :=
    assume h : α,
        iff.intro
            (assume h₂ : ∀ x : α, r,
                h₂ h)
            (assume hr : r,
                take x : α, hr)

    example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    iff.intro
        (assume h : ∀ x, p x ∨ r, by_contradiction
        (assume h₃ : ¬((∀ x, p x) ∨ r),
            have h₄ : ¬(∀ x, p x) ∧ ¬r, from (iff.elim_left lem₁) h₃,
            have hapx : ∀ x, p x, from
                take x : α, or.elim (h x)
                    (assume hpx : p x, hpx)
                    (assume hr : r, absurd hr h₄^.right),
            h₄^.left hapx))
        (assume h : (∀ x, p x) ∨ r,
            or.elim h
                (assume hpx : ∀ x, p x,
                    take x : α,
                        or.inl (hpx x))
                (assume hr : r,
                    take x : α,
                        or.inr hr))

    example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    iff.intro
        (assume h : ∀ x, r → p x,
            assume hr : r,
                take x : α,
                    h x hr)
        (assume h : r → ∀ x, p x,
            take x : α,
                assume hr : r,
                    h hr x)
    end
     
    section
    open classical
    variables (men : Type) (barber : men) (shaves : men → men → Prop)

    example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
    iffcontradiction (h barber)
    end

end

section

example : 2 + 3 = 5 := rfl

example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
@exists.intro ℕ (λ y, y < x) 0 (h)

example (x : ℕ) (h : 0 < x) : @Exists (ℕ) (λ y, y < x) :=
exists.intro 0 h
section
variables (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
@exists.elim α (λ x : α, p x ∧ q x) (∃ x, q x ∧ p x) h
(take w : α,
assume hw : (λ x : α, p x ∧ q x) w,
show ∃ x, q x ∧ p x, from @exists.intro α (λ x : α, q x ∧ p x) w ⟨hw^.right, hw^.left⟩)--⟨w, hw^.right, hw^.left⟩)
end
section
def is_even (a : ℕ) := ∃ b, a = 2 * b
/-
is_even : ℕ → Prop
exists.elim : ∀ (α : Type) (p : α → Prop) (b : Prop), (∃ (x : α), p x)
exists.elim : ∀ (α : ℕ) (p : ℕ → Prop) (b : Prop), (∃ (x : ℕ), p x)
exists.elim : ∀ (α : ℕ) (p : ℕ → Prop) (b : Prop), (∃ (x : ℕ), (p x) : Prop)
a : nat
h1 : is_even a = Prop
is_even a = ∃ b, eq a (2 * b)
is_even = ∃ b, a = 2*b
-/
theorem even_plus_even {a b : ℕ} (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
@exists.elim ℕ (λ b : ℕ, a = 2 * b) (is_even (a + b)) h1 (take w1, assume hw1 : a = 2 * w1,
exists.elim h2 (take w2, assume hw2 : b = 2 * w2,
    @exists.intro ℕ (λ (b_1 : ℕ), a + b = 2 * b_1) (w1 + w2)
        (calc
            a + b = 2 * w1 + 2 * w2 : by rw [hw1, hw2]
              ... = 2 * (w1 + w2)   : by rw mul_add)))
end

section

section
open classical

theorem contrapositive {p q : Prop} : p → q ↔ ¬q → ¬p :=
iff.intro
    (assume h : p → q,
        assume nq : ¬q,
            by_contradiction (assume nnp : ¬¬p,
                nq $ h $ dne nnp))
    (assume h : ¬q → ¬p,
        assume hp : p,
            by_contradiction (assume nq : ¬q,
                h nq hp))

end

open classical
variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

example : (∃ x : α, r) → r :=
assume h : (∃ x : α, r),
    @exists.elim α (λ x : α, r) r h
        (take a : α,
            assume r,
                r)

example : (∃ x : α, r) → r :=
assume h : (∃ x : α, r),
    match h with ⟨(a : α), (x : (λ y, r) a)⟩ :=
        x
    end

lemma existstests₂ : r → (∃ x : α, r) :=
assume hr : r,
    ⟨a, hr⟩
set_option pp.implicit true
--check @exists.intro
--print existstests₂

example : r → (∃ x : α, r) :=
λ (hr : r), @Exists.intro α (λ (x : α), r) a hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
iff.intro
    (assume h : ∃ x, p x ∧ r,
        match h with ⟨(x : α), (hp : p x ∧ r)⟩ :=
            ⟨⟨x, hp^.left⟩, hp^.right⟩
        end)
    (assume h : (∃ x, p x) ∧ r,
        have hr : r, from h^.right,
        have hp : ∃ x, p x, from h^.left,
        match hp with ⟨(x : α), (hhp : p x)⟩ :=
            ⟨x, hhp, hr⟩
        end)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
iff.intro
    (assume h : ∃ x, p x ∨ q x,
        match h with ⟨(x : α), (hpq : p x ∨ q x)⟩ :=
            or.elim hpq
                (assume hpx : p x,
                    or.inl ⟨x, hpx⟩)
                (assume hqx : q x,
                    or.inr ⟨x, hqx⟩)
        end)
    (assume h : (∃ x, p x) ∨ (∃ x, q x),
        or.elim h
            (assume epx : ∃ x, p x,
                match epx with ⟨x, (hp : p x)⟩ :=
                    ⟨x, or.inl hp⟩
                end)
            (assume eqx : ∃ x, q x,
                match eqx with ⟨x, (hq : q x)⟩ :=
                    ⟨x, or.inr hq⟩
                end))

lemma leme₁ {α : Type} {p : α → Prop} : (∀ x, p x) ↔ ¬(∃ x, ¬p x) :=
iff.intro
    (assume h : ∀ x, p x,
        not.intro (assume h₂ : ∃ x, ¬p x,
            match h₂ with ⟨(t : α), (np : ¬p t)⟩ :=
                np (h t)
            end))
    (assume h : ¬(∃ x, ¬p x),
        take x,
            by_contradiction
                (assume np : ¬p x,
                    h ⟨x, np⟩))

lemma leme₂ {α : Type} {p : α → Prop} : (¬∃ x, p x) → (∀ x, ¬p x) :=
assume h : ¬∃ x, p x,
    take x,
        (assume hpx : p x,
            false.elim $ h ⟨x, hpx⟩)

lemma leme₃ {α : Type} {p : α → Prop} : (∃ x, p x) ↔ ¬(∀ x, ¬p x) :=
iff.intro
    (assume h : ∃ x, p x,
        not.intro (assume n : ∀ x, ¬p x,
            match h with ⟨x, hp⟩ :=
                n x hp
            end))
    (assume h : ¬(∀ x, ¬p x),
        by_contradiction
            (assume h₂ : ¬∃ x, p x,
                false.elim $ h $ leme₂ h₂))

lemma leme₄ : (∀ x, ¬p x) → (¬∃ x, p x) :=
assume h : ∀ x, ¬p x,
    by_contradiction
        (assume h₂ : ¬¬∃ x, p x,
            false.elim $ leme₃^.elim_left (dne h₂) h) 

example : (¬∀ x, p x) ↔ (∃ x, ¬p x) :=
iff.intro
    (assume h : ¬∀ x, p x,
        by_contradiction (assume hn : ¬∃ x, ¬p x,
            h $ leme₁^.elim_right hn))
    (assume h : ∃ x, ¬p x,
        by_contradiction (assume hn : ¬¬∀ x, p x,
            leme₁^.elim_left (dne hn) h))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
iff.intro
    (assume h : ∀ x, p x → r,
        assume h₂ : ∃ x, p x,
            match h₂ with ⟨x, hpx⟩ :=
                h x hpx
            end)
    (assume h : (∃ x, p x) → r,
        take x,
            assume h₂ : p x,
                h (show ∃ x, p x, from
                    ⟨x, h₂⟩))

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
iff.intro
    (assume h : ∃ x, p x → r,
        assume h₂ : ∀ x, p x,
            match h with ⟨a, h₃⟩ :=
                h₃ $ h₂ a
            end)
    (assume h : (∀ x, p x) → r,
        by_cases
            (assume hap : ∀ x, p x,
                ⟨a, take hpx : p a, h hap⟩)
            (assume hnap : ¬∀ x, p x,
                by_contradiction (assume h₂ : ¬∃ x, p x → r,
                    have hap : ∀ x, p x, from
                        take x, by_contradiction (assume hnp : ¬p x,
                            have hex : ∃ x, p x → r, from
                                ⟨x, (assume hp, absurd hp hnp)⟩,
                            h₂ hex),
                    hnap hap)))

example : (∃ x, r → p x) → (r → ∃ x, p x) := --TODO converse
--iff.intro
    (assume h : ∃ x, r → p x,
        assume hr : r,
            match h with ⟨y, hy⟩ :=
                ⟨y, hy hr⟩
            end)
    /-
    (assume h : r → ∃ x, p x,
        by_cases
            (assume h₂ : p a,
                ⟨a, (assume hr : r, h₂)⟩)
            (assume h₃ : ¬p a,
                by_contradiction (assume h₄ : ¬(∃ x, r → p x),
                    by_contradiction (assume hnnr : ¬¬r,
                        have hr : r, from dne hnnr,
                        have hexp : ∃ x, p x, from h hr,
                        _
                    )
                    have h₅ : ∃ x, r → p x, from
                        ⟨a, (assume hr : r, absurd hr nr)⟩,
                    h₄ h₅))
    -/

end

--check and.intro
theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
/-begin
    apply and.intro,
    exact hp,
    apply and.intro,
    exact hq,
    exact hp
end
-/
by apply and.intro hp (and.intro hq hp)

variables x y z w : ℕ
example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
begin
    apply eq.trans,
    assumption,
    apply eq.trans,
    assumption,
    assumption
end

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
begin
    apply eq.trans _ h₃,
    apply eq.trans _ h₂,
    assumption
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
    intros,
    apply eq.trans,
    apply eq.symm,
    assumption,
    assumption
end

example : x + y + z = x + y + z :=
begin
    generalize (x + y + z) w, -- goal is x y z : N ⊢ ∀ (w : N), w = w
    clear x y z,
    intro u, -- goal is x y z u : N ⊢ u = u
    reflexivity
end

example (x : ℕ) : x = x :=
begin
    revert x, -- goal is ⊢ ∀ (x : N), x = x
    intro y, -- goal is y : N ⊢ y = y
    reflexivity
end

example (x y : ℕ) (h : x = y) : y = x :=
    begin
    revert h, -- goal is x y : N ⊢ x = y → y = x
    intro h₁, -- goal is x y : N, h 1 : x = y ⊢ y = x
    symmetry,
    assumption
end

example (p q : Prop) : p ∨ q → q ∨ p :=
begin
    intro h,
    cases h with hp hq,
    -- case hp : p
    right, exact hp,
    -- case hq : q
    left, exact hq
end

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
    revert p q,
    intros p q h,
    cases h with x px,
    existsi x, left, exact px
end

section
open nat
example (P : ℕ → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : ℕ) : P m :=
begin
    cases m with m', exact h₀, exact h₁ m'
end
end

example : ∃ x : ℕ, x + 3 = 8 :=
begin
    pose x := 5,
    existsi 5,
    clear x,
    reflexivity
end

example (a b : ℕ) (h : a = b) : a + 0 = b + 0 :=
begin
    change a = b, --since a + 0 is defined to be a
    assumption
end

section
variables (f : ℕ → ℕ) (k : ℕ)
example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
begin
    rw h₂, -- replace k with 0
    rw h₁  -- replace f 0 with 0
end
end

example (a b c : ℕ) : a + b + c = a + c + b :=
begin
    rw [add_assoc, add_comm b, -add_assoc]
end

example (a b c : ℕ) : a + b + c = a + c + b :=
begin
    rw [add_assoc, add_assoc, add_comm b]
end

example (a b c : ℕ) : a + b + c = a + c + b :=
begin
    rw [add_assoc, add_assoc, add_comm _ b]
end

section
variables (f : ℕ → ℕ) (a : ℕ)
example (h : a + 0 = 0) : f a = f 0 :=
begin
    rw add_zero at h, rw h
end
end

end

namespace nat
def addy (m n : nat) : nat :=
nat.rec_on n m (λ n addy_m_n, succ addy_m_n)

--eval addy (succ zero) (succ (succ zero))
--set_option pp.implicit true

end nat

namespace testin
inductive es
| zero : es
| succ : es → es
| succi : es → (es → es)
| succ₂ : es → es → es

end testin

namespace inductivetypes

inductive weekday : Type
| sunday : ℕ → weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

def daynumber (d : weekday) : ℕ :=
weekday.rec_on d (λ (x : ℕ), 4 * x) 10 15 20 25 30 35

--check weekday.rec_on
--check daynumber
--check weekday.induction_on
--eval daynumber (weekday.sunday 3)

inductive bol : Type
| tt : bol
| ff : bol

open bol

def bnot (b : bol) : bol :=
bol.rec_on b ff tt

def bor (b₁ b₂ : bol) : bol :=
bol.rec_on b₁ tt (bol.rec_on b₂ tt ff) 

def band (b₁ b₂ : bol) : bol :=
bol.rec_on b₁ (bol.rec_on b₂ tt ff) ff

example : bnot tt = ff := rfl
example : bnot ff = tt := rfl
example : bnot (bnot tt) = tt := rfl
example (b : bol) : bnot (bnot b) = b :=
bol.rec_on b
    (show bnot (bnot tt) = tt, from rfl)
    (show bnot (bnot ff) = ff, from rfl)
example (b₁ b₂ : bol) : bor b₁ b₂ = bor b₂ b₁ :=
bol.rec_on b₁
    (bol.rec_on b₂ rfl rfl)
    (bol.rec_on b₂ rfl rfl)
example (b₁ b₂ : bol) : bor b₁ b₂ = bnot (band (bnot b₁) (bnot b₂)) :=
bol.rec_on b₁
    (bol.rec_on b₂ rfl rfl)
    (bol.rec_on b₂ rfl rfl)
section universevariables

universe variables u v
inductive pro (α : Type u) (β : Type v)
| mk : α → β → pro
inductive su (α : Type u) (β : Type v)
| il {} : α → su
| ir {} : β → su
open pro su

def fst {α : Type u} {β : Type v} (p : pro α β) : α :=
pro.rec_on p (λ a b, a)
def snd {α : Type u} {β : Type v} (p : pro α β) : β :=
pro.rec_on p (λ a b, b)

def funky₁ (s : su ℕ ℕ) : ℕ :=
su.rec_on s (λ x, x + 12) (λ x, x * 7)

--eval funky₁ $ su.ir 3

inductive maybe (α : Type u)
| nothing {} : maybe
| just       : α → maybe

--check maybe.rec_on

def bolmaybefun (m : maybe bol) : bol :=
maybe.rec_on m (bol.ff) (λ b, b)

--eval bolmaybefun $ maybe.just ff

def maybeffun (f : ℕ) : maybe ℕ :=
cond (f < 5) (maybe.nothing) (maybe.just (f*f))
--check maybeffun

inductive inhab (α : Type u)
| mk : α → inhab

def partialsub (a : ℕ) (b : ℕ) : maybe ℕ :=
cond (a < b) (maybe.nothing) (maybe.just (a-b))

--def partialcomp {α β γ : Type u} (f : maybe (α → β)) (g : maybe (β → γ)) : maybe (α → γ) :=
lemma inhabnat : inhab ℕ :=
inhab.mk 0

lemma inhabbol : inhab bol :=
inhab.mk bol.tt

lemma inhabprod (α : Type u) (β : Type v) (a : inhab α) (b : inhab β) : inhab (α × β) :=
inhab.mk (prod.mk (inhab.rec_on a (λ a₂, a₂)) (inhab.rec_on b (λ b₂, b₂)))

inductive pfalse : Prop

inductive ptrue : Prop
| intro : ptrue

inductive pand (a b : Prop) : Prop
| intro : a → b → pand

inductive por (a b : Prop) : Prop
| inl {} : a → por
| inr {} : b → por

inductive pexists {α : Type u} (p : α → Prop) : Prop
| intro : ∀ (a : α), p a → pexists

/-
check @pand.rec_on
check @por.rec_on
check @pexists.rec_on
check @nat.rec_on
-/

end universevariables

end inductivetypes

namespace inductivetactics

open nat
variable p : ℕ → Prop

example (hz : p 0) (hs : ∀ n, p (succ n)) : ∀ n, p n :=
begin
    intro n,
    cases n,
    exact hz,
    apply hs
end

def f (n : ℕ) : ℕ :=
begin
    cases n, exact 3, exact 7
end

/-
check list.rec

variable α : Type
def appendy (s t : list α) : list α :=
list.rec t (λ x l u, x::u) s
print appendy
-/

def is_not_zero (a : nat) : bool :=
match a with
| 0 := ff
| (n+1) := tt
end

universe variable u
class has_add (α : Type u) :=
(add : α → α → α)

def add {α : Type u} [has_add α] : α → α → α := has_add.add

instance nat_has_add : has_add nat :=
--⟨nat.add⟩
has_add.mk nat.add --should be equivalent

end inductivetactics

/-
definition compA : Π p q r : Prop, (q → r) → (p → q) → p → r :=
λ p, λ q, λ r, λ h1, λ h2, λ h3, h1 (h2 h3)
variables p q r s : Prop
theorem comp (h1 : q → r) (h2 : p → q) (h3 : p): r := h1 (h2 h3)
theorem com3 (h1 : q → r) (h2 : p → q) : p → r :=
λ h3 : p, h1 (h2 h3)
theorem com2 : (q → r) → (p → q) → p → r :=
λ h1, λ h2, λ h3, h1 (h2 h3)
variable h1 : q → r
variable h2 : p → q
variable h3 : p
theorem compy : r := h1 (h2 h3)

check compA
check comp
check compy
-/

/-
universe variable u
def ident (α : Type u) (x : α) := x
def ident' := λ α : Type u, λ x : α, x
def identy {α : Type u} (x : α) := x

check ident
check ident'

variable β : Type
variable b : β
check identy b
check @identy β b

section
variables p q : Prop
theorem t1 : p → q → p := λ hp : p, λ hq : q, hp
end
--theorem t1 := λ p : Prop, λ q : Prop, λ hp : p, λ hq : q, hp
theorem t1' (p q : Prop) (hp : p) (hq : q) : p := hp
theorem t₁ (p q : Prop) : p → q → p := λ hp, λ hq, hp
theorem t₁' (p q : Prop) (hp : p) : q → p := λ hq, hp
theorem t₂ : Π p : Prop, Π q : Prop, p → q → p := λ p : Prop, λ q : Prop, λ hp, λ hq, hp
theorem t₃ : Π p q : Prop, p → q → p := λ p : Prop, λ q : Prop, λ hp, λ hq, hp
--theorem t1₁ (p q : Prop) (hp : p) (hq : q) : p := hp
check t1
check t1'
check t₁'
check t₁
check t₂
-/
