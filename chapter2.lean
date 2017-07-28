    -- Tao's Analysis I Chapter 2 Results

-- The aim of this project is to adhere as strictly as reasonable
-- to the textbook, sometimes even at the cost of clarity.
-- However, as a result, this project comes close to serving
-- as a fully formalized solutions manual for the textbook.

namespace chapter2

open nat
open classical

-- Predefined Lean library theorems may appear in other places,
-- but are mainly used only to prove the basic axioms.

-- Since in Lean the natural numbers are defined inductively,
-- the "Peano Axioms" will be results instead of "axioms".

local postfix `++` := succ

-- 0 is a natural number
theorem ax2_1 : ℕ := 0

-- If n is a natural number, then n++ is a natural number
theorem ax2_2 (n : ℕ) : ℕ := n++

theorem p2_1_4 : ℕ := 3
example : ℕ := ax2_2 $ ax2_2 $ ax2_2 ax2_1

-- 0 is not the succesor of any natural number
theorem ax2_3 : ∀ {n : ℕ}, n++ ≠ 0 := succ_ne_zero

theorem p2_1_6 : 4 ≠ 0 := ax2_3

theorem ax2_4 {n m : ℕ} : n++ = m++ → n = m :=
assume h : n++ = m++,
nat.no_confusion h id

theorem p2_1_8 : 6 ≠ 2 :=
not.intro (assume h : 6 = 2,
    have h₂ : 5 = 1, from ax2_4 h,
    have h₃ : 4 = 0, from ax2_4 h₂,
    show false, from p2_1_6 h₃)

-- Note that Lean has induction built into inductive datatypes
-- The "inductive" tactic will be used most frequently
theorem ax2_5 (P : ℕ → Prop) (h₀ : P 0) (ih : ∀ n, P n → P (n++)) : ∀ n, P n :=
assume n : ℕ, @nat.rec_on P n h₀ ih

theorem p2_1_16 (fₙ : ℕ → ℕ) (c : ℕ) : ℕ → ℕ
| 0     := c
| (a++) := fₙ a

-- Once all relevant properties have been proved,
-- Lean's natural numbers and "add" will be used instead
def d2_2_1 : ℕ → ℕ → ℕ
| 0     m := m
| (n++) m := (d2_2_1 n m)++
def tempadd := d2_2_1
local infix `+` := tempadd

lemma l2_2_2 : ∀ {n : ℕ}, n + 0 = n :=
begin
    intro n,
    apply nat.rec_on n,
    reflexivity,
    intro n,
    intro ih,
    exact calc
        n++ + 0 = (n+0)++ : rfl
        ...     = n++     : congr_arg nat.succ ih
end

lemma l2_2_3 : ∀ {n m}, n + (m++) = (n + m)++ :=
begin
    intros n m,
    apply nat.rec_on n,
    show 0 + (m++) = (0 + m)++, from calc
        0 + (m++) = m++       : rfl
        ...       = (0 + m)++ : rfl,
    intro n,
    intro ih,
    show (n++) + (m++) = ((n++) + m)++, from calc
        (n++) + (m++) = (n + (m++))++ : rfl
        ...           = ((n + m)++)++ : congr_arg nat.succ ih
        ...           = ((n++) + m)++ : rfl
end

-- See nat.add_comm
theorem p2_2_4 : ∀ {n m}, n + m = m + n :=
begin
    intros n m,
    apply nat.rec_on n,
    show 0 + m = m + 0, from calc
        0 + m = m     : rfl
        ...   = m + 0 : eq.symm $ l2_2_2,
    intro n,
    intro ih,
    show (n++) + m = m + (n++), from calc
        (n++) + m = (n + m)++ : rfl
        ...       = (m + n)++ : congr_arg _ ih
        ...       = m + (n++) : eq.symm $ l2_2_3
end

-- See nat.add_assoc
theorem p2_2_5 : ∀ {a b c}, (a + b) + c = a + (b + c) :=
begin
    intros a b c,
    apply nat.rec_on c,
    show (a + b) + 0 = a + (b + 0), from calc
        (a + b) + 0 = a + b       : l2_2_2
        ...         = a + (b + 0) : congr_arg _ (eq.symm l2_2_2),
    intro c,
    intro ih,
    show (a + b) + (c++) = a + (b + (c++)), from calc
        (a + b) + (c++) = ((a + b) + c)++ : l2_2_3
        ...             = (a + (b + c))++ : congr_arg _ ih
        ...             = a + ((b + c)++) : eq.symm l2_2_3
        ...             = a + (b + (c++)) : congr_arg _ (eq.symm l2_2_3)
end

theorem p2_2_6 : ∀ {a b c}, a + b = a + c → b = c :=
begin
    intros a b c,
    induction a with a ih,
    intro,
    exact calc
            b     = 0 + b : rfl
            ...   = 0 + c : by assumption
            ...   = c     : rfl,
    intro,
    have : (a + b)++ = (a + c)++, from calc
        (a + b)++ = (a++) + b : rfl
        ...       = (a++) + c : by assumption
        ...       = (a + c)++ : rfl,
    have : a + b = a + c, from ax2_4 this,
    show b = c, from ih this
end

def d2_2_7 (n : ℕ) : Prop := n ≠ 0
def pos := d2_2_7

theorem p2_2_8 : ∀ a b, pos a → pos (a + b) :=
begin
    intros a b pa,
    induction b with b ih,
    have : a + 0 = a, from l2_2_2,
    exact eq.substr this pa,
    have h : a + (b++) = (a + b)++, from l2_2_3,
    have : pos ((a + b)++), from ax2_3,
    exact eq.substr h this
end

theorem c2_2_9 : ∀ {a b}, a + b = 0 → a = 0 ∧ b = 0 :=
begin
    intros a b h,
    constructor,
    apply by_contradiction,
    intro na,
    have : pos a, from na,
    have : pos (a + b), from p2_2_8 a b this,
    exact this h,
    apply by_contradiction,
    intro nb,
    have : pos b, from nb,
    have : pos (b + a), from p2_2_8 b a this,
    have : pos (a + b), from eq.subst (@p2_2_4 b a) this,
    exact this h
end

lemma l2_2_10 : ∀ {a}, pos a → ∃! b, b++ = a :=
begin
    intros a pa,
    induction a with a ih,
    have : ¬pos 0, from not.intro 
    (assume h : 0 ≠ 0, h (@rfl ℕ 0)),
    exact false.elim (this pa),
    apply exists_unique.intro a,
    reflexivity,
    intro y,
    exact ax2_4
end

section ordering_properties

-- See ge (≥) and less_than_or_equal
-- Lean uses alternate definitions based on inductive types
-- We make use of the predefined ordering typeclass for convenience
def d2_2_11a (n m : ℕ) : Prop :=
∃ a : ℕ, n = m + a
def ge := d2_2_11a
def le (n m : ℕ) := ge m n
instance : has_le ℕ := ⟨le⟩

-- See gt (>)
def d2_2_11b (n m : ℕ) : Prop :=
(d2_2_11a n m) ∧ n ≠ m
def gt := d2_2_11b
def lt (n m : ℕ) := gt m n
instance : has_lt ℕ := ⟨lt⟩

variables {a b c : ℕ}

theorem p2_2_12a : a ≥ a :=
begin
    apply exists.intro 0,
    exact eq.symm l2_2_2
end

theorem p2_2_12b : a ≥ b ∧ b ≥ c → a ≥ c :=
begin
    intro h,
    cases h with ageb bgec,
    have ab : ∃ m, a = b + m, from ageb,
    have bc : ∃ n, b = c + n, from bgec,
    clear ageb bgec,
    change (∃ k, a = c + k),
    cases ab with m h₁,
    cases bc with n h₂,
    apply exists.intro,
    change a = c + (n + m),
    exact calc
        a   = b + m       : h₁
        ... = c + n + m   : congr_arg _ h₂
        ... = c + (n + m) : p2_2_5
end

theorem p2_2_12c : a ≥ b ∧ b ≥ a → a = b :=
begin
    intro h,
    cases h with aa bb,
    have ab : ∃ m, a = b + m, from aa,
    have ba : ∃ n, b = a + n, from bb,
    clear aa bb,
    cases ab with m h₁,
    cases ba with n h₂,
    have : a = a + (n + m), from calc
        a   = b + m       : h₁
        ... = a + n + m   : congr_arg _ h₂
        ... = a + (n + m) : p2_2_5,
    have : a + 0 = a + (n + m),
        rw l2_2_2, assumption,
    have : 0 = n + m, from p2_2_6 this,
    have : n = 0 ∧ m = 0, from c2_2_9 (eq.symm this),
    cases this with n0 m0,
    exact calc
        a   = b + m : h₁
        ... = b + 0 : by rw m0
        ... = b     : l2_2_2
end

theorem p2_2_12d : a ≥ b ↔ a + c ≥ b + c :=
begin
    constructor,
    intro,
        have ab : ∃ m, a = b + m, assumption,
        cases ab with m h,
        apply exists.intro m,
        show a + c = b + c + m, from calc
            a + c = a + c       : rfl
            ...   = b + m + c   : by rw h
            ...   = b + (m + c) : by rw p2_2_5
            ...   = b + (c + m) : by rw (@p2_2_4 c m)
            ...   = b + c + m   : by rw ← p2_2_5,
    intro,
        have acbc : ∃ m, a + c = b + c + m, assumption,
        cases acbc with m h,
        constructor,
        change a = b + m,
        have : a + c = c + (b + m),
            rw [h, (@p2_2_4 b c), p2_2_5],
        have : c + a = c + (b + m),
            rw p2_2_4, assumption,
        show a = b + m, from p2_2_6 this
end

theorem p2_2_12e : a < b ↔ a++ ≤ b :=
begin
    constructor,
    intro,
        have ab : (∃ m, b = a + m) ∧ b ≠ a, assumption,
        cases ab with em ne,
        cases em with m ba,
        have mn0 : m ≠ 0,
            assume : m = 0,
            have : b = a, rw [ba, this, l2_2_2], from
            ne this,
        have : ∃! d, d++ = m, from l2_2_10 mn0,
        cases this with d h₁,
        cases h₁ with h₂ h₃,
        constructor,
        show b = (a++) + d, from calc
            b   = a + m     : ba
            ... = a + (d++) : by rw h₂
            ... = (a + d)++ : by rw l2_2_3
            ... = (a++) + d : rfl,
    intro,
        have ab : ∃ m, b = (a++) + m, assumption,
        constructor,
        change ∃ d, b = a + d,
        cases ab with m ab,
        constructor,
        show b = a + (m++), from calc
            b = (a++) + m : ab
            ... = (a + m)++ : rfl
            ... = a + (m++) : by rw ← l2_2_3,
        cases ab with m ab,
        assume : b = a,
        have : b = a + (m++), from calc
            b = (a++) + m : ab
            ... = (a + m)++ : rfl
            ... = a + (m++) : by rw ← l2_2_3,
        have : a + (m++) = b, from eq.symm this,
        have : a + (m++) = a + 0, rw [this, ‹b = a›, l2_2_2],
        have : (m++) = 0, from p2_2_6 this,
        exact ax2_3 this
end

theorem p2_2_12f : a < b ↔ ∃ d, b = a + d ∧ pos d :=
begin
    constructor,
    intro ab,
        cases ab with ab ne,
        have ab : ∃ d, b = a + d, assumption,
        cases ab with d ab,
        constructor,
        constructor,
        exact ab,
        assume : d = 0,
        have : b = a, rw [ab, this, l2_2_2],
        contradiction,
    intro h,
        cases h with d h,
        cases h with ba pd,
        constructor,
        constructor,
        exact ba,
        assume : b = a,
        have ba : b + 0 = a + d, rw [ba, l2_2_2],
        have ba : a + d = b + 0, from eq.symm ba,
        have : a + d = a + 0, rw [ba, this],
        have : d = 0, from p2_2_6 this,
        contradiction
end

end ordering_properties

section order_trichotomy

variables {a b : ℕ}

lemma p2_2_13_l1_l1 : b++ ≠ b :=
begin
    induction b with b ih,
    exact ax2_3,
    assume : (b++)++ = b++,
    have : b++ = b, exact ax2_4 this,
    contradiction
end

lemma p2_2_13_l1 : (a < b ∨ a = b ∨ a > b) :=
begin
    induction a with a ih,
    have : 0 ≤ b,
        constructor,
        change b = 0 + b,
        reflexivity,
    apply by_cases,
        assume (eq : b = 0), right, left, exact eq.symm,
        assume (ne : b ≠ 0),
            have : 0 < b, constructor, assumption, assumption,
            left, assumption,
    cases ih with ablt ih,
        have : a++ ≤ b, from p2_2_12e.mp ablt,
        apply by_cases,
            assume (eq : b = a++), right, left, exact eq.symm,
            assume (ne : b ≠ a++),
                have : a++ < b, constructor, assumption, assumption,
                left, assumption,
    cases ih with abeq abgt,
    right, right,
        constructor,
        constructor,
            show a++ = b + (0++), rw [← abeq, l2_2_3, l2_2_2],
        rw abeq,
        exact p2_2_13_l1_l1,
    right, right,
        cases abgt with abge ne,
        cases abge with m ab,
        constructor,
        constructor,
        change a++ = b + (m++),
        rw [ab, ← l2_2_3],
        assume : a++ = b,
        rw [← @l2_2_2 b, ab, ← l2_2_3] at this,
        have : (m++) = 0, from p2_2_6 this,
        apply ax2_3,
        exact this
end

lemma p2_2_13_l2 : ¬(a = b ∧ a > b) :=
begin
    apply not.intro,
    intro h,
    cases h with eq gt,
    cases gt with ge ne,
    contradiction
end

lemma p2_2_13_l3 : ¬(a = b ∧ a < b) :=
begin
    apply not.intro,
    intro h,
    cases h with eq lt,
    cases lt with le ne,
    have : b = a, from eq.symm,
    contradiction
end

lemma p2_2_13_l4 : ¬(a > b ∧ a < b) :=
begin
    apply not.intro,
    intro h,
    cases h with gt lt,
    cases gt with ge ne,
    cases lt with le ne,
    have : a = b, from p2_2_12c ⟨ge, le⟩,
    contradiction
end

theorem p2_2_13 : (a < b ∨ a = b ∨ a > b) ∧
    ¬(a = b ∧ a > b) ∧ ¬(a = b ∧ a < b) ∧ ¬(a > b ∧ a < b) :=
⟨p2_2_13_l1, p2_2_13_l2, p2_2_13_l3, p2_2_13_l4⟩

end order_trichotomy

section strong_induction

lemma strong_ind_simp_l1 : ∀ {m n : ℕ}, m < n++ → m ≤ n :=
begin
    intros m n h,
    have : (m++) ≤ (n++), from p2_2_12e.mp h,
    cases this with k h₂,
    constructor,
    have : n++ = (m + k)++, assumption,
    show n = m + k, from ax2_4 this
end

lemma strong_ind_simp_l2 : ∀ {a b : ℕ}, a ≤ b → a < b ∨ a = b :=
begin
    intros a b ab,
    cases ab with k ab,
    apply by_cases,
    assume : k = 0,
        rw [‹k = 0›, l2_2_2] at ab,
        right, exact ab.symm,
    assume : k ≠ 0,
        left,
        apply p2_2_12f.mpr,
        constructor,
        exact ⟨ab, this⟩
end

-- A simpler example that starts at 0 instead of m₀
lemma strong_ind_simple (P : ℕ → Prop) (k : ℕ)
    (hh : ∀ n, (∀ m, m < n → P m) → P n) : P k :=
begin
    let Q : ℕ → Prop := λ n, ∀ m, m < n → P m,
    have hq : ∀ {n : ℕ}, Q n → P n, assumption,
    have qk : Q k,
        induction k with k qk,
        intros n h,
            cases h with k h,
            cases k with k h₂,
            have : 0 = n, rw ← (c2_2_9 h₂.symm).left,
            contradiction,
        intros m h,
            have : m < k ∨ m = k, from (strong_ind_simp_l2 (strong_ind_simp_l1 h)),
            cases this with ltk eqk,
            apply qk, assumption,
            subst m, apply hq, assumption,
    exact hq qk
end

theorem p2_2_14 (m₀ : ℕ) (P : ℕ → Prop) (k : ℕ)
    (hh : ∀ m, (∀ m', m₀ ≤ m' ∧ m' < m → P m') → P m)
    : ∀ k, k ≥ m₀ → P k :=
begin
    intros k h,
    let Q : ℕ → Prop := λ m, ∀ m', m₀ ≤ m' ∧ m' < m → P m',
    have hq : ∀ {n : ℕ}, Q n → P n, assumption,
    have qk : Q k,
        induction k with k qk,
        intros m hand,
            have : m < 0, from hand.right,
            cases this with h₂ ne,
            cases h₂ with c h₂,
            have : 0 = m, rw ← (c2_2_9 h₂.symm).left,
            contradiction,
        intros m hand,
            cases hand with hl hr,
            have : m < k ∨ m = k, from (strong_ind_simp_l2 (strong_ind_simp_l1 hr)),
            cases this with ltk eqk,
            apply qk,
                cases ltk with km ne,
                have km : k ≥ m, from km,
                exact p2_2_12b ⟨km, hl⟩,
                exact ⟨hl, ltk⟩,
            rw eqk, apply hq, apply qk,
            rw ← eqk, exact hl,
    exact hq qk
end

end strong_induction

theorem ex2_2_6 (n m : ℕ) (P : ℕ → Prop) (h : ∀ {m}, P (m++) → P m)
    (h₀ : P n) : m ≤ n → P m :=
begin
    intro mn,
    induction n with n ih,
    cases mn with k mk,
    rw (c2_2_9 mk.symm).left, assumption,
    have : m < n++ ∨ m = n++, from strong_ind_simp_l2 mn,
    cases this with mlt meq,
    have : m++ ≤ n++, from p2_2_12e.mp mlt,
    rw [← (@l2_2_2 m), ← (@l2_2_2 n)] at this,
    rw [← l2_2_3, ← l2_2_3] at this,
    have : m ≤ n, from p2_2_12d.mpr this,
    exact ih (h h₀) this,
    rw meq, exact h₀
end

def d2_3_1 : ℕ → ℕ → ℕ
| 0     m := 0
| (n++) m := (d2_3_1 n m) + m
def tempmul := d2_3_1
local infix `*` := tempmul

lemma l2_3_2_l1 {n : ℕ} : n * 0 = 0 :=
begin
    induction n with n ih,
    reflexivity,
    change (n * 0) + 0 = 0,
    rw l2_2_2, assumption
end

lemma l2_3_2_l2_l1 {a b c : ℕ} : b = c → a + b = a + c :=
begin
    intro h,
    induction a with a ih,
    exact h,
    change (a + b)++ = (a + c)++,
    rw ih
end

lemma l2_3_2_l2 {n m : ℕ} : n * (m++) = n * m + n :=
begin
    induction n with n ih,
    change 0 = 0 * m + 0,
    rw l2_2_2, reflexivity,
    change (n * (m++)) + (m++) = (n * m) + m + (n++),
    rw ih,
    rw p2_2_5, rw p2_2_5,
    rw l2_3_2_l2_l1,
    rw l2_2_3, rw l2_2_3,
    rw p2_2_4
end

lemma l2_3_2 {n m : ℕ} : n * m = m * n :=
begin
    induction n with n ih,
    rw l2_3_2_l1, reflexivity,
    change (n * m) + m = m * (n++),
    rw l2_3_2_l2,
    rw ih
end

lemma l2_3_3a_l1 {n m : ℕ} : (n * m) + m = 0 → m = 0 :=
begin
    intro h,
    induction m with m ih,
    reflexivity,
    rw l2_3_2_l2 at h,
    by_contradiction,
    have : (m++) = 0, from (c2_2_9 h).right,
    contradiction
end

lemma l2_3_3a {n m : ℕ} : n * m = 0 ↔ n = 0 ∨ m = 0 :=
begin
    constructor,
    intro h,
        induction n with n ih,
        left, reflexivity,
        unfold tempmul at h,
        unfold d2_3_1 at h,
        right, exact l2_3_3a_l1 h,
    intro h,
        cases h with h h,
        rw h, reflexivity,
        rw h, rw l2_3_2_l1
end

lemma l2_3_3b {n m : ℕ} : pos n ∧ pos m ↔ pos (n * m) :=
begin
    constructor,
    intro h,
        cases h with pn pm,
        assume : n * m = 0,
        have : n = 0 ∨ m = 0, from l2_3_3a.mp this,
        cases this, contradiction, contradiction,
    intro h,
        constructor,
        assume : n = 0,
            rw this at h,
            change pos 0 at h,
            exact ne.irrefl h,
        assume : m = 0,
            rw this at h,
            rw l2_3_2_l1 at h,
            exact ne.irrefl h,
end

theorem p2_3_4a {a b c : ℕ} : a * (b + c) = (a * b) + (a * c) :=
begin
    induction c with c ih,
    rw [l2_2_2, l2_3_2_l1, l2_2_2],
    rw [l2_2_3, l2_3_2_l2, ih, l2_3_2_l2, p2_2_5]
end

theorem p2_3_4b {a b c : ℕ} : (b + c) * a = (b * a) + (c * a) :=
begin
   rw [l2_3_2, @l2_3_2 b a, @l2_3_2 c a],
   exact p2_3_4a
end

theorem p2_3_5 {a b c : ℕ} : (a * b) * c = a * (b * c) :=
begin
    induction b with b ih,
    rw l2_3_2_l1,
    change 0 = a * 0,
    rw l2_3_2_l1,
    rw [l2_3_2_l2, p2_3_4b],
    change a * b * c + a * c = a * (b * c + c),
    rw p2_3_4a,
    rw ih.symm
end

theorem p2_3_6 {a b c : ℕ} : a < b → pos c → a * c < b * c :=
begin
    intros h pc,
    have, from p2_2_12f.mp h,
    cases this with d h,
    cases h with h pd,
    have : b * c = (a + d) * c, from h ▸ rfl,
    rw p2_3_4b at this,
    have pdc : pos (d * c), from l2_3_3b.mp ⟨pd, pc⟩,
    apply p2_2_12f.mpr,
    constructor, exact ⟨this, pdc⟩
end

theorem c2_3_7 {a b c : ℕ} : a * c = b * c → pos c → a = b :=
begin
    intros h pc,
    have tri : a < b ∨ a = b ∨ a > b, from p2_2_13_l1,
    cases tri with ablt tri,
        have : a * c < b * c, from p2_3_6 ablt pc,
        cases this, have h, from eq.symm h,
        contradiction,
    cases tri with abeq abgt, assumption,
        have : a * c > b * c, from p2_3_6 abgt pc,
        cases this,
        contradiction
end

theorem p2_3_9 {n q : ℕ} (pq : pos q) :
    ∃ m r, 0 ≤ r ∧ r < q ∧ n = m * q + r :=
begin
    induction n with n ih,
    repeat {constructor}, contradiction,
    rw [l2_2_2, l2_2_2], change 0 = 0 * q, reflexivity,
    cases ih with m ih,
    cases ih with r ih,
    cases ih with r₀ ih,
    cases ih with rq ih,
    have : r++ ≤ q, from p2_2_12e.mp rq,
    have : r++ < q ∨ r++ = q, from strong_ind_simp_l2 this,
    cases this with rlt req,
    existsi m, existsi (r++),
        constructor, constructor, reflexivity,
        constructor, exact rlt,
        rw [ih, l2_2_3],
    existsi (m++), existsi 0,
    constructor, constructor, reflexivity,
    constructor, constructor, constructor, reflexivity, exact pq,
    change n++ = m * q + q + 0,
    rw [ih, l2_2_2, ← l2_2_3, req]
end

def d2_3_11 : ℕ → ℕ → ℕ
| m 0     := 1
| m (n++) := (d2_3_11 m n) * m
def tempexp := d2_3_11
local infix `^` := tempexp

example {x : ℕ} : x ^ 3 = x ^ 2 * x := rfl
example {x : ℕ} : x ^ 3 = x * x * x := rfl

lemma ex2_3_4_l1 {n : ℕ} : n + n = 2 * n := rfl

theorem ex2_3_4 {a b : ℕ} : 
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
calc
    (a + b) ^ 2 = (a + b) * (a + b) : rfl
    ...         = (a + b) * a + (a + b) * b : p2_3_4a
    ...         = a * a + b * a + (a + b) * b : by rw p2_3_4b
    ...         = a * a + b * a + (a * b + b * b) : by rw p2_3_4b
    ...         = a * a + b * a + a * b + b * b : by rw ← p2_2_5
    ...         = a ^ 2 + b * a + a * b + b ^ 2 : rfl
    ...         = a ^ 2 + a * b + a * b + b ^ 2 : by rw l2_3_2
    ...         = a ^ 2 + (a * b + a * b) + b ^ 2 : by rw ← p2_2_5
    ...         = a ^ 2 + 2 * (a * b) + b ^ 2 : by rw ex2_3_4_l1
    ...         = a ^ 2 + 2 * a * b + b ^ 2 : by rw p2_3_5

end chapter2

-- We will now assume and employ theorems regarding
-- the natural numbers from Lean's standard library since
-- they are no longer the focus of any future chapters.