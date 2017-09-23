namespace chapter3

open nat
open classical
open set

-- Since sets are not exactly straightforward in type theory,
-- there will be some leniency with regards to the textbook
-- in order to define them type theoretically and
-- Lean's standard library will be employed
-- to express the properties of sets.
variable {α : Type}

-- "set" will be used instead
def d3_1_1 := α → Prop

-- sets are objects
theorem ax3_1 (A : set α) (B : set (set α)) : Prop := A ∈ B

def d3_1_4 {A B : set α} : A = B ↔ (∀ x : α, x ∈ A ↔ x ∈ B) :=
begin
    constructor,
    intro h,
        intro x,
        rw h,
    intro h,
        have : ∀ x, (x ∈ A) = (x ∈ B),
            intro x,
            exact iff.to_eq (h x),
        exact funext this
end

theorem ax3_2 {A : set α} : (∀ x : α, x ∉ A) → A = ∅ :=  
begin
    assume h,
    apply iff.mpr d3_1_4,
    assume x,
    constructor,
    assume xa,
    have : x ∉ A, exact h x,
    contradiction,
    assume xe,
    exact false.elim xe
end

lemma l3_1_6 {A : set α} (h : A ≠ ∅) : ∃ x, x ∈ A :=
begin
    apply by_contradiction,
    assume nh,
    have : ∀ x, x ∉ A, from forall_not_of_not_exists nh,
    have : A = ∅, from ax3_2 this,
    contradiction
end

theorem ax3_3 {y : α} {a : α} : y ∈ ({a} : set α) ↔ y = a :=
begin
    constructor,
    assume ye,
        apply or.elim ye,
        exact id,
        assume (h : set.mem y ∅),
        exact false.elim h,
    assume ye,
        exact or.inl ye
end

end chapter3