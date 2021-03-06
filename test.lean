example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
apply iff.intro,
    intro h,
    apply or.elim (and.right h),
      intro hq,
        apply or.inl,
        apply and.intro,
          apply and.left h,
          exact hq,
      intro hr,
        apply or.inr,
        apply and.intro,
          apply and.left h,
            exact hr,
    intro h,
      apply or.elim h,
        intro a,
        apply and.intro,
          apply and.elim_left a,
            apply or.intro_left,
              apply and.elim_right a,
        intro a,
          apply and.intro,
            apply and.elim_left a,
              apply or.intro_right,
              apply and.elim_right a,
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
    transitivity a,
    symmetry,
    assumption,
    assumption,
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
apply iff.intro,
  intro h,
    cases h with hp hqr,
    cases hqr with hq hr,
      left, constructor,
        assumption, assumption,
      right, constructor,
        assumption, assumption,
  intro h,
    cases h with hpq hpr,
      cases hpq with hp hq,
        constructor, assumption,
        left, assumption,
      cases hpr with hp hr,
        constructor,assumption,
        right, assumption,
end

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
  intro h,
    cases h with x px,
      constructor, left, exact px,
end

example (p q : ℕ → Prop) :
  (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
begin
  intro,
  cases a with x hx,
  cases hx,
  existsi x, constructor, assumption, assumption,
end


universes u v

def swap_pair {α : Type u} {β : Type v} : α × β → β × α :=
begin
  intro p,
  cases p,
  constructor, assumption, assumption,
end


example (x y : nat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := 
begin
  rewrite h,
end
