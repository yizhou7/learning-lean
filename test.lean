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