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