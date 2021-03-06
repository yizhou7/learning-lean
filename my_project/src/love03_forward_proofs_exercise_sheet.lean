import .lovelib


/-! # LoVe Exercise 3: Forward Proofs -/


set_option pp.beta true

namespace LoVe


/-! ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following lemmas. -/

lemma I (a : Prop) :
  a → a :=
assume ha : a,
show a, from
  ha

lemma K (a b : Prop) :
  a → b → b :=
assume ha: a,
assume hb: b,
show b, from
  hb

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
assume habc: (a → b → c),
assume hb: b,
assume ha: a,
show c, from 
  habc ha hb

lemma proj_1st (a : Prop) :
  a → a → a :=
assume ha1,
assume ha2: a,
show a, from
  ha1

/-! Please give a different answer than for `proj_1st`. -/

lemma proj_2nd (a : Prop) :
  a → a → a :=
assume ha1: a,
assume ha2: a,
show a, from
  ha2

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
assume habc: (a → b → c),
assume ha: a,
assume hac: (a → c),
assume hb: b,
show c, from 
  habc ha hb

/-! 1.2. Supply a structured proof of the contraposition rule. -/

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
assume hab: a → b,
assume nb: ¬ b,
show ¬ a, from
begin
  apply not.intro,
  intro,
  apply nb,
  apply hab,
  apply a_1,
end

/-! 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

lemma forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
iff.intro
  (assume pq: ∀ (x : α), p x ∧ q x,
    have px : (∀x, p x) := 
      fix x: α,
      and.elim_left (pq x),
    have qx :(∀x, q x) :=
      fix x: α,
      and.elim_right (pq x),
    show (∀x, p x) ∧ (∀x, q x), from
      and.intro px qx
  )
  (assume pq: (∀x, p x) ∧ (∀x, q x),
    fix x: α,
    have px: p x := 
      and.elim_left pq x,
    have qx: q x := 
      and.elim_right pq x,
    show (p x) ∧ (q x), from
      and.intro px qx
  )
/-! 1.4. Reuse, if possible, the lemma `forall_and` you proved above to prove
the following instance of the lemma. -/

lemma forall_and_inst {α : Type} (r s : α → α → Prop) :
  (∀x, r x x ∧ s x x) ↔ (∀x, r x x) ∧ (∀x, s x x) :=
forall_and _ _

/-! ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      `(a + b) * (a + b)`
    `= a * (a + b) + b * (a + b)`
    `= a * a + a * b + b * a + b * b`
    `= a * a + a * b + a * b + b * b`
    `= a * a + 2 * a * b + b * b`

Hint: You might need the tactics `simp` and `cc` and the lemmas `mul_add`,
`add_mul`, and `two_mul`. -/

lemma binomial_square (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
calc (a + b) * (a + b)
    = a * (a + b) + b * (a + b): by rewrite add_mul
... = a * a + a * b + b * (a + b): by rewrite <- mul_add
... = a * a + a * b + (b * a + b * b): by simp [mul_add b a b]
... = a * a + (a * b + a * b) + b * b: by cc
... = a * a + 2 * (a * b) + b * b: by rewrite two_mul (a * b)
... = a * a + 2 * a * b + b * b: by cc

/-! 2.2. Prove the same argument again, this time as a structured proof. Try to
reuse as much of the above proof idea as possible. -/

lemma binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
have h1: (a + b) * (a + b) = a * (a + b) + b * (a + b), by rewrite add_mul,
have h2: a * (a + b) + b * (a + b) = a * a + a * b + b * (a + b), by rewrite <- mul_add,
have h3: a * a + a * b + b * (a + b) = a * a + a * b + (b * a + b * b), by simp [mul_add b a b],
have h4: (a + b) * (a + b) = a * a + (a * b + a * b) + b * b, by cc,
have h5: a * a + (a * b + a * b) + b * b = a * a + 2 * (a * b) + b * b, by rewrite two_mul (a * b),
show (a + b) * (a + b) = a * a + 2 * a * b + b * b, from
begin
  cc,
end

/-! 2.3. Prove the same lemma again, this time using tactics. -/

lemma binomial_square₃ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
begin
  simp [add_mul, mul_add, two_mul],
  cc
end


/-! ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom forall.one_point_wrong {α : Type} {t : α} {p : α → Prop} :
  (∀x : α, x = t ∧ p x) ↔ p t

lemma proof_of_false :
  false :=
sorry

/-! 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a tactical or structured proof. -/

axiom exists.one_point_wrong {α : Type} {t : α} {p : α → Prop} :
  (∃x : α, x = t → p x) ↔ p t

lemma proof_of_false₂ :
  false :=
sorry

end LoVe
