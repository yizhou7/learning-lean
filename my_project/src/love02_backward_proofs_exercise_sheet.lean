import .love02_backward_proofs_demo


/-! # LoVe Exercise 2: Backward Proofs -/


set_option pp.beta true

namespace LoVe


/-! ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 2.3 in the Hitchhiker's Guide. -/

lemma I (a : Prop) :
  a → a :=
begin
  intro,
  exact a_1,
end 

lemma K (a b : Prop) :
  a → b → b :=
begin
  intros,
  exact a_2,
end

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
begin
  intros,
  apply a_1 a_3 a_2,
end

lemma proj_1st (a : Prop) :
  a → a → a :=
begin
  intros,
  apply a_1,
end

/-! Please give a different answer than for `proj_1st`: -/

lemma proj_2nd (a : Prop) :
  a → a → a :=
begin
  intros,
  apply a_2,
end

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
begin
  intros,
  apply a_1 a_2 a_4,
end
/-! 1.2. Prove the contraposition rule using basic tactics. -/

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
begin
  intros,
  apply not.intro,
  intro,
  apply a_2,
  apply a_1 a_3,
end
/-! 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap₂` in the lecture, might be
necessary. -/

lemma forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
begin
  apply iff.intro,
  {
    intro hpq,
    apply and.intro,
    {
      intros x,
      apply and.elim_left,
      apply hpq,
    },
    {
      intros x,
      apply and.elim_right,
      apply hpq,
    },
  },
  {
    intro hconj,
    intros x,
    apply and.intro,
    { apply and.elim_left hconj },
    { apply and.elim_right hconj },
  }
end

/-! ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

lemma mul_zero (n : ℕ) :
  mul 0 n = 0 :=
begin
  induction n,
  { refl },
  { simp [n_ih, mul, add] }
end

lemma mul_succ (m n : ℕ) :
  mul (nat.succ m) n = add (mul m n) n :=
begin
  induction n,
    { simp [add, add_zero, mul] },
    { simp [add, add_succ, n_ih, mul, mul_zero, add_assoc] },
end

/-! 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

lemma mul_comm (m n : ℕ) :
  mul m n = mul n m :=
begin
  induction m,
  { simp[mul_zero, mul] },
  {
    simp [mul_succ, m_ih, add, add_succ, mul, mul_zero, add_assoc, mul_add],
    cc
  },
end

/-! 2.3. Prove the symmetric variant of `mul_add` using `rewrite`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

lemma add_mul (l m n : ℕ) :
  mul (add l m) n = add (mul n l) (mul n m) :=
begin
  induction l,
  {
    simp [add_zero, mul, mul_comm], 
  },
  {
    rw mul_comm (add l_n.succ m) n,
    apply mul_add,
  },
end

lemma mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) :=
begin
  induction l,
  { simp[mul_zero, mul] },
  {
    simp [mul_succ],
    rw <- l_ih,
    rw mul_comm (mul l_n m) n,
    rw mul_comm m n,
    rw add_mul (mul l_n m),
  },
end

/-! ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def excluded_middle :=
∀a : Prop, a ∨ ¬ a

def peirce :=
∀a b : Prop, ((a → b) → a) → a

def double_negation :=
∀a : Prop, (¬¬ a) → a

/-! For the proofs below, please avoid using lemmas from Lean's `classical`
namespace, because this would defeat the purpose of the exercise.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `or.elim` and `false.elim`. You can use
`simp [excluded_middle, peirce]` to unfold the definitions of `excluded_middle`
and `peirce`. -/

lemma peirce_of_em :
  excluded_middle → peirce :=
sorry

/-! 3.2 (**optional**). Prove the following implication using tactics. -/

lemma dn_of_peirce :
  peirce → double_negation :=
sorry

/-! We leave the missing implication for the homework: -/

namespace sorry_lemmas

lemma em_of_dn :
  double_negation → excluded_middle :=
sorry

end sorry_lemmas

end LoVe
