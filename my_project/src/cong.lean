import data.nat.modeq -- modular arithmetic
import topology.basic

example : 5 ≡ 8 [MOD 3] := 
begin
    apply rfl,
end

#check nat.modeq.modeq_mul

example (a b c d m : ℕ) : a ≡ b [MOD m] → c ≡ d [MOD m] → a * c ≡ b * d [MOD m] := 
begin
    apply nat.modeq.modeq_mul,
end

lemma cong_mul1 (a b c d m : ℕ) : a ≡ b [MOD m] → a * c ≡ b * c [MOD m] := 
begin
    intro h1,
    apply nat.modeq.modeq_mul h1, apply rfl,
end

theorem cong_product (a b c d m : ℕ) (h1: a ≡ b * c [MOD m]) (h2: c ≡ d [MOD m]) : a ≡ b * d [MOD m] := 
begin
    have h3: b * c ≡ b * d [MOD m], from 
    begin
        apply nat.modeq.modeq_mul, apply rfl, assumption
    end,
    apply nat.modeq.trans h1 h3,
end

lemma aaa (rr R R_INV a ar aar aaa n : ℕ) :
    R * R_INV ≡ 1 [MOD n] →
    rr ≡ R * R [MOD n] →
    ar ≡ a * R_INV * rr [MOD n] →
    aar ≡ ar * ar * R_INV [MOD n] →
    aaa ≡ aar * a * R_INV [MOD n] →
    aaa ≡ a * a * a [MOD n] :=
begin
    intros h1 h2 h3 h4 h5, 
    have h: ar ≡ a * R_INV * R * R [MOD n], from
    begin
        rw [mul_assoc],
        apply cong_product ar (a * R_INV) rr (R * R) n, 
        assumption, 
        assumption, 
    end,
    
    have h: ar ≡ a * R * 1 [MOD n], from
    begin
        apply cong_product ar (a * R) (R_INV * R) 1 n, 
        rw [<- mul_assoc, mul_assoc a R, mul_comm R R_INV, <-mul_assoc],
        assumption, 
        rw [mul_comm],
        assumption, 
    end,
    sorry
end