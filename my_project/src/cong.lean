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

lemma cong_product (a b c d m : ℕ) : a ≡ c * b [MOD m] → c ≡ d [MOD m] → a ≡ d * b [MOD m] := 
begin
    intros h1 h2,
    have h3: c * b ≡ d * b [MOD m], from 
    begin
        apply nat.modeq.modeq_mul, assumption, apply rfl,
    end,
    apply nat.modeq.trans h1 h3,
end

-- lemma aaa (rr R R_INV a ar aar aaa n : ℕ) : R * R_INV ≡ 1 [MOD n] →
--     rr ≡ R * R [MOD n] →
--     ar ≡ a * rr * R_INV [MOD n] →
--     aar ≡ ar * ar * R_INV [MOD n] →
--     aaa ≡ aar * a * R_INV [MOD n] →
--     aaa ≡ a * a * a [MOD n] :=
-- begin
--     intros h1 h2 h3 h4 h5, 
--     apply show (aar ≡ ar * ar * R_INV [MOD n]),
--         begin

--         end,

-- end
