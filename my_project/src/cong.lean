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

example (a b c d m : ℕ) : a ≡ b [MOD m] → a * c ≡ b * c [MOD m] := 
begin
    intro h1,
    apply nat.modeq.modeq_mul h1, apply rfl,
end
