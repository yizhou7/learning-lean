universe u

inductive vector (α : Type u) : ℕ → Type u
| nil {} : vector 0
| cons : Π {n}, α → vector n → vector (n+1)

namespace vector

def head {α : Type} : Π {n}, vector α (n+1) → α
| n (cons x _) := x

def tail {α : Type} : Π {n}, vector α (n+1) → vector α n
| n (cons _ xs) := xs

def map {α β : Type} (f : α → β) :  Π {n}, vector α (n) → vector β (n)
| 0 nil := nil
| n (cons x xs) := cons (f x) (map xs)

def concat {α : Type} : Π {n}, vector α n → Π {m}, vector α m → vector α (n + m)
| 0 nil m ys := begin
  rw (nat.zero_add m),
  exact ys,
end
| (nat.succ n) (cons x xs) m ys :=
begin
  rw (nat.succ_add n m),
  exact (cons x (concat xs ys)),
end

def filter {α : Type} (f : α → Prop) [d : decidable_pred f] : Π {n}, vector α n → Σ {m}, vector α m
| 0 nil :=  sigma.mk 0 nil
| (nat.succ n) (cons x xs) := 
begin
  exact let p := filter xs in 
    if (f x) then (sigma.mk (p.1 + 1) (cons x p.2))
    else p,
end

end vector