import tactic.tidy

-- {! !} -> library search
example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
nat.mul_sub_left_distrib n m k 

lemma my_example : ∀ x : unit, x = unit.star :=
begin
   tidy
end

#print my_example

@[tidy] meta def big_bertha : tactic unit := `[finish]

lemma misc_tauto_a (p q : Prop) : (p ↔ p ∧ q) ↔ (p → q) :=
by tidy?

#print axioms misc_tauto_a

lemma misc_tauto_a' (p q : Prop) : (p ↔ p ∧ q) ↔ (p → q) :=
begin
 {! !}
end
