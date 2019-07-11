universe variable u
variable {α : Type u}
variable [comm_ring α]
variable [f : α → α]
variable [p : α → Prop]

/- Our first example is solved using congruence closure, and
   theory AC. It gets solved as soon as we introduce the hypothesis -/
lemma smt1 (a b c : α) : a = b → p (a + c) → p (c + b) :=
begin [smt]
  intros
end

/- The tactic performs unit propagation without performing CNF conversion,
   and propagates equivalences between propositions. -/
lemma smt2 (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin [smt]
  intros
end

#print smt1
#print smt2
