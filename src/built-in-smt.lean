import data.real.basic

constant cos : ℝ → ℝ

@[ematch]theorem cos_values (x : ℝ) : cos x ≤ 1 ∧ cos x ≥ -1 := sorry
@[ematch]theorem abs_values (a b : ℝ) : abs a > abs b → a + b ≠ 0 := sorry

set_option trace.smt.ematch true

@[ematch]theorem cosine_shift (x: ℝ) : cos x + 2 ≠ 0 :=
by {[smt] eblast}
