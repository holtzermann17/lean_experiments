import topology.basic data.set.intervals analysis.complex.exponential tactic.tidy «smt-lean»
open real set tactic

-- first part of proving that y(x)=1/(2-x) is continuous on [0,2)

def twoco_interval := (Ioo (0:ℝ) 2)

noncomputable def simple_rational := function.restrict (λ (x:ℝ), 1/(x-2)) twoco_interval

open smt.logic_fragment

lemma simple_rational_of_twoco_items_are_nonzero : ∀ (a : subtype
twoco_interval), a.val - 2 ≠ 0 := 
begin tidy,
veriT (AUFNIRA),
end
