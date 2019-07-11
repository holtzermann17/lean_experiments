import topology.basic analysis.complex.exponential
import tactic.core data.list.defs
open real set

----------------------
/- Use `refine` alongside `apply` -/
namespace sin_sin
open tactic
meta def refine_list_expr : list expr → tactic unit
| []     := do {trace "fail", fail "no matching rule"}
| (h::t) := do {trace "refine, initial goals:",
                gs ← get_goals,
                mmap infer_type gs >>= trace,
                (refine ``(%%h _ _)),
                trace (format!" REFINE: {h}"),
                trace "refine, final goals:",
                gs ← get_goals,
                mmap infer_type gs >>= trace,
                pure() <|> refine_list_expr t }

meta def exact_list_expr : list expr → tactic unit
| []     := do {trace "fail", fail "no matching rule"}
| (h::t) := do {trace "exact, initial goals:",
                gs ← get_goals,
                mmap infer_type gs >>= trace,
                trace (format!" EXACT: {h}"),
                -- Some problem here at first...
                exact h,
                trace "exact, final goals:",
                gs ← get_goals,
                mmap infer_type gs >>= trace,
                pure() <|> exact_list_expr t }

meta def apply_list_expr : list expr → tactic unit
| []     := fail "no matching rule"
| (h::t) := do { trace "apply, initial goals:",
                 gs ← get_goals,
                 mmap infer_type gs >>= trace,
                 trace (format!" APPLY: {h}") ,
                 interactive.concat_tags (apply h),
                 trace "apply, final goals:",
                 gs ← get_goals,
                 mmap infer_type gs >>= trace,
                 pure() <|> apply_list_expr t }

open nat

-- these were adjusted so that I could get the counter to print out
meta def iterate_at_most_on_all_goals' : nat → tactic unit → tactic unit
| 0        tac := trace "All goals: maximal iterations reached"
| (succ n) tac := tactic.all_goals $ (do tac, trace (format!"All goals:{n}"), iterate_at_most_on_all_goals' n tac) <|> skip

meta def iterate_at_most_on_subgoals' : nat → tactic unit → tactic unit
| 0        tac := trace "Subgoals: maximal iterations reached"
| (succ n) tac := focus1 (do tac, trace (format!"Subgoals:{n}"), iterate_at_most_on_all_goals' n tac)

meta def apply_rules_with_refine (apps : list pexpr) (refs : list pexpr) (exas : list pexpr) (n : nat) : tactic unit :=
do a ← build_list_expr_for_apply apps,
   r ← build_list_expr_for_apply refs,
   e ← build_list_expr_for_apply exas,
   iterate_at_most_on_subgoals' n (assumption
                                    <|> (do t ← tactic.target,
                                          let a := expr.app_arg t,
                                          if (band (expr.is_lambda a)
                                                   (bnot (eq a `(λ (x : ℝ), x))))
                                          then refine_list_expr r
                                          else fail "can't refine")
                                    <|> (sin_sin.apply_list_expr a)),
   -- this doesn't work if run inside the loop, above, for some reason
   sin_sin.exact_list_expr e,
   pure()

end sin_sin
----------------------

namespace tactic
namespace interactive
open lean
open lean.parser
open interactive interactive.types expr

meta def apply_rules_with_refine_interactive (as : parse pexpr_list_or_texpr)
                                             (rs : parse pexpr_list_or_texpr)
                                             (es : parse pexpr_list_or_texpr)
                                             (n : nat := 50) : tactic unit :=
sin_sin.apply_rules_with_refine as rs es n

end interactive
end tactic

-- * sin(sin(x)) and friends are continuous on ℝ

open real

lemma continuous_sin_sin : continuous (λ x : ℝ, sin(sin(sin(sin(sin(sin x)))))) := 
begin
-- Chris Hughes helped me figure out that we need "@continuous_id ℝ _" rather than "continuous_id" here
apply_rules_with_refine_interactive [continuous_sin] [continuous.comp] [@continuous_id ℝ _] 7,
end

#print continuous_sin_sin
