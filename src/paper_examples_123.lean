import topology.basic data.set.intervals analysis.exponential
open real set

-- * Example 1: y(x)=1/(2-x) is continuous on [0,2)

-- This test involves a small amount of arithmetic composition; it
-- should be slightly harder than my super-basic running examples of
-- x and 1/x.  I'll have to understand the mechanics of mathlib
-- style proofs better.

-- As a general reflection on how this work relates to F Abstracts, I'll note that 'sorry'
-- is a pretty handy tool for looking around the corner to see what's coming, or for 
-- making a theory
def twoco_interval := (Ico (0:ℝ) 2)

noncomputable def simple_rational := function.restrict (λ (x:ℝ), 1/(x-2)) twoco_interval

lemma simple_rational_of_twoco_items_are_nonzero :  ∀ (a : subtype twoco_interval), a.val - 2 ≠ 0 := 
begin
intro,
cases a.2 with l r,
-- Know: 0 ≤ a.val < 2
--     :     a.val < 2
-- Show: a.val -2 < 0
have h, from sub_neg_of_lt r,      -- lemma for moving a term from the right to the left of  <
exact (ne_of_lt h),
end

-- I guess now that I'm getting some experience with these I can begin to see
-- how to compress the tactic-mode proofs towards terms mode proofs.  I guess
-- I can also see why people who understand the term style do find it convenient.

lemma simple_rational_of_twoco_items_are_nonzero' :  ∀ (a : subtype twoco_interval), a.val - 2 ≠ 0 := 
(λ a, (ne_of_lt (sub_neg_of_lt a.2.2)))

lemma simple_denom_over_twoco_interval_continuous : continuous (λ (x : subtype twoco_interval), (x.val - 2)) := 
begin
refine continuous_add _ _,
apply continuous_subtype_val,
exact continuous_const,
end

lemma simple_rational_cont : continuous simple_rational :=
begin
  unfold simple_rational function.restrict,
  simp only [one_div_eq_inv],
  -- This roughly follows cont_punctured_inv
  -- an error when plonking that proof in here tells about the first lemma we need
  -- sorry'ing that one, I get an error that explains the other needed lemma
  -- These are then copied above and proofs filled in
  exact continuous_inv simple_rational_of_twoco_items_are_nonzero
                       simple_denom_over_twoco_interval_continuous,
end

#print simple_rational_cont

-- * Example 2: sin(sin(x)) is continuous over [1,2].

-- This again deals with composition of functions, which considered
-- over an interval rather than over all of \(\mathbb{R}\).  This
-- example also prepares for further examples based on composition in
-- coming weeks.

-- Notice that we need to use the λ because writing "sin sin" doesn't
-- work.  You need to have it apply to an (x:ℝ) in order to generate
-- a (sin_x:ℝ) for the next step

#check sin
--  sin : ℝ → ℝ
#check (λ (x:ℝ), sin(x))
-- λ (x : ℝ), sin x : ℝ → ℝ

def onetwo_interval := (Icc (1:ℝ) 2)

noncomputable def sin_sin := function.restrict (λ (x:ℝ), sin(sin(x))) onetwo_interval

lemma sin_sin_cont : continuous sin_sin :=
begin
  unfold sin_sin function.restrict,
  refine continuous.comp _ _,
  apply continuous_subtype_val.comp, -- this deals with the subtype application
  apply continuous_sin,
  apply continuous_sin,
end

noncomputable def sin_sin_sin := function.restrict (λ (x:ℝ), sin(sin(sin(x)))) onetwo_interval

lemma sin_sin_sin_cont : continuous sin_sin_sin :=
begin
  unfold sin_sin_sin function.restrict,
  refine continuous.comp _ _,
  refine continuous.comp _ _,
  apply continuous_subtype_val.comp, -- we only need this once
  apply continuous_sin,
  apply continuous_sin,
  apply continuous_sin,
end

#print sin_sin_cont

-- * Example 3: y(x)=1/2-(1/2)e^{-x^2} is continuous on (i) ℝ and (ii) [0,1].

-- This includes more arithmetic combinators than the earlier
-- examples, but (i) should follow the same style as existing mathlib
-- proofs.  It will be interesting to see how/whether what we learn in
-- (i) transfers to (ii).

-- So this is kind of interesting, it basically looks like rippling,
-- in which I follow the shape of the function and deal with each
-- "hole" or "box" as it comes up.

-- It's somewhat unexpected that mul_neg_one takes care of the
-- continuity of -1, and that continuous_neg can't be used
-- there instead.

noncomputable def my_fun := (λ (x:ℝ), 1/2 - (1/2) * exp (-x^2))

lemma my_fun_cont : continuous my_fun :=
begin
  unfold my_fun,
  refine continuous_add _ _,
  exact continuous_const,
  refine continuous_neg _,
  refine continuous_mul _ _,
  exact continuous_const,
  refine continuous.comp _ _,
  simp [mul_neg_one],         -- * something unexpected!
  refine continuous_pow _,
  exact continuous_exp,
end


#print my_fun_cont
