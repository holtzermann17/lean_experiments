import topology.basic data.set.intervals analysis.exponential data.complex.basic tactic.ring
open real set
open complex

-- * Example 4: y(x)=1/(x^2-2x+3) is continuous over [1,2].

-- Here's a way to start sketching, anyway.

constants A B C : ℝ

-- some specific quadratic
noncomputable def quadratic := (λ (x:ℝ), A * (x^2) + B * x + C)

-- take in some coefficients and generate the corresponding quadratic polynomial
def quadratic_poly := (λ (a b c : ℝ), (λ (x:ℝ), a * (x^2) + b * x + c))

-- Here's a useful lemma: also easy to prove.  We'll use this to prove the nonmonic case as well.
lemma cs_monic (b c : ℝ) : ∀ (x:ℝ), x^2 + b*x + c = (x + b/2)^2 + (c-(b^2)/4) :=
begin
intro,
ring,
end
-- use this for an example, e.g. x^2-2x+3, to show this one is continuous

-- As a quick warm-up, the polynomial itself is continuous.
-- A more general version of this result would say that *all* such polynomials are continuous.
-- Is that a known result?  Anyway, this will do for now
lemma cont_example_quad : continuous (quadratic_poly 1 (-2) 3) :=
begin
unfold quadratic_poly,
refine continuous_add _ _,
refine continuous_add _ _,
refine continuous_mul _ _,
exact continuous_const,
exact continuous_pow 2,
refine continuous_mul _ _,
exact continuous_const,
exact continuous_id,
exact continuous_const,
end

-- Now let's set up 1/quad
#check (λ (x:ℝ), 1/x)
#check function.comp (λ (x:ℝ), 1/x) (quadratic_poly 1 (-2) 3)

lemma example_inv_quad : continuous (function.comp (λ (x:ℝ), 1/x) (quadratic_poly 1 (-2) 3)) :=
begin
unfold quadratic_poly function.comp,
-- the setup looks good.
-- adjust it so that we can apply the lemma:
simp only [one_div_eq_inv],
refine real.continuous_inv _ _,
intro x,
rw one_mul,
rw cs_monic,
-- The first summand is (x + (-2) / 2) ^ 2
-- which we deem to be nonnegative because it is a square;
-- so it is sufficient to show the second summand is positive.
-- But that's easy:
-- (3 - (-2) ^ 2 / 4) = (3 - 4 / 4) = (3 - 1) = 2 > 0
-- So let's apply these ideas.
apply ne_of_gt,                 -- this is a sufficient condition
apply add_pos_of_nonneg_of_pos, -- Break the proof into parts at the + sign
rw pow_two,                     -- rewrite the square
apply mul_self_nonneg,          -- draw the first required conclusion
-- For the next part, we need to do a bit of arithmetic
-- but we can let Lean do that for us.
ring,
norm_num,
-- the last goal is the continuity of the polynomial
exact cont_example_quad,
end

