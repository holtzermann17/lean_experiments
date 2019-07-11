import data.real.basic data.set.intervals topology.basic analysis.exponential 
local attribute [instance] classical.prop_decidable

-- * Example 5: y(x) = (η e^{κx}-1)/κ (when x ≤ ξ) and (η e^{κx}-e^{κ(x-ξ)})/κ (when x > ξ) (assuming κ nonzero) is continuous on ℝ.

-- NB. I've gotten started with a simpler warm-up exercise, using the
-- absolute value function instead of the one mentioned in the
-- headline.  In the end the treatment of the two functions will be
-- similar.

open real

-- Only one of these will unfold properly
noncomputable def fake_abs : ℝ → ℝ := λ x, if x < 0 then -x else x

lemma fake_abs_is_abs : fake_abs = (λ x, abs x)  :=
begin
unfold fake_abs abs,
-- Goal is now:
-- ⊢ (λ (x : ℝ), ite (x ≤ 0) (-x) x) = λ (x : ℝ), max x (-x)
funext,
by_cases x < 0,
-- Goal is now:
-- ⊢ ite (x < 0) (-x) x = max x (-x)
simp [if_pos h],
-- * used sorry to sketch out all of the "have" steps here, getting the skeleton of the proof established
have he : -x > 0, from neg_pos_of_neg h,
have hl : -x > x, from lt_trans h he,
have hm : max x (-x) = -x, from max_eq_right_of_lt hl,
exact hm.symm,
simp [if_neg h],
-- Goal is now:
-- ⊢ x = max x (-x)
-- this intermediate step was harder than I would have thought
have he : 0 ≤ x, from begin simp at h, exact h, end,
have hl : -x ≤ 0, from neg_nonpos_of_nonneg he,
have hll : -x ≤ x, from le_trans hl he,
have hm : max x (-x) = x, from max_eq_left hll,
exact hm.symm,
end

lemma continuous_fake_abs : continuous fake_abs := begin
unfold fake_abs,
apply continuous_if _ _ _,
intro,
intro,
-- I don't know how to do this part...
sorry,
--- but the rest is then routine.
refine continuous_neg _,
exact continuous_id,
exact continuous_id,
end

lemma continuous_abs : continuous (λ (x:ℝ), abs x) := begin
rw ←fake_abs_is_abs,
exact continuous_fake_abs,
end
