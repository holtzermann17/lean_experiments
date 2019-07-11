import topology.basic data.set.intervals analysis.exponential 
open real set

-- * Objective 1: prove that 1/x is continuous on R∗ (defined using sets)

-- It's easy to define the underlying set, and a restricted version of the function
def punctured_line := (Iio (0:ℝ)) ∪ (Ioi (0:ℝ))
noncomputable def punctured_inv := function.restrict (λ (x:ℝ), 1/x) punctured_line

lemma punctured_reals_are_nonzero : ∀ (a : subtype punctured_line), a.val ≠ 0 :=
begin
intro,
-- we can decompose the property using cases
cases a.2 with l r,
have h : a.val < 0, from mem_Iio.mp l, 
have h1 : a.val ≠ 0, from ne_of_lt h,
exact  h1,
have k : a.val > 0, from mem_Ioi.mp r, 
have k1 : a.val ≠ 0, from (ne_of_lt k).symm,
exact  k1,
end

-- ... we mainly need to know that all of the possible arguments are nonzero
lemma cont_punctured_inv : continuous punctured_inv :=
begin
  unfold punctured_inv function.restrict,
  simp only [one_div_eq_inv],
  exact continuous_inv punctured_reals_are_nonzero continuous_subtype_val,
end

-- Here is a similar result that is closer to the mathlib proof
theorem continuous_1_over_x'' : continuous (λ (x : {r : ℝ | r ≠ 0} ), 1/(x:ℝ)) := 
begin
simp only [one_div_eq_inv],
refine real.continuous_inv _ _,
exact subtype.property,
apply continuous_subtype_val,
end

-- * Objective 2:  prove that tan(x) is continuous where cos(x) is nonzero

def cos_nonzero_set := {x : ℝ | cos x ≠ 0} 

-- minor change from the mathlib version
lemma continuous_tan' : continuous (λ x : cos_nonzero_set, tan x) :=
by simp only [tan_eq_sin_div_cos]; exact
continuous_mul
  (continuous_subtype_val.comp continuous_sin)
  (continuous_inv subtype.property
    (continuous_subtype_val.comp continuous_cos))

-- * Objective 3: Instantiate [0,2] as a subtype and prove that x is continuous on this interval

def two_interval_set := (Icc (0:ℝ) 2) 

theorem continuous_id_on_tworeal' : continuous (λ (x : ↥two_interval_set), x) := 
begin
exact continuous_id,
end
