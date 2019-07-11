import data.real.basic data.complex.exponential topology.basic data.set.intervals analysis.exponential order.filter.basic

constants (ξ : ℝ)
open real

noncomputable def step_fun : ℝ → ℝ := λ x, if x ≤ ξ then 1 else 0

-- * Example 6: The function r(x) = 1 (when x ≤ ξ) and 0  (when x > ξ) is discontinuous over [0,2], assuming ξ=1.

lemma discont_at_step : ¬ (continuous_at step_fun ξ) := begin
unfold continuous_at,
-- our goal:
-- ⊢ ¬filter.tendsto step_fun (nhds ξ) (nhds (step_fun ξ))
rw metric.tendsto_nhds_nhds,
-- our goal:
-- ⊢ ¬∀ (ε : ℝ),
--      ε > 0 → (∃ (δ : ℝ) (H : δ > 0),
--                ∀ {x : ℝ}, dist x ξ < δ → dist (step_fun x)
--                                                 (step_fun ξ) < ε)
end
