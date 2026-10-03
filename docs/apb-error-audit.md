# WP0216 persistence accounting: explicit reconstruction allowance

October 3, 2026. The frame slack s and residual reconstruction complexity δ are independent. `algorithmic_persistence_balance_with_error` gives ν ≤ ΣJ + δ + 2s; `bounded_persistence_forces_flow_with_error` and `flow_pigeonhole_with_error` subtract δ + 5s after bounding all three internal channels. The original declarations retain their statements under δ ≤ s.

`bounded_self_code_update_capacity` uses K(Z₁ | Z₀,C) ≤ K₀ directly, matching the paper's update budget; the older `bounded_self_code_capacity` assumes an unconditional budget and conditioning monotonicity.

All four new declarations compile. `#print axioms` reports `[propext, Quot.sound]` for each, with no custom axioms or sorryAx. The full library build and `scripts/check_sync.sh` both pass. These checks establish the implications from their named AIT hypotheses, not a physical choice of identity projection or completion records.

The finite `noGapFrame` witness remains a witness in the abstract frame interface. Its assigned complexity values are not an instantiation of a universal prefix machine.
