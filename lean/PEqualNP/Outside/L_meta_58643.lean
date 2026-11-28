import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58643 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6474802 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [2, 5]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [1, 0]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [6, 1]⟩, ⟨.not, [9]⟩, ⟨.not, [12]⟩, ⟨.and, [13, 7]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [18, 17]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
