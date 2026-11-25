import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_2582_1
    (norm : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      ∃ C' : Circuit, IsAO2 (N + N) C' ∧
        (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C' z =
          decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧
        C'.size ≤ C.size ∧
        ∀ j < C'.gates.length, (gateAt C' j).op = GateOp.or →
          (∃ w ∈ (gateAt C' j).inputs, ∀ z : Fin (N + N) → Bool,
            (C'.wires (List.ofFn z)).getD w false = true →
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
          ∀ z : Fin (N + N) → Bool,
            (C'.wires (List.ofFn z)).getD (N + N + j) false = true →
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (from_norm : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      (∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
        (∃ w ∈ (gateAt C j).inputs, ∀ z : Fin (N + N) → Bool,
          (C.wires (List.ofFn z)).getD w false = true →
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        ∀ z : Fin (N + N) → Bool,
          (C.wires (List.ofFn z)).getD (N + N + j) false = true →
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      ∃ D : Circuit, IsAO2 (N + N) D ∧
        (∀ y : Fin (N + N) → Bool, circuitFun (N + N) D y =
          decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧
        D.size ≤ C.size ∧ IsReadK (N + N) D 2) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 2 := by
  intro q N I decI C hq hN hdeg huniq hao hfun
  obtain ⟨C', hao', hfun', hsize', hnorm⟩ := norm q N I C hq hN hdeg huniq hao hfun
  obtain ⟨D, haoD, hfunD, hsizeD, hread⟩ := from_norm q N I C' hq hN hdeg huniq hao' hfun' hnorm
  exact ⟨D, haoD, hfunD, le_trans hsizeD hsize', hread⟩
