import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1772_1
    (hits : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∃ u v : Fin n, G.Adj u v ∧ gateVal n C j (pairInput u v) = true)
    (owns : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∃ u v : Fin n, G.Adj u v ∧ gateVal n C j (pairInput u v) = true) →
      ∃ C' : Circuit, IsMinimalMonoCircuit n C' ∧ circuitFun n C' = graphFun G ∅ ∧
        ∀ j < C'.gates.length, (gateAt C' j).op = GateOp.and →
          ∃ u v : Fin n, G.Adj u v ∧ Owns n C' j u v) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11 := by
  intro n G decG tri four
  obtain ⟨C, hmin, hfun, hhit⟩ := hits n G tri four
  exact owns n G C tri four hmin hfun hhit
