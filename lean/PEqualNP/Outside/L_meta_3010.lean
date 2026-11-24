import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3010

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wire {n : ℕ} (p : Fin n → Fin n) (i : ℕ) : ℕ :=
  if hi : i < n then (p ⟨i, hi⟩).val else i

def gate {n : ℕ} (p : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire p)⟩

def circuit {n : ℕ} (p : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gate p), wire p C.output⟩

theorem preservesSize {n : ℕ} (p : Fin n → Fin n) (C : Circuit) :
    (circuit p C).size = C.size := by
  simp [circuit, Circuit.size]

theorem preservesBasis {n : ℕ} (p : Fin n → Fin n) {C : Circuit} (h : FanInTwo C) :
    FanInTwo (circuit p C) := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
  simpa [gate] using h f hf

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma mapRelated {n : ℕ} (p : Fin n → Fin n) (gs : List Gate) (x y : List Bool)
    (hl : x.length = y.length) (hn : n ≤ x.length)
    (h : ∀ i, x.getD (wire p i) false = y.getD i false) :
    ∀ i, ((gs.map (gate p)).foldl step x).getD (wire p i) false =
      (gs.foldl step y).getD i false := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have eqStep : (gate p g).op.eval ((gate p g).inputs.map fun i => x.getD i false) =
        g.op.eval (g.inputs.map fun i => y.getD i false) := by
      simp only [gate, List.map_map]
      congr 1
      exact List.map_congr_left fun a _ => h a
    apply ih _ _ (by simp [step,hl]) (by simp [step]; omega)
    intro j
    have hj : j < x.length ↔ wire p j < x.length := by
      unfold wire
      split
      · rename_i hj
        have hi := (p ⟨j,hj⟩).isLt
        omega
      · rfl
    by_cases hlt : j < x.length
    · have hj' := hj.mp hlt
      rw [step, step, List.getD_append _ _ _ _ hj',
        List.getD_append _ _ _ _ (by omega)]
      exact h j
    · have hjn : ¬ j < n := by omega
      have jEq : wire p j = j := by simp [wire,hjn]
      rw [jEq]
      rw [step, step, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), eqStep, hl]

theorem evalRelabeled {n : ℕ} (p : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
    (circuit p C).eval (List.ofFn x) = C.eval (List.ofFn fun j => x (p j)) := by
  change (((C.gates.map (gate p)).foldl step (List.ofFn x)).getD (wire p C.output) false) =
    (C.gates.foldl step (List.ofFn fun j => x (p j))).getD C.output false
  apply mapRelated p C.gates _ _ (by simp) (by simp)
  intro i
  by_cases hi : i < n
  · have hp : (p ⟨i,hi⟩).val < (List.ofFn x).length := by simp
    rw [wire, dite_eq_left hi, List.getD_eq_getElem _ _ hp,
      List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  · simp only [wire, dite_eq_right hi]
    rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]


lemma dataTwo (g : Gate) (h : g.inputs.length = 2) :
    ∃ a b, g.inputs = [a,b] := by
  rcases e : g.inputs with _ | ⟨a, rest⟩
  · simp [e] at h
  rcases rest with _ | ⟨b,tail⟩
  · simp [e] at h
  have ht : tail = [] := by simpa [e] using h
  subst tail
  exact ⟨a,b,rfl⟩

lemma wirePrimary {n : ℕ} (p : Fin n → Fin n) (i : Fin n) :
    wire p i.val = (p i).val := by simp [wire, i.isLt]

lemma wireBound (p : Equiv.Perm (Fin 14)) {i : ℕ} (h : i < 15) :
    wire p i < 15 := by
  unfold wire
  split
  · rename_i hi
    exact Nat.lt_trans (p ⟨i,hi⟩).isLt (by decide)
  · exact h

lemma wireInj {n : ℕ} (p : Equiv.Perm (Fin n)) : Function.Injective (wire p) := by
  intro a b e
  by_cases ha : a < n <;> by_cases hb : b < n
  · simp only [wire, dite_eq_left ha, dite_eq_left hb] at e
    exact congrArg Fin.val (p.injective (Fin.ext e))
  · simp only [wire, dite_eq_left ha, dite_eq_right hb] at e
    have h := (p ⟨a,ha⟩).isLt
    omega
  · simp only [wire, dite_eq_right ha, dite_eq_left hb] at e
    have h := (p ⟨b,hb⟩).isLt
    omega
  · simpa only [wire, dite_eq_right ha, dite_eq_right hb] using e

lemma wireTrans {n : ℕ} (p q : Equiv.Perm (Fin n)) (i : ℕ) :
    wire (p.trans q) i = wire q (wire p i) := by
  by_cases hi : i < n
  · let j : Fin n := ⟨i,hi⟩
    change wire (p.trans q) j.val = wire q (wire p j.val)
    simp only [wirePrimary, Equiv.trans_apply]
  · simp [wire,hi]

lemma fixedOrPerm (p : Equiv.Perm (Fin 14)) (a : Fin 15) :
    wire p a.val = (if a.val < 14 then (p (Fin.ofNat 14 a.val)).val else 14) := by
  by_cases h : a.val < 14
  · have e : Fin.ofNat 14 a.val = (⟨a.val, h⟩ : Fin 14) := Fin.ext (Nat.mod_eq_of_lt h)
    rw [ite_eq_left h, e, wire, dite_eq_left h]
  · have ha := a.isLt
    simp [wire, show a.val = 14 by omega]

def pairCode (a b : ℕ) : ℕ := 15 * min a b + max a b
def prefixCode (a b c d : ℕ) : ℕ := pairCode a b * 225 + pairCode c d

lemma sortCode (f : ℕ → ℕ) (a b : ℕ) :
    pairCode (f (min a b)) (f (max a b)) = pairCode (f a) (f b) := by
  rcases le_total a b with h | h
  · simp only [min_eq_left h, max_eq_right h]
  · simp only [min_eq_right h, max_eq_left h, pairCode]
    rw [min_comm (f b), max_comm (f b)]

lemma sortedLt {a b : ℕ} (h : a ≠ b) : min a b < max a b := by
  rcases lt_or_gt_of_ne h with h' | h'
  · simpa [min_eq_left h'.le, max_eq_right h'.le] using h'
  · simpa [min_eq_right h'.le, max_eq_left h'.le] using h'

lemma sortedEval (op : GateOp) (hop : op = .and ∨ op = .or)
    (f : ℕ → Bool) (a b : ℕ) :
    op.eval [f (min a b), f (max a b)] = op.eval [f a, f b] := by
  rcases le_total a b with h | h
  · simp only [min_eq_left h, max_eq_right h]
  · simp only [min_eq_right h, max_eq_left h]
    rcases hop with rfl | rfl
    · simp [GateOp.eval, Bool.and_comm]
    · simp [GateOp.eval, Bool.or_comm]

lemma prefixCanonical (f : (Fin 14 → Bool) → Bool) (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 14 C)
    (hUnique : ∀ g ∈ C.gates, g.inputs.Nodup)
    (hMin : 2 ≤ C.size) (hMax : C.size ≤ 26)
    (hEq : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = f x) :
    ∃ (a b : Fin 14) (c d : Fin 15) (o₀ o₁ : GateOp) (D : Circuit),
      a < b ∧ c < d ∧ (o₀ = .and ∨ o₀ = .or) ∧ (o₁ = .and ∨ o₁ = .or) ∧
      (∀ q : Equiv.Perm (Fin 14), (∀ x, f (x ∘ q) = f x) →
        prefixCode a.val b.val c.val d.val ≤
          prefixCode (q a).val (q b).val (wire q c.val) (wire q d.val)) ∧
      PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 24 ∧
      ∀ x : Fin 14 → Bool,
        let w := List.ofFn x ++ [o₀.eval [x a, x b]]
        D.eval (w ++ [o₁.eval [w.getD c.val false, w.getD d.val false]]) = f x := by
  classical
  change 2 ≤ C.gates.length at hMin
  change C.gates.length ≤ 26 at hMax
  rcases hG : C.gates with _ | ⟨g, rest⟩
  · simp [hG] at hMin
  rcases rest with _ | ⟨h, tail⟩
  · simp [hG] at hMin
  have hg : g ∈ C.gates := by simp [hG]
  have hh : h ∈ C.gates := by simp [hG]
  obtain ⟨a,b,hi₀⟩ := dataTwo g (hAO.2.2 g hg)
  obtain ⟨c,d,hi₁⟩ := dataTwo h (hAO.2.2 h hh)
  have op₀ := hAO.1 g hg
  have op₁ := hAO.1 h hh
  have hab : a ≠ b := by simpa [hi₀] using hUnique g hg
  have hcd : c ≠ d := by simpa [hi₁] using hUnique h hh
  have read₀ (i : ℕ) (hi : i ∈ g.inputs) : i < 14 := by
    have hBound := hAO.2.1 0 (by simp [hG]) i
    exact hBound (by simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, hG] using hi)
  have read₁ (i : ℕ) (hi : i ∈ h.inputs) : i < 15 := by
    have hBound := hAO.2.1 1 (by simp [hG]) i
    exact hBound (by simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, hG] using hi)
  have ha := read₀ a (by simp [hi₀])
  have hb := read₀ b (by simp [hi₀])
  have hc := read₁ c (by simp [hi₁])
  have hd := read₁ d (by simp [hi₁])
  let syms : Set (Equiv.Perm (Fin 14)) := {p | ∀ x : Fin 14 → Bool, f (x ∘ p) = f x}
  let score (p : Equiv.Perm (Fin 14)) :=
    prefixCode (wire p a) (wire p b) (wire p c) (wire p d)
  have nonempty : syms.Nonempty := ⟨Equiv.refl _, fun _ => rfl⟩
  obtain ⟨p,hp,hBest⟩ := Set.exists_min_image syms score (Set.toFinite _) nonempty
  let a' : Fin 14 := ⟨min (wire p a) (wire p b), by
    exact lt_of_le_of_lt (min_le_left _ _) (by simp [wire,ha])⟩
  let b' : Fin 14 := ⟨max (wire p a) (wire p b), by simp [wire,ha,hb]⟩
  let c' : Fin 15 := ⟨min (wire p c) (wire p d), (min_le_left _ _).trans_lt (wireBound p hc)⟩
  let d' : Fin 15 := ⟨max (wire p c) (wire p d), max_lt (wireBound p hc) (wireBound p hd)⟩
  let D : Circuit := ⟨tail.map (gate p), wire p C.output⟩
  have hCanonical (q : Equiv.Perm (Fin 14))
      (hq : ∀ x : Fin 14 → Bool, f (x ∘ q) = f x) :
      prefixCode a'.val b'.val c'.val d'.val ≤
        prefixCode (q a').val (q b').val (wire q c'.val) (wire q d'.val) := by
    have hpq : p.trans q ∈ syms := by
      intro x
      change f ((x ∘ q) ∘ p) = f x
      exact (hp (x ∘ q)).trans (hq x)
    have h := hBest (p.trans q) hpq
    unfold score at h
    simp only [wireTrans] at h
    rw [← wirePrimary q a', ← wirePrimary q b']
    change prefixCode (min (wire p a) (wire p b)) (max (wire p a) (wire p b))
        (min (wire p c) (wire p d)) (max (wire p c) (wire p d)) ≤
      prefixCode (wire q (min (wire p a) (wire p b))) (wire q (max (wire p a) (wire p b)))
        (wire q (min (wire p c) (wire p d))) (wire q (max (wire p c) (wire p d)))
    unfold prefixCode at h ⊢
    have hid (u v : ℕ) : pairCode (min u v) (max u v) = pairCode u v := sortCode id u v
    simpa only [sortCode, hid] using h
  refine ⟨a',b',c',d',g.op,h.op,D, sortedLt (wireInj p |>.ne hab),
    sortedLt (wireInj p |>.ne hcd),op₀,op₁,hCanonical, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hk
    have hkC : k' ∈ C.gates := by simp [hG,hk']
    exact ⟨hAO.1 k' hkC, by simp [gate, hAO.2.2 k' hkC]⟩
  · simp only [D, Circuit.size, List.length_map]
    simp [hG] at hMax
    omega
  · intro x
    have val := evalRelabeled p C x
    rw [hEq] at val
    have hv : (circuit p C).eval (List.ofFn x) = f x := val.trans (hp x)
    let init := List.ofFn x
    let w := init ++ [g.op.eval [x a',x b']]
    have inputVal (i : Fin 14) : init.getD i.val false = x i := by
      have hi : i.val < init.length := by simp [init]
      rw [List.getD_eq_getElem _ _ hi]
      change (List.ofFn x)[i.val] = x i
      rw [List.getElem_ofFn]
    have first : step init (gate p g) = w := by
      change init ++ [g.op.eval ((g.inputs.map (wire p)).map fun i => init.getD i false)] = w
      rw [hi₀]
      change init ++ [g.op.eval [init.getD (wire p a) false, init.getD (wire p b) false]] = w
      have e := sortedEval g.op op₀ (fun i => init.getD i false) (wire p a) (wire p b)
      change g.op.eval [init.getD a'.val false, init.getD b'.val false] = _ at e
      rw [inputVal, inputVal] at e
      rw [← e]
    have second : step w (gate p h) =
        w ++ [h.op.eval [w.getD c'.val false, w.getD d'.val false]] := by
      change w ++ [h.op.eval ((h.inputs.map (wire p)).map fun i => w.getD i false)] = _
      rw [hi₁]
      congr 2
      exact (sortedEval h.op op₁ (fun i => w.getD i false) (wire p c) (wire p d)).symm
    unfold circuit at hv
    rw [Circuit.eval, Circuit.wires] at hv
    simp only [hG, List.map_cons, List.foldl_cons] at hv
    change ((tail.map (gate p)).foldl step (step (step init (gate p g)) (gate p h))).getD
      (wire p C.output) false = f x at hv
    rw [first,second] at hv
    exact hv
end PEqualNP.Outside.L_meta_3010

open PEqualNP.Outside.L_meta_3010 in
theorem PEqualNP.Outside.L_meta_3010 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if ↑x10 < (14 : ℕ) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  intro f C hAO hN dupMin dupMax hE
  obtain ⟨a,b,c,d,g,h,D,hab,hcd,hg,hh,hKey,hD,hSize,hEval⟩ :=
    prefixCanonical f C hAO hN dupMin dupMax hE
  refine ⟨a,b,c,d,g,h,D,hab,hcd,hg,hh,?_,hD,hSize,hEval⟩
  intro q hq
  simpa only [fixedOrPerm, prefixCode, pairCode] using hKey q hq
