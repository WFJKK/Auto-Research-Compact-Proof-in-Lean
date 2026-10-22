import Protected.N_max2_tiny_v8_s0_c64
import CompactCheck.Soundness
import CompactCheck.CountedOps
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# 64 of 64 inputs of max2_tiny-v8-s0 from the eight columns of the product matrix

The network is linear: its logits on `[a, b]` are column `a` plus column `b` of `M = U L E`. The checker
computes the eight columns (48 operations each), per column the off-diagonal maximum `mx`, the column
maximum `top` and the guarded diagonal margin `dm`, then certifies the diagonal `[m, m]` by `0 < dm_m`,
a pair `[a, m]`, `[m, a]` (`a < m`) by `top_a - M[m,a] < dm_m` (2 operations, implying `[m, m]` too),
by the refined test `mx_a - M[m,a] < dm_m ∧ M[a,a] - M[m,a] < M[m,m] - M[a,m]` (6 operations), or by the
exact test on the summed columns (16 operations). One `single` on `[6, 7]` guards the well-formedness of
the weights and counts its two inputs.
-/

namespace Candidate.Full64

open CompactCheck Protected.N_max2_tiny_v8_s0_c64

/-! ## The checker -/

def dotRow (I : Interp) (name : String) (base : Nat) : List I.V → Nat → I.V → I.M I.V
  | [], _, acc => pure acc
  | v :: vs, i, acc => do
    let x ← I.weight name (base + i)
    let acc' ← I.muladd "mac" acc x v
    dotRow I name base vs (i + 1) acc'

def rows (I : Interp) (name : String) (n : Nat) (v : List I.V) : List Nat → I.M (List I.V)
  | [] => pure []
  | r :: rs => do
    let d ← dotRow I name (r * n) v 0 I.zero
    let ds ← rows I name n v rs
    pure (d :: ds)

def readCol (I : Interp) (a : Nat) : List Nat → I.M (List I.V)
  | [] => pure []
  | i :: is => do
    let x ← I.weight "embedding.weight" (i * 8 + a)
    let xs ← readCol I a is
    pure (x :: xs)

def column (I : Interp) (a : Nat) : I.M (List I.V) := do
  let e ← readCol I a (List.range 4)
  let h ← rows I "linear.weight" 4 e (List.range 4)
  rows I "unembedding.weight" 4 h (List.range 8)

def maxFrom (I : Interp) : I.V → List I.V → I.M I.V
  | acc, [] => pure acc
  | acc, y :: ys => do
    let acc' ← I.max "max" acc y
    maxFrom I acc' ys

def maxList (I : Interp) : List I.V → I.M I.V
  | [] => pure I.zero
  | y :: ys => maxFrom I y ys

def others (m : Nat) : List Nat := (List.range 8).filter fun j => j != m

def maxOthers (I : Interp) (L : List I.V) (a : Nat) : I.M I.V :=
  maxList I ((others a).map fun j => L.getD j I.zero)

def addLists (I : Interp) : List I.V → List I.V → I.M (List I.V)
  | x :: xs, y :: ys => do
    let z ← I.add "add" x y
    let zs ← addLists I xs ys
    pure (z :: zs)
  | _, _ => pure []

structure ColInfo (I : Interp) where
  col : List I.V
  mx : I.V
  top : I.V
  dm : I.V

def colInfo (I : Interp) (G : I.B) (a : Nat) : I.M (ColInfo I) := do
  let col ← column I a
  let mx ← maxOthers I col a
  let d := col.getD a I.zero
  let top ← I.max "max" mx d
  let dm0 ← I.sub "sub" d mx
  let dm ← I.selectV "sel" G dm0 I.zero
  pure ⟨col, mx, top, dm⟩

def columns (I : Interp) (G : I.B) : List Nat → I.M (List (Nat × ColInfo I))
  | [] => pure []
  | a :: as => do
    let c ← colInfo I G a
    let cs ← columns I G as
    pure ((a, c) :: cs)

def defaultInfo (I : Interp) : ColInfo I := ⟨[], I.zero, I.zero, I.zero⟩

inductive Term where
  | diag (m : Nat)
  | pair (a m : Nat) (wd : Bool)
  | rpair (a m : Nat)
  | exact (a m : Nat)

def Term.inputs : Term → List Input
  | .diag m => [[m, m]]
  | .pair a m wd => if wd then [[a, m], [m, a], [m, m]] else [[a, m], [m, a]]
  | .rpair a m => [[a, m], [m, a]]
  | .exact a m => [[a, m], [m, a]]

def runTerm (I : Interp) (G : I.B) (cv : List (Nat × ColInfo I)) : Term → I.M I.N
  | .diag m => do
    let cm := (cv.lookup m).getD (defaultInfo I)
    let b ← I.lt "cmp" I.zero cm.dm
    pure (I.nscale 1 b)
  | .pair a m wd => do
    let ca := (cv.lookup a).getD (defaultInfo I)
    let cm := (cv.lookup m).getD (defaultInfo I)
    let x ← I.sub "sub" ca.top (ca.col.getD m I.zero)
    let b ← I.lt "cmp" x cm.dm
    pure (I.nscale (if wd then 3 else 2) b)
  | .rpair a m => do
    let ca := (cv.lookup a).getD (defaultInfo I)
    let cm := (cv.lookup m).getD (defaultInfo I)
    let x ← I.sub "sub" ca.mx (ca.col.getD m I.zero)
    let b1 ← I.lt "cmp" x cm.dm
    let y ← I.sub "sub" (ca.col.getD a I.zero) (ca.col.getD m I.zero)
    let z ← I.sub "sub" (cm.col.getD m I.zero) (cm.col.getD a I.zero)
    let b2 ← I.lt "cmp" y z
    let b ← I.band "gate" b1 b2
    pure (I.nscale 2 b)
  | .exact a m => do
    let ca := (cv.lookup a).getD (defaultInfo I)
    let cm := (cv.lookup m).getD (defaultInfo I)
    let s ← addLists I ca.col cm.col
    let mo ← maxOthers I s m
    let b0 ← I.lt "cmp" mo (s.getD m I.zero)
    let b ← I.band "gate" G b0
    pure (I.nscale 2 b)

def runTerms (I : Interp) (G : I.B) (cv : List (Nat × ColInfo I)) : List Term → I.M I.N
  | [] => pure I.nzero
  | t :: ts => do
    let n ← runTerm I G cv t
    let ns ← runTerms I G cv ts
    pure (I.nadd n ns)

structure Plan where
  cols : List Nat
  guard : Nat × Nat
  terms : List Term

def guardInputs (g : Nat × Nat) : List Input :=
  if g.1 = g.2 then [[g.1, g.2]] else [[g.1, g.2], [g.2, g.1]]

def shapesOk (I : Interp) : I.M Bool := do
  let s1 ← I.weightShape "embedding.weight"
  let s2 ← I.weightShape "linear.weight"
  let s3 ← I.weightShape "unembedding.weight"
  pure (s1 == [4, 8] && s2 == [4, 4] && s3 == [8, 4])

def runPlan (I : Interp) (p : Plan) : I.M I.N := do
  let ok ← shapesOk I
  if ok then
    let G ← I.single graph task [p.guard.1, p.guard.2]
    let cv ← columns I G p.cols
    let n ← runTerms I G cv p.terms
    pure (I.nadd (I.nscale (guardInputs p.guard).length G) n)
  else pure I.nzero

def thePlan : Plan where
  cols := [0, 1, 2, 3, 4, 5, 6, 7]
  guard := (6, 7)
  terms := [.diag 0, .diag 3,
    .pair 0 1 true, .pair 1 2 true, .pair 0 4 true, .pair 0 5 true, .pair 0 6 true, .pair 0 7 true,
    .pair 1 4 false, .pair 1 6 false, .pair 1 7 false, .pair 2 4 false, .pair 2 5 false,
    .pair 2 7 false, .pair 3 4 false, .pair 3 6 false, .pair 4 6 false, .pair 4 7 false,
    .rpair 0 2, .rpair 0 3, .rpair 1 3, .rpair 1 5, .rpair 2 3, .rpair 3 5, .rpair 3 7,
    .rpair 5 6, .rpair 5 7,
    .exact 2 6, .exact 4 5]

def D : Checker := fun I => runPlan I thePlan

/-! ## Plans that count correctly (proof side only) -/

def Plan.inputs (p : Plan) : List Input := guardInputs p.guard ++ p.terms.flatMap Term.inputs

def termOk (cols : List Nat) : Term → Bool
  | .diag m => decide (m < 8) && decide (m ∈ cols)
  | .pair a m _ => decide (a < m) && decide (m < 8) && decide (a ∈ cols) && decide (m ∈ cols)
  | .rpair a m => decide (a < m) && decide (m < 8) && decide (a ∈ cols) && decide (m ∈ cols)
  | .exact a m => decide (a < m) && decide (m < 8) && decide (a ∈ cols) && decide (m ∈ cols)

def planOk (p : Plan) : Bool :=
  decide (p.guard.1 < 8) && decide (p.guard.2 < 8) && p.terms.all (termOk p.cols) &&
  p.inputs.all (fun x => decide (x ∈ allInputs [8, 8])) && decide p.inputs.Nodup

theorem thePlan_ok : planOk thePlan = true := by decide +kernel

theorem sym_graph : symmetricNet graph = true := by decide +kernel

/-! ## Pure semantics -/

def wget (w : Weights ℚ) (name : String) (i : Nat) : ℚ :=
  match List.lookup name w with
  | some t => t.get i
  | none => 0

def hid (w : Weights ℚ) (a i : Nat) : ℚ :=
  ((List.range 4).map fun k => wget w "linear.weight" (i * 4 + k) * wget w "embedding.weight" (k * 8 + a)).sum

def logit (w : Weights ℚ) (a j : Nat) : ℚ :=
  ((List.range 4).map fun i => wget w "unembedding.weight" (j * 4 + i) * hid w a i).sum

def dotVal (w : Weights ℚ) (name : String) (base : Nat) : List ℚ → Nat → ℚ → ℚ
  | [], _, acc => acc
  | v :: vs, i, acc => dotVal w name base vs (i + 1) (acc + wget w name (base + i) * v)

def rowsVal (w : Weights ℚ) (name : String) (n : Nat) (v : List ℚ) : List Nat → List ℚ
  | [] => []
  | r :: rs => dotVal w name (r * n) v 0 0 :: rowsVal w name n v rs

def colVal (w : Weights ℚ) (a : Nat) : List ℚ :=
  rowsVal w "unembedding.weight" 4
    (rowsVal w "linear.weight" 4 ((List.range 4).map fun i => wget w "embedding.weight" (i * 8 + a))
      (List.range 4))
    (List.range 8)

def maxFromVal : ℚ → List ℚ → ℚ
  | acc, [] => acc
  | acc, y :: ys => maxFromVal (max acc y) ys

def maxListVal : List ℚ → ℚ
  | [] => 0
  | y :: ys => maxFromVal y ys

def maxOthersVal (L : List ℚ) (a : Nat) : ℚ := maxListVal ((others a).map fun j => L.getD j 0)

def addVal : List ℚ → List ℚ → List ℚ
  | x :: xs, y :: ys => (x + y) :: addVal xs ys
  | _, _ => []

theorem colVal_getD (w : Weights ℚ) (a j : Nat) (hj : j < 8) : (colVal w a).getD j 0 = logit w a j := by
  have h4 : List.range 4 = [0, 1, 2, 3] := rfl
  have h8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  simp only [colVal, logit, hid, h4, h8, List.map_cons, List.map_nil, rowsVal, dotVal,
    List.sum_cons, List.sum_nil]
  interval_cases j <;> simp <;> ring

theorem colVal_length (w : Weights ℚ) (a : Nat) : (colVal w a).length = 8 := rfl

theorem le_maxFromVal_acc : ∀ (ys : List ℚ) (acc : ℚ), acc ≤ maxFromVal acc ys
  | [], _ => le_refl _
  | y :: ys, acc => le_trans (le_max_left acc y) (le_maxFromVal_acc ys _)

theorem le_maxFromVal_mem : ∀ (ys : List ℚ) (acc y : ℚ), y ∈ ys → y ≤ maxFromVal acc ys
  | [], _, _, h => absurd h (List.not_mem_nil)
  | z :: zs, acc, y, h => by
    simp only [maxFromVal]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_trans (le_max_right acc y) (le_maxFromVal_acc zs _)
    · exact le_maxFromVal_mem zs _ y h'

theorem le_maxOthersVal (L : List ℚ) (a j : Nat) (hj : j < 8) (hne : j ≠ a) :
    L.getD j 0 ≤ maxOthersVal L a := by
  have hmem : L.getD j 0 ∈ (others a).map (fun j => L.getD j 0) :=
    List.mem_map.mpr ⟨j, by simp [others, List.mem_filter, hj, hne], rfl⟩
  unfold maxOthersVal
  generalize hl : (others a).map (fun j => L.getD j 0) = l at hmem
  cases l with
  | nil => simp at hmem
  | cons y ys =>
    simp only [maxListVal]
    rcases List.mem_cons.mp hmem with h1 | h1
    · rw [h1]; exact le_maxFromVal_acc ys y
    · exact le_maxFromVal_mem ys y _ h1

theorem getD_val : ∀ (L : List Q) (j : Nat), (L.map Q.val).getD j 0 = (L.getD j ⟨0⟩).val
  | [], j => by simp
  | x :: xs, 0 => by simp
  | x :: xs, j + 1 => by simp [getD_val xs j]

theorem addVal_getD : ∀ (l1 l2 : List ℚ) (j : Nat), j < l1.length → j < l2.length →
    (addVal l1 l2).getD j 0 = l1.getD j 0 + l2.getD j 0
  | [], _, j, h1, _ => absurd h1 (by simp)
  | _ :: _, [], j, _, h2 => absurd h2 (by simp)
  | x :: xs, y :: ys, 0, _, _ => by simp [addVal]
  | x :: xs, y :: ys, j + 1, h1, h2 => by
    simp only [addVal, List.getD_cons_succ]
    exact addVal_getD xs ys j (by simpa using h1) (by simpa using h2)

/-! ## The network on a pair of tokens -/

structure WF (w : Weights ℚ) : Prop where
  E : ∃ t, List.lookup "embedding.weight" w = some t ∧ t.shape = [4, 8] ∧ t.data.size = 32
  L : ∃ t, List.lookup "linear.weight" w = some t ∧ t.shape = [4, 4] ∧ t.data.size = 16
  U : ∃ t, List.lookup "unembedding.weight" w = some t ∧ t.shape = [8, 4] ∧ t.data.size = 32

theorem graph_nodes : graph.nodes = [.input, .sum 0 1, .linear 1 "embedding.weight" none,
    .linear 2 "linear.weight" none, .linear 3 "unembedding.weight" none] := rfl

theorem graph_output : graph.output = 4 := rfl

theorem label_pair (a b : Nat) : task.label [a, b] = max a b := by
  show [a, b].foldl max 0 = max a b
  simp [List.foldl]

theorem get_range_map (s : List Nat) (n : Nat) (f : Nat → ℚ) (i : Nat) (hi : i < n) :
    (Tensor.mk s ((Array.range n).map f)).get i = f i := by
  simp [Tensor.get, Array.getD_eq_getD_getElem?, hi]

theorem oneHot_eval (a b : Nat) (ha : a < 8) (hb : b < 8) :
    ∃ t : Tensor ℚ, oneHotInput 2 8 [a, b] = some t ∧ t.shape = [1, 2, 8] ∧ t.data.size = 16 ∧
      ∀ m < 8, t.get m = (if a = m then 1 else 0) ∧ t.get (8 + m) = (if b = m then 1 else 0) := by
  unfold oneHotInput
  simp only [List.length_cons, List.length_nil, List.all_cons, List.all_nil, ha, hb, decide_true,
    Bool.and_true, beq_self_eq_true, ite_true]
  refine ⟨_, rfl, rfl, by simp, fun m hm => ⟨?_, ?_⟩⟩
  · rw [get_range_map _ _ _ m (by omega)]
    simp [Nat.div_eq_of_lt hm, Nat.mod_eq_of_lt hm]
  · rw [get_range_map _ _ _ (8 + m) (by omega)]
    have h1 : (8 + m) / 8 = 1 := by omega
    have h2 : (8 + m) % 8 = m := by omega
    simp [h1, h2]

theorem sum_eval (t0 : Tensor ℚ) (hs : t0.shape = [1, 2, 8]) (hn : t0.data.size = 16) :
    ∃ t : Tensor ℚ, sumOp 1 t0 = some t ∧ t.shape = [1, 8] ∧ t.data.size = 8 ∧
      ∀ m < 8, t.get m = t0.get m + t0.get (8 + m) := by
  unfold sumOp
  simp only [hs, hn, normDim, shapeSize]
  simp
  intro m hm
  rw [get_range_map _ _ _ m hm]
  have h2 : List.range 2 = [0, 1] := rfl
  rw [h2]
  simp [Nat.div_eq_of_lt hm, Nat.mod_eq_of_lt hm]

theorem linear_eval (W t : Tensor ℚ) (o n : Nat) (hW : W.shape = [o, n]) (hWn : W.data.size = o * n)
    (ht : t.shape = [1, n]) (htn : t.data.size = n) :
    ∃ t' : Tensor ℚ, linearOp W none t = some t' ∧ t'.shape = [1, o] ∧ t'.data.size = o ∧
      ∀ j < o, t'.get j = ((List.range n).map fun i => W.get (j * n + i) * t.get i).sum := by
  unfold linearOp
  simp only [hW, ht, hWn, htn, shapeSize]
  simp
  intro j hj
  rw [get_range_map _ _ _ j hj]
  simp [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]

theorem sum8_ite (g : Nat → ℚ) (a : Nat) (ha : a < 8) :
    ((List.range 8).map fun m => g m * (if a = m then (1 : ℚ) else 0)).sum = g a := by
  have h8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  rw [h8]
  interval_cases a <;> simp

theorem entry_eq (w : Weights ℚ) (E L U : Tensor ℚ) (hE : List.lookup "embedding.weight" w = some E)
    (hL : List.lookup "linear.weight" w = some L) (hU : List.lookup "unembedding.weight" w = some U)
    (a b : Nat) (ha : a < 8) (hb : b < 8) (j : Nat) :
    ((List.range 4).map fun i => U.get (j * 4 + i) *
      ((List.range 4).map fun k => L.get (i * 4 + k) *
        ((List.range 8).map fun m => E.get (k * 8 + m) *
          ((if a = m then (1 : ℚ) else 0) + (if b = m then 1 else 0))).sum).sum).sum =
    logit w a j + logit w b j := by
  simp only [logit, hid, wget, hE, hL, hU, mul_add, List.sum_map_add, sum8_ite _ a ha, sum8_ite _ b hb]

theorem net_eval (w : Weights ℚ) (hw : WF w) (a b : Nat) (ha : a < 8) (hb : b < 8) :
    ∃ out : Tensor ℚ, evalGraph graph w [a, b] = some out ∧ out.shape = [1, 8] ∧
      out.data.size = 8 ∧ ∀ j < 8, out.get j = logit w a j + logit w b j := by
  obtain ⟨E, hE, hEs, hEn⟩ := hw.E
  obtain ⟨L, hL, hLs, hLn⟩ := hw.L
  obtain ⟨U, hU, hUs, hUn⟩ := hw.U
  obtain ⟨t0, h0, h0s, h0n, h0e⟩ := oneHot_eval a b ha hb
  obtain ⟨t1, h1, h1s, h1n, h1e⟩ := sum_eval t0 h0s h0n
  obtain ⟨t2, h2, h2s, h2n, h2e⟩ := linear_eval E t1 4 8 hEs hEn h1s h1n
  obtain ⟨t3, h3, h3s, h3n, h3e⟩ := linear_eval L t2 4 4 hLs hLn h2s h2n
  obtain ⟨t4, h4, h4s, h4n, h4e⟩ := linear_eval U t3 8 4 hUs hUn h3s h3n
  refine ⟨t4, ?_, h4s, h4n, ?_⟩
  · have e0 : evalOp graph w [a, b] #[] .input = some t0 := h0
    have e1 : evalOp graph w [a, b] #[t0] (.sum 0 1) = some t1 := h1
    have e2 : evalOp graph w [a, b] #[t0, t1] (.linear 1 "embedding.weight" none) = some t2 := by
      simp only [evalOp, hE]
      exact h2
    have e3 : evalOp graph w [a, b] #[t0, t1, t2] (.linear 2 "linear.weight" none) = some t3 := by
      simp only [evalOp, hL]
      exact h3
    have e4 : evalOp graph w [a, b] #[t0, t1, t2, t3] (.linear 3 "unembedding.weight" none) = some t4 := by
      simp only [evalOp, hU]
      exact h4
    simp only [evalGraph, graph_nodes, graph_output, evalOps, e0, List.push_toArray, List.nil_append,
      List.cons_append, e1, e2, e3, e4]
    all_goals rfl
  · intro j hj
    rw [h4e j hj]
    have H3 : ∀ i < 4, t3.get i = ((List.range 4).map fun k => L.get (i * 4 + k) *
        ((List.range 8).map fun m => E.get (k * 8 + m) *
          ((if a = m then (1 : ℚ) else 0) + (if b = m then 1 else 0))).sum).sum := by
      intro i hi
      rw [h3e i hi]
      apply congrArg
      apply List.map_congr_left
      intro k hk
      simp only [List.mem_range] at hk
      rw [h2e k hk]
      apply congrArg
      apply congrArg
      apply List.map_congr_left
      intro m hm
      simp only [List.mem_range] at hm
      rw [h1e m hm, (h0e m hm).1, (h0e m hm).2]
    have H4 : ((List.range 4).map fun i => U.get (j * 4 + i) * t3.get i).sum =
        ((List.range 4).map fun i => U.get (j * 4 + i) *
          ((List.range 4).map fun k => L.get (i * 4 + k) *
            ((List.range 8).map fun m => E.get (k * 8 + m) *
              ((if a = m then (1 : ℚ) else 0) + (if b = m then 1 else 0))).sum).sum).sum := by
      apply congrArg
      apply List.map_congr_left
      intro i hi
      simp only [List.mem_range] at hi
      rw [H3 i hi]
    rw [H4]
    exact entry_eq w E L U hE hL hU a b ha hb j

theorem correct_of_margins (w : Weights ℚ) (hw : WF w) (a b : Nat) (ha : a < 8) (hb : b < 8)
    (hm : ∀ j < 8, j ≠ max a b →
      logit w a j + logit w b j < logit w a (max a b) + logit w b (max a b)) :
    Correct graph w task [a, b] := by
  obtain ⟨out, hout, hs, hn, he⟩ := net_eval w hw a b ha hb
  refine ⟨out.map (fun q : ℚ => (q : ℝ)), realOutput_of_evalGraph hout, ?_, ?_, ?_⟩
  · simp [Tensor.map, hs, hn]
  · simp only [Tensor.map_data_size, hn, label_pair]
    omega
  · intro j hj hne
    simp only [Tensor.map_data_size, hn] at hj
    rw [label_pair] at hne ⊢
    rw [Tensor.get_map_cast, Tensor.get_map_cast, he j hj, he (max a b) (by omega)]
    exact_mod_cast hm j hj hne

/-! ## The tests imply correctness -/

theorem diag_correct (w : Weights ℚ) (hw : WF w) (m : Nat) (hm : m < 8)
    (h : 0 < (colVal w m).getD m 0 - maxOthersVal (colVal w m) m) : Correct graph w task [m, m] := by
  apply correct_of_margins w hw m m hm hm
  intro j hj hne
  simp only [max_self] at hne ⊢
  have h1 := le_maxOthersVal (colVal w m) m j hj hne
  rw [colVal_getD w m j hj] at h1
  rw [colVal_getD w m m hm] at h
  linarith

theorem top_ge (w : Weights ℚ) (a j : Nat) (hj : j < 8) :
    logit w a j ≤ max (maxOthersVal (colVal w a) a) ((colVal w a).getD a 0) := by
  by_cases hja : j = a
  · subst hja
    rw [colVal_getD w j j hj]
    exact le_max_right _ _
  · have := le_maxOthersVal (colVal w a) a j hj hja
    rw [colVal_getD w a j hj] at this
    exact le_trans this (le_max_left _ _)

theorem mx_ge (w : Weights ℚ) (a j : Nat) (hj : j < 8) (hne : j ≠ a) :
    logit w a j ≤ maxOthersVal (colVal w a) a := by
  have := le_maxOthersVal (colVal w a) a j hj hne
  rwa [colVal_getD w a j hj] at this

theorem pair_correct (w : Weights ℚ) (hw : WF w) (a m : Nat) (ham : a < m) (hm : m < 8)
    (h : max (maxOthersVal (colVal w a) a) ((colVal w a).getD a 0) - (colVal w a).getD m 0 <
      (colVal w m).getD m 0 - maxOthersVal (colVal w m) m) :
    Correct graph w task [a, m] ∧ Correct graph w task [m, a] ∧ Correct graph w task [m, m] := by
  have ha : a < 8 := by omega
  rw [colVal_getD w a m hm, colVal_getD w m m hm] at h
  have hmax1 : max a m = m := Nat.max_eq_right ham.le
  have hmax2 : max m a = m := Nat.max_eq_left ham.le
  have hmar : ∀ j < 8, j ≠ m → logit w a j + logit w m j < logit w a m + logit w m m := by
    intro j hj hne
    have h1 := top_ge w a j hj
    have h2 := mx_ge w m j hj hne
    linarith
  refine ⟨?_, ?_, ?_⟩
  · apply correct_of_margins w hw a m ha hm
    rw [hmax1]
    exact hmar
  · apply correct_of_margins w hw m a hm ha
    rw [hmax2]
    intro j hj hne
    have := hmar j hj hne
    linarith
  · apply diag_correct w hw m hm
    rw [colVal_getD w m m hm]
    have := top_ge w a m hm
    linarith

theorem rpair_correct (w : Weights ℚ) (hw : WF w) (a m : Nat) (ham : a < m) (hm : m < 8)
    (h1 : maxOthersVal (colVal w a) a - (colVal w a).getD m 0 <
      (colVal w m).getD m 0 - maxOthersVal (colVal w m) m)
    (h2 : (colVal w a).getD a 0 - (colVal w a).getD m 0 <
      (colVal w m).getD m 0 - (colVal w m).getD a 0) :
    Correct graph w task [a, m] ∧ Correct graph w task [m, a] := by
  have ha : a < 8 := by omega
  rw [colVal_getD w a m hm, colVal_getD w m m hm] at h1
  rw [colVal_getD w a m hm, colVal_getD w m m hm, colVal_getD w a a ha, colVal_getD w m a ha] at h2
  have hmax1 : max a m = m := Nat.max_eq_right ham.le
  have hmax2 : max m a = m := Nat.max_eq_left ham.le
  have hmar : ∀ j < 8, j ≠ m → logit w a j + logit w m j < logit w a m + logit w m m := by
    intro j hj hne
    by_cases hja : j = a
    · subst hja
      linarith
    · have e1 := mx_ge w a j hj hja
      have e2 := mx_ge w m j hj hne
      linarith
  refine ⟨?_, ?_⟩
  · apply correct_of_margins w hw a m ha hm
    rw [hmax1]
    exact hmar
  · apply correct_of_margins w hw m a hm ha
    rw [hmax2]
    intro j hj hne
    have := hmar j hj hne
    linarith

theorem exact_correct (w : Weights ℚ) (hw : WF w) (a m : Nat) (ham : a < m) (hm : m < 8)
    (h : maxOthersVal (addVal (colVal w a) (colVal w m)) m < (addVal (colVal w a) (colVal w m)).getD m 0) :
    Correct graph w task [a, m] ∧ Correct graph w task [m, a] := by
  have ha : a < 8 := by omega
  have hget : ∀ j < 8, (addVal (colVal w a) (colVal w m)).getD j 0 = logit w a j + logit w m j := by
    intro j hj
    rw [addVal_getD _ _ j (by rw [colVal_length]; exact hj) (by rw [colVal_length]; exact hj),
      colVal_getD w a j hj, colVal_getD w m j hj]
  rw [hget m hm] at h
  have hmax1 : max a m = m := Nat.max_eq_right ham.le
  have hmax2 : max m a = m := Nat.max_eq_left ham.le
  have hmar : ∀ j < 8, j ≠ m → logit w a j + logit w m j < logit w a m + logit w m m := by
    intro j hj hne
    have e1 := le_maxOthersVal (addVal (colVal w a) (colVal w m)) m j hj hne
    rw [hget j hj] at e1
    linarith
  refine ⟨?_, ?_⟩
  · apply correct_of_margins w hw a m ha hm
    rw [hmax1]
    exact hmar
  · apply correct_of_margins w hw m a hm ha
    rw [hmax2]
    intro j hj hne
    have := hmar j hj hne
    linarith

/-! ## Well-formedness from the guard -/

structure Shapes (w : Weights ℚ) : Prop where
  E : ∃ t, List.lookup "embedding.weight" w = some t ∧ t.shape = [4, 8]
  L : ∃ t, List.lookup "linear.weight" w = some t ∧ t.shape = [4, 4]
  U : ∃ t, List.lookup "unembedding.weight" w = some t ∧ t.shape = [8, 4]

theorem linearOp_size {W t v : Tensor ℚ} (h : linearOp W none t = some v) :
    W.data.size = W.shape.getD 0 0 * W.shape.getD 1 0 := by
  unfold linearOp at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.1.1.2
  · cases h

theorem evalOps_linear {g : Graph} {w : Weights ℚ} {x : Input} :
    ∀ {ops : List Op} {vals out : Array (Tensor ℚ)}, evalOps g w x ops vals = some out →
      ∀ a wn, (Op.linear a wn none) ∈ ops →
        ∃ W, List.lookup wn w = some W ∧ W.data.size = W.shape.getD 0 0 * W.shape.getD 1 0
  | [], _, _, _, _, _, hmem => absurd hmem List.not_mem_nil
  | op :: ops, vals, out, h, a, wn, hmem => by
    simp only [evalOps] at h
    split at h
    · rename_i v hv
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · simp only [evalOp] at hv
        split at hv
        · rename_i t W _ hW
          exact ⟨W, hW, linearOp_size hv⟩
        · cases hv
      · exact evalOps_linear h a wn hmem'
    · cases h

theorem wf_of_single (w : Weights ℚ) (hs : Shapes w) (x : Input) (h : singleOk graph w task x = true) :
    WF w := by
  unfold singleOk at h
  split at h
  · rename_i out hout
    unfold evalGraph at hout
    split at hout
    · rename_i vals hv
      obtain ⟨tE, hE, hEs⟩ := hs.E
      obtain ⟨tL, hL, hLs⟩ := hs.L
      obtain ⟨tU, hU, hUs⟩ := hs.U
      obtain ⟨WE, hWE, hWEn⟩ := evalOps_linear hv 1 "embedding.weight" (by rw [graph_nodes]; simp)
      obtain ⟨WL, hWL, hWLn⟩ := evalOps_linear hv 2 "linear.weight" (by rw [graph_nodes]; simp)
      obtain ⟨WU, hWU, hWUn⟩ := evalOps_linear hv 3 "unembedding.weight" (by rw [graph_nodes]; simp)
      rw [hE, Option.some.injEq] at hWE
      rw [hL, Option.some.injEq] at hWL
      rw [hU, Option.some.injEq] at hWU
      subst hWE hWL hWU
      refine ⟨⟨tE, hE, hEs, ?_⟩, ⟨tL, hL, hLs, ?_⟩, ⟨tU, hU, hUs, ?_⟩⟩
      · rw [hWEn, hEs]; rfl
      · rw [hWLn, hLs]; rfl
      · rw [hWUn, hUs]; rfl
    · cases hout
  · cases h

/-! ## Partial correctness of counted computations -/

def Sem {α : Type} (env : Env) (m : CostM α) (P : α → Prop) : Prop :=
  ∀ c r c', m.run env c = some (r, c') → P r

theorem Sem.pure {α : Type} {env : Env} {a : α} {P : α → Prop} (h : P a) :
    Sem env (pure a) P := by
  intro c r c' hr
  simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
  exact hr.1 ▸ h

theorem Sem.bind {α β : Type} {env : Env} {x : CostM α} {f : α → CostM β} {P : α → Prop}
    {R : β → Prop} (hx : Sem env x P) (hf : ∀ a, P a → Sem env (f a) R) : Sem env (x >>= f) R := by
  intro c r c' hr
  rw [CostM.run_bind] at hr
  split at hr
  · rename_i a c1 ha
    exact hf a (hx c a c1 ha) c1 r c' hr
  · cases hr

theorem Sem.mono {α : Type} {env : Env} {x : CostM α} {P R : α → Prop} (hx : Sem env x P)
    (h : ∀ a, P a → R a) : Sem env x R :=
  fun c r c' hr => h r (hx c r c' hr)

theorem sem_weight (env : Env) (name : String) (i : Nat) :
    Sem env (CostM.weight name i) (fun r => r.val = wget env.weights name i) := by
  intro c r c' h
  simp only [CostM.weight] at h
  split at h
  · rename_i t ht
    split at h
    · rename_i hi
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      simp only [wget, ht, Tensor.get]
      rw [getElem!_pos t.data i hi, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
      rfl
    · cases h
  · cases h

theorem sem_weightShape (env : Env) (name : String) :
    Sem env (CostM.weightShape name)
      (fun s => ∃ t, List.lookup name env.weights = some t ∧ t.shape = s) := by
  intro c r c' h
  simp only [CostM.weightShape] at h
  split at h
  · rename_i t ht
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨t, ht, h.1⟩
  · cases h

theorem sem_muladd (env : Env) (cat : String) (acc a b : Q) :
    Sem env (CostM.qmuladd cat acc a b) (fun r => r.val = acc.val + a.val * b.val) := by
  intro c r c' h
  simp only [CostM.qmuladd, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.1]

theorem sem_add (env : Env) (cat : String) (a b : Q) :
    Sem env (CostM.qadd cat a b) (fun r => r.val = a.val + b.val) := by
  intro c r c' h
  simp only [CostM.qadd, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.1]

theorem sem_sub (env : Env) (cat : String) (a b : Q) :
    Sem env (CostM.qsub cat a b) (fun r => r.val = a.val - b.val) := by
  intro c r c' h
  simp only [CostM.qsub, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.1]

theorem sem_max (env : Env) (cat : String) (a b : Q) :
    Sem env (CostM.qmax cat a b) (fun r => r.val = max a.val b.val) := by
  intro c r c' h
  simp only [CostM.qmax, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.1]

theorem sem_lt (env : Env) (cat : String) (a b : Q) :
    Sem env (CostM.qlt cat a b) (fun r => r = decide (a.val < b.val)) := by
  intro c r c' h
  simp only [CostM.qlt, Option.some.injEq, Prod.mk.injEq] at h
  exact h.1.symm

theorem sem_select (env : Env) (cat : String) (b : Bool) (x y : Q) :
    Sem env (Interp.counting.selectV cat b x y) (fun r => r = cond b x y) := by
  intro c r c' h
  rw [Interp.counting_selectV_run] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact h.1.symm

theorem sem_band (env : Env) (cat : String) (a b : Bool) :
    Sem env (Interp.counting.band cat a b) (fun r => r = (a && b)) := by
  intro c r c' h
  rw [Interp.counting_band_run] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact h.1.symm

theorem sem_single (env : Env) (g : Graph) (t : Task) (x : Input) :
    Sem env (CostM.single g t x) (fun b => b = true → singleOk g env.weights t x = true) := by
  intro c r c' h hb
  subst hb
  exact CostM.single_spec h

/-! ## The loops -/

theorem sem_dotRow (env : Env) (name : String) (base : Nat) :
    ∀ (vs : List Q) (i : Nat) (acc : Q),
      Sem env (dotRow Interp.counting name base vs i acc)
        (fun r => r.val = dotVal env.weights name base (vs.map Q.val) i acc.val)
  | [], i, acc => by
    simp only [dotRow, Interp.counting_pure, List.map_nil, dotVal]
    exact Sem.pure rfl
  | v :: vs, i, acc => by
    simp only [dotRow, Interp.counting_bind, List.map_cons, dotVal]
    refine Sem.bind (sem_weight env name (base + i)) fun x hx => ?_
    refine Sem.bind (sem_muladd env "mac" acc x v) fun acc' hacc' => ?_
    refine (sem_dotRow env name base vs (i + 1) acc').mono fun r hr => ?_
    rw [hr, hacc', hx]

theorem sem_rows (env : Env) (name : String) (n : Nat) (v : List Q) :
    ∀ (rs : List Nat),
      Sem env (rows Interp.counting name n v rs)
        (fun r => r.map Q.val = rowsVal env.weights name n (v.map Q.val) rs)
  | [] => by
    simp only [rows, Interp.counting_pure, rowsVal]
    exact Sem.pure rfl
  | r :: rs => by
    simp only [rows, Interp.counting_bind, Interp.counting_pure, rowsVal]
    refine Sem.bind (sem_dotRow env name (r * n) v 0 Interp.counting.zero) fun d hd => ?_
    refine Sem.bind (sem_rows env name n v rs) fun ds hds => ?_
    refine Sem.pure ?_
    simp only [List.map_cons, hds, hd]

theorem sem_readCol (env : Env) (a : Nat) :
    ∀ (is : List Nat),
      Sem env (readCol Interp.counting a is)
        (fun r => r.map Q.val = is.map fun i => wget env.weights "embedding.weight" (i * 8 + a))
  | [] => by
    simp only [readCol, Interp.counting_pure, List.map_nil]
    exact Sem.pure rfl
  | i :: is => by
    simp only [readCol, Interp.counting_bind, Interp.counting_pure]
    refine Sem.bind (sem_weight env "embedding.weight" (i * 8 + a)) fun x hx => ?_
    refine Sem.bind (sem_readCol env a is) fun xs hxs => ?_
    refine Sem.pure ?_
    simp only [List.map_cons, hxs, hx]

theorem sem_column (env : Env) (a : Nat) :
    Sem env (column Interp.counting a) (fun r => r.map Q.val = colVal env.weights a) := by
  simp only [column, Interp.counting_bind]
  refine Sem.bind (sem_readCol env a (List.range 4)) fun e he => ?_
  refine Sem.bind (sem_rows env "linear.weight" 4 e (List.range 4)) fun h hh => ?_
  refine (sem_rows env "unembedding.weight" 4 h (List.range 8)).mono fun r hr => ?_
  rw [hr, hh, he]
  rfl

theorem sem_maxFrom (env : Env) :
    ∀ (ys : List Q) (acc : Q),
      Sem env (maxFrom Interp.counting acc ys) (fun r => r.val = maxFromVal acc.val (ys.map Q.val))
  | [], acc => by
    simp only [maxFrom, Interp.counting_pure, List.map_nil, maxFromVal]
    exact Sem.pure rfl
  | y :: ys, acc => by
    simp only [maxFrom, Interp.counting_bind, List.map_cons, maxFromVal]
    refine Sem.bind (sem_max env "max" acc y) fun acc' hacc' => ?_
    refine (sem_maxFrom env ys acc').mono fun r hr => ?_
    rw [hr, hacc']

theorem sem_maxList (env : Env) :
    ∀ (ys : List Q), Sem env (maxList Interp.counting ys) (fun r => r.val = maxListVal (ys.map Q.val))
  | [] => by
    simp only [maxList, Interp.counting_pure, List.map_nil, maxListVal]
    exact Sem.pure rfl
  | y :: ys => by
    simp only [maxList, List.map_cons, maxListVal]
    exact sem_maxFrom env ys y

theorem sem_maxOthers (env : Env) (L : List Q) (a : Nat) :
    Sem env (maxOthers Interp.counting L a) (fun r => r.val = maxOthersVal (L.map Q.val) a) := by
  simp only [maxOthers, maxOthersVal]
  refine (sem_maxList env _).mono fun r hr => ?_
  rw [hr, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp, getD_val]

theorem sem_addLists (env : Env) :
    ∀ (xs ys : List Q),
      Sem env (addLists Interp.counting xs ys) (fun r => r.map Q.val = addVal (xs.map Q.val) (ys.map Q.val))
  | [], _ => by
    simp only [addLists, Interp.counting_pure, List.map_nil, addVal]
    exact Sem.pure rfl
  | _ :: _, [] => by
    simp only [addLists, Interp.counting_pure, List.map_nil, List.map_cons, addVal]
    exact Sem.pure rfl
  | x :: xs, y :: ys => by
    simp only [addLists, Interp.counting_bind, Interp.counting_pure, List.map_cons, addVal]
    refine Sem.bind (sem_add env "add" x y) fun z hz => ?_
    refine Sem.bind (sem_addLists env xs ys) fun zs hzs => ?_
    refine Sem.pure ?_
    simp only [List.map_cons, hzs, hz]

/-- What is known about a column's info. -/
def ColSem (env : Env) (G : Bool) (c : ColInfo Interp.counting) (a : Nat) : Prop :=
  c.col.map Q.val = colVal env.weights a ∧
  c.mx.val = maxOthersVal (colVal env.weights a) a ∧
  c.top.val = max c.mx.val ((colVal env.weights a).getD a 0) ∧
  c.dm.val = cond G ((colVal env.weights a).getD a 0 - c.mx.val) 0

theorem sem_colInfo (env : Env) (G : Bool) (a : Nat) :
    Sem env (colInfo Interp.counting G a) (fun c => ColSem env G c a) := by
  simp only [colInfo, Interp.counting_bind, Interp.counting_pure]
  refine Sem.bind (sem_column env a) fun col hcol => ?_
  refine Sem.bind (sem_maxOthers env col a) fun mx hmx => ?_
  refine Sem.bind (sem_max env "max" mx _) fun top htop => ?_
  refine Sem.bind (sem_sub env "sub" _ mx) fun dm0 hdm0 => ?_
  refine Sem.bind (sem_select env "sel" G dm0 _) fun dm hdm => ?_
  refine Sem.pure ?_
  refine ⟨hcol, ?_, ?_, ?_⟩
  · rw [hmx, hcol]
  · rw [htop, ← getD_val, hcol]
  · rw [hdm]
    cases G
    · rfl
    · simp only [Bool.cond_true]
      rw [hdm0, ← getD_val, hcol]

theorem sem_columns (env : Env) (G : Bool) :
    ∀ (cols : List Nat),
      Sem env (columns Interp.counting G cols)
        (fun cv => ∀ m, m ∈ cols → ∃ c, cv.lookup m = some c ∧ ColSem env G c m)
  | [] => by
    simp only [columns, Interp.counting_pure]
    exact Sem.pure (fun m h => absurd h List.not_mem_nil)
  | a :: as => by
    simp only [columns, Interp.counting_bind, Interp.counting_pure]
    refine Sem.bind (sem_colInfo env G a) fun c hc => ?_
    refine Sem.bind (sem_columns env G as) fun cs hcs => ?_
    refine Sem.pure ?_
    intro m hm
    by_cases ham : a = m
    · subst ham
      exact ⟨c, by simp [List.lookup_cons], hc⟩
    · rcases List.mem_cons.mp hm with rfl | hm'
      · exact absurd rfl ham
      · obtain ⟨c', hc', hcs'⟩ := hcs m hm'
        refine ⟨c', ?_, hcs'⟩
        have hne : (m == a) = false := beq_eq_false_iff_ne.mpr (Ne.symm ham)
        have hne' : (a == m) = false := beq_eq_false_iff_ne.mpr ham
        simp [List.lookup_cons, hne, hne', hc']

theorem sem_shapesOk (env : Env) :
    Sem env (shapesOk Interp.counting) (fun ok => ok = true → Shapes env.weights) := by
  simp only [shapesOk, Interp.counting_bind, Interp.counting_pure]
  refine Sem.bind (sem_weightShape env "embedding.weight") fun s1 hs1 => ?_
  refine Sem.bind (sem_weightShape env "linear.weight") fun s2 hs2 => ?_
  refine Sem.bind (sem_weightShape env "unembedding.weight") fun s3 hs3 => ?_
  refine Sem.pure ?_
  intro h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨t1, ht1, hs1⟩ := hs1
  obtain ⟨t2, ht2, hs2⟩ := hs2
  obtain ⟨t3, ht3, hs3⟩ := hs3
  exact ⟨⟨t1, ht1, hs1.trans h1⟩, ⟨t2, ht2, hs2.trans h2⟩, ⟨t3, ht3, hs3.trans h3⟩⟩

/-! ## The terms -/

open Classical in
theorem sem_runTerm (env : Env) (G : Bool) (cv : List (Nat × ColInfo Interp.counting)) (cols : List Nat)
    (hcv : ∀ m, m ∈ cols → ∃ c, cv.lookup m = some c ∧ ColSem env G c m)
    (hG : G = true → WF env.weights) (t : Term) (hok : termOk cols t = true) :
    Sem env (runTerm Interp.counting G cv t)
      (fun n => n ≤ t.inputs.countP fun x => decide (Correct graph env.weights task x)) := by
  cases t with
  | diag m =>
    simp only [termOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨c, hc, hcs⟩ := hcv m hok.2
    simp only [runTerm, Interp.counting_bind, Interp.counting_pure, hc, Option.getD_some]
    refine Sem.bind (sem_lt env "cmp" _ _) fun b hb => Sem.pure ?_
    try simp only [Interp.counting_nscale]
    cases b with
    | false => simp
    | true =>
      simp only [Bool.cond_true]
      have hpos : 0 < c.dm.val := of_decide_eq_true hb.symm
      cases G with
      | false => rw [hcs.2.2.2] at hpos; simp at hpos
      | true =>
        have hw := hG rfl
        rw [hcs.2.2.2, hcs.2.1] at hpos
        have hcor := diag_correct env.weights hw m hok.1 hpos
        simp [Term.inputs, hcor]
  | pair a m wd =>
    simp only [termOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨ham, hm⟩, hac⟩, hmc⟩ := hok
    obtain ⟨ca, hca, hcas⟩ := hcv a hac
    obtain ⟨cm, hcm, hcms⟩ := hcv m hmc
    simp only [runTerm, Interp.counting_bind, Interp.counting_pure, hca, hcm, Option.getD_some]
    refine Sem.bind (sem_sub env "sub" _ _) fun x hx => ?_
    refine Sem.bind (sem_lt env "cmp" _ _) fun b hb => Sem.pure ?_
    try simp only [Interp.counting_nscale]
    cases b with
    | false => simp
    | true =>
      simp only [Bool.cond_true]
      have hlt : x.val < cm.dm.val := of_decide_eq_true hb.symm
      have ecol : (ca.col.getD m ⟨0⟩).val = (colVal env.weights a).getD m 0 := by
        rw [← getD_val, hcas.1]
      rw [hx, hcas.2.2.1, ecol] at hlt
      have hge : (colVal env.weights a).getD m 0 ≤ max ca.mx.val ((colVal env.weights a).getD a 0) := by
        rw [hcas.2.1]
        exact le_trans (le_maxOthersVal _ a m hm (by omega)) (le_max_left _ _)
      cases G with
      | false =>
        rw [hcms.2.2.2] at hlt
        simp only [Bool.cond_false] at hlt
        linarith
      | true =>
        have hw := hG rfl
        rw [hcms.2.2.2, hcms.2.1, hcas.2.1] at hlt
        obtain ⟨h1, h2, h3⟩ := pair_correct env.weights hw a m ham hm hlt
        cases wd <;> simp [Term.inputs, h1, h2, h3]
  | rpair a m =>
    simp only [termOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨ham, hm⟩, hac⟩, hmc⟩ := hok
    obtain ⟨ca, hca, hcas⟩ := hcv a hac
    obtain ⟨cm, hcm, hcms⟩ := hcv m hmc
    simp only [runTerm, Interp.counting_bind, Interp.counting_pure, hca, hcm, Option.getD_some]
    refine Sem.bind (sem_sub env "sub" _ _) fun x hx => ?_
    refine Sem.bind (sem_lt env "cmp" _ _) fun b1 hb1 => ?_
    refine Sem.bind (sem_sub env "sub" _ _) fun y hy => ?_
    refine Sem.bind (sem_sub env "sub" _ _) fun z hz => ?_
    refine Sem.bind (sem_lt env "cmp" _ _) fun b2 hb2 => ?_
    refine Sem.bind (sem_band env "gate" b1 b2) fun b hb => Sem.pure ?_
    try simp only [Interp.counting_nscale]
    rw [hb]
    cases b1 with
    | false => simp
    | true =>
      cases b2 with
      | false => simp
      | true =>
        simp only [Bool.and_self, Bool.cond_true]
        have hlt1 : x.val < cm.dm.val := of_decide_eq_true hb1.symm
        have hlt2 : y.val < z.val := of_decide_eq_true hb2.symm
        have ecol1 : (ca.col.getD m ⟨0⟩).val = (colVal env.weights a).getD m 0 := by
          rw [← getD_val, hcas.1]
        have ecol2 : (ca.col.getD a ⟨0⟩).val = (colVal env.weights a).getD a 0 := by
          rw [← getD_val, hcas.1]
        have ecol3 : (cm.col.getD m ⟨0⟩).val = (colVal env.weights m).getD m 0 := by
          rw [← getD_val, hcms.1]
        have ecol4 : (cm.col.getD a ⟨0⟩).val = (colVal env.weights m).getD a 0 := by
          rw [← getD_val, hcms.1]
        rw [hx, hcas.2.1, ecol1] at hlt1
        rw [hy, hz, ecol1, ecol2, ecol3, ecol4] at hlt2
        have hge : (colVal env.weights a).getD m 0 ≤ maxOthersVal (colVal env.weights a) a :=
          le_maxOthersVal _ a m hm (by omega)
        cases G with
        | false =>
          rw [hcms.2.2.2] at hlt1
          simp only [Bool.cond_false] at hlt1
          linarith
        | true =>
          have hw := hG rfl
          rw [hcms.2.2.2, hcms.2.1] at hlt1
          obtain ⟨h1, h2⟩ := rpair_correct env.weights hw a m ham hm hlt1 hlt2
          simp [Term.inputs, h1, h2]
  | exact a m =>
    simp only [termOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨ham, hm⟩, hac⟩, hmc⟩ := hok
    obtain ⟨ca, hca, hcas⟩ := hcv a hac
    obtain ⟨cm, hcm, hcms⟩ := hcv m hmc
    simp only [runTerm, Interp.counting_bind, Interp.counting_pure, hca, hcm, Option.getD_some]
    refine Sem.bind (sem_addLists env _ _) fun s hs => ?_
    refine Sem.bind (sem_maxOthers env s m) fun mo hmo => ?_
    refine Sem.bind (sem_lt env "cmp" _ _) fun b0 hb0 => ?_
    refine Sem.bind (sem_band env "gate" G b0) fun b hb => Sem.pure ?_
    try simp only [Interp.counting_nscale]
    rw [hb]
    cases G with
    | false => simp
    | true =>
      cases b0 with
      | false => simp
      | true =>
        simp only [Bool.and_self, Bool.cond_true]
        have hw := hG rfl
        have hlt : mo.val < (s.getD m ⟨0⟩).val := of_decide_eq_true hb0.symm
        rw [hmo, ← getD_val, hs, hcas.1, hcms.1] at hlt
        obtain ⟨h1, h2⟩ := exact_correct env.weights hw a m ham hm hlt
        simp [Term.inputs, h1, h2]

open Classical in
theorem sem_runTerms (env : Env) (G : Bool) (cv : List (Nat × ColInfo Interp.counting)) (cols : List Nat)
    (hcv : ∀ m, m ∈ cols → ∃ c, cv.lookup m = some c ∧ ColSem env G c m)
    (hG : G = true → WF env.weights) :
    ∀ (ts : List Term), (∀ t ∈ ts, termOk cols t = true) →
      Sem env (runTerms Interp.counting G cv ts)
        (fun n => n ≤ (ts.flatMap Term.inputs).countP fun x => decide (Correct graph env.weights task x))
  | [], _ => by
    simp only [runTerms, Interp.counting_pure]
    exact Sem.pure (by simp)
  | t :: ts, hall => by
    simp only [runTerms, Interp.counting_bind, Interp.counting_pure]
    refine Sem.bind (sem_runTerm env G cv cols hcv hG t (hall t (by simp))) fun n hn => ?_
    refine Sem.bind (sem_runTerms env G cv cols hcv hG ts (fun t' ht' => hall t' (by simp [ht'])))
      fun ns hns => ?_
    refine Sem.pure ?_
    simp only [List.flatMap_cons, List.countP_append]
    exact Nat.add_le_add hn hns

open Classical in
theorem guard_count (w : Weights ℚ) (g : Nat × Nat) (h : singleOk graph w task [g.1, g.2] = true) :
    (guardInputs g).length ≤ (guardInputs g).countP fun x => decide (Correct graph w task x) := by
  have h1 : Correct graph w task [g.1, g.2] := singleOk_correct graph w task _ h
  have h2 : Correct graph w task [g.2, g.1] :=
    singleOk_correct graph w task _ (singleOk_perm sym_graph rfl (List.Perm.swap g.2 g.1 []) h)
  unfold guardInputs
  split <;> simp [h1, h2]

theorem task_space : task.space = [8, 8] := rfl

open Classical in
theorem sem_runPlan (env : Env) (p : Plan) (hp : planOk p = true) :
    Sem env (runPlan Interp.counting p) (fun n => n ≤ numCorrect graph env.weights task) := by
  simp only [planOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hp
  obtain ⟨⟨⟨⟨_, _⟩, hterms⟩, hsub⟩, hnodup⟩ := hp
  simp only [runPlan, Interp.counting_bind, Interp.counting_pure]
  refine Sem.bind (sem_shapesOk env) fun ok hok => ?_
  cases ok with
  | false =>
    exact Sem.pure (Nat.zero_le _)
  | true =>
    refine Sem.bind (sem_single env graph task _) fun G hGs => ?_
    have hG : G = true → WF env.weights := fun h => wf_of_single env.weights (hok rfl) _ (hGs h)
    refine Sem.bind (sem_columns env G p.cols) fun cv hcv => ?_
    refine Sem.bind (sem_runTerms env G cv p.cols hcv hG p.terms hterms) fun n hn => ?_
    refine Sem.pure ?_
    try simp only [Interp.counting_nadd, Interp.counting_nscale]
    have hguard : cond G (guardInputs p.guard).length 0 ≤
        (guardInputs p.guard).countP fun x => decide (Correct graph env.weights task x) := by
      cases G with
      | false => exact Nat.zero_le _
      | true => exact guard_count env.weights p.guard (hGs rfl)
    have hall : cond G (guardInputs p.guard).length 0 + n ≤
        p.inputs.countP fun x => decide (Correct graph env.weights task x) := by
      unfold Plan.inputs
      rw [List.countP_append]
      exact Nat.add_le_add hguard hn
    unfold numCorrect
    rw [task_space]
    have hsp : p.inputs.Subperm (allInputs [8, 8]) := List.subperm_of_subset hnodup hsub
    exact le_trans hall (hsp.countP_le _)

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  exact sem_runPlan ⟨w, c⟩ thePlan thePlan_ok [] n cost h

/-! ## Specific layer -/

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (64, 639) := by
  decide +kernel

theorem performance : Target := by
  show claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 64 cost h

end Candidate.Full64
