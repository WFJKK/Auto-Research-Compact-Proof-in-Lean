import Protected.N_max2_tiny_v8_s0_c38
import CompactCheck.Soundness
import CompactCheck.CountedOps
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# 38 inputs of max2_tiny-v8-s0 from six columns of the product matrix

The network is linear: its logits on `[a, b]` are column `a` plus column `b` of `M = U L E`. The checker
computes six columns of `M` (48 operations each), the maximum `mx` of each column off its diagonal entry,
the column maximum `top`, and the guarded diagonal margin `dm = M[m,m] - mx_m` (zero unless the guarding
`single` passed). The diagonal input `[m, m]` is certified by `0 < dm_m`; a pair `[a, m]`, `[m, a]`
(`a < m`) by `top_a - M[m,a] < dm_m` (2 operations, and it implies `[m, m]` too) or by the refined test
`mx_a - M[m,a] < dm_m ∧ M[a,a] - M[m,a] < M[m,m] - M[a,m]` (6 operations). One `single` on `[5, 6]` guards
the well-formedness of the weights and counts its two inputs.
-/

namespace Candidate.Col38

open CompactCheck Protected.N_max2_tiny_v8_s0_c38

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
  | rpair (a m : Nat) (wd : Bool)

def Term.inputs : Term → List Input
  | .diag m => [[m, m]]
  | .pair a m wd => if wd then [[a, m], [m, a], [m, m]] else [[a, m], [m, a]]
  | .rpair a m wd => if wd then [[a, m], [m, a], [m, m]] else [[a, m], [m, a]]

def runTerm (I : Interp) (cv : List (Nat × ColInfo I)) : Term → I.M I.N
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
  | .rpair a m wd => do
    let ca := (cv.lookup a).getD (defaultInfo I)
    let cm := (cv.lookup m).getD (defaultInfo I)
    let x ← I.sub "sub" ca.mx (ca.col.getD m I.zero)
    let b1 ← I.lt "cmp" x cm.dm
    let y ← I.sub "sub" (ca.col.getD a I.zero) (ca.col.getD m I.zero)
    let z ← I.sub "sub" (cm.col.getD m I.zero) (cm.col.getD a I.zero)
    let b2 ← I.lt "cmp" y z
    let b ← I.band "gate" b1 b2
    pure (I.nscale (if wd then 3 else 2) b)

def runTerms (I : Interp) (cv : List (Nat × ColInfo I)) : List Term → I.M I.N
  | [] => pure I.nzero
  | t :: ts => do
    let n ← runTerm I cv t
    let ns ← runTerms I cv ts
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
    let n ← runTerms I cv p.terms
    pure (I.nadd (I.nscale (guardInputs p.guard).length G) n)
  else pure I.nzero

def thePlan : Plan where
  cols := [0, 1, 2, 3, 4, 7]
  guard := (5, 6)
  terms := [.diag 0,
    .pair 0 1 true, .pair 1 2 true, .rpair 0 3 true, .pair 0 4 true, .pair 0 7 true,
    .pair 1 4 false, .pair 1 7 false, .pair 2 4 false, .pair 2 7 false, .pair 3 4 false,
    .pair 4 7 false,
    .rpair 0 2 false, .rpair 1 3 false, .rpair 2 3 false, .rpair 3 7 false]

def D : Checker := fun I => runPlan I thePlan

/-! ## Plans that count correctly (proof side only) -/

def Plan.inputs (p : Plan) : List Input := guardInputs p.guard ++ p.terms.flatMap Term.inputs

def termOk (cols : List Nat) : Term → Bool
  | .diag m => decide (m < 8) && decide (m ∈ cols)
  | .pair a m _ => decide (a < m) && decide (m < 8) && decide (a ∈ cols) && decide (m ∈ cols)
  | .rpair a m _ => decide (a < m) && decide (m < 8) && decide (a ∈ cols) && decide (m ∈ cols)

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

theorem colVal_getD (w : Weights ℚ) (a j : Nat) (hj : j < 8) : (colVal w a).getD j 0 = logit w a j := by
  have h4 : List.range 4 = [0, 1, 2, 3] := rfl
  have h8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  simp only [colVal, logit, hid, h4, h8, List.map_cons, List.map_nil, rowsVal, dotVal,
    List.sum_cons, List.sum_nil]
  interval_cases j <;> simp <;> ring

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

theorem sem_single (env : Env) (g : Graph) (tk : Task) (x : Input) :
    Sem env (CostM.single g tk x) (fun b => b = true → singleOk g env.weights tk x = true) := by
  intro c r c' h hb
  subst hb
  exact CostM.single_spec h

theorem sem_dotRow (env : Env) (name : String) (base : Nat) : ∀ (vs : List Q) (i : Nat) (acc : Q),
    Sem env (dotRow Interp.counting name base vs i acc)
      (fun r => r.val = dotVal env.weights name base (vs.map Q.val) i acc.val)
  | [], i, acc => by
    simp only [dotRow, dotVal, List.map_nil, Interp.counting_pure]
    exact Sem.pure rfl
  | v :: vs, i, acc => by
    simp only [dotRow, Interp.counting_bind]
    refine Sem.bind (sem_weight env name (base + i)) fun x hx => ?_
    refine Sem.bind (sem_muladd env "mac" acc x v) fun acc' hacc => ?_
    refine (sem_dotRow env name base vs (i + 1) acc').mono fun r hr => ?_
    simp only [dotVal, List.map_cons]
    rw [hr, hacc, hx]

theorem sem_rows (env : Env) (name : String) (n : Nat) (v : List Q) : ∀ (rs : List Nat),
    Sem env (rows Interp.counting name n v rs)
      (fun L => L.map Q.val = rowsVal env.weights name n (v.map Q.val) rs)
  | [] => by
    simp only [rows, rowsVal, Interp.counting_pure]
    exact Sem.pure rfl
  | r :: rs => by
    simp only [rows, Interp.counting_bind]
    refine Sem.bind (sem_dotRow env name (r * n) v 0 ⟨0⟩) fun d hd => ?_
    refine Sem.bind (sem_rows env name n v rs) fun ds hds => ?_
    refine Sem.pure ?_
    simp only [List.map_cons, rowsVal, hds, hd]

theorem sem_readCol (env : Env) (a : Nat) : ∀ (is : List Nat),
    Sem env (readCol Interp.counting a is)
      (fun L => L.map Q.val = is.map fun i => wget env.weights "embedding.weight" (i * 8 + a))
  | [] => by
    simp only [readCol, List.map_nil, Interp.counting_pure]
    exact Sem.pure rfl
  | i :: is => by
    simp only [readCol, Interp.counting_bind]
    refine Sem.bind (sem_weight env "embedding.weight" (i * 8 + a)) fun x hx => ?_
    refine Sem.bind (sem_readCol env a is) fun xs hxs => ?_
    refine Sem.pure ?_
    simp only [List.map_cons, hxs, hx]

theorem sem_column (env : Env) (a : Nat) :
    Sem env (column Interp.counting a) (fun L => L.map Q.val = colVal env.weights a) := by
  simp only [column, Interp.counting_bind]
  refine Sem.bind (sem_readCol env a (List.range 4)) fun e he => ?_
  refine Sem.bind (sem_rows env "linear.weight" 4 e (List.range 4)) fun h hh => ?_
  refine (sem_rows env "unembedding.weight" 4 h (List.range 8)).mono fun L hL => ?_
  rw [hL, hh, he]
  rfl

theorem sem_maxFrom (env : Env) : ∀ (ys : List Q) (acc : Q),
    Sem env (maxFrom Interp.counting acc ys) (fun r => r.val = maxFromVal acc.val (ys.map Q.val))
  | [], acc => by
    simp only [maxFrom, maxFromVal, List.map_nil, Interp.counting_pure]
    exact Sem.pure rfl
  | y :: ys, acc => by
    simp only [maxFrom, Interp.counting_bind]
    refine Sem.bind (sem_max env "max" acc y) fun acc' hacc => ?_
    refine (sem_maxFrom env ys acc').mono fun r hr => ?_
    simp only [List.map_cons, maxFromVal]
    rw [hr, hacc]

theorem sem_maxList (env : Env) : ∀ (ys : List Q),
    Sem env (maxList Interp.counting ys) (fun r => r.val = maxListVal (ys.map Q.val))
  | [] => by
    simp only [maxList, maxListVal, List.map_nil, Interp.counting_pure]
    exact Sem.pure rfl
  | y :: ys => by
    simp only [maxList, maxListVal, List.map_cons]
    exact sem_maxFrom env ys y

theorem sem_maxOthers (env : Env) (L : List Q) (a : Nat) :
    Sem env (maxOthers Interp.counting L a) (fun r => r.val = maxOthersVal (L.map Q.val) a) := by
  unfold maxOthers maxOthersVal
  refine (sem_maxList env _).mono fun r hr => ?_
  rw [hr, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp]
  exact (getD_val L j).symm

structure ColSem (w : Weights ℚ) (G : Bool) (a : Nat) (ci : ColInfo Interp.counting) : Prop where
  col : ci.col.map Q.val = colVal w a
  mx : ci.mx.val = maxOthersVal (colVal w a) a
  top : ci.top.val = max (maxOthersVal (colVal w a) a) ((colVal w a).getD a 0)
  dm : ci.dm.val = cond G ((colVal w a).getD a 0 - maxOthersVal (colVal w a) a) 0

theorem sem_colInfo (env : Env) (G : Bool) (a : Nat) :
    Sem env (colInfo Interp.counting G a) (ColSem env.weights G a) := by
  simp only [colInfo, Interp.counting_bind]
  refine Sem.bind (sem_column env a) fun col hcol => ?_
  refine Sem.bind (sem_maxOthers env col a) fun mx hmx => ?_
  refine Sem.bind (sem_max env "max" mx _) fun top htop => ?_
  refine Sem.bind (sem_sub env "sub" _ mx) fun dm0 hdm0 => ?_
  refine Sem.bind (sem_select env "sel" G dm0 ⟨0⟩) fun dm hdm => ?_
  refine Sem.pure ?_
  have hd : (col.getD a ⟨0⟩).val = (colVal env.weights a).getD a 0 := by rw [← hcol, getD_val]
  refine ⟨hcol, by rw [hmx, hcol], by rw [htop, hmx, hcol, hd], ?_⟩
  rw [hdm]
  cases G
  · rfl
  · show dm0.val = _
    rw [hdm0, hmx, hcol, hd]
    rfl

theorem sem_columns (env : Env) (G : Bool) : ∀ (cols : List Nat),
    Sem env (columns Interp.counting G cols)
      (fun cv => ∀ a ∈ cols, ∃ ci, cv.lookup a = some ci ∧ ColSem env.weights G a ci)
  | [] => by
    simp only [columns, Interp.counting_pure]
    exact Sem.pure (by simp)
  | a :: as => by
    simp only [columns, Interp.counting_bind]
    refine Sem.bind (sem_colInfo env G a) fun c hc => ?_
    refine Sem.bind (sem_columns env G as) fun cs hcs => ?_
    refine Sem.pure ?_
    intro a' ha'
    by_cases h : a' = a
    · subst h
      exact ⟨c, by simp [List.lookup], hc⟩
    · obtain ⟨ci, hci, hsem⟩ := hcs a' (by simpa [h] using ha')
      refine ⟨ci, ?_, hsem⟩
      have hb : (a' == a) = false := beq_eq_false_iff_ne.mpr h
      simp [List.lookup, hb, hci]

def Shapes (w : Weights ℚ) : Prop :=
  (∃ t, List.lookup "embedding.weight" w = some t ∧ t.shape = [4, 8]) ∧
  (∃ t, List.lookup "linear.weight" w = some t ∧ t.shape = [4, 4]) ∧
  (∃ t, List.lookup "unembedding.weight" w = some t ∧ t.shape = [8, 4])

theorem sem_shapesOk (env : Env) :
    Sem env (shapesOk Interp.counting) (fun ok => ok = true → Shapes env.weights) := by
  simp only [shapesOk, Interp.counting_bind, Interp.counting_pure]
  refine Sem.bind (sem_weightShape env _) fun s1 hs1 => ?_
  refine Sem.bind (sem_weightShape env _) fun s2 hs2 => ?_
  refine Sem.bind (sem_weightShape env _) fun s3 hs3 => ?_
  refine Sem.pure fun hok => ?_
  obtain ⟨t1, h1, e1⟩ := hs1
  obtain ⟨t2, h2, e2⟩ := hs2
  obtain ⟨t3, h3, e3⟩ := hs3
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  exact ⟨⟨t1, h1, e1.trans hok.1.1⟩, ⟨t2, h2, e2.trans hok.1.2⟩, ⟨t3, h3, e3.trans hok.2⟩⟩

/-! ## The network on `[a, b]`: column `a` plus column `b` -/

structure WF (w : Weights ℚ) : Prop where
  E : ∃ t, List.lookup "embedding.weight" w = some t ∧ t.shape = [4, 8] ∧ t.data.size = 32
  L : ∃ t, List.lookup "linear.weight" w = some t ∧ t.shape = [4, 4] ∧ t.data.size = 16
  U : ∃ t, List.lookup "unembedding.weight" w = some t ∧ t.shape = [8, 4] ∧ t.data.size = 32

theorem get_map_range {s : List Nat} {n : Nat} {f : Nat → ℚ} {j : Nat} (hj : j < n) :
    Tensor.get ⟨s, (Array.range n).map f⟩ j = f j := by
  simp [Tensor.get, Array.getD_eq_getD_getElem?, hj]

def ind (a v : Nat) : ℚ := if a = v then 1 else 0

theorem ind_sum (f : Nat → ℚ) (a b : Nat) (ha : a < 8) (hb : b < 8) :
    ((List.range 8).map fun v => f v * (ind a v + ind b v)).sum = f a + f b := by
  have h8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  simp only [h8, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ind]
  interval_cases a <;> interval_cases b <;> simp <;> ring

theorem onehot_spec (a b : Nat) (ha : a < 8) (hb : b < 8) :
    ∃ t : Tensor ℚ, oneHotInput 2 8 [a, b] = some t ∧ t.shape = [1, 2, 8] ∧ t.data.size = 16 ∧
      ∀ i < 16, t.get i = if [a, b].getD (i / 8) 0 = i % 8 then 1 else 0 := by
  simp only [oneHotInput, List.length_cons, List.length_nil, List.all_cons, List.all_nil, ha, hb,
    decide_true, Bool.and_self, beq_self_eq_true, ite_true, Nat.reduceMul, Nat.reduceAdd]
  refine ⟨_, rfl, rfl, by simp, ?_⟩
  intro i hi
  rw [get_map_range hi]

theorem sum_spec (t : Tensor ℚ) (a b : Nat) (hs : t.shape = [1, 2, 8]) (hn : t.data.size = 16)
    (ht : ∀ i < 16, t.get i = if [a, b].getD (i / 8) 0 = i % 8 then 1 else 0) :
    ∃ r, sumOp 1 t = some r ∧ r.shape = [1, 8] ∧ r.data.size = 8 ∧
      ∀ v < 8, r.get v = ind a v + ind b v := by
  have h1 : normDim 1 3 = some 1 := rfl
  have h2 : shapeSize (List.take 1 [1, 2, 8]) = 1 := rfl
  have h3 : shapeSize (List.drop (1 + 1) [1, 2, 8]) = 8 := rfl
  have h4 : ([1, 2, 8] : List Nat).getD 1 0 = 2 := rfl
  have h5 : ([1, 2, 8] : List Nat).eraseIdx 1 = [1, 8] := rfl
  simp only [sumOp, hs, hn, List.length_cons, List.length_nil, Nat.reduceAdd, h1, h2, h3, h4, h5,
    Nat.reduceMul, Nat.one_mul, beq_self_eq_true, ite_true]
  refine ⟨_, rfl, rfl, by simp, ?_⟩
  intro v hv
  rw [get_map_range hv]
  have e1 : v / 8 = 0 := Nat.div_eq_of_lt hv
  have e2 : v % 8 = v := Nat.mod_eq_of_lt hv
  have e3 : (8 + v) / 8 = 1 := by omega
  have e4 : (8 + v) % 8 = v := by omega
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, e1, e2, Nat.zero_mul, Nat.zero_add, Nat.one_mul]
  rw [ht v (by omega), ht (8 + v) (by omega), e1, e2, e3, e4]
  simp [ind]

theorem linearOp_spec (W t : Tensor ℚ) (out inn : Nat) (hWs : W.shape = [out, inn])
    (hWn : W.data.size = out * inn) (hts : t.shape = [1, inn]) (htn : t.data.size = inn) :
    ∃ r, linearOp W none t = some r ∧ r.shape = [1, out] ∧ r.data.size = out ∧
      ∀ j < out, r.get j = ((List.range inn).map fun i => W.get (j * inn + i) * t.get i).sum := by
  have hl : ([1, inn] : List Nat).getLast? = some inn := rfl
  have hd : ([1, inn] : List Nat).dropLast = [1] := rfl
  have hp : shapeSize [1] = 1 := rfl
  simp only [linearOp, hWs, hts, hWn, htn, hl, hd, hp, List.getD_cons_zero, List.getD_cons_succ,
    Nat.one_mul, beq_self_eq_true, Bool.and_self, ite_true]
  refine ⟨_, rfl, rfl, by simp, ?_⟩
  intro j hj
  rw [get_map_range hj]
  simp [Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj]

theorem evalOps_cons (g : Graph) (w : Weights ℚ) (x : Input) (op : Op) (ops : List Op)
    (vals out : Array (Tensor ℚ)) :
    evalOps g w x (op :: ops) vals = some out ↔
      ∃ v, evalOp g w x vals op = some v ∧ evalOps g w x ops (vals.push v) = some out := by
  simp only [evalOps]
  cases evalOp g w x vals op <;> simp

theorem graph_nodes : graph.nodes = [.input, .sum 0 1, .linear 1 "embedding.weight" none,
    .linear 2 "linear.weight" none, .linear 3 "unembedding.weight" none] := rfl

theorem net_eval (w : Weights ℚ) (hw : WF w) (a b : Nat) (ha : a < 8) (hb : b < 8) :
    ∃ out : Tensor ℚ, evalGraph graph w [a, b] = some out ∧ out.shape = [1, 8] ∧
      out.data.size = 8 ∧ ∀ j < 8, out.get j = logit w a j + logit w b j := by
  obtain ⟨tE, hE, hEs, hEn⟩ := hw.E
  obtain ⟨tL, hL, hLs, hLn⟩ := hw.L
  obtain ⟨tU, hU, hUs, hUn⟩ := hw.U
  obtain ⟨t0, h0, h0s, h0n, h0g⟩ := onehot_spec a b ha hb
  obtain ⟨t1, h1, h1s, h1n, h1g⟩ := sum_spec t0 a b h0s h0n h0g
  obtain ⟨t2, h2, h2s, h2n, h2g⟩ := linearOp_spec tE t1 4 8 hEs hEn h1s h1n
  obtain ⟨t3, h3, h3s, h3n, h3g⟩ := linearOp_spec tL t2 4 4 hLs hLn h2s h2n
  obtain ⟨t4, h4, h4s, h4n, h4g⟩ := linearOp_spec tU t3 8 4 hUs hUn h3s h3n
  have hops : evalOps graph w [a, b] graph.nodes #[] = some #[t0, t1, t2, t3, t4] := by
    rw [graph_nodes, evalOps_cons]
    refine ⟨t0, h0, ?_⟩
    rw [evalOps_cons]
    refine ⟨t1, h1, ?_⟩
    rw [evalOps_cons]
    refine ⟨t2, ?_, ?_⟩
    · simp only [evalOp, hE]
      exact h2
    rw [evalOps_cons]
    refine ⟨t3, ?_, ?_⟩
    · simp only [evalOp, hL]
      exact h3
    rw [evalOps_cons]
    refine ⟨t4, ?_, ?_⟩
    · simp only [evalOp, hU]
      exact h4
    rfl
  refine ⟨t4, ?_, h4s, h4n, ?_⟩
  · simp only [evalGraph, hops]
    rfl
  · have hwE : ∀ i, wget w "embedding.weight" i = tE.get i := fun i => by simp [wget, hE]
    have hwL : ∀ i, wget w "linear.weight" i = tL.get i := fun i => by simp [wget, hL]
    have hwU : ∀ i, wget w "unembedding.weight" i = tU.get i := fun i => by simp [wget, hU]
    have e2 : ∀ k < 4, t2.get k = tE.get (k * 8 + a) + tE.get (k * 8 + b) := by
      intro k hk
      rw [h2g k hk]
      have hmap : ((List.range 8).map fun v => tE.get (k * 8 + v) * t1.get v) =
          (List.range 8).map fun v => tE.get (k * 8 + v) * (ind a v + ind b v) :=
        List.map_congr_left fun v hv => by rw [h1g v (List.mem_range.mp hv)]
      rw [hmap]
      exact ind_sum (fun v => tE.get (k * 8 + v)) a b ha hb
    have h4r : List.range 4 = [0, 1, 2, 3] := rfl
    have e3 : ∀ i < 4, t3.get i = hid w a i + hid w b i := by
      intro i hi
      rw [h3g i hi]
      simp only [hid, hwL, hwE, h4r, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        e2 0 (by norm_num), e2 1 (by norm_num), e2 2 (by norm_num), e2 3 (by norm_num)]
      ring
    intro j hj
    rw [h4g j hj]
    simp only [logit, hwU, h4r, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      e3 0 (by norm_num), e3 1 (by norm_num), e3 2 (by norm_num), e3 3 (by norm_num)]
    ring

theorem label_pair (a b : Nat) : task.label [a, b] = max a b := by
  show [a, b].foldl max 0 = max a b
  simp

theorem correct_of_margins (w : Weights ℚ) (hw : WF w) (a b : Nat) (ha : a < 8) (hb : b < 8)
    (hm : ∀ j < 8, j ≠ max a b →
      logit w a j + logit w b j < logit w a (max a b) + logit w b (max a b)) :
    Correct graph w task [a, b] := by
  obtain ⟨out, hout, hs, hn, hg⟩ := net_eval w hw a b ha hb
  refine ⟨out.map (fun q : ℚ => (q : ℝ)), realOutput_of_evalGraph hout, ?_, ?_, ?_⟩
  · rw [Tensor.map_shape', Tensor.map_data_size, hs, hn]
  · rw [Tensor.map_data_size, hn, label_pair]
    omega
  · intro j hj hne
    rw [Tensor.map_data_size, hn] at hj
    rw [label_pair] at hne ⊢
    rw [Tensor.get_map_cast, Tensor.get_map_cast, hg j hj, hg (max a b) (by omega)]
    exact_mod_cast hm j hj hne

theorem linearOp_size (W t v : Tensor ℚ) (h : linearOp W none t = some v) :
    W.data.size = W.shape.getD 0 0 * W.shape.getD 1 0 := by
  unfold linearOp at h
  simp only [Bool.and_true] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.1.2
  · cases h

theorem wf_of_single (w : Weights ℚ) (hs : Shapes w) (x : Input)
    (h : singleOk graph w task x = true) : WF w := by
  obtain ⟨⟨tE, hE, hEs⟩, ⟨tL, hL, hLs⟩, ⟨tU, hU, hUs⟩⟩ := hs
  unfold singleOk at h
  split at h
  · rename_i out hout
    unfold evalGraph at hout
    split at hout
    · rename_i vals hv
      rw [graph_nodes, evalOps_cons] at hv
      obtain ⟨t0, h0, hv⟩ := hv
      rw [evalOps_cons] at hv
      obtain ⟨t1, h1, hv⟩ := hv
      rw [evalOps_cons] at hv
      obtain ⟨t2, h2, hv⟩ := hv
      rw [evalOps_cons] at hv
      obtain ⟨t3, h3, hv⟩ := hv
      rw [evalOps_cons] at hv
      obtain ⟨t4, h4, _⟩ := hv
      simp only [evalOp, hE] at h2
      simp only [evalOp, hL] at h3
      simp only [evalOp, hU] at h4
      have e2 := linearOp_size tE t1 t2 h2
      have e3 := linearOp_size tL t2 t3 h3
      have e4 := linearOp_size tU t3 t4 h4
      rw [hEs] at e2
      rw [hLs] at e3
      rw [hUs] at e4
      exact ⟨⟨tE, hE, hEs, e2⟩, ⟨tL, hL, hLs, e3⟩, ⟨tU, hU, hUs, e4⟩⟩
    · cases hout
  · cases h

/-! ## Margins to correctness -/

def cvv (w : Weights ℚ) (a j : Nat) : ℚ := (colVal w a).getD j 0
def mxo (w : Weights ℚ) (a : Nat) : ℚ := maxOthersVal (colVal w a) a

theorem cvv_eq (w : Weights ℚ) (a j : Nat) (hj : j < 8) : cvv w a j = logit w a j :=
  colVal_getD w a j hj

theorem cvv_le_mxo (w : Weights ℚ) (a j : Nat) (hj : j < 8) (hne : j ≠ a) : cvv w a j ≤ mxo w a :=
  le_maxOthersVal _ a j hj hne

theorem diag_correct (w : Weights ℚ) (hw : WF w) (m : Nat) (hm : m < 8)
    (h : 0 < cvv w m m - mxo w m) : Correct graph w task [m, m] := by
  apply correct_of_margins w hw m m hm hm
  intro j hj hne
  rw [Nat.max_self] at hne ⊢
  have := cvv_le_mxo w m j hj hne
  rw [← cvv_eq w m j hj, ← cvv_eq w m m hm]
  linarith

theorem pair_margins (w : Weights ℚ) (a m : Nat) (ha : a < m) (hm : m < 8)
    (h : ∀ j < 8, j ≠ m → cvv w a j + cvv w m j < cvv w a m + cvv w m m) (hw : WF w) :
    Correct graph w task [a, m] ∧ Correct graph w task [m, a] := by
  have ha8 : a < 8 := by omega
  have key : ∀ j < 8, j ≠ m → logit w a j + logit w m j < logit w a m + logit w m m := by
    intro j hj hne
    rw [← cvv_eq w a j hj, ← cvv_eq w m j hj, ← cvv_eq w a m hm, ← cvv_eq w m m hm]
    exact h j hj hne
  constructor
  · apply correct_of_margins w hw a m ha8 hm
    rw [Nat.max_eq_right ha.le]
    exact key
  · apply correct_of_margins w hw m a hm ha8
    rw [Nat.max_eq_left ha.le]
    intro j hj hne
    have := key j hj hne
    linarith

theorem pair_correct (w : Weights ℚ) (hw : WF w) (a m : Nat) (ha : a < m) (hm : m < 8)
    (h : max (mxo w a) (cvv w a a) - cvv w a m < cvv w m m - mxo w m) :
    Correct graph w task [a, m] ∧ Correct graph w task [m, a] := by
  apply pair_margins w a m ha hm _ hw
  intro j hj hne
  have h1 : cvv w a j ≤ max (mxo w a) (cvv w a a) := by
    by_cases hja : j = a
    · subst hja
      exact le_max_right _ _
    · exact le_trans (cvv_le_mxo w a j hj hja) (le_max_left _ _)
  have h2 := cvv_le_mxo w m j hj hne
  linarith

theorem rpair_correct (w : Weights ℚ) (hw : WF w) (a m : Nat) (ha : a < m) (hm : m < 8)
    (h1 : mxo w a - cvv w a m < cvv w m m - mxo w m)
    (h2 : cvv w a a - cvv w a m < cvv w m m - cvv w m a) :
    Correct graph w task [a, m] ∧ Correct graph w task [m, a] := by
  apply pair_margins w a m ha hm _ hw
  intro j hj hne
  by_cases hja : j = a
  · subst hja
    linarith
  · have h3 := cvv_le_mxo w a j hj hja
    have h4 := cvv_le_mxo w m j hj hne
    linarith

/-! ## Terms and plans -/

open Classical in
theorem sem_runTerm (env : Env) (G : Bool) (cols : List Nat)
    (cv : List (Nat × ColInfo Interp.counting))
    (hcv : ∀ a ∈ cols, ∃ ci, cv.lookup a = some ci ∧ ColSem env.weights G a ci)
    (hG : G = true → WF env.weights) (t : Term) (ht : termOk cols t = true) :
    Sem env (runTerm Interp.counting cv t)
      (fun n => n ≤ t.inputs.countP fun x => decide (Correct graph env.weights task x)) := by
  cases t with
  | diag m =>
    simp only [termOk, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨hm, hmc⟩ := ht
    obtain ⟨cm, hcm, scm⟩ := hcv m hmc
    simp only [runTerm, hcm, Option.getD_some, Interp.counting_bind]
    refine Sem.bind (sem_lt env "cmp" ⟨0⟩ cm.dm) fun b hb => Sem.pure ?_
    cases b with
    | false => exact Nat.zero_le _
    | true =>
      have hlt : (0 : ℚ) < cm.dm.val := of_decide_eq_true hb.symm
      rw [scm.dm] at hlt
      cases G with
      | false => exact absurd hlt (lt_irrefl 0)
      | true =>
        have hc := diag_correct env.weights (hG rfl) m hm hlt
        simp [Term.inputs, hc]
  | pair a m wd =>
    simp only [termOk, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨⟨⟨ham, hm⟩, hac⟩, hmc⟩ := ht
    obtain ⟨ca, hca, sca⟩ := hcv a hac
    obtain ⟨cm, hcm, scm⟩ := hcv m hmc
    simp only [runTerm, hca, hcm, Option.getD_some, Interp.counting_bind]
    refine Sem.bind (sem_sub env "sub" ca.top (ca.col.getD m ⟨0⟩)) fun x hx => ?_
    refine Sem.bind (sem_lt env "cmp" x cm.dm) fun b hb => Sem.pure ?_
    cases b with
    | false => exact Nat.zero_le _
    | true =>
      have hlt : x.val < cm.dm.val := of_decide_eq_true hb.symm
      have hcam : (ca.col.getD m ⟨0⟩).val = cvv env.weights a m := by
        rw [← getD_val, sca.col]
        try rfl
      rw [hx, sca.top, hcam, scm.dm] at hlt
      have hge : cvv env.weights a m ≤ max (mxo env.weights a) (cvv env.weights a a) :=
        le_trans (cvv_le_mxo env.weights a m hm (by omega)) (le_max_left _ _)
      cases G with
      | false =>
        exfalso
        change max (mxo env.weights a) (cvv env.weights a a) - cvv env.weights a m < 0 at hlt
        linarith
      | true =>
        have hw := hG rfl
        change max (mxo env.weights a) (cvv env.weights a a) - cvv env.weights a m <
          cvv env.weights m m - mxo env.weights m at hlt
        obtain ⟨c1, c2⟩ := pair_correct env.weights hw a m ham hm hlt
        have c3 := diag_correct env.weights hw m hm (by linarith)
        cases wd <;> simp [Term.inputs, c1, c2, c3]
  | rpair a m wd =>
    simp only [termOk, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨⟨⟨ham, hm⟩, hac⟩, hmc⟩ := ht
    obtain ⟨ca, hca, sca⟩ := hcv a hac
    obtain ⟨cm, hcm, scm⟩ := hcv m hmc
    simp only [runTerm, hca, hcm, Option.getD_some, Interp.counting_bind]
    refine Sem.bind (sem_sub env "sub" ca.mx (ca.col.getD m ⟨0⟩)) fun x hx => ?_
    refine Sem.bind (sem_lt env "cmp" x cm.dm) fun b1 hb1 => ?_
    refine Sem.bind (sem_sub env "sub" (ca.col.getD a ⟨0⟩) (ca.col.getD m ⟨0⟩)) fun y hy => ?_
    refine Sem.bind (sem_sub env "sub" (cm.col.getD m ⟨0⟩) (cm.col.getD a ⟨0⟩)) fun z hz => ?_
    refine Sem.bind (sem_lt env "cmp" y z) fun b2 hb2 => ?_
    refine Sem.bind (sem_band env "gate" b1 b2) fun b hb => Sem.pure ?_
    cases b with
    | false => exact Nat.zero_le _
    | true =>
      cases b1 <;> cases b2 <;> simp at hb
      have hlt1 : x.val < cm.dm.val := of_decide_eq_true hb1.symm
      have hlt2 : y.val < z.val := of_decide_eq_true hb2.symm
      have hcam : (ca.col.getD m ⟨0⟩).val = cvv env.weights a m := by
        rw [← getD_val, sca.col]
        try rfl
      have hcaa : (ca.col.getD a ⟨0⟩).val = cvv env.weights a a := by
        rw [← getD_val, sca.col]
        try rfl
      have hcmm : (cm.col.getD m ⟨0⟩).val = cvv env.weights m m := by
        rw [← getD_val, scm.col]
        try rfl
      have hcma : (cm.col.getD a ⟨0⟩).val = cvv env.weights m a := by
        rw [← getD_val, scm.col]
        try rfl
      rw [hx, sca.mx, hcam, scm.dm] at hlt1
      rw [hy, hz, hcaa, hcam, hcmm, hcma] at hlt2
      have hge : cvv env.weights a m ≤ mxo env.weights a :=
        cvv_le_mxo env.weights a m hm (by omega)
      cases G with
      | false =>
        exfalso
        change mxo env.weights a - cvv env.weights a m < 0 at hlt1
        linarith
      | true =>
        have hw := hG rfl
        change mxo env.weights a - cvv env.weights a m <
          cvv env.weights m m - mxo env.weights m at hlt1
        obtain ⟨c1, c2⟩ := rpair_correct env.weights hw a m ham hm hlt1 hlt2
        have c3 := diag_correct env.weights hw m hm (by linarith)
        cases wd <;> simp [Term.inputs, c1, c2, c3]

open Classical in
theorem sem_runTerms (env : Env) (G : Bool) (cols : List Nat)
    (cv : List (Nat × ColInfo Interp.counting))
    (hcv : ∀ a ∈ cols, ∃ ci, cv.lookup a = some ci ∧ ColSem env.weights G a ci)
    (hG : G = true → WF env.weights) : ∀ (ts : List Term), (∀ t ∈ ts, termOk cols t = true) →
    Sem env (runTerms Interp.counting cv ts)
      (fun n => n ≤ (ts.flatMap Term.inputs).countP
        fun x => decide (Correct graph env.weights task x))
  | [], _ => by
    simp only [runTerms, Interp.counting_pure]
    exact Sem.pure (Nat.zero_le _)
  | t :: ts, hts => by
    simp only [runTerms, Interp.counting_bind]
    refine Sem.bind (sem_runTerm env G cols cv hcv hG t (hts t (by simp))) fun n hn => ?_
    refine Sem.bind (sem_runTerms env G cols cv hcv hG ts fun t' ht' => hts t' (by simp [ht']))
      fun ns hns => ?_
    refine Sem.pure ?_
    rw [List.flatMap_cons, List.countP_append]
    exact Nat.add_le_add hn hns

theorem guard_correct (w : Weights ℚ) (g : Nat × Nat)
    (h : singleOk graph w task [g.1, g.2] = true) : ∀ x ∈ guardInputs g, Correct graph w task x := by
  intro x hx
  unfold guardInputs at hx
  split at hx
  · simp at hx
    subst hx
    exact singleOk_correct graph w task _ h
  · simp at hx
    rcases hx with rfl | rfl
    · exact singleOk_correct graph w task _ h
    · exact singleOk_correct graph w task _ (singleOk_perm sym_graph rfl (List.Perm.swap _ _ _) h)

open Classical in
theorem countP_all_of_correct (w : Weights ℚ) (l : List Input)
    (h : ∀ x ∈ l, Correct graph w task x) :
    l.countP (fun x => decide (Correct graph w task x)) = l.length := by
  rw [List.countP_eq_length]
  intro x hx
  simpa using h x hx

open Classical in
theorem sem_runPlan (env : Env) (p : Plan) (hp : planOk p = true) :
    Sem env (runPlan Interp.counting p) (fun n => n ≤ numCorrect graph env.weights task) := by
  simp only [planOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hp
  obtain ⟨⟨⟨⟨_, _⟩, hterms⟩, hsub⟩, hnd⟩ := hp
  simp only [runPlan, Interp.counting_bind, Interp.counting_pure]
  refine Sem.bind (sem_shapesOk env) fun ok hok => ?_
  cases ok with
  | false =>
    rw [if_neg (by decide)]
    exact Sem.pure (Nat.zero_le _)
  | true =>
    rw [if_pos rfl]
    have hs := hok rfl
    refine Sem.bind (sem_single env graph task _) fun G hG => ?_
    have hwf : G = true → WF env.weights := fun h => wf_of_single env.weights hs _ (hG h)
    refine Sem.bind (sem_columns env G p.cols) fun cv hcv => ?_
    refine Sem.bind (sem_runTerms env G p.cols cv hcv hwf p.terms hterms) fun n hn => ?_
    refine Sem.pure ?_
    have hguard : (Interp.counting.nscale (guardInputs p.guard).length G : Nat) ≤
        (guardInputs p.guard).countP fun x => decide (Correct graph env.weights task x) := by
      cases G with
      | false => exact Nat.zero_le _
      | true =>
        rw [countP_all_of_correct env.weights _ (guard_correct env.weights p.guard (hG rfl))]
        exact le_refl _
    have hsum : (guardInputs p.guard ++ p.terms.flatMap Term.inputs).countP
        (fun x => decide (Correct graph env.weights task x)) ≤ numCorrect graph env.weights task := by
      unfold numCorrect
      apply List.Subperm.countP_le
      exact List.Nodup.subperm hnd (fun x hx => hsub x hx)
    rw [List.countP_append] at hsum
    exact le_trans (Nat.add_le_add hguard hn) hsum

/-! ## The two statements -/

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  exact sem_runPlan ⟨w, c⟩ thePlan thePlan_ok [] n cost h

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (38, 456) := by
  decide +kernel

theorem performance : Target := by
  show claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 38 cost h

end Candidate.Col38
