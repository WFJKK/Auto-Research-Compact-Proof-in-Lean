import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.List
import CompactCheck.Spec
import CompactCheck.SymmetrySound

/-!
# Soundness of the checker

The theorem `check_sound` at the end: if the checker certifies `n` inputs,
the network answers at least `n` inputs correctly, in the sense of
`Spec.lean`. It holds for every network, every weights and every proof
file. The steps:

1. The checker's numbers are the spec's numbers: when the exact evaluator
   runs a network (`evalGraph`, linear networks), the spec's semantics
   (`semGraph`) gives the same result, and every operation commutes with
   reading rationals as reals. So the real output is the exact rational
   output, read as reals (`realOutput_of_evalGraph`).
2. An input the exact single-input test accepts is answered correctly
   (`singleOk_correct`). The test accepts every input of a certified leaf
   (`certifiedLeaf_single`): an interval leaf through `intervalLeaf_sound`
   in `IntervalSound.lean`, with any approximation the checker builds, whose
   error bounds the difference to the weight (`buildApprox_ok`).
3. The certified leaves hold distinct inputs, because the leaves partition
   the input space (`walk_partition`), and a leaf's box holds `boxSize`
   inputs of the space (`countP_inBox`). So adding up the certified leaves
   never counts an input twice.
4. The leaves are checked on the network after the proof's contractions,
   which outputs nothing the original network does not
   (`contractAll_sound` in `ContractSound.lean`). So the original network
   passes the single-input test wherever the contracted one does
   (`singleOk_of_outputs`).
5. With the symmetry rule, an input counts if its sorted version lies in a
   certified leaf. The network computes the same on both
   (`evalGraph_perm` in `SymmetrySound.lean`) and the task gives both the
   same label, so the test accepts the input too (`singleOk_perm`).
-/

namespace CompactCheck

/-! ## 1. The checker's numbers are the spec's numbers -/

section cast

/-- Reading a rational as a real. -/
local notation "toR" => (fun q : ℚ => (q : ℝ))

@[simp] theorem Tensor.map_shape' {α β : Type} (f : α → β) (t : Tensor α) :
    (t.map f).shape = t.shape := rfl

@[simp] theorem Tensor.map_data_size {α β : Type} (f : α → β) (t : Tensor α) :
    (t.map f).data.size = t.data.size := by
  simp [Tensor.map]

@[simp] theorem Tensor.map_mk {α β : Type} (f : α → β) (s : List Nat) (d : Array α) :
    (Tensor.mk s d).map f = ⟨s, d.map f⟩ := rfl

theorem Tensor.get_map_cast (t : Tensor ℚ) (i : Nat) :
    (t.map toR).get i = ((t.get i : ℚ) : ℝ) := by
  simp only [Tensor.get, Tensor.map, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases t.data[i]? <;> simp

@[simp] theorem Tensor.get_mk_map_cast (s : List Nat) (d : Array ℚ) (i : Nat) :
    Tensor.get ⟨s, d.map toR⟩ i = ((Tensor.get ⟨s, d⟩ i : ℚ) : ℝ) :=
  Tensor.get_map_cast ⟨s, d⟩ i

theorem cast_list_sum (l : List ℚ) : ((l.sum : ℚ) : ℝ) = (l.map toR).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem oneHotInput_cast (P V : Nat) (x : Input) :
    (oneHotInput P V x : Option (Tensor ℝ)) =
      (oneHotInput P V x : Option (Tensor ℚ)).map (Tensor.map toR) := by
  simp only [oneHotInput]
  split_ifs <;> simp [Array.map_map, Function.comp_def, apply_ite (fun q : ℚ => (q : ℝ))]

theorem linearOp_cast (W : Tensor ℚ) (b : Option (Tensor ℚ)) (t : Tensor ℚ) :
    linearOp (W.map toR) (b.map (Tensor.map toR)) (t.map toR) =
      (linearOp W b t).map (Tensor.map toR) := by
  cases b <;>
  · simp only [linearOp, Tensor.map, Option.map_none, Option.map_some, Array.size_map]
    split_ifs <;> simp [Array.map_map, Function.comp_def, cast_list_sum]

theorem sumOp_cast (dim : Int) (t : Tensor ℚ) :
    sumOp dim (t.map toR) = (sumOp dim t).map (Tensor.map toR) := by
  simp only [sumOp, Tensor.map, Array.size_map]
  cases normDim dim t.shape.length with
  | none => rfl
  | some d =>
    dsimp only
    split_ifs <;> simp [Array.map_map, Function.comp_def, cast_list_sum]

theorem addOp_cast (a b : Tensor ℚ) :
    addOp (a.map toR) (b.map toR) = (addOp a b).map (Tensor.map toR) := by
  simp only [addOp, Tensor.map, Array.size_map]
  split_ifs <;> simp [Array.map_map, Function.comp_def]

theorem lookup_realWeights (n : String) (w : Weights ℚ) :
    List.lookup n (realWeights w) = (List.lookup n w).map (Tensor.map toR) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    obtain ⟨m, t⟩ := p
    simp only [realWeights, List.map_cons, List.lookup] at *
    split <;> simp_all

theorem evalOp_cast (g : Graph) (w : Weights ℚ) (x : Input) (vals : Array (Tensor ℚ))
    (op : Op) :
    evalOp g (realWeights w) x (vals.map (Tensor.map toR)) op =
      (evalOp g w x vals op).map (Tensor.map toR) := by
  cases op with
  | input => simp only [evalOp, oneHotInput_cast]
  | linear a wn bn =>
    simp only [evalOp, Array.getElem?_map, lookup_realWeights]
    cases vals[a]? <;> cases List.lookup wn w <;> simp only [Option.map_none, Option.map_some]
    rename_i t W
    cases bn with
    | none => simpa using linearOp_cast W none t
    | some bn =>
      dsimp only
      cases List.lookup bn w with
      | none => rfl
      | some b => simpa using linearOp_cast W (some b) t
  | sum a d =>
    simp only [evalOp, Array.getElem?_map]
    cases vals[a]? <;> simp [sumOp_cast]
  | add a b =>
    simp only [evalOp, Array.getElem?_map]
    cases vals[a]? <;> cases vals[b]? <;> simp [addOp_cast]
  | _ => simp [evalOp]

theorem evalOps_cast (g : Graph) (w : Weights ℚ) (x : Input) (ops : List Op)
    (vals : Array (Tensor ℚ)) :
    evalOps g (realWeights w) x ops (vals.map (Tensor.map toR)) =
      (evalOps g w x ops vals).map (Array.map (Tensor.map toR)) := by
  induction ops generalizing vals with
  | nil => simp [evalOps]
  | cons op ops ih =>
    simp only [evalOps, evalOp_cast]
    cases evalOp g w x vals op with
    | none => rfl
    | some v => simp [← Array.map_push, ih]

/-- Over the reals, the exact evaluator's output is its output over the
    rationals, read as real numbers. -/
theorem evalGraph_cast (g : Graph) (w : Weights ℚ) (x : Input) :
    evalGraph g (realWeights w) x = (evalGraph g w x).map (Tensor.map toR) := by
  unfold evalGraph
  have h := evalOps_cast g w x g.nodes #[]
  simp only [Array.map_empty] at h
  rw [h]
  cases evalOps g w x g.nodes #[] <;> simp [Array.getElem?_map]

/-! ### The exact evaluator computes what the spec computes

`semOp` gives every operation of `evalOp` the value `evalOp` gives it; the
other operations are those `evalOp` does not run. -/

section bridge

variable {α : Type} [Zero α] [One α] [Add α] [Mul α] [Neg α] [ExpDiv α]

theorem semOp_of_evalOp {g : Graph} {w : Weights α} {x : Input} {vals : Array (Tensor α)}
    {op : Op} {v : Tensor α} (h : evalOp g w x vals op = some v) :
    semOp g w x vals op = some v := by
  cases op <;> first | exact h | simp [evalOp] at h

theorem semOps_of_evalOps {g : Graph} {w : Weights α} {x : Input} :
    ∀ {ops : List Op} {vals out : Array (Tensor α)},
      evalOps g w x ops vals = some out → semOps g w x ops vals = some out
  | [], vals, out, h => by simpa [evalOps, semOps] using h
  | op :: ops, vals, out, h => by
    simp only [evalOps] at h
    cases hv : evalOp g w x vals op with
    | none => simp [hv] at h
    | some v =>
      simp only [hv] at h
      simp only [semOps, semOp_of_evalOp hv]
      exact semOps_of_evalOps h

theorem semGraph_of_evalGraph {g : Graph} {w : Weights α} {x : Input} {out : Tensor α}
    (h : evalGraph g w x = some out) : semGraph g w x = some out := by
  unfold evalGraph at h
  unfold semGraph
  cases hv : evalOps g w x g.nodes #[] with
  | none => simp [hv] at h
  | some vals =>
    simp only [hv] at h
    rw [semOps_of_evalOps hv]
    exact h

end bridge

/-- When the exact evaluator runs the network, the real output is its exact
    output, read as real numbers. -/
theorem realOutput_of_evalGraph {g : Graph} {w : Weights ℚ} {x : Input} {out : Tensor ℚ}
    (h : evalGraph g w x = some out) : realOutput g w x = some (out.map toR) := by
  apply semGraph_of_evalGraph
  rw [evalGraph_cast, h]
  rfl

end cast

/-! ## 2. An accepted input is answered correctly -/

theorem strictMaxAt_spec (v : Vec) (l : Nat) (h : strictMaxAt v l = true) :
    l < v.length ∧ ∀ j < v.length, j ≠ l → vecGet v j < vecGet v l := by
  simp only [strictMaxAt, allPosExcept, marginsAt, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.length_map] at h
  obtain ⟨hl, hall⟩ := h
  refine ⟨hl, fun j hj hne => ?_⟩
  have hmem : (j, vecGet v l - v[j]) ∈
      (List.range v.length).zip (v.map fun a => vecGet v l - a) := by
    rw [List.mem_iff_getElem]
    refine ⟨j, by simp [hj], ?_⟩
    simp [List.getElem_zip, List.getElem_range, List.getElem_map]
  have hpos := hall _ hmem
  simp only [Bool.or_eq_true, beq_iff_eq, hne, false_or, decide_eq_true_eq] at hpos
  have hj' : vecGet v j = v[j] := by
    simp [vecGet, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [hj']
  exact sub_pos.mp hpos

/-- `single_sound`: an input the checker accepts is answered correctly. -/
theorem singleOk_correct (g : Graph) (w : Weights ℚ) (task : Task) (x : Input)
    (h : singleOk g w task x = true) : Correct g w task x := by
  unfold singleOk at h
  split at h
  · rename_i out hout
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hshape, hmax⟩ := h
    obtain ⟨hl, hlt⟩ := strictMaxAt_spec _ _ hmax
    simp only [Array.length_toList] at hl hlt
    refine ⟨out.map (fun q : ℚ => (q : ℝ)), realOutput_of_evalGraph hout, ?_, ?_, ?_⟩
    · simpa [Tensor.map] using hshape
    · simpa using hl
    · intro j hj hne
      simp only [Tensor.map_data_size] at hj
      rw [Tensor.get_map_cast, Tensor.get_map_cast]
      have := hlt j hj hne
      rw [vecGet_toList, vecGet_toList] at this
      exact_mod_cast this
  · exact absurd h (by simp)

/-! ## 3. Counting: no input is certified twice -/

/-- A leaf the checker certifies. -/
def certifiedLeaf (g : Graph) (w : Weights ℚ) (task : Task) (approxs : List Approx)
    (leaf : Leaf) : Bool :=
  match leafOk g w task approxs leaf with
  | .ok true => true
  | _ => false

theorem checkLeaves_eq (g : Graph) (w : Weights ℚ) (task : Task) (approxs : List Approx)
    (leaves : List Leaf) (n : Nat) (h : checkLeaves g w task approxs leaves = .ok n) :
    n = (leaves.map fun l =>
      if certifiedLeaf g w task approxs l then boxSize l.box else 0).sum := by
  induction leaves generalizing n with
  | nil =>
    simp only [checkLeaves] at h
    cases h
    simp
  | cons leaf rest ih =>
    simp only [checkLeaves] at h
    cases hr : checkLeaves g w task approxs rest with
    | error e => simp [hr] at h
    | ok m =>
      simp only [hr] at h
      cases hl : leafOk g w task approxs leaf with
      | error e => simp [hl] at h
      | ok ok =>
        simp only [hl, Except.ok.injEq] at h
        subst h
        rw [List.map_cons, List.sum_cons, ← ih m hr]
        cases ok
        · simp [certifiedLeaf, hl]
        · simp only [certifiedLeaf, hl, ↓reduceIte]
          omega

/-- A box that holds exactly one input contains that input and no other. -/
theorem boxInput_spec (box : Box) (x : Input) (h : boxInput box = some x) :
    inBox box x = true ∧ ∀ y, inBox box y = true → y = x := by
  induction box generalizing x with
  | nil =>
    simp only [boxInput, Option.some.injEq] at h
    subst h
    refine ⟨rfl, fun y hy => ?_⟩
    cases y with
    | nil => rfl
    | cons _ _ => simp [inBox] at hy
  | cons r rs ih =>
    simp only [boxInput] at h
    split at h
    · rename_i hr
      cases hrs : boxInput rs with
      | none => simp [hrs] at h
      | some xs =>
        simp only [hrs, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hin, huniq⟩ := ih xs hrs
        refine ⟨by simp [inBox, inRange, hr, hin], fun y hy => ?_⟩
        cases y with
        | nil => simp [inBox] at hy
        | cons t ts =>
          simp only [inBox, inRange, Bool.and_eq_true, decide_eq_true_eq] at hy
          obtain ⟨⟨h1, h2⟩, h3⟩ := hy
          rw [huniq ts h3]
          congr
          omega
    · cases h

/-- The single-input test accepts every input in a certified leaf. -/
theorem certifiedLeaf_single (g : Graph) (w : Weights ℚ) (task : Task) (approxs : List Approx)
    (happrox : ∀ a ∈ approxs, ApproxOk g w a) (l : Leaf) (x : Input)
    (hl : certifiedLeaf g w task approxs l = true) (hx : inBox l.box x = true) :
    singleOk g w task x = true := by
  unfold certifiedLeaf at hl
  cases hok : leafOk g w task approxs l with
  | error e => simp [hok] at hl
  | ok b =>
    cases b with
    | false => simp [hok] at hl
    | true =>
      unfold leafOk at hok
      cases hr : l.rule with
      | skip => simp [hr] at hok
      | single =>
        simp only [hr] at hok
        cases hb : boxInput l.box with
        | none => simp [hb] at hok
        | some x0 =>
          simp only [hb, Except.ok.injEq] at hok
          obtain ⟨_, huniq⟩ := boxInput_spec _ _ hb
          rw [huniq x hx]
          exact hok
      | interval a =>
        cases a with
        | none =>
          simp only [hr] at hok
          exact intervalLeaf_sound g w task l.box none (fun _ h => by cases h) hok x hx
        | some name =>
          simp only [hr] at hok
          cases hf : approxs.find? (·.name == name) with
          | none => simp [hf] at hok
          | some a =>
            simp only [hf] at hok
            have ha : ∀ a', some a = some a' → ApproxOk g w a' := by
              intro a' h
              cases h
              exact happrox a (List.mem_of_find?_eq_some hf)
            exact intervalLeaf_sound g w task l.box (some a) ha hok x hx
      | tokenInterval =>
        simp only [hr] at hok
        cases hl : task.constantLabel l.box with
        | none => simp [hl] at hok
        | some _ => simp [hl] at hok

/-! ### The number of inputs in a box -/

/-- Every range of the box ends inside the space. -/
def fits : Box → List Nat → Bool
  | [], [] => true
  | r :: rs, v :: vs => r.hi < v && fits rs vs
  | _, _ => false

theorem sum_ite_const {α : Type} (l : List α) (p : α → Bool) (c : Nat) :
    (l.map fun a => if p a then c else 0).sum = l.countP p * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.countP_cons]
    split <;> simp [Nat.add_mul, Nat.add_comm]

theorem countP_range_inRange (r : Range) (v : Nat) :
    (List.range v).countP (inRange r) = min v (r.hi + 1) - r.lo := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, inRange, Bool.and_eq_true, decide_eq_true_eq]
    split <;> omega

/-- A box inside the space holds `boxSize` of its inputs. -/
theorem countP_inBox : ∀ (space : List Nat) (box : Box), fits box space = true →
    (allInputs space).countP (inBox box) = boxSize box
  | [], [], _ => by simp [allInputs, inBox, boxSize]
  | v :: vs, r :: rs, h => by
    simp only [fits, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [allInputs, List.countP_flatMap]
    have hinner : ∀ t, ((List.countP (inBox (r :: rs)) ∘ fun t => (allInputs vs).map (t :: ·)) t) =
        if inRange r t then boxSize rs else 0 := by
      intro t
      simp only [Function.comp_def, List.countP_map]
      have : (allInputs vs).countP (fun y => inBox (r :: rs) (t :: y)) =
          (allInputs vs).countP (fun y => inRange r t && inBox rs y) := by
        apply List.countP_congr
        intro y _
        simp [inBox]
      rw [this, countP_const_and, countP_inBox vs rs h.2]
    rw [List.map_congr_left (fun t _ => hinner t), sum_ite_const, countP_range_inRange]
    simp only [boxSize, List.foldr_cons]
    congr 1
    omega
  | [], _ :: _, h => by simp [fits] at h
  | _ :: _, [], h => by simp [fits] at h

theorem boxSize_ne_zero : ∀ {box : Box}, boxSize box ≠ 0 → ∀ r ∈ box, r.lo ≤ r.hi
  | [], _, r, hr => by simp at hr
  | r :: rs, h, r', hr' => by
    simp only [boxSize, List.foldr_cons] at h
    have h1 : r.hi + 1 - r.lo ≠ 0 := fun h0 => h (by rw [h0, Nat.zero_mul])
    have h2 : boxSize rs ≠ 0 := fun h0 => h (by simp only [boxSize] at h0; rw [h0, Nat.mul_zero])
    rcases List.mem_cons.mp hr' with rfl | hr'
    · omega
    · exact boxSize_ne_zero h2 r' hr'

theorem inBox_highs : ∀ {box : Box}, (∀ r ∈ box, r.lo ≤ r.hi) → inBox box (box.map Range.hi) = true
  | [], _ => rfl
  | r :: rs, h => by
    simp only [List.map_cons, inBox, inRange, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨h r (by simp), le_refl _⟩, inBox_highs fun r' hr' => h r' (by simp [hr'])⟩

theorem fits_of_root : ∀ {space : List Nat} {box : Box}, (∀ v ∈ space, 0 < v) →
    inBox (rootBox space) (box.map Range.hi) = true → fits box space = true
  | [], [], _, _ => rfl
  | v :: vs, r :: rs, hpos, h => by
    simp only [rootBox, List.map_cons, inBox, inRange, Bool.and_eq_true,
      decide_eq_true_eq] at h
    have hv := hpos v (by simp)
    simp only [fits, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, fits_of_root (fun u hu => hpos u (by simp [hu])) h.2⟩
  | [], _ :: _, _, h => by simp [rootBox, inBox] at h
  | _ :: _, [], _, h => by simp [rootBox, inBox] at h

/-- A leaf of an accepted tree holds `boxSize` inputs of the space. -/
theorem boxSize_le_count (space : List Nat) (hpos : ∀ v ∈ space, 0 < v) (tree : SplitTree)
    (leaves : List Leaf) (hw : walk tree (rootBox space) = .ok leaves) (l : Leaf)
    (hl : l ∈ leaves) : boxSize l.box ≤ (allInputs space).countP (inBox l.box) := by
  by_cases h0 : boxSize l.box = 0
  · omega
  · have hin : inBox l.box (l.box.map Range.hi) = true := inBox_highs (boxSize_ne_zero h0)
    have hroot : inBox (rootBox space) (l.box.map Range.hi) = true := by
      have hp := walk_partition tree _ leaves hw (l.box.map Range.hi)
      have : 0 < leaves.countP (fun l' => inBox l'.box (l.box.map Range.hi)) :=
        List.countP_pos_iff.mpr ⟨l, hl, hin⟩
      split at hp <;> simp_all
    rw [countP_inBox space l.box (fits_of_root hpos hroot)]

theorem countP_eq_sum {α : Type} (X : List α) (p : α → Bool) :
    X.countP p = (X.map fun x => if p x then 1 else 0).sum := by
  induction X with
  | nil => simp
  | cons a X ih => simp [List.countP_cons, ih]; omega

/-- Counting by inputs instead of by leaves. -/
theorem sum_countP_swap {α β : Type} (X : List α) (L : List β) (P : β → α → Bool) :
    (X.map fun x => L.countP (fun l => P l x)).sum = (L.map fun l => X.countP (P l)).sum := by
  induction L with
  | nil => simp
  | cons l L ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons, List.sum_map_add, ih,
      countP_eq_sum X (P l)]
    omega

/-- A network that outputs whatever another network outputs passes the
    single-input test wherever the other passes it. -/
theorem singleOk_of_outputs {g g' : Graph} {w w' : Weights ℚ} {task : Task}
    (h : ∀ x out, evalGraph g' w' x = some out → evalGraph g w x = some out) {x : Input}
    (hx : singleOk g' w' task x = true) : singleOk g w task x = true := by
  unfold singleOk at hx ⊢
  cases he : evalGraph g' w' x with
  | none => simp [he] at hx
  | some out =>
    rw [h x out he]
    simpa [he] using hx

open Classical in
/-- The leaves of an accepted tree that a test `ok` accepts never hold more
    inputs than satisfy `C`, if every input of an accepted leaf satisfies
    `C`: the leaves do not overlap, and each holds `boxSize` inputs. -/
theorem leaves_certified_le (task : Task) (ok : Leaf → Bool) (C : Input → Prop)
    (hok : ∀ l x, ok l = true → inBox l.box x = true → C x) (tree : SplitTree)
    (leaves : List Leaf) (hw : walk tree (rootBox task.space) = .ok leaves)
    (hpos : ∀ v ∈ task.space, 0 < v) :
    (leaves.map fun l => if ok l then boxSize l.box else 0).sum ≤
      (allInputs task.space).countP fun x => decide (C x) := by
  -- For each input: at most one leaf contains it, and only if it satisfies C.
  have hpoint : ∀ x ∈ allInputs task.space,
      leaves.countP (fun l => ok l && inBox l.box x) ≤ (if decide (C x) then 1 else 0) := by
    intro x _
    by_cases hcx : C x
    · have hle : leaves.countP (fun l => ok l && inBox l.box x) ≤
          leaves.countP (fun l => inBox l.box x) :=
        List.countP_mono_left (fun l _ h => by simp_all)
      rw [walk_partition tree _ leaves hw x] at hle
      simp only [hcx, decide_true, ↓reduceIte]
      split at hle <;> omega
    · have : leaves.countP (fun l => ok l && inBox l.box x) = 0 := by
        rw [List.countP_eq_zero]
        intro l _ h
        simp only [Bool.and_eq_true] at h
        exact hcx (hok l x h.1 h.2)
      simp [this]
  -- Each accepted leaf holds `boxSize` inputs of the space.
  have hleaf : ∀ l ∈ leaves, (if ok l then boxSize l.box else 0) ≤
      (allInputs task.space).countP (fun x => ok l && inBox l.box x) := by
    intro l hl
    split
    · rename_i hcl
      simp only [hcl, Bool.true_and]
      exact boxSize_le_count task.space hpos tree leaves hw l hl
    · exact Nat.zero_le _
  calc (leaves.map fun l => if ok l then boxSize l.box else 0).sum
      ≤ (leaves.map fun l => (allInputs task.space).countP
          (fun x => ok l && inBox l.box x)).sum := List.sum_le_sum hleaf
    _ = ((allInputs task.space).map fun x =>
          leaves.countP (fun l => ok l && inBox l.box x)).sum :=
        (sum_countP_swap _ _ (fun l x => ok l && inBox l.box x)).symm
    _ ≤ ((allInputs task.space).map fun x => if decide (C x) then 1 else 0).sum :=
        List.sum_le_sum hpoint
    _ = (allInputs task.space).countP fun x => decide (C x) := by
          rw [countP_eq_sum]

/-- The certified leaves of an accepted tree, checked on the network `g'`
    after the proof's contractions, never certify more inputs than the
    original network `g` answers correctly. -/
theorem certified_le {g g' : Graph} {w w' : Weights ℚ} (task : Task) (approxs : List Approx)
    (hc : ∀ x out, evalGraph g' w' x = some out → evalGraph g w x = some out)
    (happrox : ∀ a ∈ approxs, ApproxOk g' w' a) (tree : SplitTree)
    (leaves : List Leaf) (hw : walk tree (rootBox task.space) = .ok leaves)
    (hpos : ∀ v ∈ task.space, 0 < v) :
    (leaves.map fun l => if certifiedLeaf g' w' task approxs l then boxSize l.box else 0).sum ≤
      numCorrect g w task :=
  leaves_certified_le task _ (Correct g w task)
    (fun l x hl hx => singleOk_correct g w task x
      (singleOk_of_outputs hc (certifiedLeaf_single g' w' task approxs happrox l x hl hx)))
    tree leaves hw hpos

/-! ## 5. Approximations and symmetry -/

/-- The error of an approximation bounds `|W - P|` at every entry. -/
theorem approxError_spec (W : Tensor ℚ) (f : ApproxForm) : ∀ o < W.shape.getD 0 0,
    ∀ t < W.shape.getD 1 0,
      |W.get (o * W.shape.getD 1 0 + t) - f.entry (W.shape.getD 1 0) o t| ≤ approxError W f := by
  intro o ho t ht
  set inn := W.shape.getD 1 0 with hinn
  have he : o * inn + t ∈ List.range (W.shape.getD 0 0 * inn) :=
    List.mem_range.mpr (idx_lt ho ht)
  have key := (le_foldl_max (fun e =>
    max (W.get e - f.entry inn (e / inn) (e % inn)) (-(W.get e - f.entry inn (e / inn) (e % inn))))
    (List.range (W.shape.getD 0 0 * inn)) 0).2 _ he
  simp only [idx_div ht, idx_mod ht] at key
  rw [abs_eq_max_neg]
  exact key

/-- An approximation the checker builds is of a linear map of the network,
    with that map's weight, and its error bounds the difference. -/
theorem buildApprox_ok {g : Graph} {w : Weights ℚ} {s : ApproxSpec} {a : Approx}
    (h : buildApprox g w s = .ok a) : ApproxOk g w a := by
  unfold buildApprox at h
  split at h
  · rename_i arg wn bn hop
    cases hW : List.lookup wn w with
    | none => simp [hW] at h
    | some W =>
      simp only [hW] at h
      cases hf : approxForm W s.form with
      | error e => simp [hf] at h
      | ok form =>
        simp only [hf, Except.ok.injEq] at h
        subst h
        exact ⟨⟨arg, wn, bn, hop, hW⟩, approxError_spec W form⟩
  · cases h

theorem buildApproxs_ok {g : Graph} {w : Weights ℚ} :
    ∀ {specs : List ApproxSpec} {approxs : List Approx}, buildApproxs g w specs = .ok approxs →
      ∀ a ∈ approxs, ApproxOk g w a
  | [], approxs, h => by
    simp only [buildApproxs, Except.ok.injEq] at h
    subst h
    simp
  | s :: rest, approxs, h => by
    simp only [buildApproxs] at h
    cases h1 : buildApprox g w s with
    | error e => simp [h1] at h
    | ok a =>
      cases h2 : buildApproxs g w rest with
      | error e => simp [h1, h2] at h
      | ok as =>
        simp only [h1, h2] at h
        split_ifs at h
        simp only [Except.ok.injEq] at h
        subst h
        intro a' ha'
        rcases List.mem_cons.mp ha' with rfl | ha'
        · exact buildApprox_ok h1
        · exact buildApproxs_ok h2 a' ha'

/-- The single-input test accepts an input if it accepts a reordering of it,
    when the network passes `symmetricNet` and the task's label does not
    depend on the order. -/
theorem singleOk_perm {g : Graph} {w : Weights ℚ} {task : Task} (hsym : symmetricNet g = true)
    (hlab : task.labelSymmetric = true) {x y : Input} (hxy : x.Perm y)
    (hx : singleOk g w task x = true) : singleOk g w task y = true := by
  have hlabel : task.label y = task.label x := (task.labelSymmetric_spec hlab x y hxy).symm
  unfold singleOk at hx ⊢
  rw [← evalGraph_perm hsym hxy, hlabel]
  exact hx

/-- The boxes `certifiedBoxes` gives are those of certified leaves. -/
theorem certifiedBoxes_spec (g : Graph) (w : Weights ℚ) (task : Task) (approxs : List Approx) :
    ∀ (leaves : List Leaf) (boxes : List Box),
      certifiedBoxes g w task approxs leaves = .ok boxes →
        ∀ b ∈ boxes, ∃ l ∈ leaves, certifiedLeaf g w task approxs l = true ∧ l.box = b
  | [], boxes, h => by
    simp only [certifiedBoxes, Except.ok.injEq] at h
    subst h
    simp
  | leaf :: rest, boxes, h => by
    simp only [certifiedBoxes] at h
    cases hr : certifiedBoxes g w task approxs rest with
    | error e => simp [hr] at h
    | ok bs =>
      simp only [hr] at h
      cases hl : leafOk g w task approxs leaf with
      | error e => simp [hl] at h
      | ok ok =>
        simp only [hl, Except.ok.injEq] at h
        subst h
        intro b hb
        have hrest : ∀ b ∈ bs, ∃ l ∈ leaf :: rest,
            certifiedLeaf g w task approxs l = true ∧ l.box = b := by
          intro b hb
          obtain ⟨l, hlm, hc, hbox⟩ := certifiedBoxes_spec g w task approxs rest bs hr b hb
          exact ⟨l, List.mem_cons_of_mem _ hlm, hc, hbox⟩
        cases ok with
        | false => exact hrest b (by simpa using hb)
        | true =>
          simp only [↓reduceIte, List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact ⟨leaf, List.mem_cons_self, by simp [certifiedLeaf, hl], rfl⟩
          · exact hrest b hb

/-- **symmetry_sound**: under the symmetry rule the checker never counts
    more inputs than the network answers correctly. -/
theorem sortedCount_le {g g' : Graph} {w w' : Weights ℚ} {task : Task} {approxs : List Approx}
    {leaves : List Leaf} {boxes : List Box} (hsym : symmetricNet g = true)
    (hlab : task.labelSymmetric = true)
    (hc : ∀ x out, evalGraph g' w' x = some out → evalGraph g w x = some out)
    (happrox : ∀ a ∈ approxs, ApproxOk g' w' a)
    (hb : certifiedBoxes g' w' task approxs leaves = .ok boxes) :
    sortedCount task.space boxes ≤ numCorrect g w task := by
  classical
  unfold sortedCount numCorrect
  apply List.countP_mono_left
  intro y _ hy
  obtain ⟨b, hbm, hin⟩ := List.any_eq_true.mp hy
  obtain ⟨l, -, hcert, rfl⟩ := certifiedBoxes_spec g' w' task approxs leaves boxes hb b hbm
  have h1 := certifiedLeaf_single g' w' task approxs happrox l _ hcert hin
  have h2 := singleOk_of_outputs hc h1
  exact decide_eq_true (singleOk_correct g w task y
    (singleOk_perm hsym hlab (List.mergeSort_perm y _) h2))

/-- **Soundness**: if the checker certifies `n` inputs, the network answers
    at least `n` inputs correctly. For every network, weights and proof
    file. -/
theorem check_sound (g : Graph) (w : Weights ℚ) (task : Task) (proof : ProofFile) (n : Nat)
    (h : checkProof g w task proof = .ok n) : n ≤ numCorrect g w task := by
  unfold checkProof at h
  split at h
  · cases h
  rename_i hsym
  split at h
  · cases h
  rename_i hlab
  split at h
  · cases h
  rename_i hzero
  have hpos : ∀ v ∈ task.space, 0 < v := by
    intro v hv
    have : ¬ (task.space.any (· == 0) = true) := by simpa using hzero
    simp only [List.any_eq_true, beq_iff_eq, not_exists, not_and] at this
    exact Nat.pos_of_ne_zero (this v hv)
  cases hc : contractAll g w proof.contractions with
  | error e => simp [hc] at h
  | ok r =>
    obtain ⟨g', w'⟩ := r
    simp only [hc] at h
    cases ha : buildApproxs g' w' proof.approximations with
    | error e => simp [ha] at h
    | ok approxs =>
      simp only [ha] at h
      have happrox := buildApproxs_ok ha
      cases hw : walk proof.tree (rootBox task.space) with
      | error e => simp [hw] at h
      | ok leaves =>
        simp only [hw] at h
        by_cases hs : proof.symmetry = true
        · simp only [hs, ↓reduceIte] at h
          cases hb : certifiedBoxes g' w' task approxs leaves with
          | error e => simp [hb] at h
          | ok boxes =>
            simp only [hb, Except.ok.injEq] at h
            subst h
            have hsym' : symmetricNet g = true := by simpa [hs] using hsym
            have hlab' : task.labelSymmetric = true := by simpa [hs] using hlab
            exact sortedCount_le hsym' hlab' (contractAll_sound hc) happrox hb
        · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
          rw [checkLeaves_eq g' w' task approxs leaves n h]
          exact certified_le task approxs (contractAll_sound hc) happrox proof.tree leaves hw hpos

end CompactCheck
