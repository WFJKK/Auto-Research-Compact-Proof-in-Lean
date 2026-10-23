import CompactCheck.GeneralSound
import CompactCheck.CountedGeneral
import CompactCheck.TokensLeafSound
import CompactCheck.TokensCost

/-!
# The soundness of the counted single rule on general networks

A run of `CostM.gsingle g task x` that answers `true` means the network answers `x` correctly, in
the real semantics of the specification (`Correct`, with the real exponential): the verdict is
`generalSingle`'s (`gsingleRun_generalSingle`), and `generalSingle_correct` (GeneralSound.lean) is
the general checker's soundness theorem for a single leaf. A run of `CostM.ginterval g task box`
that answers `true` means the same for every input of the box (`generalInterval_correct`). A run
of `CostM.gtokenIntervals g task boxes` gives one verdict per box, and a box answered `true` has
every input answered correctly (`gtokenLeaf_verdict` and `generalTokenInterval_correct`,
TokensLeafSound.lean).
-/

namespace CompactCheck

namespace CostM

theorem gsingle_correct {g : Graph} {task : Task} {x : Input} {env : Env} {c c' : Cost}
    (h : (gsingle g task x).run env c = some (true, c')) : Correct g env.weights task x := by
  have h' : (match dweights env.weights with
      | none => none
      | some dw =>
        match gsingleRun g dw task x with
        | some (b, k) => some (b, c.add "single" k)
        | none => none) = some (true, c') := h
  cases hdw : dweights env.weights with
  | none => simp [hdw] at h'
  | some dw =>
    simp only [hdw] at h'
    cases hr : gsingleRun g dw task x with
    | none => simp [hr] at h'
    | some p =>
      obtain ⟨b, k⟩ := p
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h'
      rw [h'.1] at hr
      exact generalSingle_correct hdw (gsingleRun_generalSingle hr)

/-- A run of the interval rule that answers `true` means the network answers every input of the box
    correctly (`generalInterval_correct`). -/
theorem ginterval_correct {g : Graph} {task : Task} {box : Box} {env : Env} {c c' : Cost}
    (h : (ginterval g task box).run env c = some (true, c')) (x : Input) (hx : inBox box x = true) :
    Correct g env.weights task x := by
  have h' : (match dweights env.weights with
      | none => none
      | some dw =>
        match gintervalRun g dw task box with
        | some (b, k) => some (b, c.add "interval" k)
        | none => none) = some (true, c') := h
  cases hdw : dweights env.weights with
  | none => simp [hdw] at h'
  | some dw =>
    simp only [hdw] at h'
    cases hr : gintervalRun g dw task box with
    | none => simp [hr] at h'
    | some p =>
      obtain ⟨b, k⟩ := p
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h'
      rw [h'.1] at hr
      exact generalInterval_correct hdw (gintervalRun_generalInterval hr) x hx

/-- `mapM` in `Option`: one result per element, each the function's. -/
theorem mapM_option_spec {α β : Type} (f : α → Option β) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      ys.length = xs.length ∧
        ∀ (i : Nat) (x : α), xs[i]? = some x → ∃ y, ys[i]? = some y ∧ f x = some y
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some ys' =>
        simp only [hx, hxs, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        obtain ⟨hl, hi⟩ := mapM_option_spec f hxs
        refine ⟨by simp [hl], ?_⟩
        intro i x' hi'
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi'
          subst hi'
          exact ⟨y, rfl, hx⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hi' ⊢
          exact hi i x' hi'

/-- A run of the token_interval rule gives one verdict per box, and a box answered `true` has every
    input answered correctly. -/
theorem gtokenIntervals_correct {g : Graph} {task : Task} {boxes : List Box} {env : Env}
    {c c' : Cost} {bs : List Bool} (h : (gtokenIntervals g task boxes).run env c = some (bs, c')) :
    bs.length = boxes.length ∧
      ∀ (i : Nat) (box : Box), boxes[i]? = some box → bs[i]? = some true →
        ∀ x, inBox box x = true → Correct g env.weights task x := by
  have h' : (match dweights env.weights with
      | none => none
      | some dw =>
        match gtokenRun g dw task boxes with
        | some (bs, k, t) => some (bs, (c.add "token_interval" k).add "tables" t)
        | none => none) = some (bs, c') := h
  cases hdw : dweights env.weights with
  | none => simp [hdw] at h'
  | some dw =>
    simp only [hdw] at h'
    cases hr : gtokenRun g dw task boxes with
    | none => simp [hr] at h'
    | some p =>
      obtain ⟨bs', k, t⟩ := p
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h'
      unfold gtokenRun at hr
      cases hm : boxes.mapM (gtokenLeaf g dw task) with
      | none => simp [hm] at hr
      | some rs =>
        simp only [hm, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨hlen, hspec⟩ := mapM_option_spec _ hm
        have hbs : bs = rs.map (·.1) := by rw [← h'.1, ← hr.1]
        subst hbs
        refine ⟨by simp [hlen], ?_⟩
        intro i box hbox hbi x hx
        obtain ⟨r, hri, hfr⟩ := hspec i box hbox
        rw [List.getElem?_map, hri] at hbi
        obtain ⟨v, k', rq⟩ := r
        simp only [Option.map_some, Option.some.injEq] at hbi
        subst hbi
        exact generalTokenInterval_correct hdw (gtokenLeaf_verdict hfr) x hx

end CostM

/-! ## Counting the inputs of the boxes a rule certified

A checker that runs a rule on a list of boxes (`I.gtokenIntervals`) counts the inputs of the boxes
answered `true`. If no two boxes share an input (`pairwiseApart`, decided on the checker's own boxes)
and every box lies in the input space, that count is at most the number of inputs the network answers
correctly (`certifiedCount_le`). -/

/-- Two boxes share no input: at some position their ranges do not meet. -/
def boxesApart (a b : Box) : Bool :=
  (a.zip b).any fun (r, s) => r.hi < s.lo || s.hi < r.lo

/-- No two boxes of the list share an input. -/
def pairwiseApart : List Box → Bool
  | [] => true
  | b :: bs => bs.all (boxesApart b) && pairwiseApart bs

/-- The inputs of the boxes whose verdict is `true` (the counting interpreter's
    `nadd (nscale (boxSize b) v) ...`, box by box). -/
def certifiedCount : List Box → List Bool → Nat
  | b :: bs, v :: vs => cond v (boxSize b) 0 + certifiedCount bs vs
  | _, _ => 0

theorem inBox_of_apart : ∀ {a b : Box} {x : Input}, boxesApart a b = true → inBox a x = true →
    inBox b x = false
  | r :: rs, s :: ss, t :: ts, h, ha => by
    simp only [boxesApart, List.zip_cons_cons, List.any_cons, Bool.or_eq_true,
      decide_eq_true_eq] at h
    simp only [inBox, inRange, Bool.and_eq_true, decide_eq_true_eq] at ha
    simp only [inBox, inRange, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
    rcases h with h | h
    · left; omega
    · right; exact inBox_of_apart h ha.2
  | [], _, _, h, _ => by simp [boxesApart] at h
  | _ :: _, [], _, h, _ => by simp [boxesApart] at h
  | _ :: _, _ :: _, [], _, ha => by simp [inBox] at ha

theorem countP_add_le {α : Type} (l : List α) (p q r : α → Bool)
    (hdis : ∀ x ∈ l, ¬ (p x = true ∧ q x = true)) (hsub : ∀ x ∈ l, p x = true ∨ q x = true → r x = true) :
    l.countP p + l.countP q ≤ l.countP r := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    have h := ih (fun x hx => hdis x (List.mem_cons_of_mem a hx))
      (fun x hx => hsub x (List.mem_cons_of_mem a hx))
    have ha := hdis a List.mem_cons_self
    have hs := hsub a List.mem_cons_self
    cases hp : p a <;> cases hq : q a <;> cases hr : r a <;> simp_all <;> omega

/-- The inputs of the certified boxes are at most the inputs of the space with property `P`, if every
    input of a certified box has it, no two boxes share an input and every box lies in the space. -/
theorem certifiedCount_le {space : List Nat} {P : Input → Bool} :
    ∀ {boxes : List Box} {vs : List Bool},
      pairwiseApart boxes = true → (boxes.all fun b => fits b space) = true →
      (∀ (i : Nat) (box : Box), boxes[i]? = some box → vs[i]? = some true →
        ∀ x, inBox box x = true → P x = true) →
      certifiedCount boxes vs ≤ (allInputs space).countP fun x => P x && boxes.any fun b => inBox b x
  | [], _, _, _, _ => by simp [certifiedCount]
  | _ :: _, [], _, _, _ => by simp [certifiedCount]
  | b :: bs, v :: vs, hap, hfit, hok => by
    simp only [pairwiseApart, Bool.and_eq_true] at hap
    simp only [List.all_cons, Bool.and_eq_true] at hfit
    have ih := certifiedCount_le (boxes := bs) (vs := vs) hap.2 hfit.2
      (fun i box hb hv x hx => hok (i + 1) box (by simpa using hb) (by simpa using hv) x hx)
    simp only [certifiedCount]
    cases v with
    | false =>
      simp only [cond_false, Nat.zero_add]
      refine Nat.le_trans ih (List.countP_mono_left fun x _ h => ?_)
      simp only [Bool.and_eq_true, List.any_cons, Bool.or_eq_true] at h ⊢
      exact ⟨h.1, Or.inr h.2⟩
    | true =>
      simp only [cond_true]
      rw [← countP_inBox space b hfit.1]
      refine Nat.le_trans (Nat.add_le_add_left ih _) (countP_add_le _ _ _ _ ?_ ?_)
      · intro x _ ⟨hb, hrest⟩
        simp only [Bool.and_eq_true, List.any_eq_true] at hrest
        obtain ⟨b', hb', hx'⟩ := hrest.2
        have hapart : boxesApart b b' = true := List.all_eq_true.mp hap.1 b' hb'
        rw [inBox_of_apart hapart hb] at hx'
        cases hx'
      · intro x _ h
        simp only [Bool.and_eq_true, List.any_cons, Bool.or_eq_true] at h ⊢
        rcases h with h | h
        · exact ⟨hok 0 b rfl rfl x h, Or.inl h⟩
        · exact ⟨h.1, Or.inr h.2⟩

open Classical in
/-- The same, against the number of inputs the network answers correctly. -/
theorem certifiedCount_le_numCorrect {g : Graph} {w : Weights ℚ} {task : Task} {boxes : List Box}
    {vs : List Bool} (hap : pairwiseApart boxes = true)
    (hfit : (boxes.all fun b => fits b task.space) = true)
    (hok : ∀ (i : Nat) (box : Box), boxes[i]? = some box → vs[i]? = some true →
      ∀ x, inBox box x = true → Correct g w task x) :
    certifiedCount boxes vs ≤ numCorrect g w task := by
  unfold numCorrect
  refine Nat.le_trans (certifiedCount_le (P := fun x => decide (Correct g w task x)) hap hfit
    (fun i box hb hv x hx => decide_eq_true (hok i box hb hv x hx))) ?_
  exact List.countP_mono_left fun x _ h => by
    simp only [Bool.and_eq_true] at h
    exact h.1

end CompactCheck
