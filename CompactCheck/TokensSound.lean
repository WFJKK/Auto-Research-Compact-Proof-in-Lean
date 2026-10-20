import CompactCheck.TokensLeaveSound

/-!
# Soundness of token_interval leaves: the operations

`tevalOp_sim`: on an input `x` of the leaf, every value the token evaluator
computes is related to the real value (`TRel`), operation by operation: the
token rules (`TokensSepSound.lean`, `TokensMixSound.lean`), leaving the
domain (`TokensLeaveSound.lean`), the operations on values per input
(`tVarOp_sim`), and the interval operations for everything else
(`gevalOp_sim`).

`TokensLeafSound.lean` bounds the margin (`lowestMargin_sound`) and proves
the leaf correct (`generalTokenInterval_correct`).
-/

namespace CompactCheck

/-! ## Operations on values per input -/

/-- The values of an argument input by input: each encloses a real value,
    `x`'s the real argument. -/
theorem varSlices_sim {g : Graph} {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x)
    (hal : ctx.aligned = true) {u : TV} {t : Tensor ℝ} {f : ℕ → DT} (hu : TRel g ctx x u t)
    (h : varSlices ctx u = some f) :
    (∀ i < ctx.k, ∃ T, (f i).Encl T) ∧ (f (inputIdx ctx x)).Encl t := by
  cases u with
  | dt d =>
    simp only [varSlices, Option.some.injEq] at h
    subst h
    exact ⟨fun _ _ => ⟨t, hu⟩, hu⟩
  | box => simp [varSlices, tToVar] at h
  | _ =>
    simp only [varSlices] at h
    obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h
    have hv := tToVar_sim hf hal hu (fun d hd => by cases hd) hxs
    exact ⟨hv.2.1, hv.2.2⟩

theorem varEach_val {ctx : TCtx} {F : ℕ → Option DT} {v : TV} (h : varEach ctx F = .val v) :
    ∃ arr : Array DT, v = .var arr ∧ arr.size = ctx.k ∧
      ∀ i < ctx.k, F i = some (arr.getD i emptyDT) := by
  unfold varEach at h
  cases hm : (Array.range ctx.k).mapM F with
  | none => simp [hm, Step.ofOption] at h
  | some arr =>
    simp only [hm, Option.map_some, Step.ofOption] at h
    cases h
    obtain ⟨hsz, hper⟩ := array_mapM_range hm
    exact ⟨arr, rfl, hsz, fun i hi => hper i hi emptyDT⟩

/-- Values per input made input by input: related to the real value of
    `x`'s input. -/
theorem varEach_sim {g : Graph} {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x)
    {F : ℕ → Option DT} {v : TV} (h : varEach ctx F = .val v)
    (hall : ∀ i < ctx.k, ∀ d, F i = some d → ∃ T, d.Encl T) :
    ∃ d, F (inputIdx ctx x) = some d ∧ ∀ t', d.Encl t' → TRel g ctx x v t' := by
  obtain ⟨arr, rfl, hsz, hper⟩ := varEach_val h
  refine ⟨_, hper _ hf.idx_lt, fun t' ht' => ⟨hsz, fun i hi => hall i hi _ (hper i hi), ht'⟩⟩

theorem forall₂_one {β γ : Type} {R : β → γ → Prop} {a : β} {l : List γ}
    (h : List.Forall₂ R [a] l) : ∃ u, l = [u] ∧ R a u := by
  cases h with
  | cons h1 h2 => cases h2; exact ⟨_, rfl, h1⟩

theorem forall₂_two {β γ : Type} {R : β → γ → Prop} {a b : β} {l : List γ}
    (h : List.Forall₂ R [a, b] l) : ∃ u1 u2, l = [u1, u2] ∧ R a u1 ∧ R b u2 := by
  cases h with
  | cons h1 h2 =>
    cases h2 with
    | cons h3 h4 => cases h4; exact ⟨_, _, rfl, h1, h3⟩

/-- An argument of an operation, related to the real value. -/
def ArgR (g : Graph) (ctx : TCtx) (x : Input) (rvals : Array (Tensor ℝ)) (a : ℕ) (u : TV) : Prop :=
  ∃ t, rvals[a]? = some t ∧ TRel g ctx x u t

/-- **The operations on values per input** keep the relation. -/
theorem tVarOp_sim {g : Graph} {w : Weights ℚ} {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x)
    {rvals : Array (Tensor ℝ)} {op : Op} {args : List TV} {v : TV}
    (hargs : List.Forall₂ (ArgR g ctx x rvals) op.args args) (h : tVarOp ctx op args = .val v) :
    ∃ t, semOp g (realWeights w) x rvals op = some t ∧ TRel g ctx x v t := by
  unfold tVarOp at h
  by_cases hal : ctx.aligned = true
  · simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases op with
    | binary f a b =>
      obtain ⟨u1, u2, rfl, ⟨t1, ht1, hu1⟩, ⟨t2, ht2, hu2⟩⟩ := forall₂_two hargs
      simp only at h
      cases hs1 : varSlices ctx u1 with
      | none => simp [hs1] at h
      | some f1 =>
        cases hs2 : varSlices ctx u2 with
        | none => simp [hs1, hs2] at h
        | some f2 =>
          simp only [hs1, hs2] at h
          obtain ⟨hall1, hx1⟩ := varSlices_sim hf hal hu1 hs1
          obtain ⟨hall2, hx2⟩ := varSlices_sim hf hal hu2 hs2
          obtain ⟨d, hd, hrel⟩ := varEach_sim hf h (fun i hi d hd => by
            obtain ⟨T1, hT1⟩ := hall1 i hi
            obtain ⟨T2, hT2⟩ := hall2 i hi
            obtain ⟨T, -, hT⟩ := dbinary_sim hT1 hT2 hd
            exact ⟨T, hT⟩)
          obtain ⟨T, hT, hdT⟩ := dbinary_sim hx1 hx2 hd
          exact ⟨T, by simp only [semOp, ht1, ht2, hT], hrel T hdT⟩
    | neg a =>
      obtain ⟨u, rfl, ⟨t1, ht1, hu⟩⟩ := forall₂_one hargs
      simp only at h
      cases hs : varSlices ctx u with
      | none => simp [hs] at h
      | some f1 =>
        simp only [hs] at h
        obtain ⟨hall, hx⟩ := varSlices_sim hf hal hu hs
        obtain ⟨d, hd, hrel⟩ := varEach_sim hf h (fun i hi d hd => by
          obtain ⟨T1, hT1⟩ := hall i hi
          simp only [Option.some.injEq] at hd
          subst hd
          exact ⟨_, dneg_encl hT1⟩)
        simp only [Option.some.injEq] at hd
        subst hd
        exact ⟨t1.map Neg.neg, by simp only [semOp, ht1, Option.map_some], hrel _ (dneg_encl hx)⟩
    | matmul a b =>
      obtain ⟨u1, u2, rfl, ⟨t1, ht1, hu1⟩, ⟨t2, ht2, hu2⟩⟩ := forall₂_two hargs
      simp only at h
      split_ifs at h with hdom
      cases hs1 : varSlices ctx u1 with
      | none => simp [hs1] at h
      | some f1 =>
        cases u2 with
        | dt b2 =>
          simp only [hs1] at h
          obtain ⟨hall1, hx1⟩ := varSlices_sim hf hal hu1 hs1
          obtain ⟨d, hd, hrel⟩ := varEach_sim hf h (fun i hi d hd => by
            obtain ⟨T1, hT1⟩ := hall1 i hi
            obtain ⟨T, -, hT⟩ := dmatmul_sim hT1 hu2 hd
            exact ⟨T, hT⟩)
          obtain ⟨T, hT, hdT⟩ := dmatmul_sim hx1 hu2 hd
          exact ⟨T, by simp only [semOp, ht1, ht2, hT], hrel T hdT⟩
        | _ => simp [TV.isDomain] at hdom
    | unsqueeze a dim =>
      obtain ⟨u, rfl, ⟨t1, ht1, hu⟩⟩ := forall₂_one hargs
      simp only at h
      cases hs : varSlices ctx u with
      | none => simp [hs] at h
      | some f1 =>
        simp only [hs] at h
        obtain ⟨hall, hx⟩ := varSlices_sim hf hal hu hs
        obtain ⟨d, hd, hrel⟩ := varEach_sim hf h (fun i hi d hd => by
          obtain ⟨T1, hT1⟩ := hall i hi
          obtain ⟨T, -, hT⟩ := dtUnsqueeze_sim hT1 hd
          exact ⟨T, hT⟩)
        obtain ⟨T, hT, hdT⟩ := dtUnsqueeze_sim hx hd
        exact ⟨T, by simp only [semOp, ht1, Option.bind_some, hT], hrel T hdT⟩
    | sum a dim =>
      obtain ⟨u, rfl, ⟨t1, ht1, hu⟩⟩ := forall₂_one hargs
      simp only at h
      cases hs : varSlices ctx u with
      | none => simp [hs] at h
      | some f1 =>
        simp only [hs] at h
        obtain ⟨hall, hx⟩ := varSlices_sim hf hal hu hs
        obtain ⟨d, hd, hrel⟩ := varEach_sim hf h (fun i hi d hd => by
          obtain ⟨T1, hT1⟩ := hall i hi
          obtain ⟨T, -, hT⟩ := dsum_sim hT1 hd
          exact ⟨T, hT⟩)
        obtain ⟨T, hT, hdT⟩ := dsum_sim hx hd
        refine ⟨T, ?_, hrel T hdT⟩
        change evalOp g (realWeights w) x rvals (.sum a dim) = some T
        simp only [evalOp, ht1, hT]
    | softmax a dim =>
      obtain ⟨u, rfl, ⟨t1, ht1, hu⟩⟩ := forall₂_one hargs
      simp only at h
      cases hs : varSlices ctx u with
      | none => simp [hs] at h
      | some f1 =>
        simp only [hs] at h
        obtain ⟨hall, hx⟩ := varSlices_sim hf hal hu hs
        obtain ⟨d, hd, hrel⟩ := varEach_sim hf h (fun i hi d hd => by
          obtain ⟨T1, hT1⟩ := hall i hi
          obtain ⟨T, -, hT⟩ := dsoftmax_sim hT1 hd
          exact ⟨T, hT⟩)
        obtain ⟨T, hT, hdT⟩ := dsoftmax_sim hx hd
        exact ⟨T, by simp only [semOp, ht1, Option.bind_some, hT], hrel T hdT⟩
    | exp a =>
      obtain ⟨u, rfl, ⟨t1, ht1, hu⟩⟩ := forall₂_one hargs
      simp only at h
      cases hs : varSlices ctx u with
      | none => simp [hs] at h
      | some f1 =>
        simp only [hs] at h
        obtain ⟨hall, hx⟩ := varSlices_sim hf hal hu hs
        obtain ⟨d, hd, hrel⟩ := varEach_sim hf h (fun i hi d hd => by
          obtain ⟨T1, hT1⟩ := hall i hi
          exact ⟨_, dexp_sim hT1 hd⟩)
        exact ⟨t1.map Real.exp, by simp only [semOp, ht1, Option.map_some]; rfl,
          hrel _ (dexp_sim hx hd)⟩
    | index a items =>
      obtain ⟨u, rfl, ⟨t1, ht1, hu⟩⟩ := forall₂_one hargs
      simp only at h
      cases hs : varSlices ctx u with
      | none => simp [hs] at h
      | some f1 =>
        simp only [hs] at h
        obtain ⟨hall, hx⟩ := varSlices_sim hf hal hu hs
        obtain ⟨d, hd, hrel⟩ := varEach_sim hf h (fun i hi d hd => by
          obtain ⟨T1, hT1⟩ := hall i hi
          obtain ⟨T, -, hT⟩ := dtIndex_sim hT1 hd
          exact ⟨T, hT⟩)
        obtain ⟨T, hT, hdT⟩ := dtIndex_sim hx hd
        exact ⟨T, by simp only [semOp, ht1, Option.bind_some, hT], hrel T hdT⟩
    | input => cases hargs; simp at h
    | linear a wn bn =>
      obtain ⟨u, rfl, -⟩ := forall₂_one hargs
      simp at h
    | add a b =>
      obtain ⟨u1, u2, rfl, -, -⟩ := forall₂_two hargs
      simp at h
    | param n => cases hargs; simp at h
    | transpose a =>
      obtain ⟨u, rfl, -⟩ := forall₂_one hargs
      simp at h
    | expand a s =>
      obtain ⟨u, rfl, -⟩ := forall₂_one hargs
      simp at h
    | cat as d => simp at h
    | stack as d => simp at h
    | zerosLike a =>
      obtain ⟨u, rfl, -⟩ := forall₂_one hargs
      simp at h
  · simp [hal] at h

/-! ## Sums and products with constants -/

theorem tAdd_sim {g : Graph} {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {u1 u2 v : TV}
    {t1 t2 : Tensor ℝ} (hu1 : TRel g ctx x u1 t1) (hu2 : TRel g ctx x u2 t2)
    (h : tAdd u1 u2 = .val v) :
    ∃ t, broadcastOp BinOp.add.apply t1 t2 = some t ∧ TRel g ctx x v t := by
  rcases u1 with _ | s1 | m1 | ⟨w1, s1⟩ | ⟨ws1, s1⟩ | vs1 | d1 <;>
  rcases u2 with _ | s2 | m2 | ⟨w2, s2⟩ | ⟨ws2, s2⟩ | vs2 | d2 <;>
  simp only [tAdd, reduceCtorEq] at h
  · obtain ⟨s', hs', h2⟩ := Step.bind_eq_val' h
    cases h2
    exact (addConst_sim hf hu1 hu2 hs').1
  · obtain ⟨m', hm', h2⟩ := Step.bind_eq_val' h
    cases h2
    exact addMixes_sim hu1 hu2 hm'
  · obtain ⟨m', hm', h2⟩ := Step.bind_eq_val' h
    cases h2
    exact (addMix_sim hu1 hu2 hm').1
  · obtain ⟨s', hs', h2⟩ := Step.bind_eq_val' h
    cases h2
    exact (addConst_sim hf hu2 hu1 hs').2
  · obtain ⟨m', hm', h2⟩ := Step.bind_eq_val' h
    cases h2
    exact (addMix_sim hu2 hu1 hm').2

theorem shapeSize_eq_one {s : List ℕ} (h : shapeSize s = 1) : s = List.replicate s.length 1 := by
  induction s with
  | nil => rfl
  | cons d s ih =>
    rw [shapeSize_cons] at h
    have h1 := Nat.eq_one_of_mul_eq_one_right h
    have h2 := Nat.eq_one_of_mul_eq_one_left h
    rw [h1, List.length_cons, List.replicate_succ, ← ih h2]

/-- A product with one number keeps the shape. -/
theorem mul_scalar_real {t C : Tensor ℝ} {rest : List ℕ} (hts : t.shape = 1 :: rest)
    (htwf : t.wellFormed = true) (hCwf : C.wellFormed = true) (hC1 : shapeSize C.shape = 1)
    (hClen : C.shape.length ≤ (1 :: rest).length) :
    (∃ t', broadcastOp BinOp.mul.apply t C = some t' ∧ t'.shape = t.shape ∧
      t'.data.size = t.data.size ∧ ∀ q < t.data.size, t'.get q = t.get q * C.get 0) ∧
    (∃ t', broadcastOp BinOp.mul.apply C t = some t' ∧ t'.shape = t.shape ∧
      t'.data.size = t.data.size ∧ ∀ q < t.data.size, t'.get q = t.get q * C.get 0) := by
  have hCs := shapeSize_eq_one hC1
  have hfit : (List.zipWith (fun d f => d == f || d == 1) C.shape
      ((1 :: rest).drop ((1 :: rest).length - C.shape.length))).all id = true := by
    rw [hCs]
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    simp
  obtain ⟨hbs1, hbs2⟩ := broadcastShape_of_fits hClen hfit
  rw [← hts] at hbs1 hbs2
  have htsz : t.data.size = shapeSize t.shape := by simpa [Tensor.wellFormed] using htwf
  have hle : C.shape.length ≤ t.shape.length := by rw [hts]; exact hClen
  obtain ⟨n, hCn⟩ : ∃ n, C.shape = List.replicate n 1 := ⟨_, hCs⟩
  have hentry : ∀ q < shapeSize t.shape,
      C.entry (broadcastIndex C.shape (unravel t.shape q)) = C.get 0 := by
    intro q _
    have hlen : ((unravel t.shape q).drop ((unravel t.shape q).length - n)).length = n := by
      simp only [List.length_drop, unravel_length]
      rw [hCn, List.length_replicate] at hle
      omega
    unfold broadcastIndex
    rw [hCn, List.length_replicate, zipWith_bcast_replicate_one _ _ hlen, Tensor.entry_eq, hCn,
      ravel_zeros]
  constructor
  · obtain ⟨h1, h2, h3⟩ := broadcastOp_full_left rfl (broadcastOp_eq BinOp.mul.apply htwf hCwf hbs1)
      hbs1
    refine ⟨_, broadcastOp_eq BinOp.mul.apply htwf hCwf hbs1, h1, by rw [h2, htsz], fun q hq => ?_⟩
    rw [htsz] at hq
    rw [h3 q hq, hentry q hq]
    rfl
  · obtain ⟨h1, h2, h3⟩ :=
      broadcastOp_full_right rfl (broadcastOp_eq BinOp.mul.apply hCwf htwf hbs2)
      hbs2
    refine ⟨_, broadcastOp_eq BinOp.mul.apply hCwf htwf hbs2, h1, by rw [h2, htsz], fun q hq => ?_⟩
    rw [htsz] at hq
    rw [h3 q hq, hentry q hq]
    simp only [BinOp.apply]
    ring

theorem scalar_encl {c : DT} {C : Tensor ℝ} (hc : c.Encl C) :
    (⟨[], #[c.lo.getD 0 0], #[c.hi.getD 0 0], c.e, c.exact⟩ : DT).Encl ⟨[], #[C.get 0]⟩ := by
  refine DT.Encl.mk rfl rfl rfl rfl (fun hx => ?_) (fun j hj => ?_)
  · simp only at hx
    rw [hc.2.2.2.2.1 hx]
  · have : j = 0 := by simpa [shapeSize] using hj
    subst this
    have := hc.2.2.2.2.2 0
    simpa [mget, Tensor.get] using this

theorem mulMix_sim {g : Graph} {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {m : Mix} {c : DT}
    {t C : Tensor ℝ} {v : TV} (hm : MixR ctx x m t) (hc : c.Encl C)
    (h : (if shapeSize c.shape == 1 && c.ok && c.shape.length ≤ m.const.shape.length then
      (scaleMix m ⟨[], #[c.lo.getD 0 0], #[c.hi.getD 0 0], c.e, c.exact⟩).bind fun m =>
        .val (.mix m)
      else .decline) = .val v) :
    (∃ t', broadcastOp BinOp.mul.apply t C = some t' ∧ TRel g ctx x v t') ∧
    (∃ t', broadcastOp BinOp.mul.apply C t = some t' ∧ TRel g ctx x v t') := by
  split_ifs at h with hcond
  obtain ⟨m', hm', h2⟩ := Step.bind_eq_val' h
  cases h2
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
  obtain ⟨⟨hc1, -⟩, hlen⟩ := hcond
  have hm2 := hm
  obtain ⟨rest, hcrest, hts, htsz, -⟩ := hm2
  have htwf : t.wellFormed = true := by simp [Tensor.wellFormed, hts, htsz, shapeSize_cons]
  have hC1 : shapeSize C.shape = 1 := by rw [hc.1, hc1]
  have hClen : C.shape.length ≤ (1 :: rest).length := by rw [hc.1, ← hcrest]; exact hlen
  obtain ⟨⟨t', ht', h1s, h1sz, h1get⟩, ⟨t'', ht'', h2s, h2sz, h2get⟩⟩ :=
    mul_scalar_real hts htwf hc.wf hC1 hClen
  exact ⟨⟨t', ht', scaleMix_sim hf hm (scalar_encl hc) hm' h1s h1sz h1get⟩,
    ⟨t'', ht'', scaleMix_sim hf hm (scalar_encl hc) hm' h2s h2sz h2get⟩⟩

theorem tMul_sim {g : Graph} {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {u1 u2 v : TV}
    {t1 t2 : Tensor ℝ} (hu1 : TRel g ctx x u1 t1) (hu2 : TRel g ctx x u2 t2)
    (h : tMul u1 u2 = .val v) :
    ∃ t, broadcastOp BinOp.mul.apply t1 t2 = some t ∧ TRel g ctx x v t := by
  rcases u1 with _ | s1 | m1 | ⟨w1, s1⟩ | ⟨ws1, s1⟩ | vs1 | d1 <;>
  rcases u2 with _ | s2 | m2 | ⟨w2, s2⟩ | ⟨ws2, s2⟩ | vs2 | d2 <;>
  simp only [tMul, TV.isDomain, Bool.and_self, Bool.and_true,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
  · exact (mulSep_sim hf hu1 hu2 h).1
  · exact (mulMix_sim hf hu1 hu2 h).1
  · exact (mulSep_sim hf hu2 hu1 h).2
  · exact (mulMix_sim hf hu2 hu1 h).2

/-! ## Sums over a dimension -/

theorem normDim_of {dim : ℤ} {r j : ℕ} (hd : (if dim ≥ 0 then dim else (r : ℤ) + dim) = (j : ℤ))
    (hj : j < r) : normDim dim r = some j := by
  unfold normDim
  by_cases h1 : dim ≥ 0
  · rw [ite_eq_left h1] at hd
    have h2 : ¬ dim < 0 := by omega
    rw [ite_eq_right h2, ite_eq_left (by omega)]
    simp only [Option.some.injEq]
    omega
  · rw [ite_eq_right h1] at hd
    have h2 : dim < 0 := by omega
    rw [ite_eq_left h2, ite_eq_left (by omega)]
    simp only [Option.some.injEq]
    omega

/-- The dimension a sum over a token value reads. -/
theorem tSum_dim {dim : ℤ} {L : ℕ} {t : Tensor ℝ} (hL : t.shape.length = L) {d : ℤ}
    (hd : (if dim ≥ 0 then dim else (L : ℤ) + dim) = d) {j : ℕ} (hj : d = j) (hjL : j < L) :
    normDim dim t.shape.length = some j := by
  rw [hL]
  exact normDim_of (by rw [hd, hj]) hjL

theorem tSum_sim {g : Graph} {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {u v : TV}
    {t : Tensor ℝ} {dim : ℤ} (hu : TRel g ctx x u t) (h : tSum ctx u dim = .val v) :
    ∃ t', sumOp dim t = some t' ∧ TRel g ctx x v t' := by
  unfold tSum at h
  dsimp only at h
  generalize hd : (if dim ≥ 0 then dim else ((u.shape ctx).length : ℤ) + dim) = d at h
  rcases u with _ | s | m | ⟨w, s⟩ | ⟨ws, s⟩ | vs | dd <;> simp only [reduceCtorEq] at h
  · -- a value kept per token
    have hts : t.shape = 1 :: s.rows.length :: s.rest := by rw [hu.2.2.1, hu.2.1]
    have hL : t.shape.length = (TV.shape ctx (.sep s)).length := by
      rw [hts]; simp [TV.shape, Sep.shape]
    split_ifs at h with h1 h2
    · obtain ⟨m', hm', h3⟩ := Step.bind_eq_val' h
      cases h3
      simp only [beq_iff_eq] at h1
      have hnd : normDim dim t.shape.length = some 1 :=
        tSum_dim hL hd (by rw [h1]; rfl) (by simp [TV.shape, Sep.shape])
      exact sumPositions_sim hu (fun p _ wp hwp => wOf_none ctx x p s.rest hwp) hnd hm'
    · obtain ⟨s', hs', h3⟩ := Step.bind_eq_val' h
      cases h3
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      have hnd : normDim dim t.shape.length = some d.toNat :=
        tSum_dim hL hd (Int.toNat_of_nonneg (by omega)).symm (by omega)
      exact sumRows_sim hf hu hnd (by omega) hs'
  · -- a `WSep`
    obtain ⟨hws, W, hwW, hsep⟩ := hu
    have hts : t.shape = 1 :: s.rows.length :: s.rest := by rw [hsep.2.2.1, hsep.2.1]
    have hL : t.shape.length = (TV.shape ctx (.wsep w s)).length := by
      rw [hts]; simp [TV.shape, Sep.shape]
    split_ifs at h with h1
    obtain ⟨m', hm', h3⟩ := Step.bind_eq_val' h
    cases h3
    simp only [beq_iff_eq] at h1
    have hnd : normDim dim t.shape.length = some 1 :=
      tSum_dim hL hd (by rw [h1]; rfl) (by simp [TV.shape, Sep.shape])
    exact sumPositions_sim hsep (fun p _ wp hwp => wOf_inl hwW hws hwp) hnd hm'
  · -- a `WSep` with weights per input
    obtain ⟨hwsz, hall, W, hwW, hsep⟩ := hu
    have hts : t.shape = 1 :: s.rows.length :: s.rest := by rw [hsep.2.2.1, hsep.2.1]
    have hL : t.shape.length = (TV.shape ctx (.wsepv ws s)).length := by
      rw [hts]; simp [TV.shape, Sep.shape]
    split_ifs at h with h1
    obtain ⟨m', hm', h3⟩ := Step.bind_eq_val' h
    cases h3
    simp only [beq_iff_eq] at h1
    have hnd : normDim dim t.shape.length = some 1 :=
      tSum_dim hL hd (by rw [h1]; rfl) (by simp [TV.shape, Sep.shape])
    exact sumPositions_sim hsep (fun p _ wp hwp => wOf_inr hf hwsz hall hwW hwp) hnd hm'

/-! ## The token rules -/

theorem forall₂_pair {β γ : Type} {R : β → γ → Prop} {a b : β} {u1 u2 : γ}
    (h : List.Forall₂ R [a, b] [u1, u2]) : R a u1 ∧ R b u2 := by
  cases h with
  | cons h1 h2 => cases h2 with
    | cons h3 _ => exact ⟨h1, h3⟩

theorem forall₂_single {β γ : Type} {R : β → γ → Prop} {a : β} {u : γ}
    (h : List.Forall₂ R [a] [u]) : R a u := by
  cases h with
  | cons h1 _ => exact h1

theorem shapes_of_guard {bs rest : List ℕ} (h1 : bs.length = 2) (h2 : rest.length = 1)
    (h3 : bs.head? = rest.head?) : ∃ dd d', rest = [dd] ∧ bs = [dd, d'] := by
  match bs, rest, h1, h2 with
  | [p, q], [r], _, _ =>
    simp only [List.head?_cons, Option.some.injEq] at h3
    exact ⟨r, q, rfl, by rw [h3]⟩

theorem const_shapes_of_guard {bs cs : List ℕ} {rest : List ℕ} (hcs : cs = 1 :: rest)
    (h1 : bs.length = 2) (h2 : cs.length = 2) (h3 : bs.head? = cs.getLast?) :
    ∃ dd d', cs = [1, dd] ∧ bs = [dd, d'] := by
  subst hcs
  match bs, rest, h1, h2 with
  | [p, q], [r], _, _ =>
    simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at h3
    exact ⟨r, q, rfl, by rw [h3]⟩

/-- **The token rules** keep the relation. -/
theorem tEvaluate_sim {g : Graph} {w : Weights ℚ} {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x)
    (hval : ctx.values = g.values) {rvals : Array (Tensor ℝ)} {free : ℕ → Bool} {op : Op}
    {args : List TV} {v : TV} (hargs : List.Forall₂ (ArgR g ctx x rvals) op.args args)
    (h : tEvaluate ctx free op args = .val v) :
    ∃ t, semOp g (realWeights w) x rvals op = some t ∧ TRel g ctx x v t := by
  unfold tEvaluate at h
  split at h
  · -- the lookup
    simp only [Op.args] at hargs
    obtain ⟨⟨t1, ht1, hu1⟩, ⟨t2, ht2, hu2⟩⟩ := forall₂_pair hargs
    split at h
    · split_ifs at h
      obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp (Step.ofOption_eq_val h)
      obtain ⟨t, ht, hst⟩ := tLookup_sim hf hval hu1.2 hu2 hs
      exact ⟨t, by simp only [semOp, ht1, ht2, ht], hst⟩
    · cases h
  · cases h
  · -- per-input weights times a value kept per token
    simp only [Op.args] at hargs
    obtain ⟨⟨t1, ht1, hu1⟩, ⟨t2, ht2, hu2⟩⟩ := forall₂_pair hargs
    obtain ⟨t, ht, hvt⟩ := (mulVarSep_sim (g := g) hf hu1 hu2 h).1
    exact ⟨t, by simp only [semOp, ht1, ht2, ht], hvt⟩
  · simp only [Op.args] at hargs
    obtain ⟨⟨t1, ht1, hu1⟩, ⟨t2, ht2, hu2⟩⟩ := forall₂_pair hargs
    obtain ⟨t, ht, hvt⟩ := (mulVarSep_sim (g := g) hf hu2 hu1 h).2
    exact ⟨t, by simp only [semOp, ht1, ht2, ht], hvt⟩
  · split_ifs at h with hvar
    · exact tVarOp_sim hf hargs h
    · split at h
      · -- a product of rows with a matrix
        simp only [Op.args] at hargs
        obtain ⟨⟨t1, ht1, hu1⟩, ⟨t2, ht2, hu2⟩⟩ := forall₂_pair hargs
        split_ifs at h with hg
        obtain ⟨s', hs', h2⟩ := Step.bind_eq_val' h
        cases h2
        simp only [Bool.and_eq_true, beq_iff_eq] at hg
        obtain ⟨⟨⟨hg1, hg2⟩, hg3⟩, hg4⟩ := hg
        obtain ⟨dd, d', hrest, hbs⟩ := shapes_of_guard hg1 hg3 hg4
        obtain ⟨t, ht, hst⟩ := matmulSep_sim hf hu1 hu2 hg2 hrest hbs hs'
        exact ⟨t, by simp only [semOp, ht1, ht2, ht], hst⟩
      · simp only [Op.args] at hargs
        obtain ⟨⟨t1, ht1, hu1⟩, ⟨t2, ht2, hu2⟩⟩ := forall₂_pair hargs
        split_ifs at h with hg
        obtain ⟨m', hm', h2⟩ := Step.bind_eq_val' h
        cases h2
        simp only [Bool.and_eq_true, beq_iff_eq] at hg
        obtain ⟨⟨⟨hg1, hg2⟩, hg3⟩, hg4⟩ := hg
        obtain ⟨rest, hcrest, -⟩ := id hu1
        obtain ⟨dd, d', hcs, hbs⟩ := const_shapes_of_guard hcrest hg1 hg3 hg4
        obtain ⟨t, ht, hmt⟩ := matmulMix_sim hf hu1 hu2 hg2 hcs hbs hm'
        exact ⟨t, by simp only [semOp, ht1, ht2, ht], hmt⟩
      · simp only [Op.args] at hargs
        obtain ⟨⟨t1, ht1, hu1⟩, ⟨t2, ht2, hu2⟩⟩ := forall₂_pair hargs
        obtain ⟨t, ht, hvt⟩ := tAdd_sim hf hu1 hu2 h
        exact ⟨t, by simp only [semOp, ht1, ht2, ht], hvt⟩
      · simp only [Op.args] at hargs
        obtain ⟨⟨t1, ht1, hu1⟩, ⟨t2, ht2, hu2⟩⟩ := forall₂_pair hargs
        obtain ⟨t, ht, hvt⟩ := tMul_sim hf hu1 hu2 h
        exact ⟨t, by simp only [semOp, ht1, ht2, ht], hvt⟩
      · -- `-x` of a `Mix`
        simp only [Op.args] at hargs
        obtain ⟨t1, ht1, hu1⟩ := forall₂_single hargs
        obtain ⟨m', hm', h2⟩ := Step.bind_eq_val' h
        cases h2
        refine ⟨t1.map Neg.neg, by simp only [semOp, ht1, Option.map_some], ?_⟩
        have hsc : (dtScalar (-1)).Encl ⟨[], #[(-1 : ℝ)]⟩ := by
          have := dtScalar_encl (-1)
          push_cast at this
          exact this
        exact scaleMix_sim hf hu1 hsc hm' (by simp [Tensor.map]) (by simp [Tensor.map])
          (fun q _ => by rw [Tensor.get_map_zero _ (by simp)]; ring)
      · simp only [Op.args] at hargs
        obtain ⟨t1, ht1, hu1⟩ := forall₂_single hargs
        obtain ⟨t, ht, hvt⟩ := tSum_sim hf hu1 h
        refine ⟨t, ?_, hvt⟩
        change evalOp g (realWeights w) x rvals (.sum _ _) = some t
        simp only [evalOp, ht1, ht]
      · simp only [Op.args] at hargs
        obtain ⟨t1, ht1, hu1⟩ := forall₂_single hargs
        obtain ⟨t, ht, hvt⟩ := tGetitem_sim (g := g) hu1 h
        exact ⟨t, by simp only [semOp, ht1, Option.bind_some, ht], hvt⟩
      · cases h

/-! ## One operation of a leaf -/

theorem args_rel {g : Graph} {ctx : TCtx} {x : Input} {vals : Array TV} {rvals : Array (Tensor ℝ)}
    (hr : ARel (TRel g ctx x) vals rvals) :
    ∀ {as : List ℕ} {args : List TV}, as.mapM (vals[·]?) = some args →
      List.Forall₂ (fun a u => vals[a]? = some u ∧ ArgR g ctx x rvals a u) as args := by
  intro as args h
  refine List.Forall₂.imp ?_ (mapM_forall₂ h)
  intro a u hu
  obtain ⟨t, ht, hut⟩ := hr.get? hu
  exact ⟨hu, t, ht, hut⟩

theorem forall₂_zip_mem {β γ : Type} {R : β → γ → Prop} :
    ∀ {l1 : List β} {l2 : List γ}, List.Forall₂ R l1 l2 → ∀ pr ∈ l1.zip l2, R pr.1 pr.2
  | [], [], _, _, h => by simp at h
  | a :: l1, b :: l2, h, pr, hpr => by
    cases h with
    | cons hab h' =>
      simp only [List.zip_cons_cons, List.mem_cons] at hpr
      rcases hpr with rfl | hpr
      · exact hab
      · exact forall₂_zip_mem h' pr hpr

theorem foldl_set_size {β : Type} {F : Array β → ℕ × β → Array β}
    (hF : ∀ acc a v, F acc (a, v) = acc.set! a v) :
    ∀ (pairs : List (ℕ × β)) (vals : Array β), (pairs.foldl F vals).size = vals.size
  | [], _ => rfl
  | (a, v) :: pairs, vals => by
    rw [List.foldl_cons, foldl_set_size hF pairs, hF, Array.set!_eq_setIfInBounds,
      Array.size_setIfInBounds]

theorem foldl_set_other {β : Type} {F : Array β → ℕ × β → Array β}
    (hF : ∀ acc a v, F acc (a, v) = acc.set! a v) :
    ∀ (pairs : List (ℕ × β)) (vals : Array β) (a : ℕ), a ∉ pairs.map Prod.fst →
      (pairs.foldl F vals)[a]? = vals[a]?
  | [], _, _, _ => rfl
  | (b, v) :: pairs, vals, a, ha => by
    simp only [List.map_cons, List.mem_cons, not_or] at ha
    rw [List.foldl_cons, foldl_set_other hF pairs _ a ha.2, hF, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (Ne.symm ha.1)]

theorem foldl_set_mem {β : Type} {F : Array β → ℕ × β → Array β}
    (hF : ∀ acc a v, F acc (a, v) = acc.set! a v) {G : ℕ → Option β} :
    ∀ (pairs : List (ℕ × β)) (vals : Array β) (a : ℕ), (∀ pr ∈ pairs, G pr.1 = some pr.2) →
      a ∈ pairs.map Prod.fst → a < vals.size → (pairs.foldl F vals)[a]? = G a
  | [], _, _, _, ha, _ => by simp at ha
  | (b, v) :: pairs, vals, a, hG, ha, hlt => by
    rw [List.foldl_cons]
    by_cases hin : a ∈ pairs.map Prod.fst
    · exact foldl_set_mem hF pairs _ a (fun pr hpr => hG pr (List.mem_cons_of_mem _ hpr)) hin
        (by rw [hF, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hlt)
    · simp only [List.map_cons, List.mem_cons] at ha
      have hab : a = b := ha.resolve_right hin
      subst hab
      rw [foldl_set_other hF pairs _ a hin, hF, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt hlt, hG (a, v) List.mem_cons_self]

theorem forall₂_comp {β γ δ : Type} {R : β → γ → Prop} {S : γ → δ → Prop} {U : β → δ → Prop}
    (hRSU : ∀ a b c, R a b → S b c → U a c) :
    ∀ {l1 : List β} {l2 : List γ} {l3 : List δ}, List.Forall₂ R l1 l2 → List.Forall₂ S l2 l3 →
      List.Forall₂ U l1 l3
  | [], [], [], _, _ => List.Forall₂.nil
  | a :: l1, b :: l2, c :: l3, h1, h2 => by
    cases h1 with
    | cons hab h1' =>
      cases h2 with
      | cons hbc h2' => exact List.Forall₂.cons (hRSU a b c hab hbc) (forall₂_comp hRSU h1' h2')

/-- The interval operations, when every argument is an interval tensor. -/
theorem plain_sim {g : Graph} {w : Weights ℚ} {dw : DWeights} (hdw : dweights w = some dw)
    {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {vals : Array TV}
    {rvals : Array (Tensor ℝ)} {op : Op} {v : TV}
    (hgen : ∀ a ∈ op.args, ∀ u, vals[a]? = some u → ∃ d t, u = .dt d ∧ rvals[a]? = some t ∧
      d.Encl t)
    (h : ((gevalOp g dw (.box ctx.box) (vals.map (·.toGVal ctx)) op).bind GVal.tensor).map TV.dt =
      some v) :
    ∃ t, semOp g (realWeights w) x rvals op = some t ∧ TRel g ctx x v t := by
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨gv, hgv, hgvd⟩ := Option.bind_eq_some_iff.mp hd
  have hin : InputRel g x (.box ctx.box) := hf.inbox
  have hargs : ArgsRel g x (vals.map (·.toGVal ctx)) rvals op.args := by
    intro a ha u hu
    rw [Array.getElem?_map] at hu
    obtain ⟨u', hu', rfl⟩ := Option.map_eq_some_iff.mp hu
    obtain ⟨d', t, rfl, ht, hdt⟩ := hgen a ha u' hu'
    exact ⟨t, ht, hdt⟩
  obtain ⟨t, ht, hrel⟩ := gevalOp_sim hdw hin hargs hgv
  cases gv with
  | box b => simp [GVal.tensor] at hgvd
  | dt d' =>
    simp only [GVal.tensor, Option.some.injEq] at hgvd
    subst hgvd
    exact ⟨t, ht, hrel⟩

/-- **One operation of a token_interval leaf** keeps the relation. -/
theorem tevalOp_sim {g : Graph} {w : Weights ℚ} {dw : DWeights} (hdw : dweights w = some dw)
    {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) (hval : ctx.values = g.values)
    {deps : Array Bool} {vals : Array TV} {rvals : Array (Tensor ℝ)}
    (hr : ARel (TRel g ctx x) vals rvals) {op : Op} {v : TV}
    (h : tevalOp g dw ctx deps vals op = some v) :
    ∃ t, semOp g (realWeights w) x rvals op = some t ∧ TRel g ctx x v t := by
  unfold tevalOp at h
  split at h
  · -- the input
    split_ifs at h with hfit
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, beq_iff_eq] at hfit
    have hok : (x.length == g.positions && x.all (· < g.values)) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨(inBox_length hf.inbox).trans hfit.1, inBox_all_lt hf.inbox hfit.2⟩
    cases ht : (oneHotInput g.positions g.values x : Option (Tensor ℝ)) with
    | none => simp [oneHotInput, hok] at ht
    | some t => exact ⟨t, ht, hf.inbox, ht⟩
  · split at h
    · cases h
    · rename_i args hargs0
      have hargs1 := args_rel hr hargs0
      have hargs : List.Forall₂ (ArgR g ctx x rvals) op.args args :=
        List.Forall₂.imp (fun _ _ h => h.2) hargs1
      dsimp only at h
      split_ifs at h with hdom
      · -- no argument in the domain
        refine plain_sim hdw hf (fun a ha u hu => ?_) h
        obtain ⟨t, ht, hut⟩ := hr.get? hu
        have hmem : u ∈ args := by
          have := forall₂_zip_mem hargs1
          obtain ⟨i, hi, hai⟩ := List.getElem_of_mem ha
          have hi' : i < args.length := by rw [← hargs1.length_eq]; exact hi
          have hrel := (List.forall₂_iff_get.mp hargs1).2 i hi hi'
          simp only [List.get_eq_getElem] at hrel
          rw [hai, hu, Option.some.injEq] at hrel
          rw [hrel.1]
          exact List.getElem_mem hi'
        cases u with
        | dt d => exact ⟨d, t, rfl, ht, hut⟩
        | _ =>
          exfalso
          simp only [Bool.not_eq_true', List.any_eq_false] at hdom
          exact absurd (hdom _ hmem) (by simp [TV.isDomain])
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          rename_i v' hev
          exact tEvaluate_sim hf hval hargs hev
        · cases h
        · -- the arguments leave the domain
          split at h
          · cases h
          · rename_i left hleft
            have hleft2 := mapM_forall₂ hleft
            -- each argument, after leaving
            have hL : ∀ (a : ℕ) (L : TV),
                (vals[a]?.bind fun v => if v.isDomain then tLeave ctx v else some v) =
                  some L → ∃ t, rvals[a]? = some t ∧ TRel g ctx x L t ∧
                  ((∃ vs, L = .var vs) ∨ (∃ d, L = .dt d)) := by
              intro a L hLa
              obtain ⟨u, hu, hu2⟩ := Option.bind_eq_some_iff.mp hLa
              obtain ⟨t, ht, hut⟩ := hr.get? hu
              split_ifs at hu2 with hd
              · exact ⟨t, ht, tLeave_sim hf hut hu2⟩
              · simp only [Option.some.injEq] at hu2
                subst hu2
                cases u with
                | dt d => exact ⟨t, ht, hut, Or.inr ⟨d, rfl⟩⟩
                | _ => simp [TV.isDomain] at hd
            have hleftR : List.Forall₂ (ArgR g ctx x rvals) op.args left := by
              refine List.Forall₂.imp (fun a L hLa => ?_) hleft2
              obtain ⟨t, ht, hLt, -⟩ := hL a L hLa
              exact ⟨t, ht, hLt⟩
            have hsize : ∀ a ∈ op.args, a < vals.size := by
              intro a ha
              obtain ⟨i, hi, hai⟩ := List.getElem_of_mem ha
              have hi' : i < args.length := by rw [← hargs1.length_eq]; exact hi
              have hrel := (List.forall₂_iff_get.mp hargs1).2 i hi hi'
              simp only [List.get_eq_getElem, hai] at hrel
              have := hrel.1
              by_contra hc
              rw [Array.getElem?_eq_none (by omega)] at this
              cases this
            have hfst : ∀ (l : List TV), l.length = op.args.length → ∀ a ∈ op.args,
                a ∈ (op.args.zip l).map Prod.fst := by
              intro l hl a ha
              rw [List.map_fst_zip (by omega)]
              exact ha
            -- the operation on the new arguments
            have hset : ∀ (l : List TV) (G : ℕ → Option TV), List.Forall₂ (fun a L => G a = some L)
                op.args l → (∀ a ∈ op.args, ∃ L d t, G a = some L ∧ L = .dt d ∧
                  rvals[a]? = some t ∧ d.Encl t) →
                (((gevalOp g dw (.box ctx.box) (((op.args.zip l).foldl
                  (fun acc (pr : ℕ × TV) => acc.set! pr.1 pr.2) vals).map (·.toGVal ctx)) op).bind
                  GVal.tensor).map TV.dt = some v) →
                ∃ t, semOp g (realWeights w) x rvals op = some t ∧ TRel g ctx x v t := by
              intro l G hlG hG hplain
              refine plain_sim hdw hf (fun a ha u hu => ?_) hplain
              rw [foldl_set_mem (G := G) (fun _ _ _ => rfl) _ vals a (forall₂_zip_mem hlG)
                (hfst l hlG.length_eq.symm a ha) (hsize a ha)] at hu
              obtain ⟨L, d, t, hGa, rfl, ht, hdt⟩ := hG a ha
              rw [hGa, Option.some.injEq] at hu
              subst hu
              exact ⟨d, t, rfl, ht, hdt⟩
            split_ifs at h with hvar
            · split at h
              · simp only [Option.some.injEq] at h
                subst h
                rename_i v' hvo
                exact tVarOp_sim hf hleftR hvo
              · cases h
              · split at h
                · cases h
                · rename_i boxed hboxed
                  have hboxed2 := mapM_forall₂ hboxed
                  let G : ℕ → Option TV := fun a =>
                    (vals[a]?.bind fun v => if v.isDomain then tLeave ctx v else some v).bind
                      fun v => match v with
                        | .var vs => (collapseVar vs).map TV.dt
                        | v => some v
                  refine hset boxed G ?_ ?_ h
                  · -- the boxed arguments, argument by argument
                    exact forall₂_comp (fun a L B hLa hLB => show G a = some B from by
                      simp only [G, hLa, Option.bind_some]
                      exact hLB) hleft2 hboxed2
                  · intro a ha
                    obtain ⟨i, hi, hai⟩ := List.getElem_of_mem ha
                    have hi1 : i < left.length := by rw [← hleft2.length_eq]; exact hi
                    have hi2 : i < boxed.length := by rw [← hboxed2.length_eq]; exact hi1
                    have hLa := (List.forall₂_iff_get.mp hleft2).2 i hi hi1
                    have hLB := (List.forall₂_iff_get.mp hboxed2).2 i hi1 hi2
                    simp only [List.get_eq_getElem, hai] at hLa hLB
                    obtain ⟨t, ht, hLt, hkind⟩ := hL a _ hLa
                    rcases hkind with ⟨vs, hvs⟩ | ⟨d, hd⟩
                    · rw [hvs] at hLB hLt
                      simp only at hLB
                      obtain ⟨d, hd, hdB⟩ := Option.map_eq_some_iff.mp hLB
                      refine ⟨_, d, t, ?_, hdB.symm, ht, collapseVar_sim hf hLt hd⟩
                      simp only [G, hLa, Option.bind_some, hvs, hd, Option.map_some]
                      rw [hdB]
                    · rw [hd] at hLB hLt
                      simp only [Option.some.injEq] at hLB
                      refine ⟨_, d, t, ?_, hLB.symm, ht, hLt⟩
                      simp only [G, hLa, Option.bind_some, hd]
                      rw [hLB]
            · refine hset left (fun a => vals[a]?.bind fun v =>
                if v.isDomain then tLeave ctx v else some v) hleft2 ?_ h
              intro a ha
              obtain ⟨i, hi, hai⟩ := List.getElem_of_mem ha
              have hi1 : i < left.length := by rw [← hleft2.length_eq]; exact hi
              have hLa := (List.forall₂_iff_get.mp hleft2).2 i hi hi1
              simp only [List.get_eq_getElem, hai] at hLa
              obtain ⟨t, ht, hLt, hkind⟩ := hL a _ hLa
              rcases hkind with ⟨vs, hvs⟩ | ⟨d, hd⟩
              · exfalso
                simp only [Bool.not_eq_true, List.any_eq_false] at hvar
                exact absurd (hvar _ (List.getElem_mem hi1)) (by rw [hvs]; simp [TV.isVar])
              · exact ⟨_, d, t, hLa, hd, ht, by rw [hd] at hLt; exact hLt⟩

end CompactCheck
