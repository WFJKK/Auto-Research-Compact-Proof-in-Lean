import CompactCheck.TokensSepSound

/-!
# The rules on `Mix` values keep their relation to the real values

The weights of the terms of a sum over the positions, and the rules that
act on a `Mix`: products with a matrix (each term's rows by linearity),
sums with a constant or with another `Mix`, and products with one number.
-/

namespace CompactCheck

/-! ## The weights of a sum over the positions -/

theorem wOf_none (ctx : TCtx) (x : Input) (p : ℕ) (rest : List ℕ) {wp : DT}
    (h : wOf none p rest = some wp) :
    (wp.shape = [] ∨ wp.shape = [ctx.k]) ∧ ∃ Ω, wp.Encl Ω ∧ (1 : ℝ) = Ω.get (wIdx ctx x wp) := by
  simp only [wOf, Option.some.injEq] at h
  subst h
  refine ⟨Or.inl rfl, _, dtScalar_encl 1, ?_⟩
  simp [wIdx, dtScalar, Tensor.get]

theorem wOf_inl {ctx : TCtx} {x : Input} {w : DT} {s : Sep} {W : Tensor ℝ} (hw : w.Encl W)
    (hws : w.shape = weightShape ctx.box.length s.rest) {p : ℕ} {wp : DT}
    (h : wOf (some (.inl w)) p s.rest = some wp) :
    (wp.shape = [] ∨ wp.shape = [ctx.k]) ∧ ∃ Ω, wp.Encl Ω ∧ W.get p = Ω.get (wIdx ctx x wp) := by
  simp only [wOf, weightAt] at h
  obtain ⟨Ω, hΩ, hwpΩ⟩ := dtIndex_sim hw h
  obtain ⟨hΩs, -, hΩget⟩ := indexOp_weight (by rw [hw.1, hws]) hΩ
  have hwps : wp.shape = [] := by rw [← hwpΩ.1, hΩs]
  refine ⟨Or.inl hwps, Ω, hwpΩ, ?_⟩
  simp [wIdx, hwps, hΩget]

theorem forall₂_range_map {β γ : Type} {R : β → γ → Prop} (l : List β) (F : ℕ → γ) (d : β)
    (h : ∀ i < l.length, R (l.getD i d) (F i)) :
    List.Forall₂ R l ((List.range l.length).map F) := by
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp, fun i h1 h2 => ?_⟩
  have := h i h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
  simpa using this

theorem wOf_inr {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {ws : Array DT} {s : Sep}
    (hsz : ws.size = ctx.k)
    (hall : ∀ i < ctx.k, (ws.getD i emptyDT).shape = weightShape ctx.box.length s.rest ∧
      ∃ W, (ws.getD i emptyDT).Encl W)
    {W : Tensor ℝ} (hW : (ws.getD (inputIdx ctx x) emptyDT).Encl W) {p : ℕ}
    {wp : DT} (h : wOf (some (.inr ws)) p s.rest = some wp) :
    (wp.shape = [] ∨ wp.shape = [ctx.k]) ∧ ∃ Ω, wp.Encl Ω ∧ W.get p = Ω.get (wIdx ctx x wp) := by
  simp only [wOf, weightsAt] at h
  obtain ⟨xs, hxs, hstack⟩ := Option.bind_eq_some_iff.mp h
  have hf2 := mapM_forall₂ hxs
  have hlen : xs.length = ctx.k := by rw [← hf2.length_eq]; simp [hsz]
  -- a real weight for each input: `x`'s own for `x`
  have hreal : ∀ i < ctx.k, ∃ Ωi : Tensor ℝ, (xs.getD i emptyDT).Encl Ωi ∧ Ωi.shape = [] ∧
      (i = inputIdx ctx x → Ωi.get 0 = W.get p) := by
    intro i hi
    have hi' : i < ws.toList.length := by simp [hsz, hi]
    have hwi := forall₂_getD hf2 hi' emptyDT emptyDT
    rw [array_getD_toList] at hwi
    simp only [weightAt] at hwi
    by_cases hix : i = inputIdx ctx x
    · subst hix
      obtain ⟨Ω, hΩ, hxΩ⟩ := dtIndex_sim hW hwi
      obtain ⟨hΩs, -, hΩget⟩ := indexOp_weight (by rw [hW.1, (hall _ hi).1]) hΩ
      exact ⟨Ω, hxΩ, hΩs, fun _ => hΩget⟩
    · obtain ⟨W', hW'⟩ := (hall i hi).2
      obtain ⟨Ω, hΩ, hxΩ⟩ := dtIndex_sim hW' hwi
      obtain ⟨hΩs, -, -⟩ := indexOp_weight (by rw [hW'.1, (hall i hi).1]) hΩ
      exact ⟨Ω, hxΩ, hΩs, fun h => absurd h hix⟩
  have : Nonempty (Tensor ℝ) := ⟨⟨[], #[]⟩⟩
  choose! F hF using hreal
  have hrel : List.Forall₂ DT.Encl xs ((List.range xs.length).map F) :=
    forall₂_range_map xs F emptyDT (fun i hi => (hF i (by omega)).1)
  obtain ⟨r, hr, hwpr⟩ := djoin_sim (stackOp_mover 0) hrel hstack
  have hne : (List.range xs.length).map F ≠ [] := by
    simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    have := hf.idx_lt
    omega
  have hshapes : ∀ T ∈ (List.range xs.length).map F, T.shape = [] := by
    intro T hT
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hT
    exact (hF i (by have := List.mem_range.mp hi; omega)).2.1
  obtain ⟨hrs, -, hrget⟩ := stackOp_first hshapes hne hr
  have hwps : wp.shape = [ctx.k] := by rw [← hwpr.1, hrs]; simp [hlen]
  refine ⟨Or.inr hwps, r, hwpr, ?_⟩
  have hidx := hf.idx_lt
  have hwIdx : wIdx ctx x wp = inputIdx ctx x := by simp [wIdx, hwps]
  rw [hwIdx]
  have := hrget (inputIdx ctx x) (by simp; omega) 0 (by simp [shapeSize])
  rw [shapeSize_nil, Nat.mul_one, Nat.add_zero] at this
  rw [this, list_getD_map _ (by simp; omega) 0, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp; omega), Option.getD_some, List.getElem_range]
  exact ((hF _ hidx).2.2 rfl).symm

/-! ## Sums over the terms -/

theorem termsVal_cons (box : Box) (x : Input) (S : ℕ) (τ : Term) (terms : List Term) (ω : ℝ)
    (ωs : List ℝ) (q : ℕ) :
    termsVal box x S (τ :: terms) (ω :: ωs) q =
      ω * τ.rows.real.get (rowOf box x τ.pos * S + q) + termsVal box x S terms ωs q := by
  simp [termsVal]

theorem sum_mul_termsVal (box : Box) (x : Input) (S n : ℕ) (B : ℕ → ℝ) :
    ∀ (terms : List Term) (ωs : List ℝ),
    ((List.range n).map fun k => termsVal box x S terms ωs k * B k).sum =
      (List.zipWith (fun τ ω => ω * ((List.range n).map fun k =>
        τ.rows.real.get (rowOf box x τ.pos * S + k) * B k).sum) terms ωs).sum
  | [], _ => by simp [termsVal]
  | _ :: _, [] => by simp [termsVal]
  | τ :: terms, ω :: ωs => by
    simp only [termsVal_cons, add_mul, List.sum_map_add, List.zipWith_cons_cons, List.sum_cons,
      mul_assoc]
    rw [sum_mul_termsVal box x S n B terms ωs, ← List.sum_map_mul_left]

theorem zipWith_congr_forall₂ {β γ δ ε : Type} {g : γ → δ → ε} {g' : β → δ → ε} :
    ∀ {l1 : List β} {l2 : List γ} (ωs : List δ),
      List.Forall₂ (fun a b => ∀ ω, g b ω = g' a ω) l1 l2 →
      List.zipWith g l2 ωs = List.zipWith g' l1 ωs
  | [], [], _, _ => by simp
  | a :: l1, b :: l2, [], _ => by simp
  | a :: l1, b :: l2, ω :: ωs, h => by
    cases h with
    | cons hab h' =>
      simp only [List.zipWith_cons_cons, hab ω, zipWith_congr_forall₂ ωs h']

theorem forall₂_combine {β γ δ : Type} {R : β → γ → Prop} {S : β → δ → Prop} {U : β → δ → Prop}
    (hRSU : ∀ a b c, R a b → S a c → U a c) :
    ∀ {l1 : List β} {l2 : List γ} {l3 : List δ}, List.Forall₂ R l1 l2 → List.Forall₂ S l1 l3 →
      List.Forall₂ U l1 l3
  | [], [], [], _, _ => List.Forall₂.nil
  | a :: l1, b :: l2, c :: l3, h1, h2 => by
    cases h1 with
    | cons hab h1' =>
      cases h2 with
      | cons hac h2' => exact List.Forall₂.cons (hRSU a b c hab hac) (forall₂_combine hRSU h1' h2')

theorem forall₂_trans_left {β γ δ : Type} {R : β → γ → Prop} {S : β → δ → Prop} {T : δ → γ → Prop}
    (hRST : ∀ a b c, R a b → S a c → T c b) :
    ∀ {l1 : List β} {l2 : List γ} {l3 : List δ}, List.Forall₂ R l1 l2 → List.Forall₂ S l1 l3 →
      List.Forall₂ T l3 l2
  | [], [], [], _, _ => List.Forall₂.nil
  | a :: l1, b :: l2, c :: l3, h1, h2 => by
    cases h1 with
    | cons hab h1' =>
      cases h2 with
      | cons hac h2' =>
        exact List.Forall₂.cons (hRST a b c hab hac) (forall₂_trans_left hRST h1' h2')

/-! ## Products with a matrix -/

theorem matmulMix_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {m m' : Mix}
    {t tb : Tensor ℝ} {b : DT} {dd d' : ℕ} (hm : MixR ctx x m t) (hb : b.Encl tb)
    (hbx : b.exact = true) (hcs : m.const.shape = [1, dd]) (hbs : b.shape = [dd, d'])
    (h : matmulMix m b = .val m') :
    ∃ t', matmulOp t tb = some t' ∧ MixR ctx x m' t' := by
  obtain ⟨rest, hcrest, hts, htsz, C, hC, ωs, hterms, hval⟩ := hm
  rw [hcs, List.cons.injEq] at hcrest
  obtain ⟨-, hrest⟩ := hcrest
  subst hrest
  have hdd : shapeSize [dd] = dd := by simp [shapeSize]
  have hd' : shapeSize [d'] = d' := by simp [shapeSize]
  have htbs : tb.shape = [dd, d'] := by rw [hb.1, hbs]
  have htwf : t.wellFormed = true := by simp [Tensor.wellFormed, hts, htsz, shapeSize_cons, hdd]
  obtain ⟨t', ht', ht's, ht'sz, ht'get⟩ := matmulOp_two hts htbs htwf hb.wf
  unfold matmulMix at h
  obtain ⟨terms', hterms', h2⟩ := Step.bind_eq_val h
  dsimp only at h2
  have hf2 := mapM_forall₂ (Step.ofOption_eq_val hterms')
  -- the new constant
  have hconst : ∃ C' : Tensor ℝ, m'.const.Encl C' ∧ m'.const.shape = [1, d'] ∧
      m'.terms = terms' ∧
      ∀ c < d', C'.get c = ((List.range dd).map fun k => C.get k * tb.get (k * d' + c)).sum := by
    split_ifs at h2 with hz
    · cases h2
      simp only [Bool.and_eq_true, Array.all_eq_true, beq_iff_eq] at hz
      refine ⟨_, dtZeros_encl _, by simp [dtZeros, DT.ofInts, hcs, hbs], rfl, fun c _ => ?_⟩
      rw [zeros_get]
      symm
      apply List.sum_eq_zero
      intro a ha
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      have hk' := List.mem_range.mp hk
      have hsz : m.const.lo.size = dd := by rw [hC.2.2.1, hcs]; simp [shapeSize]
      have hlo : mget m.const.lo k = 0 := by
        have := hz.2 k (by omega)
        simpa [mget, Array.getD_eq_getD_getElem?, hsz, hk'] using this
      rw [hC.eq_of_exact hz.1, hlo, dv_zero, zero_mul]
    · obtain ⟨const', hconst', h3⟩ := Step.bind_eq_val h2
      cases h3
      obtain ⟨C', hC', hcC'⟩ := dmatmul_sim hC hb (Step.ofOption_eq_val hconst')
      obtain ⟨C'', hC'', hC''s, -, hC''get⟩ := matmulOp_two (by rw [hC.1, hcs]) htbs hC.wf hb.wf
      rw [hC'', Option.some.injEq] at hC'
      subst hC'
      refine ⟨C'', hcC', by rw [← hcC'.1, hC''s], rfl, fun c hc => ?_⟩
      have := hC''get 0 (by omega) c hc
      simp only [Nat.zero_mul, Nat.zero_add] at this
      exact this
  obtain ⟨C', hC', hC's, hm'terms, hC'get⟩ := hconst
  -- the new terms
  have hrows : List.Forall₂ (fun τ τ' => τ'.w = τ.w ∧ τ'.pos = τ.pos ∧
      dmatmul τ.rows b = some τ'.rows) m.terms terms' := by
    refine List.Forall₂.imp ?_ hf2
    intro τ τ' hτ
    obtain ⟨rows, hrows, h4⟩ := Option.bind_eq_some_iff.mp hτ
    simp only [Option.pure_def, Option.some.injEq] at h4
    subst h4
    exact ⟨rfl, rfl, hrows⟩
  have hterms2 : List.Forall₂ (TermR ctx x [d']) terms' ωs := by
    refine forall₂_trans_left (fun τ ω τ' hτω hττ' => ?_) hterms hrows
    obtain ⟨hpos, hrok, hsh, Ω, hΩ, hω⟩ := hτω
    obtain ⟨hw, hp, hmm⟩ := hττ'
    obtain ⟨R', hR', hR'e⟩ := dmatmul_sim hrok.encl hb hmm
    obtain ⟨R'', hR'', hR''s, -, -⟩ := matmulOp_two hrok.2.2.2 htbs hrok.encl.wf hb.wf
    rw [hR''] at hR'
    cases hR'
    have hex : τ'.rows.exact = true := by rw [dmatmul_exact hmm, hrok.2.1, hbx]; rfl
    refine ⟨by rw [hp]; exact hpos, ⟨hR'e.ok, hex, hR'e.2.2.2.2.1 hex, ?_⟩, by rw [hw]; exact hsh,
      Ω, by rw [hw]; exact hΩ, by rw [hw]; exact hω⟩
    rw [← hR'e.1, hR''s, hp]
  refine ⟨t', ht', [d'], hC's, ht's, by rw [ht'sz, hd']; ring, C', hC', ωs,
    by rw [hm'terms]; exact hterms2, fun c hc => ?_⟩
  rw [hd'] at hc ⊢
  have h5 := ht'get 0 (by omega) c hc
  simp only [Nat.zero_mul, Nat.zero_add] at h5
  rw [h5, hC'get c hc]
  rw [hdd] at hval
  have h6 : ((List.range dd).map fun k => t.get k * tb.get (k * d' + c)).sum =
      ((List.range dd).map fun k => C.get k * tb.get (k * d' + c)).sum +
      ((List.range dd).map fun k =>
        termsVal ctx.box x dd m.terms ωs k * tb.get (k * d' + c)).sum := by
    rw [← List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    rw [hval k (List.mem_range.mp hk), add_mul]
  rw [h6, sum_mul_termsVal]
  congr 1
  have hprop : List.Forall₂ (fun τ τ' => ∀ ω : ℝ,
      ω * τ'.rows.real.get (rowOf ctx.box x τ'.pos * d' + c) =
        ω * ((List.range dd).map fun k => τ.rows.real.get (rowOf ctx.box x τ.pos * dd + k) *
          tb.get (k * d' + c)).sum) m.terms terms' := by
    refine forall₂_combine (fun τ ω τ' hτω hττ' => ?_) hterms hrows
    intro ω'
    obtain ⟨hpos, hrok, -, -⟩ := hτω
    obtain ⟨-, hp, hmm⟩ := hττ'
    obtain ⟨R', hR', hR'e⟩ := dmatmul_sim hrok.encl hb hmm
    obtain ⟨R'', hR'', -, -, hR''get⟩ := matmulOp_two hrok.2.2.2 htbs hrok.encl.wf hb.wf
    rw [hR''] at hR'
    cases hR'
    have hex : τ'.rows.exact = true := by rw [dmatmul_exact hmm, hrok.2.1, hbx]; rfl
    rw [hp, ← hR'e.get_real hex, hR''get _ (hf.row_lt _ hpos) c hc]
  unfold termsVal
  rw [hm'terms, zipWith_congr_forall₂ ωs hprop]

/-! ## Sums with constants and with other `Mix`es -/

theorem mapM_map' {β γ δ : Type} (f : γ → Option δ) (g : β → γ) :
    ∀ l : List β, (l.map g).mapM f = l.mapM (f ∘ g)
  | [] => rfl
  | a :: l => by simp [List.mapM_cons, mapM_map' f g l]

theorem broadcastShape_comm (a b : List ℕ) : broadcastShape a b = broadcastShape b a := by
  unfold broadcastShape
  dsimp only
  rw [max_comm]
  conv_rhs => rw [← List.zip_swap]
  rw [mapM_map']
  congr 1
  funext pr
  obtain ⟨u, v⟩ := pr
  simp only [Function.comp, Prod.swap]
  by_cases h1 : u = v
  · subst h1; simp
  · have h1' : ¬ v = u := fun h => h1 h.symm
    by_cases h2 : u = 1
    · subst h2
      simp [h1, h1']
    · by_cases h3 : v = 1
      · subst h3
        simp [h1, h1']
      · simp [h1, h1', h2, h3]

theorem broadcastShape_nil_right (s : List ℕ) : broadcastShape s [] = some s :=
  (broadcastShape_of_fits (by simp) (by simp)).1

theorem termsVal_append (box : Box) (x : Input) (S : ℕ) {t1 t2 : List Term} {w1 w2 : List ℝ}
    (hl : t1.length = w1.length) (q : ℕ) :
    termsVal box x S (t1 ++ t2) (w1 ++ w2) q =
      termsVal box x S t1 w1 q + termsVal box x S t2 w2 q := by
  unfold termsVal
  rw [List.zipWith_append hl, List.sum_append]

theorem forall₂_append {β γ : Type} {R : β → γ → Prop} :
    ∀ {l1 : List β} {l2 : List γ} {l3 : List β} {l4 : List γ}, List.Forall₂ R l1 l2 →
      List.Forall₂ R l3 l4 → List.Forall₂ R (l1 ++ l3) (l2 ++ l4)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, h1, h2 => by
    cases h1 with
    | cons hab h1' => exact List.Forall₂.cons hab (forall₂_append h1' h2)

theorem addMix_sim {ctx : TCtx} {x : Input} {m m' : Mix} {c : DT} {t tc : Tensor ℝ}
    (hm : MixR ctx x m t) (hc : c.Encl tc) (h : addMix m c = .val m') :
    (∃ t', broadcastOp BinOp.add.apply t tc = some t' ∧ MixR ctx x m' t') ∧
    (∃ t', broadcastOp BinOp.add.apply tc t = some t' ∧ MixR ctx x m' t') := by
  obtain ⟨rest, hcrest, hts, htsz, C, hC, ωs, hterms, hval⟩ := hm
  unfold addMix at h
  split at h
  · cases h
  · rename_i const hconst
    split_ifs at h with hsh
    cases h
    simp only [beq_iff_eq] at hsh
    obtain ⟨C', hC', hcC'⟩ := dbinary_sim hC hc hconst
    obtain ⟨sh, hbsh, hC'eq, -, -⟩ := broadcastOp_spec hC'
    have hsh' : sh = 1 :: rest := by
      have := hcC'.1
      rw [hC'eq, Tensor.ofFn_shape, hsh, hcrest] at this
      exact this
    subst hsh'
    have hCs : C.shape = 1 :: rest := by rw [hC.1, hcrest]
    have hbs1 : broadcastShape t.shape tc.shape = some (1 :: rest) := by
      rw [hts]
      have := hbsh
      rw [hCs] at this
      exact this
    have hbs2 : broadcastShape tc.shape t.shape = some (1 :: rest) := by
      rw [broadcastShape_comm]; exact hbs1
    have hwf : t.wellFormed = true := by simp [Tensor.wellFormed, hts, htsz, shapeSize_cons]
    have hC'get : ∀ q < shapeSize rest, C'.get q =
        C.get q + tc.entry (broadcastIndex tc.shape (unravel (1 :: rest) q)) := by
      intro q hq
      have hq' : q < shapeSize (1 :: rest) := by rw [shapeSize_cons]; omega
      obtain ⟨-, -, hget⟩ := broadcastOp_full_left hCs hC' hbsh
      rw [hget q hq']
      rfl
    have hsz : shapeSize (1 :: rest) = shapeSize rest := by rw [shapeSize_cons, Nat.one_mul]
    constructor
    · obtain ⟨h1s, h1sz, h1get⟩ :=
        broadcastOp_full_left hts (broadcastOp_eq BinOp.add.apply hwf hc.wf hbs1) hbs1
      refine ⟨_, broadcastOp_eq BinOp.add.apply hwf hc.wf hbs1, rest, by rw [hsh, hcrest], h1s,
        by rw [h1sz, hsz], C', hcC', ωs, hterms, fun q hq => ?_⟩
      rw [h1get q (by rw [hsz]; exact hq), hC'get q hq, hval q hq]
      simp only [BinOp.apply]
      ring
    · obtain ⟨h1s, h1sz, h1get⟩ :=
        broadcastOp_full_right hts (broadcastOp_eq BinOp.add.apply hc.wf hwf hbs2) hbs2
      refine ⟨_, broadcastOp_eq BinOp.add.apply hc.wf hwf hbs2, rest, by rw [hsh, hcrest], h1s,
        by rw [h1sz, hsz], C', hcC', ωs, hterms, fun q hq => ?_⟩
      rw [h1get q (by rw [hsz]; exact hq), hC'get q hq, hval q hq]
      simp only [BinOp.apply]
      ring

theorem addMixes_sim {ctx : TCtx} {x : Input} {mx my m' : Mix} {tx ty : Tensor ℝ}
    (hx : MixR ctx x mx tx) (hy : MixR ctx x my ty) (h : addMixes mx my = .val m') :
    ∃ t', broadcastOp BinOp.add.apply tx ty = some t' ∧ MixR ctx x m' t' := by
  obtain ⟨rest, hcrest, hts, htsz, C, hC, ωs, hterms, hval⟩ := hx
  obtain ⟨rest', hcrest', hts', htsz', C2, hC2, ωs', hterms', hval'⟩ := hy
  unfold addMixes at h
  split_ifs at h with hsh
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hsh
  have hrr : rest' = rest := by
    rw [hcrest, hcrest', List.cons.injEq] at hsh
    exact hsh.2.symm
  subst hrr
  split at h
  · cases h
  · rename_i const hconst
    cases h
    obtain ⟨C', hC', hcC'⟩ := dbinary_sim hC hC2 hconst
    have hCs : C.shape = 1 :: rest' := by rw [hC.1, hcrest]
    have hC2s : C2.shape = 1 :: rest' := by rw [hC2.1, hcrest']
    have hbs : broadcastShape C.shape C2.shape = some (1 :: rest') := by
      rw [hCs, hC2s, broadcastShape_self]
    obtain ⟨-, -, hC'get⟩ := broadcastOp_full_left hCs hC' hbs
    have hbs' : broadcastShape tx.shape ty.shape = some (1 :: rest') := by
      rw [hts, hts', broadcastShape_self]
    have hwf : tx.wellFormed = true := by simp [Tensor.wellFormed, hts, htsz, shapeSize_cons]
    have hwf' : ty.wellFormed = true := by simp [Tensor.wellFormed, hts', htsz', shapeSize_cons]
    obtain ⟨h1s, h1sz, h1get⟩ :=
      broadcastOp_full_left hts (broadcastOp_eq BinOp.add.apply hwf hwf' hbs') hbs'
    have hsz : shapeSize (1 :: rest') = shapeSize rest' := by rw [shapeSize_cons, Nat.one_mul]
    have hl := hterms.length_eq
    refine ⟨_, broadcastOp_eq BinOp.add.apply hwf hwf' hbs', rest', ?_, h1s, by rw [h1sz, hsz], C',
      hcC', ωs ++ ωs', forall₂_append hterms hterms', fun q hq => ?_⟩
    · have := hcC'.1
      rw [← this]
      obtain ⟨sh, hsh2, hC'eq, -, -⟩ := broadcastOp_spec hC'
      rw [hbs] at hsh2
      cases hsh2
      rw [hC'eq]
      rfl
    · have hq' : q < shapeSize (1 :: rest') := by rw [hsz]; exact hq
      rw [h1get q hq', hC'get q hq', termsVal_append _ _ _ hl, hval q hq,
        entry_broadcast_self hts' hq', entry_broadcast_self hC2s hq', hval' q hq]
      simp only [BinOp.apply]
      ring

/-! ## Products with one number -/

theorem broadcastOp_scalar_right {f : ℝ → ℝ → ℝ} {a r : Tensor ℝ} {σ : ℝ} {s : List ℕ}
    (hs : a.shape = s) (h : broadcastOp f a ⟨[], #[σ]⟩ = some r) :
    r.shape = s ∧ r.data.size = shapeSize s ∧ ∀ j < shapeSize s, r.get j = f (a.get j) σ := by
  have hbs : broadcastShape a.shape ([] : List ℕ) = some s := by rw [hs, broadcastShape_nil_right]
  obtain ⟨h1, h2, h3⟩ := broadcastOp_full_left hs h hbs
  refine ⟨h1, h2, fun j hj => ?_⟩
  rw [h3 j hj]
  simp [broadcastIndex, Tensor.entry, ravel, strides, Tensor.get]

theorem real_list_sum_mul (l : List ℝ) (a : ℝ) : (l.map (· * a)).sum = l.sum * a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih, add_mul]

theorem scaleMix_sim {ctx : TCtx} {x : Input} (hf : LeafFacts ctx x) {m m' : Mix} {sc : DT}
    {σ : ℝ} {t t' : Tensor ℝ} (hm : MixR ctx x m t) (hs : sc.Encl ⟨[], #[σ]⟩)
    (h : scaleMix m sc = .val m') (ht's : t'.shape = t.shape) (ht'sz : t'.data.size = t.data.size)
    (ht'get : ∀ q < t.data.size, t'.get q = t.get q * σ) : MixR ctx x m' t' := by
  obtain ⟨rest, hcrest, hts, htsz, C, hC, ωs, hterms, hval⟩ := hm
  unfold scaleMix at h
  obtain ⟨terms', hterms', h2⟩ := Step.bind_eq_val h
  obtain ⟨const', hconst', h3⟩ := Step.bind_eq_val h2
  cases h3
  obtain ⟨C', hC', hcC'⟩ := dbinary_sim hC hs (Step.ofOption_eq_val hconst')
  have hCs : C.shape = 1 :: rest := by rw [hC.1, hcrest]
  obtain ⟨hC's, -, hC'get⟩ := broadcastOp_scalar_right hCs hC'
  have hf2 := mapM_forall₂ (Step.ofOption_eq_val hterms')
  have hterms2 : List.Forall₂ (TermR ctx x rest) terms' (ωs.map (· * σ)) := by
    have hl : terms'.length = (ωs.map (· * σ)).length := by
      rw [List.length_map, ← hterms.length_eq, hf2.length_eq]
    apply List.forall₂_iff_get.mpr
    refine ⟨hl, fun i h1 h2 => ?_⟩
    have hi : i < m.terms.length := by rw [hf2.length_eq]; exact h1
    have hτ := (List.forall₂_iff_get.mp hf2).2 i hi h1
    have hτω := (List.forall₂_iff_get.mp hterms).2 i hi (by rw [← hterms.length_eq]; exact hi)
    simp only [List.get_eq_getElem] at hτ hτω ⊢
    obtain ⟨w', hw', h4⟩ := Option.bind_eq_some_iff.mp hτ
    simp only [Option.pure_def, Option.some.injEq] at h4
    rw [← h4]
    obtain ⟨hpos, hrok, hsh, Ω, hΩ, hω⟩ := hτω
    obtain ⟨Ω', hΩ', hwΩ'⟩ := dbinary_sim hΩ hs hw'
    have hΩs : Ω.shape = (m.terms[i]).w.shape := hΩ.1
    obtain ⟨hΩ's, -, hΩ'get⟩ := broadcastOp_scalar_right hΩs hΩ'
    have hw's : w'.shape = (m.terms[i]).w.shape := by rw [← hwΩ'.1, hΩ's]
    refine ⟨hpos, hrok, by rw [hw's]; exact hsh, Ω', hwΩ', ?_⟩
    simp only [List.getElem_map]
    have hidx : wIdx ctx x w' = wIdx ctx x (m.terms[i]).w := by simp [wIdx, hw's]
    have hlt : wIdx ctx x (m.terms[i]).w < shapeSize (m.terms[i]).w.shape := by
      rcases hsh with h0 | h0
      · simp [wIdx, h0, shapeSize]
      · have := hf.idx_lt
        have hne : (m.terms[i]).w.shape ≠ [] := by rw [h0]; simp
        simp only [wIdx, h0]
        simp [shapeSize]
        omega
    rw [hidx, hω, hΩ'get _ hlt]
    rfl
  have hsz : shapeSize (1 :: rest) = shapeSize rest := by rw [shapeSize_cons, Nat.one_mul]
  refine ⟨rest, by rw [← hcC'.1, hC's], by rw [ht's, hts], by rw [ht'sz, htsz], C', hcC',
    _, hterms2, fun q hq => ?_⟩
  rw [ht'get q (by rw [htsz]; exact hq), hval q hq, hC'get q (by rw [hsz]; exact hq)]
  have hval2 : termsVal ctx.box x (shapeSize rest) terms' (ωs.map (· * σ)) q =
      termsVal ctx.box x (shapeSize rest) m.terms ωs q * σ := by
    unfold termsVal
    rw [← real_list_sum_mul]
    congr 1
    have hl := hterms.length_eq
    apply List.ext_getElem (by simp [hf2.length_eq])
    intro i h1 h2
    have hi : i < m.terms.length := by simp at h2; omega
    have hi' : i < terms'.length := by rw [← hf2.length_eq]; exact hi
    have hτ := (List.forall₂_iff_get.mp hf2).2 i hi hi'
    obtain ⟨w', -, h4⟩ := Option.bind_eq_some_iff.mp hτ
    simp only [Option.pure_def, Option.some.injEq] at h4
    simp only [List.getElem_zipWith, List.getElem_map, List.get_eq_getElem] at h4 ⊢
    rw [← h4]
    ring
  rw [hval2]
  simp only [BinOp.apply]
  ring

end CompactCheck
