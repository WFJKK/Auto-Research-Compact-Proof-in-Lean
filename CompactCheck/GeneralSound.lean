import CompactCheck.GeneralOpsSound

/-!
# Soundness of the checker on attention networks: single and interval leaves

`generalSingle_correct` and `generalInterval_correct`: every input of a
single or interval leaf the checker accepts is answered correctly, in the
sense of `Spec.lean` (over the reals, with the real exponential). The steps:

1. On an input `x`, every value the checker computes is related to the real
   value (`GRel`): an interval tensor encloses it, and the box of an
   interval leaf contains `x`. Each operation keeps this (`gevalOp_sim`):
   the operations of `GeneralOpsSound.lean`, the weights, and the lookup of
   the input in an interval leaf (`lookupMatmul_sim`). So the logits the
   checker computes enclose the real logits (`gevalGraph_sim`).
2. If the lower bound of the label's logit is above the upper bound of
   every other logit, the real logits have their strict maximum at the
   label (`marginTest_correct`).

`TokensLeafSound.lean` adds the token_interval leaves and puts the leaves
together (`checkGeneral_sound`).
-/

namespace CompactCheck

/-! ## Values related to the real values -/

/-- How a value of the checker relates to the real value on input `x`: an
    interval tensor encloses it; the box of an interval leaf contains `x`,
    and the real value is the one-hot encoding of `x`. -/
def GRel (g : Graph) (x : Input) : GVal → Tensor ℝ → Prop
  | .dt v, t => v.Encl t
  | .box b, t => inBox b x = true ∧ oneHotInput g.positions g.values x = some t

/-- The checker's input for `x`: an interval tensor that encloses the real
    one-hot input of `x`, or a box that contains `x`. -/
def InputRel (g : Graph) (x : Input) : GVal → Prop
  | .dt v => ∃ t, oneHotInput g.positions g.values x = some t ∧ v.Encl t
  | .box b => inBox b x = true

/-- Two arrays related entry by entry. -/
def ARel {β γ : Type} (R : β → γ → Prop) (a : Array β) (b : Array γ) : Prop :=
  a.size = b.size ∧ ∀ i (h1 : i < a.size) (h2 : i < b.size), R a[i] b[i]

theorem ARel.empty {β γ : Type} (R : β → γ → Prop) : ARel R #[] #[] :=
  ⟨rfl, fun i h1 => absurd h1 (by simp)⟩

theorem ARel.get? {β γ : Type} {R : β → γ → Prop} {a : Array β} {b : Array γ} (h : ARel R a b)
    {i : ℕ} {u : β} (hu : a[i]? = some u) : ∃ t, b[i]? = some t ∧ R u t := by
  have hi : i < a.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at hu
    cases hu
  have hi' : i < b.size := h.1 ▸ hi
  rw [Array.getElem?_eq_getElem hi, Option.some.injEq] at hu
  subst hu
  exact ⟨b[i], Array.getElem?_eq_getElem hi', h.2 i hi hi'⟩

theorem ARel.push {β γ : Type} {R : β → γ → Prop} {a : Array β} {b : Array γ} (h : ARel R a b)
    {u : β} {t : γ} (hut : R u t) : ARel R (a.push u) (b.push t) := by
  have hs := h.1
  refine ⟨by simp [hs], fun i h1 h2 => ?_⟩
  by_cases ha : i < a.size
  · have hb : i < b.size := hs ▸ ha
    simp only [Array.getElem_push, ha, hb, ↓reduceDIte]
    exact h.2 i ha hb
  · have hb : ¬ i < b.size := hs ▸ ha
    simp only [Array.getElem_push, ha, hb, ↓reduceDIte]
    exact hut

/-- An argument that is an interval tensor is enclosing the real argument. -/
theorem tensor_sim {g : Graph} {x : Input} {vals : Array GVal} {rvals : Array (Tensor ℝ)}
    (hr : ARel (GRel g x) vals rvals) {a : ℕ} {v : DT} (h : vals[a]?.bind GVal.tensor = some v) :
    ∃ t, rvals[a]? = some t ∧ v.Encl t := by
  cases hu : vals[a]? with
  | none => simp [hu] at h
  | some u =>
    obtain ⟨t, ht, hrel⟩ := hr.get? hu
    cases u with
    | box b => simp [hu, GVal.tensor] at h
    | dt v' =>
      simp only [hu, Option.bind_some, GVal.tensor, Option.some.injEq] at h
      subst h
      exact ⟨t, ht, hrel⟩

theorem tensors_sim {g : Graph} {x : Input} {vals : Array GVal} {rvals : Array (Tensor ℝ)}
    (hr : ARel (GRel g x) vals rvals) :
    ∀ {args : List ℕ} {as : List DT}, (args.mapM fun a => vals[a]?.bind GVal.tensor) = some as →
      ∃ ts, args.mapM (rvals[·]?) = some ts ∧ List.Forall₂ DT.Encl as ts
  | [], as, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, List.Forall₂.nil⟩
  | a :: args, as, h => by
    simp only [List.mapM_cons] at h
    cases ha : vals[a]?.bind GVal.tensor with
    | none => simp [ha] at h
    | some v =>
      cases hl : args.mapM (fun a => vals[a]?.bind GVal.tensor) with
      | none => simp [ha, hl] at h
      | some vs =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        obtain ⟨t, ht, hvt⟩ := tensor_sim hr ha
        obtain ⟨ts, hts, hrel⟩ := tensors_sim hr hl
        refine ⟨t :: ts, ?_, List.Forall₂.cons hvt hrel⟩
        simp [List.mapM_cons, ht, hts]

/-- The arguments `as` of an operation related to the real values: all an
    operation reads. -/
def ArgsRel (g : Graph) (x : Input) (vals : Array GVal) (rvals : Array (Tensor ℝ)) (as : List ℕ) :
    Prop :=
  ∀ a ∈ as, ∀ u, vals[a]? = some u → ∃ t, rvals[a]? = some t ∧ GRel g x u t

theorem ARel.args {g : Graph} {x : Input} {vals : Array GVal} {rvals : Array (Tensor ℝ)}
    (h : ARel (GRel g x) vals rvals) (as : List ℕ) : ArgsRel g x vals rvals as :=
  fun _ _ _ hu => h.get? hu

theorem tensor_sim' {g : Graph} {x : Input} {vals : Array GVal} {rvals : Array (Tensor ℝ)}
    {as : List ℕ} (hr : ArgsRel g x vals rvals as) {a : ℕ} (ham : a ∈ as) {v : DT}
    (h : vals[a]?.bind GVal.tensor = some v) : ∃ t, rvals[a]? = some t ∧ v.Encl t := by
  cases hu : vals[a]? with
  | none => simp [hu] at h
  | some u =>
    obtain ⟨t, ht, hrel⟩ := hr a ham u hu
    cases u with
    | box b => simp [hu, GVal.tensor] at h
    | dt v' =>
      simp only [hu, Option.bind_some, GVal.tensor, Option.some.injEq] at h
      subst h
      exact ⟨t, ht, hrel⟩

theorem tensors_sim' {g : Graph} {x : Input} {vals : Array GVal} {rvals : Array (Tensor ℝ)}
    {bs : List ℕ} (hr : ArgsRel g x vals rvals bs) :
    ∀ {args : List ℕ} {as : List DT}, (∀ a ∈ args, a ∈ bs) →
      (args.mapM fun a => vals[a]?.bind GVal.tensor) = some as →
      ∃ ts, args.mapM (rvals[·]?) = some ts ∧ List.Forall₂ DT.Encl as ts
  | [], as, _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, List.Forall₂.nil⟩
  | a :: args, as, hsub, h => by
    simp only [List.mapM_cons] at h
    cases ha : vals[a]?.bind GVal.tensor with
    | none => simp [ha] at h
    | some v =>
      cases hl : args.mapM (fun a => vals[a]?.bind GVal.tensor) with
      | none => simp [ha, hl] at h
      | some vs =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        obtain ⟨t, ht, hvt⟩ := tensor_sim' hr (hsub a List.mem_cons_self) ha
        obtain ⟨ts, hts, hrel⟩ :=
          tensors_sim' hr (fun b hb => hsub b (List.mem_cons_of_mem _ hb)) hl
        refine ⟨t :: ts, ?_, List.Forall₂.cons hvt hrel⟩
        simp [List.mapM_cons, ht, hts]

/-! ## The weights -/

theorem dweights_lookup {w : Weights ℚ} {dw : DWeights} (h : dweights w = some dw) {n : String}
    {v : DT} (hv : List.lookup n dw = some v) :
    ∃ t, List.lookup n w = some t ∧ DT.ofRat t = some v := by
  induction w generalizing dw with
  | nil =>
    simp only [dweights, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp [List.lookup] at hv
  | cons p w ih =>
    obtain ⟨m, t⟩ := p
    simp only [dweights, List.mapM_cons] at h
    cases ht : DT.ofRat t with
    | none => simp [ht] at h
    | some u =>
      cases hw : w.mapM (fun p => (DT.ofRat p.2).map fun v => (p.1, v)) with
      | none => simp [ht, hw] at h
      | some dw' =>
        simp only [ht, hw, Option.map_some, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at h
        subst h
        cases hnm : (n == m) with
        | true =>
          simp only [List.lookup, hnm, Option.some.injEq] at hv ⊢
          subst hv
          exact ⟨t, rfl, ht⟩
        | false =>
          simp only [List.lookup, hnm] at hv ⊢
          exact ih hw hv

/-! ## Boxes -/

theorem inBox_all_lt {V : ℕ} : ∀ {b : Box} {x : Input}, inBox b x = true →
    b.all (·.hi < V) = true → x.all (· < V) = true
  | [], [], _, _ => rfl
  | r :: rs, t :: ts, h, hb => by
    simp only [inBox, inRange, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
    exact ⟨by omega, inBox_all_lt h3 hb.2⟩
  | [], _ :: _, h, _ => by simp [inBox] at h
  | _ :: _, [], h, _ => by simp [inBox] at h

theorem boxFits_spec {V : ℕ} {b : Box} (h : boxFits V b = true) : b.all (·.hi < V) = true := by
  simp only [boxFits, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact fun r hr => (h r hr).2

/-! ## The one-hot input -/

theorem oneHotInput_int (P V : ℕ) (x : Input) :
    (oneHotInput P V x : Option (Tensor ℝ)) =
      (oneHotInput P V x : Option (Tensor ℤ)).map (Tensor.map fun z : ℤ => (z : ℝ)) := by
  simp only [oneHotInput]
  split_ifs <;> simp [Array.map_map, Function.comp_def, apply_ite (fun z : ℤ => (z : ℝ))]

theorem oneHotInput_eq {α : Type} [Zero α] [One α] [Add α] [Mul α] {P V : ℕ} {x : Input}
    {t : Tensor α} (h : oneHotInput P V x = some t) :
    x.length = P ∧ x.all (· < V) = true ∧ t = ⟨[1, P, V], (Array.range (P * V)).map fun j =>
      if x.getD (j / V) 0 = j % V then 1 else 0⟩ := by
  unfold oneHotInput at h
  split_ifs at h with hx
  simp only [Option.some.injEq] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at hx
  exact ⟨hx.1, hx.2, h.symm⟩

theorem shapeSize_three (P V : ℕ) : shapeSize [1, P, V] = P * V := by
  simp [shapeSize]

/-- In a single leaf the input is the exact one-hot tensor of `x`. -/
theorem oneHotDT_input {g : Graph} {x : Input} {input : GVal} (h : oneHotDT g x = some input) :
    InputRel g x input := by
  unfold oneHotDT at h
  obtain ⟨ti, hti, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨ti.map fun z : ℤ => (z : ℝ), by rw [oneHotInput_int, hti]; rfl, ?_⟩
  obtain ⟨-, -, rfl⟩ := oneHotInput_eq hti
  apply DT.ofInts_encl rfl (by simp [shapeSize_three]) (by simp [shapeSize_three])
  intro j _
  rw [Tensor.get_map_zero _ (by simp)]
  simp [dv, mget, Tensor.get]

/-! ## The lookup of the input in an interval leaf -/

theorem irangeMin_le (f : ℕ → ℤ) {lo hi t : ℕ} (h1 : lo ≤ t) (h2 : t ≤ hi) :
    irangeMin f lo hi ≤ f t := by
  unfold irangeMin
  rw [← List.foldl_map (f := fun k => f (lo + 1 + k)) (g := min)]
  apply foldl_min_le_int
  by_cases ht : t = lo
  · subst ht
    exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨t - lo - 1, ?_, ?_⟩)
    · exact List.mem_range.mpr (by omega)
    · show f (lo + 1 + (t - lo - 1)) = f t
      rw [show lo + 1 + (t - lo - 1) = t by omega]

theorem le_foldl_max_int (l : List ℤ) (a : ℤ) : ∀ x ∈ a :: l, x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => intro x hx; simp at hx; simp [hx]
  | cons b l ih =>
    intro x hx
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_left _ _) (ih _ _ List.mem_cons_self)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact le_trans (le_max_right _ _) (ih _ _ List.mem_cons_self)
      · exact ih _ _ (List.mem_cons_of_mem _ hx)

theorem le_irangeMax (f : ℕ → ℤ) {lo hi t : ℕ} (h1 : lo ≤ t) (h2 : t ≤ hi) :
    f t ≤ irangeMax f lo hi := by
  unfold irangeMax
  rw [← List.foldl_map (f := fun k => f (lo + 1 + k)) (g := max)]
  apply le_foldl_max_int
  by_cases ht : t = lo
  · subst ht
    exact List.mem_cons_self
  · refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨t - lo - 1, ?_, ?_⟩)
    · exact List.mem_range.mpr (by omega)
    · show f (lo + 1 + (t - lo - 1)) = f t
      rw [show lo + 1 + (t - lo - 1) = t by omega]

/-- A sum against a one-hot vector picks one term. -/
theorem onehot_sum (V xp : ℕ) (hx : xp < V) (f : ℕ → ℝ) :
    ((List.range V).map fun t => (if xp = t then (1 : ℝ) else 0) * f t).sum = f xp := by
  induction V with
  | zero => omega
  | succ V ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases h : xp = V
    · subst h
      have : ((List.range xp).map fun t => (if xp = t then (1 : ℝ) else 0) * f t).sum = 0 := by
        apply List.sum_eq_zero
        intro a ha
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
        have := List.mem_range.mp ht
        simp [show xp ≠ t by omega]
      rw [this]
      simp
    · rw [ih (by omega)]
      simp [h]

theorem matmulShape_lookup (P V d : ℕ) :
    matmulShape [1, P, V] [V, d] = some ⟨[1, P, V], [V, d], P, V, d, [1], [], [1], [1, P, d]⟩ := by
  simp [matmulShape, padRow, padCol, keepDim, broadcastShape]

theorem unravel_three (P d j : ℕ) : unravel [1, P, d] j = [0, j / d % P, j % d] := by
  simp [unravel, strides, shapeSize, Nat.mod_one]

theorem ravel_three (P V p t : ℕ) : ravel [1, P, V] [0, p, t] = p * V + t := by
  simp [ravel, strides, shapeSize]
  ring

theorem ravel_pair (V d t q : ℕ) : ravel [V, d] [t, q] = t * d + q := by
  simp [ravel, strides, shapeSize]
  ring

theorem Tensor.get_mk_ofFn {α : Type} [Zero α] (s s' : List ℕ) (F : List ℕ → α) {j : ℕ}
    (hj : j < shapeSize s') : (⟨s, (Tensor.ofFn s' F).data⟩ : Tensor α).get j = F (unravel s' j) :=
  Tensor.ofFn_get s' F hj

/-- **The lookup**: in an interval leaf, the product of the one-hot input
    with an exact matrix lies between the smallest and largest entries over
    the tokens of the box, for every input of the box. -/
theorem lookupMatmul_sim {g : Graph} {x : Input} {bx : Box} {ta tb : Tensor ℝ} {y c : DT}
    (hx : GRel g x (.box bx) ta) (hy : y.Encl tb) (h : lookupMatmul g.values bx y = some c) :
    ∃ r, matmulOp ta tb = some r ∧ c.Encl r := by
  obtain ⟨hin, hoh⟩ := hx
  obtain ⟨hxlen, hxall, rfl⟩ := oneHotInput_eq hoh
  have hblen := inBox_length hin
  unfold lookupMatmul at h
  split at h
  · rename_i V d hys
    split_ifs at h with hcond
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨⟨⟨hex, -⟩, hV⟩, -⟩ := hcond
    subst hV
    have hbP : bx.length = g.positions := by rw [← hblen, hxlen]
    have htbs : tb.shape = [g.values, d] := by rw [hy.1, hys]
    -- the real product: at `(0, p, q)`, the entry `(x[p], q)` of the matrix
    have hmm : ∃ R, matmulOp ⟨[1, g.positions, g.values], (Array.range (g.positions * g.values)).map
          fun j => if x.getD (j / g.values) 0 = j % g.values then (1 : ℝ) else 0⟩ tb = some R ∧
        R.shape = [1, g.positions, d] ∧ R.data.size = g.positions * d ∧
        ∀ j < g.positions * d, R.get j = tb.get (x.getD (j / d) 0 * d + j % d) := by
      have hwfa : (⟨[1, g.positions, g.values], (Array.range (g.positions * g.values)).map
          fun j => if x.getD (j / g.values) 0 = j % g.values then (1 : ℝ) else 0⟩ :
            Tensor ℝ).wellFormed = true := by
        simp [Tensor.wellFormed, shapeSize]
      unfold matmulOp
      simp only [hwfa, hy.wf, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte, htbs,
        matmulShape_lookup, Option.map_some]
      refine ⟨_, rfl, rfl, by simp [Tensor.ofFn_data_size, shapeSize], fun j hj => ?_⟩
      have hdpos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
      have hpP : j / d < g.positions := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj)
      have hxp : x.getD (j / d) 0 < g.values := by
        have hpx : j / d < x.length := by rw [hxlen]; exact hpP
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpx, Option.getD_some]
        have := List.all_eq_true.mp hxall _ (List.getElem_mem hpx)
        simpa using this
      rw [Tensor.get_mk_ofFn]
      · simp only [List.cons_append, List.nil_append, unravel_three,
          Nat.mod_eq_of_lt hpP]
        simp only [broadcastIndex, List.length_cons, List.length_nil, List.take_succ_cons,
          List.take_zero, Nat.sub_self, List.drop_zero, List.zipWith_cons_cons,
          List.zipWith_nil_left, ↓reduceIte, List.nil_append, List.singleton_append,
          List.getD_cons_succ, List.getD_cons_zero, Tensor.entry, ravel_three, ravel_pair]
        rw [List.map_congr_left (g := fun t => (if x.getD (j / d) 0 = t then (1 : ℝ) else 0) *
          tb.get (t * d + j % d)) ?_, onehot_sum _ _ hxp]
        intro t ht
        have ht' := List.mem_range.mp ht
        rw [Tensor.get_mk_map_range _ _ _ (idx_lt hpP ht'), idx_div ht', idx_mod ht']
        rfl
      · simpa [shapeSize] using hj
    obtain ⟨R, hR, hRs, hRsz, hRget⟩ := hmm
    refine ⟨R, hR, DT.Encl.mk (by rw [hRs, hbP]) (by rw [hRsz, hbP]; simp [shapeSize])
      (by simp [shapeSize]) (by simp [shapeSize]) (by intro h; cases h) ?_⟩
    intro j hj
    have hj' : j < g.positions * d := by rw [← hbP]; simpa [shapeSize] using hj
    have hpP : j / d < bx.length := by
      rw [hbP]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj')
    have hbox := inBox_getD hin (j / d) hpP
    rw [hRget j hj', hy.eq_of_exact hex]
    simp only [mget_map_range _ _ (show j < bx.length * d by rw [hbP]; exact hj'),
      Nat.mod_eq_of_lt hpP]
    exact ⟨dv_le_dv _ (irangeMin_le (fun t => mget y.lo (t * d + j % d)) hbox.1 hbox.2),
      dv_le_dv _ (le_irangeMax (fun t => mget y.lo (t * d + j % d)) hbox.1 hbox.2)⟩
  · cases h

/-! ## Sums of tensors of the same shape -/

theorem broadcastShape_self (s : List ℕ) : broadcastShape s s = some s := by
  unfold broadcastShape
  simp only [max_self, Nat.sub_self, List.replicate_zero, List.nil_append]
  induction s with
  | nil => rfl
  | cons a s ih => simp [List.zip_cons_cons, List.mapM_cons, ih]

theorem broadcastIndex_unravel (s : List ℕ) (j : ℕ) :
    broadcastIndex s (unravel s j) = unravel s j := by
  unfold broadcastIndex
  rw [unravel_length, Nat.sub_self, List.drop_zero]
  induction s with
  | nil => simp [unravel]
  | cons d s ih =>
    have h1 : unravel (d :: s) j = (j / shapeSize s % d) :: unravel s j := by
      simp [unravel, strides]
    rw [h1, List.zipWith_cons_cons, ih]
    congr 1
    split_ifs with hd
    · rw [hd, Nat.mod_one]
    · rfl

/-- An enclosure of a tensor encloses any tensor with the same shape and
    entries. -/
theorem DT.Encl.congr {v : DT} {t t' : Tensor ℝ} (h : v.Encl t) (hs : t'.shape = t.shape)
    (hsz : t'.data.size = t.data.size) (hget : ∀ j < t.data.size, t'.get j = t.get j) :
    v.Encl t' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hs.trans h1, hsz.trans h2, h3, h4, h5, fun j => ?_⟩
  by_cases hj : j < t.data.size
  · rw [hget j hj]
    exact h6 j
  · have h7 := h6 j
    rw [Tensor.get_of_le (t := t) (by omega)] at h7
    rw [Tensor.get_of_le (t := t') (by omega)]
    exact h7

/-- `addOp`, the sum of linear networks, computes what the broadcasting sum
    computes on tensors of the same shape. -/
theorem add_sim {a b c : DT} {ta tb : Tensor ℝ} (ha : a.Encl ta) (hb : b.Encl tb)
    (hs : a.shape = b.shape) (h : dbinary .add a b = some c) :
    ∃ r, addOp ta tb = some r ∧ c.Encl r := by
  obtain ⟨tc, htc, hc⟩ := dbinary_sim ha hb h
  have hts : ta.shape = tb.shape := by rw [ha.1, hb.1, hs]
  have hsz : ta.data.size = tb.data.size := by rw [ha.2.1, hb.2.1, hs]
  have hsa : ta.data.size = shapeSize ta.shape := by rw [ha.2.1, ha.1]
  refine ⟨⟨ta.shape, (Array.range ta.data.size).map fun j => ta.get j + tb.get j⟩, ?_, ?_⟩
  · simp [addOp, hts, hsz]
  · unfold broadcastOp at htc
    rw [← hts, broadcastShape_self] at htc
    simp only [ha.wf, hb.wf, Bool.and_self, ↓reduceIte, Option.map_some, Option.some.injEq] at htc
    subst htc
    refine hc.congr rfl (by simp [Tensor.ofFn_data_size, hsa]) (fun j hj => ?_)
    rw [Tensor.ofFn_data_size] at hj
    rw [Tensor.get_mk_map_range _ _ _ (by rw [hsa]; exact hj), Tensor.ofFn_get _ _ hj]
    simp only [BinOp.apply, Tensor.entry, broadcastIndex_unravel, ← hts, ravel_unravel_of_lt hj]

theorem getD_replicate {α : Type} (n j : ℕ) (a : α) : (Array.replicate n a).getD j a = a := by
  unfold Array.getD
  split <;> simp

/-! ## The network -/

/-- **Each operation keeps the relation** between the checker's values and
    the real values. -/
theorem gevalOp_sim {g : Graph} {w : Weights ℚ} {dw : DWeights} (hdw : dweights w = some dw)
    {x : Input} {input : GVal} (hin : InputRel g x input) {vals : Array GVal}
    {rvals : Array (Tensor ℝ)} {op : Op} (hr : ArgsRel g x vals rvals op.args) {v : GVal}
    (h : gevalOp g dw input vals op = some v) :
    ∃ t, semOp g (realWeights w) x rvals op = some t ∧ GRel g x v t := by
  cases op with
  | input =>
    cases input with
    | dt u =>
      simp only [gevalOp, Option.some.injEq] at h
      subst h
      obtain ⟨t, ht, hu⟩ := hin
      exact ⟨t, ht, hu⟩
    | box b =>
      simp only [gevalOp] at h
      split_ifs at h with hfit
      simp only [Option.some.injEq] at h
      subst h
      have hin' : inBox b x = true := hin
      simp only [Bool.and_eq_true, beq_iff_eq] at hfit
      have hok : (x.length == g.positions && x.all (· < g.values)) = true := by
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact ⟨(inBox_length hin').trans hfit.1, inBox_all_lt hin' hfit.2⟩
      cases ht : (oneHotInput g.positions g.values x : Option (Tensor ℝ)) with
      | none => simp [oneHotInput, hok] at ht
      | some t => exact ⟨t, ht, hin', ht⟩
  | linear a wn bn => simp [gevalOp] at h
  | param n =>
    simp only [gevalOp] at h
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨tq, htq, hdq⟩ := dweights_lookup hdw hd
    exact ⟨tq.map fun q : ℚ => (q : ℝ),
      by simp only [semOp, lookup_realWeights, htq, Option.map_some], DT.ofRat_encl hdq⟩
  | sum a d =>
    simp only [gevalOp] at h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨u, hu, huc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨t, ht, hut⟩ := tensor_sim' hr (by simp [Op.args]) hu
    obtain ⟨r, hr', hcr⟩ := dsum_sim hut huc
    exact ⟨r, by
      change evalOp g (realWeights w) x rvals (.sum a d) = some r
      simp only [evalOp, ht, hr'], hcr⟩
  | add a b =>
    simp only [gevalOp] at h
    cases ha : vals[a]?.bind GVal.tensor with
    | none => simp [ha] at h
    | some xa =>
      cases hb : vals[b]?.bind GVal.tensor with
      | none => simp [ha, hb] at h
      | some xb =>
        simp only [ha, hb] at h
        split_ifs at h with hs
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨ta, hta, hea⟩ := tensor_sim' hr (by simp [Op.args]) ha
        obtain ⟨tb, htb, heb⟩ := tensor_sim' hr (by simp [Op.args]) hb
        obtain ⟨r, hr', hcr⟩ := add_sim hea heb (by simpa using hs) hc
        exact ⟨r, by
          change evalOp g (realWeights w) x rvals (.add a b) = some r
          simp only [evalOp, hta, htb, hr'], hcr⟩
  | binary f a b =>
    simp only [gevalOp] at h
    cases ha : vals[a]?.bind GVal.tensor with
    | none => simp [ha] at h
    | some xa =>
      cases hb : vals[b]?.bind GVal.tensor with
      | none => simp [ha, hb] at h
      | some xb =>
        simp only [ha, hb] at h
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨ta, hta, hea⟩ := tensor_sim' hr (by simp [Op.args]) ha
        obtain ⟨tb, htb, heb⟩ := tensor_sim' hr (by simp [Op.args]) hb
        obtain ⟨r, hr', hcr⟩ := dbinary_sim hea heb hc
        exact ⟨r, by simp only [semOp, hta, htb, hr'], hcr⟩
  | neg a =>
    simp only [gevalOp] at h
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨t, ht, hut⟩ := tensor_sim' hr (by simp [Op.args]) hu
    exact ⟨t.map Neg.neg, by simp only [semOp, ht, Option.map_some], dneg_encl hut⟩
  | matmul a b =>
    simp only [gevalOp] at h
    cases hb : vals[b]?.bind GVal.tensor with
    | none => simp [hb] at h
    | some y =>
      obtain ⟨tb, htb, hyb⟩ := tensor_sim' hr (by simp [Op.args]) hb
      cases ha : vals[a]? with
      | none => simp [ha, hb] at h
      | some u =>
        obtain ⟨ta, hta, hua⟩ := hr a (by simp [Op.args]) _ ha
        cases u with
        | box bx =>
          simp only [ha, hb] at h
          obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨r, hr', hcr⟩ := lookupMatmul_sim hua hyb hc
          exact ⟨r, by simp only [semOp, hta, htb, hr'], hcr⟩
        | dt xa =>
          simp only [ha, hb] at h
          obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨r, hr', hcr⟩ := dmatmul_sim hua hyb hc
          exact ⟨r, by simp only [semOp, hta, htb, hr'], hcr⟩
  | index a items =>
    simp only [gevalOp] at h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨u, hu, huc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨t, ht, hut⟩ := tensor_sim' hr (by simp [Op.args]) hu
    obtain ⟨r, hr', hcr⟩ := dmove_sim (indexOp_mover items) hut huc
    exact ⟨r, by simp only [semOp, ht, Option.bind_some, hr'], hcr⟩
  | transpose a =>
    simp only [gevalOp] at h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨u, hu, huc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨t, ht, hut⟩ := tensor_sim' hr (by simp [Op.args]) hu
    obtain ⟨r, hr', hcr⟩ := dmove_sim transposeOp_mover hut huc
    exact ⟨r, by simp only [semOp, ht, Option.bind_some, hr'], hcr⟩
  | unsqueeze a d =>
    simp only [gevalOp] at h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨u, hu, huc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨t, ht, hut⟩ := tensor_sim' hr (by simp [Op.args]) hu
    obtain ⟨r, hr', hcr⟩ := dmove_sim (unsqueezeOp_mover d) hut huc
    exact ⟨r, by simp only [semOp, ht, Option.bind_some, hr'], hcr⟩
  | expand a shape =>
    simp only [gevalOp] at h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨u, hu, huc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨t, ht, hut⟩ := tensor_sim' hr (by simp [Op.args]) hu
    obtain ⟨r, hr', hcr⟩ := dmove_sim (expandOp_mover shape) hut huc
    exact ⟨r, by simp only [semOp, ht, Option.bind_some, hr'], hcr⟩
  | cat args d =>
    simp only [gevalOp] at h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨as, has, hac⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨ts, hts, hrel⟩ := tensors_sim' (args := args) hr (fun a ha => ha) has
    obtain ⟨r, hr', hcr⟩ := djoin_sim (catOp_mover d) hrel hac
    exact ⟨r, by simp only [semOp, hts, Option.bind_some, hr'], hcr⟩
  | stack args d =>
    simp only [gevalOp] at h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨as, has, hac⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨ts, hts, hrel⟩ := tensors_sim' (args := args) hr (fun a ha => ha) has
    obtain ⟨r, hr', hcr⟩ := djoin_sim (stackOp_mover d) hrel hac
    exact ⟨r, by simp only [semOp, hts, Option.bind_some, hr'], hcr⟩
  | exp a =>
    simp only [gevalOp] at h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨u, hu, huc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨t, ht, hut⟩ := tensor_sim' hr (by simp [Op.args]) hu
    exact ⟨t.map Real.exp, by simp only [semOp, ht, Option.map_some]; rfl, dexp_sim hut huc⟩
  | softmax a d =>
    simp only [gevalOp] at h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨u, hu, huc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨t, ht, hut⟩ := tensor_sim' hr (by simp [Op.args]) hu
    obtain ⟨r, hr', hcr⟩ := dsoftmax_sim hut huc
    exact ⟨r, by simp only [semOp, ht, Option.bind_some, hr'], hcr⟩
  | zerosLike a =>
    simp only [gevalOp] at h
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨t, ht, hut⟩ := tensor_sim' hr (by simp [Op.args]) hu
    refine ⟨⟨t.shape, Array.replicate (shapeSize t.shape) 0⟩,
      by simp only [semOp, ht, Option.map_some], ?_⟩
    change (DT.ofInts u.shape (Array.replicate (shapeSize u.shape) 0) 0).Encl _
    rw [← hut.1]
    apply DT.ofInts_encl rfl (by simp) (by simp)
    intro j _
    simp only [Tensor.get, mget, getD_replicate, dv_zero]

theorem gevalOps_sim {g : Graph} {w : Weights ℚ} {dw : DWeights} (hdw : dweights w = some dw)
    {x : Input} {input : GVal} (hin : InputRel g x input) :
    ∀ {ops : List Op} {vals vals' : Array GVal} {rvals : Array (Tensor ℝ)},
      ARel (GRel g x) vals rvals → gevalOps g dw input ops vals = some vals' →
      ∃ rvals', semOps g (realWeights w) x ops rvals = some rvals' ∧ ARel (GRel g x) vals' rvals'
  | [], vals, vals', rvals, hr, h => by
    simp only [gevalOps, Option.some.injEq] at h
    subst h
    exact ⟨rvals, rfl, hr⟩
  | op :: ops, vals, vals', rvals, hr, h => by
    simp only [gevalOps] at h
    cases hv : gevalOp g dw input vals op with
    | none => simp [hv] at h
    | some v =>
      simp only [hv] at h
      obtain ⟨t, ht, hvt⟩ := gevalOp_sim hdw hin (hr.args _) hv
      obtain ⟨rvals', h', hr'⟩ := gevalOps_sim hdw hin (hr.push hvt) h
      exact ⟨rvals', by simp only [semOps, ht]; exact h', hr'⟩

/-- **The logits the checker computes enclose the real logits.** -/
theorem gevalGraph_sim {g : Graph} {w : Weights ℚ} {dw : DWeights} (hdw : dweights w = some dw)
    {x : Input} {input : GVal} (hin : InputRel g x input) {out : DT}
    (h : gevalGraph g dw input = some out) : ∃ t, realOutput g w x = some t ∧ out.Encl t := by
  unfold gevalGraph at h
  cases hv : gevalOps g dw input g.nodes #[] with
  | none => simp [hv] at h
  | some vals =>
    simp only [hv] at h
    obtain ⟨rvals, hrv, hr⟩ := gevalOps_sim hdw hin (ARel.empty _) hv
    obtain ⟨t, ht, henc⟩ := tensor_sim hr h
    exact ⟨t, by simp only [realOutput, semGraph, hrv, ht], henc⟩

/-! ## The margin test -/

/-- **The margin test**: if the lower bound of the label's logit is above
    the upper bound of every other logit, the real logits have their strict
    maximum at the label. -/
theorem marginTest_correct {out : DT} {t : Tensor ℝ} {l : ℕ} (henc : out.Encl t)
    (h : marginTest out l = some true) :
    t.shape = [1, t.data.size] ∧ l < t.data.size ∧
      ∀ j < t.data.size, j ≠ l → t.get j < t.get l := by
  unfold marginTest at h
  split at h
  · rename_i n hn
    split_ifs at h with hok
    simp only [Option.some.injEq, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    have hsize : t.data.size = n := by rw [henc.2.1, hn]; simp [shapeSize]
    refine ⟨by rw [henc.1, hn, hsize], by rw [hsize]; exact hok.2, fun j hj hne => ?_⟩
    rw [hsize] at hj
    have hlt := (h j hj).resolve_left hne
    calc t.get j ≤ dv (mget out.hi j) out.e := (henc.2.2.2.2.2 j).2
      _ < dv (mget out.lo l) out.e := dv_lt_dv _ hlt
      _ ≤ t.get l := (henc.2.2.2.2.2 l).1
  · cases h

/-! ## Leaves -/

/-- An input a single leaf accepts is answered correctly. -/
theorem generalSingle_correct {g : Graph} {w : Weights ℚ} {dw : DWeights}
    (hdw : dweights w = some dw) {task : Task} {x : Input}
    (h : generalSingle g dw task x = some true) : Correct g w task x := by
  unfold generalSingle at h
  cases hi : oneHotDT g x with
  | none => simp [hi] at h
  | some input =>
    cases ho : gevalGraph g dw input with
    | none => simp [hi, ho] at h
    | some out =>
      simp only [hi, ho, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨t, ht, henc⟩ := gevalGraph_sim hdw (oneHotDT_input hi) ho
      obtain ⟨hs, hl, hlt⟩ := marginTest_correct henc h
      exact ⟨t, ht, hs, hl, hlt⟩

/-- Every input of a box an interval leaf accepts is answered correctly. -/
theorem generalInterval_correct {g : Graph} {w : Weights ℚ} {dw : DWeights}
    (hdw : dweights w = some dw) {task : Task} {box : Box}
    (h : generalInterval g dw task box = some true) (x : Input) (hx : inBox box x = true) :
    Correct g w task x := by
  unfold generalInterval at h
  cases hl : task.constantLabel box with
  | none => simp [hl] at h
  | some l =>
    simp only [hl] at h
    cases ho : gevalGraph g dw (.box box) with
    | none => simp [ho] at h
    | some out =>
      simp only [ho, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨t, ht, henc⟩ := gevalGraph_sim hdw (show InputRel g x (.box box) from hx) ho
      obtain ⟨hs, hlt, hmax⟩ := marginTest_correct henc h
      have hlab : task.label x = l := task.constantLabel_spec box l x hl hx
      unfold Correct
      rw [hlab]
      exact ⟨t, ht, hs, hlt, hmax⟩

end CompactCheck
