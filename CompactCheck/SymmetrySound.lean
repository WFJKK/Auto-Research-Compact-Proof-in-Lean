import CompactCheck.ContractSound

/-!
# The network part of the symmetry rule

`evalGraph_perm`: a network that passes `symmetricNet` computes the same
output on every reordering of an input. Its only input is read only by a sum
over the positions, and that sum is the number of times each token occurs,
which reordering does not change. So the values of all operations but the
input are the same for the input and for its reordering.
-/

namespace CompactCheck

/-! ## What `symmetricNet` says -/

theorem eq_of_filter_eq_singleton {l : List Nat} {p : Nat → Bool} {i : Nat}
    (h : l.filter p = [i]) : i ∈ l ∧ p i = true ∧ ∀ k ∈ l, p k = true → k = i := by
  have hi : i ∈ l.filter p := by rw [h]; exact List.mem_singleton_self i
  refine ⟨(List.mem_filter.mp hi).1, (List.mem_filter.mp hi).2, fun k hk hp => ?_⟩
  have : k ∈ l.filter p := List.mem_filter.mpr ⟨hk, hp⟩
  rw [h] at this
  exact List.mem_singleton.mp this

theorem isInput_iff {op : Op} : op.isInput = true ↔ op = .input := by
  cases op <;> simp [Op.isInput]

/-- The network has one input, at position `i`, which is not its output; the
    sum at position `s` reads it over the positions, and nothing else reads
    it. -/
theorem symmetricNet_spec {g : Graph} (h : symmetricNet g = true) :
    ∃ i s d, i < g.nodes.length ∧ g.nodes[i]? = some .input ∧ g.output ≠ i ∧
      (∀ k (hk : k < g.nodes.length), g.nodes[k] = .input → k = i) ∧
      g.nodes[s]? = some (.sum i d) ∧ normDim d 3 = some 1 ∧
      (∀ k (hk : k < g.nodes.length), i ∈ g.nodes[k].args → k = s) := by
  unfold symmetricNet at h
  split at h
  · rename_i i hin
    obtain ⟨hi, hpi, huniq⟩ := eq_of_filter_eq_singleton hin
    have hi' := List.mem_range.mp hi
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨hout, h⟩ := h
    split at h
    · rename_i s hrd
      obtain ⟨hs, hps, hruniq⟩ := eq_of_filter_eq_singleton hrd
      have hs' := List.mem_range.mp hs
      split at h
      · rename_i a d hsum
        simp only [beq_iff_eq] at h
        have hai : a = i := by
          simp only [List.contains_nil, Bool.not_false, Bool.true_and, hsum, Option.any_some,
            Op.args, List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hps
          exact hps.symm
        subst hai
        refine ⟨a, s, d, hi', ?_, hout, ?_, hsum, h, ?_⟩
        · simp only [List.getElem?_eq_getElem hi', Option.any_some, isInput_iff] at hpi
          rw [List.getElem?_eq_getElem hi', hpi]
        · intro k hk hkin
          apply huniq k (List.mem_range.mpr hk)
          simp [List.getElem?_eq_getElem hk, hkin, Op.isInput]
        · intro k hk hka
          apply hruniq k (List.mem_range.mpr hk)
          simp [List.getElem?_eq_getElem hk, hka]
      · simp at h
    · simp at h
  · simp at h

/-! ## Reordering the input -/

/-- Reordering an input keeps it in the space. -/
theorem oneHot_cond_perm {P V : Nat} {x y : Input} (hxy : x.Perm y) :
    (x.length == P && x.all (· < V)) = (y.length == P && y.all (· < V)) := by
  rw [hxy.length_eq]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun h a ha => h a (hxy.mem_iff.mpr ha), fun h a ha => h a (hxy.mem_iff.mp ha)⟩

theorem oneHotInput_perm {P V : Nat} {x y : Input} (hxy : x.Perm y) {tx : Tensor ℚ}
    (hx : oneHotInput P V x = some tx) :
    ∃ ty, (oneHotInput P V y : Option (Tensor ℚ)) = some ty := by
  unfold oneHotInput at hx ⊢
  rw [← oneHot_cond_perm hxy]
  by_cases hc : (x.length == P && x.all (· < V)) = true
  · rw [ite_eq_left hc]
    exact ⟨_, rfl⟩
  · rw [ite_eq_right hc] at hx
    cases hx

/-- The one-hot input is what the interval rule's `oneHot false` describes,
    for a box of the right length. -/
theorem oneHot_rel {P V : Nat} {x : Input} {t : Tensor ℚ} (ht : oneHotInput P V x = some t) :
    IRel P V (List.replicate P ⟨0, 0⟩) x (.oneHot false) t := by
  unfold oneHotInput at ht
  split_ifs at ht with hc
  cases ht
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hlen, hV⟩ := hc
  refine ⟨List.length_replicate, ?_, rfl, by simp, ?_⟩
  · intro r hr
    obtain ⟨hP, rfl⟩ := List.mem_replicate.mp hr
    obtain ⟨v, hv⟩ : ∃ v, v ∈ x := List.exists_mem_of_ne_nil x (by
      intro h0; rw [h0] at hlen; simp at hlen; omega)
    exact lt_of_le_of_lt (Nat.zero_le v) (hV v hv)
  · intro p hp i hi
    rw [Tensor.get_range, ite_eq_left (idx_lt hp hi), idx_div hi, idx_mod hi]

/-- Two tensors with the same shape and the same entries are equal. -/
theorem Tensor.ext_get {t1 t2 : Tensor ℚ} (hs : t1.shape = t2.shape)
    (hd : t1.data.size = t2.data.size) (h : ∀ i < t1.data.size, t1.get i = t2.get i) :
    t1 = t2 := by
  obtain ⟨s1, d1⟩ := t1
  obtain ⟨s2, d2⟩ := t2
  simp only at hs hd h
  subst hs
  congr 1
  apply Array.ext hd
  intro i h1 h2
  have := h i h1
  simp only [Tensor.get, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2, Option.getD_some] at this
  exact this

/-- Summing the one-hot input over the positions counts the tokens, so a
    reordering gives the same sum. -/
theorem sumOp_oneHot_perm {P V : Nat} {x y : Input} {tx ty : Tensor ℚ} {d : Int}
    (hd : normDim d 3 = some 1) (hxy : x.Perm y) (hx : oneHotInput P V x = some tx)
    (hy : oneHotInput P V y = some ty) : sumOp d tx = sumOp d ty := by
  obtain ⟨sx, hsx, hrx⟩ := sum_onehot_rel (oneHot_rel hx) hd
  obtain ⟨sy, hsy, hry⟩ := sum_onehot_rel (oneHot_rel hy) hd
  rw [hsx, hsy]
  congr 1
  obtain ⟨-, -, hshx, hszx, hgx⟩ := hrx
  obtain ⟨-, -, hshy, hszy, hgy⟩ := hry
  apply Tensor.ext_get (hshx.trans hshy.symm) (hszx.trans hszy.symm)
  intro i hi
  rw [hszx] at hi
  rw [hgx i hi, hgy i hi]
  have hlen : ∀ (z : Input) (t : Tensor ℚ), oneHotInput P V z = some t → z.length = P := by
    intro z t hz
    unfold oneHotInput at hz
    split_ifs at hz with hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.1
  have key : ∀ z : Input, z.length = P →
      ((List.range P).map fun k => if z.getD k 0 = i then (1 : ℚ) else 0).sum =
        (z.map fun v => if v = i then (1 : ℚ) else 0).sum := by
    intro z hz
    rw [← hz]
    exact sum_range_getD z (fun v => if v = i then (1 : ℚ) else 0)
  rw [key x (hlen x tx hx), key y (hlen y ty hy)]
  exact (hxy.map _).sum_eq

/-- A non-input operation does not look at the input itself. -/
theorem evalOp_other_input {g : Graph} {w : Weights ℚ} {x y : Input} {vals : Array (Tensor ℚ)}
    {op : Op} (h : op ≠ .input) : evalOp g w x vals op = evalOp g w y vals op := by
  cases op with
  | input => exact absurd rfl h
  | linear => rfl
  | sum => rfl
  | add => rfl
  | _ => simp [evalOp]

/-- **The network computes the same on a reordering of its input**, if it
    passes `symmetricNet`: every value but the input's is the same. -/
theorem evalOps_perm {g : Graph} {w : Weights ℚ} (hsym : symmetricNet g = true) {x y : Input}
    (hxy : x.Perm y) {vals : Array (Tensor ℚ)} (hx : evalOps g w x g.nodes #[] = some vals) :
    ∃ i vals', g.output ≠ i ∧ evalOps g w y g.nodes #[] = some vals' ∧
      ∀ k, k ≠ i → vals'[k]? = vals[k]? := by
  obtain ⟨i, s, d, hi, hinput, hout, huniq, hsum, hd, hread⟩ := symmetricNet_spec hsym
  obtain ⟨hsize, -, hev⟩ := (evalOps_spec g w x g.nodes #[] vals).mp hx
  simp only [Array.size_empty, Nat.zero_add] at hsize hev
  have hnode_i : g.nodes[i] = .input := by
    rw [List.getElem?_eq_getElem hi] at hinput
    exact Option.some.inj hinput
  have his : i < vals.size := by omega
  -- the input's value
  obtain ⟨-, hev_i⟩ := hev i hi
  rw [hnode_i] at hev_i
  have htx : oneHotInput g.positions g.values x = some vals[i] := by
    rw [← Array.getElem?_eq_getElem his, ← hev_i]
    rfl
  obtain ⟨ty, hty⟩ := oneHotInput_perm hxy htx
  refine ⟨i, vals.set i ty his, hout, ?_, fun k hk => Array.getElem?_set_ne his (Ne.symm hk)⟩
  have hs' : s < g.nodes.length := (List.getElem?_eq_some_iff.mp hsum).1
  have hnode_s : g.nodes[s] = .sum i d := (List.getElem?_eq_some_iff.mp hsum).2
  have hsi : s ≠ i := by
    intro h
    subst h
    rw [hnode_i] at hnode_s
    cases hnode_s
  apply (evalOps_spec g w y g.nodes #[] _).mpr
  refine ⟨by simp [hsize], fun _ h => absurd h (by simp), ?_⟩
  intro j hj
  obtain ⟨hargs, hevj⟩ := hev j hj
  refine ⟨by simpa using hargs, ?_⟩
  simp only [Array.size_empty, Nat.zero_add] at hevj ⊢
  by_cases hji : j = i
  · subst hji
    rw [hnode_i, Array.getElem?_set_self his]
    exact hty
  · rw [Array.getElem?_set_ne his (Ne.symm hji)]
    by_cases hjs : j = s
    · subst hjs
      rw [hnode_s] at hevj ⊢
      simp only [evalOp, Array.getElem?_set_self his] at hevj ⊢
      rw [Array.getElem?_eq_getElem his] at hevj
      rw [← hevj]
      exact (sumOp_oneHot_perm hd hxy htx hty).symm
    · have hnotin : i ∉ g.nodes[j].args := fun h => hjs (hread j hj h)
      have hnotinput : g.nodes[j] ≠ .input := fun h => hji (huniq j hj h)
      rw [evalOp_congr (fun a ha => Array.getElem?_set_ne his (fun h => hnotin (h ▸ ha))),
        ← evalOp_other_input hnotinput]
      exact hevj

theorem evalGraph_perm {g : Graph} {w : Weights ℚ} (hsym : symmetricNet g = true) {x y : Input}
    (hxy : x.Perm y) : evalGraph g w x = evalGraph g w y := by
  unfold evalGraph
  cases hx : evalOps g w x g.nodes #[] with
  | some vals =>
    obtain ⟨i, vals', hout, hy, hk⟩ := evalOps_perm hsym hxy hx
    rw [hy]
    exact (hk _ hout).symm
  | none =>
    cases hy : evalOps g w y g.nodes #[] with
    | none => rfl
    | some vals' =>
      obtain ⟨i, vals, -, hx', -⟩ := evalOps_perm hsym hxy.symm hy
      rw [hx] at hx'
      cases hx'

end CompactCheck
