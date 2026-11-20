import JSP000933LargeCategory

namespace JSP000933

noncomputable section

private def corridorWidth (n : ℕ) : ℕ :=
  (Finset.univ.sup (fun v : Fin n → Bool => (justSourceBlock (Encodable.encode (List.ofFn v))).card)) + 1

private theorem card_lt_corridorWidth (s : List Bool) :
    (justSourceBlock (Encodable.encode s)).card < corridorWidth s.length := by
  let v : Fin s.length → Bool := fun i => s[i.1]
  have hFn : List.ofFn v = s := List.ofFn_getElem
  have hsup : (justSourceBlock (Encodable.encode (List.ofFn v))).card ≤
      Finset.univ.sup (fun t : Fin s.length → Bool =>
        (justSourceBlock (Encodable.encode (List.ofFn t))).card) :=
    Finset.le_sup (f := fun t : Fin s.length → Bool =>
      (justSourceBlock (Encodable.encode (List.ofFn t))).card) (Finset.mem_univ v)
  rw [hFn] at hsup
  exact Nat.lt_succ_of_le hsup

private def stem (d : ℕ) : List Bool → List Bool
  | [] => []
  | bit :: rest => List.replicate (corridorWidth d) false ++ (bit :: stem (d + 1) rest)

private def stemLength (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => corridorWidth d + 1 + stemLength (d + 1) n

private theorem stem_length (d : ℕ) (s : List Bool) :
    (stem d s).length = stemLength d s.length := by
  induction s generalizing d with
  | nil => rfl
  | cons b s ih => simp [stem,stemLength,ih] <;> omega

private theorem stem_append (d : ℕ) (s t : List Bool) :
    stem d (s ++ t) = stem d s ++ stem (d + s.length) t := by
  induction s generalizing d with
  | nil => simp [stem]
  | cons x s ih =>
    simp only [List.cons_append,stem,ih,List.length_cons,List.append_assoc]
    have he : (d + 1) + s.length = d + (s.length + 1) := by omega
    rw [he]

private theorem stem_is_injective (d : ℕ) : Function.Injective (stem d) := by
  intro s
  induction s generalizing d with
  | nil =>
    intro t h
    cases t with
    | nil => rfl
    | cons y t =>
      have hh := congrArg List.length h
      simp [stem] at hh
  | cons x s ih =>
    intro t h
    cases t with
    | nil =>
      have hh := congrArg List.length h
      simp [stem] at hh
    | cons y t =>
      change List.replicate (corridorWidth d) false ++ (x :: stem (d + 1) s) =
        List.replicate (corridorWidth d) false ++ (y :: stem (d + 1) t) at h
      obtain ⟨hb,he⟩ := List.cons.inj (List.append_inj_right h rfl)
      rw [hb, ih (d + 1) he]

private theorem stemLength_succ_last (d n : ℕ) :
    stemLength d (n + 1) = stemLength d n + corridorWidth (d + n) + 1 := by
  induction n generalizing d with
  | zero => simp [stemLength]
  | succ n ih =>
    have hd : d + 1 + n = d + (n + 1) := by omega
    change corridorWidth d + 1 + stemLength (d + 1) (n + 1) =
      (corridorWidth d + 1 + stemLength (d + 1) n) + corridorWidth (d + (n + 1)) + 1
    rw [ih,hd]
    omega

private theorem stemLength_monotone (d : ℕ) : Monotone (stemLength d) := by
  have h (n : ℕ) : stemLength d n < stemLength d (n + 1) := by
    rw [stemLength_succ_last]
    omega
  exact (strictMono_nat_of_lt_succ h).monotone

private def atomTag (s : List Bool) (offset : ℕ) : List Bool :=
  stem 0 s ++ List.replicate offset false

private theorem atomTag_length (s : List Bool) (k : ℕ) :
    (atomTag s k).length = stemLength 0 s.length + k := by
  simp [atomTag,stem_length]

private theorem atomTag_injective {s t : List Bool} {i j : ℕ}
    (hi : i < corridorWidth s.length) (hj : j < corridorWidth t.length)
    (h : atomTag s i = atomTag t j) : s = t ∧ i = j := by
  have hL : stemLength 0 s.length + i = stemLength 0 t.length + j := by
    simpa only [atomTag_length] using congrArg List.length h
  have hn : s.length = t.length := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hc := stemLength_monotone 0 (Nat.succ_le_of_lt hlt)
      rw [stemLength_succ_last,zero_add] at hc
      omega
    · have hc := stemLength_monotone 0 (Nat.succ_le_of_lt hlt)
      rw [stemLength_succ_last,zero_add] at hc
      omega
  have hs : (stem 0 s).length = (stem 0 t).length := by simp only [stem_length,hn]
  have he : stem 0 s = stem 0 t := List.append_inj_left h hs
  have hi' : i = j := by rw [hn] at hL; omega
  exact ⟨stem_is_injective 0 he,hi'⟩

private theorem replicate_add_r11 (n m : ℕ) :
    List.replicate (n + m) false = List.replicate n false ++ List.replicate m false := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [List.replicate_succ, ih, List.cons_append]

private theorem list_prefix_binaryPrefix {x : ℕ → Bool} {n m : ℕ} (h : n ≤ m) :
    List.IsPrefix (binaryPrefixList x n) (binaryPrefixList x m) := by
  have he : m = n + (m - n) := (Nat.add_sub_of_le h).symm
  rw [he]
  unfold binaryPrefixList
  rw [List.ofFn_add]
  exact ⟨_,rfl⟩

private theorem same_node_tags_prefix (s : List Bool) {i j : ℕ} (h : i ≤ j) :
    List.IsPrefix (atomTag s i) (atomTag s j) := by
  refine ⟨List.replicate (j - i) false,?_⟩
  unfold atomTag
  rw [List.append_assoc,← replicate_add_r11,Nat.add_sub_of_le h]

private theorem earlier_node_tags_prefix {s t : List Bool} (h : List.IsPrefix s t) (hne : s ≠ t)
    {i j : ℕ} (hi : i < corridorWidth s.length) :
    List.IsPrefix (atomTag s i) (atomTag t j) := by
  obtain ⟨v,rfl⟩ := h
  cases v with
  | nil => exact False.elim (hne (by simp))
  | cons bit tail =>
    refine ⟨List.replicate (corridorWidth s.length - i) false ++
      (bit :: stem (0 + s.length + 1) tail) ++ List.replicate j false,?_⟩
    unfold atomTag
    simp only [stem_append,stem,zero_add]
    have he : List.replicate i false ++ List.replicate (corridorWidth s.length - i) false =
      List.replicate (corridorWidth s.length) false := by
      rw [← replicate_add_r11,Nat.add_sub_of_le hi.le]
    rw [← he]
    simp only [List.append_assoc]

private def inCodedBlock (m : ℕ) (s : List Bool) : Prop :=
  m ∈ justSourceBlock (Encodable.encode s)

private def offsetOf (s : List Bool) (m : ℕ) : ℕ :=
  m - justSourceStart (Encodable.encode s)

private theorem offset_lt_corridor {m : ℕ} {s : List Bool} (h : inCodedBlock m s) :
    offsetOf s m < corridorWidth s.length := by
  have hh : m ∈ Finset.Ico (justSourceStart (Encodable.encode s))
      (justSourceStart (Encodable.encode s + 1)) := h
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hh
  have hcard : (justSourceBlock (Encodable.encode s)).card =
      justSourceStart (Encodable.encode s + 1) - justSourceStart (Encodable.encode s) := by
    unfold justSourceBlock
    rw [Nat.card_Ico]
  have hoff : offsetOf s m < (justSourceBlock (Encodable.encode s)).card := by
    unfold offsetOf
    rw [hcard]
    omega
  exact hoff.trans (card_lt_corridorWidth s)

private theorem offset_inj_on_block {m n : ℕ} {s : List Bool}
    (hm : inCodedBlock m s) (hn : inCodedBlock n s) (h : offsetOf s m = offsetOf s n) :
    m = n := by
  have hm' : m ∈ Finset.Ico (justSourceStart (Encodable.encode s))
      (justSourceStart (Encodable.encode s + 1)) := hm
  have hn' : n ∈ Finset.Ico (justSourceStart (Encodable.encode s))
      (justSourceStart (Encodable.encode s + 1)) := hn
  have hlo := (Finset.mem_Ico.mp hm').1
  have hhi := (Finset.mem_Ico.mp hn').1
  unfold offsetOf at h
  omega

def neatBlockLabel (m : ℕ) : List Bool := by
  classical
  exact if h : ∃ s : List Bool, inCodedBlock m s then
    true :: atomTag (Classical.choose h) (offsetOf (Classical.choose h) m)
  else false :: List.replicate m false

private theorem neatBlockLabel_of_coded {m : ℕ} {s : List Bool} (hm : inCodedBlock m s) :
    neatBlockLabel m = true :: atomTag s (offsetOf s m) := by
  classical
  have he : ∃ t : List Bool, inCodedBlock m t := ⟨s,hm⟩
  have hother := Classical.choose_spec he
  have hs : Classical.choose he = s := by
    apply Encodable.encode_injective
    by_contra hh
    exact Finset.disjoint_left.mp (justSourceBlock_pairwise hh) hother hm
  simp only [neatBlockLabel,dite_eq_left he,hs]

private theorem neatBlockLabel_of_uncoded {m : ℕ}
    (hm : ¬∃ s : List Bool, inCodedBlock m s) :
    neatBlockLabel m = false :: List.replicate m false := by
  classical
  simp only [neatBlockLabel,dite_eq_right hm]

theorem neatBlockLabel_injective : Function.Injective neatBlockLabel := by
  classical
  intro m n h
  by_cases hm : ∃ s : List Bool, inCodedBlock m s
  · obtain ⟨s,hs⟩ := hm
    rw [neatBlockLabel_of_coded hs] at h
    by_cases hn : ∃ t : List Bool, inCodedBlock n t
    · obtain ⟨t,ht⟩ := hn
      rw [neatBlockLabel_of_coded ht] at h
      obtain ⟨h₁,h₂⟩ := atomTag_injective
        (offset_lt_corridor hs) (offset_lt_corridor ht) (List.cons.inj h).2
      subst t
      exact offset_inj_on_block hs ht h₂
    · rw [neatBlockLabel_of_uncoded hn] at h
      simp at h
  · rw [neatBlockLabel_of_uncoded hm] at h
    by_cases hn : ∃ t : List Bool, inCodedBlock n t
    · obtain ⟨t,ht⟩ := hn
      rw [neatBlockLabel_of_coded ht] at h
      simp at h
    · rw [neatBlockLabel_of_uncoded hn] at h
      have he := congrArg List.length ((List.cons.inj h).2)
      simpa using he

private theorem prefix_after_cons {s t : List Bool} {b : Bool} :
    List.IsPrefix s t → List.IsPrefix (b :: s) (b :: t) := by
  rintro ⟨v,hv⟩
  exact ⟨v,by simp [hv]⟩

theorem branch_labels_comparable (x : ℕ → Bool) {m n : ℕ}
    (hm : m ∈ branchLargeSet x) (hn : n ∈ branchLargeSet x) :
    List.IsPrefix (neatBlockLabel m) (neatBlockLabel n) ∨
      List.IsPrefix (neatBlockLabel n) (neatBlockLabel m) := by
  obtain ⟨i,hi⟩ := hm
  obtain ⟨j,hj⟩ := hn
  have hi' : inCodedBlock m (binaryPrefixList x i) := hi
  have hj' : inCodedBlock n (binaryPrefixList x j) := hj
  rw [neatBlockLabel_of_coded hi',neatBlockLabel_of_coded hj']
  have forward (a c : ℕ) {u v : ℕ}
      (hu : inCodedBlock u (binaryPrefixList x a))
      (hac : a < c) :
      List.IsPrefix (atomTag (binaryPrefixList x a) (offsetOf (binaryPrefixList x a) u))
        (atomTag (binaryPrefixList x c) (offsetOf (binaryPrefixList x c) v)) := by
    have hne : binaryPrefixList x a ≠ binaryPrefixList x c := by
      intro he
      have he' : a = c := by simpa [binaryPrefixList] using congrArg List.length he
      exact hac.ne he'
    exact earlier_node_tags_prefix (list_prefix_binaryPrefix hac.le) hne (offset_lt_corridor hu)
  rcases lt_trichotomy i j with h | h | h
  · exact Or.inl (prefix_after_cons (forward i j hi' h))
  · subst j
    rcases le_total (offsetOf (binaryPrefixList x i) m) (offsetOf (binaryPrefixList x i) n) with hs | hs
    · exact Or.inl (prefix_after_cons (same_node_tags_prefix _ hs))
    · exact Or.inr (prefix_after_cons (same_node_tags_prefix _ hs))
  · exact Or.inr (prefix_after_cons (forward j i hj' h))

theorem exists_neat_uncountable_almost_disjoint_large_family :
    ∃ (A : Set (Set ℕ)) (e : ℕ ↪ List Bool),
      ¬ A.Countable ∧
      (∀ a ∈ A, LongBlockLarge a) ∧
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a ∩ b).Finite) ∧
      ∀ a ∈ A, ∀ m ∈ a, ∀ n ∈ a, List.IsPrefix (e m) (e n) ∨ List.IsPrefix (e n) (e m) := by
  refine ⟨Set.range branchLargeSet,⟨neatBlockLabel,neatBlockLabel_injective⟩,
    branchLargeSet_range_uncountable,?_,?_,?_⟩
  · rintro _ ⟨x,rfl⟩
    exact branchLargeSet_large x
  · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ h
    exact branchLargeSet_almost_disjoint (fun hxy => h (congrArg branchLargeSet hxy))
  · rintro _ ⟨x,rfl⟩ m hm n hn
    exact branch_labels_comparable x hm hn

private theorem prefixList_succ_r11 (x : ℕ → Bool) (n : ℕ) :
    binaryPrefixList x (n+1) = binaryPrefixList x n ++ [x n] := by
  unfold binaryPrefixList
  rw [List.ofFn_succ_last] <;> rfl

private theorem split_binaryPrefix_at_bit_r11 (x : ℕ → Bool) {n d : ℕ} (h : d < n) :
    ∃ tail : List Bool, binaryPrefixList x n = binaryPrefixList x d ++ (x d :: tail) := by
  obtain ⟨t,ht⟩ := list_prefix_binaryPrefix (x := x) (Nat.succ_le_of_lt h)
  rw [prefixList_succ_r11,List.append_assoc] at ht
  exact ⟨t,ht.symm⟩

private theorem atomTag_split_bit_r11 (s : List Bool) (b : Bool) (t : List Bool) (k : ℕ) :
    atomTag (s ++ (b :: t)) k =
      (stem 0 s ++ List.replicate (corridorWidth s.length) false) ++
        (b :: (stem (s.length+1) t ++ List.replicate k false)) := by
  simp [atomTag,stem_append,stem,List.append_assoc]

private theorem no_prefix_of_different_head_r11 (p s t : List Bool) {b c : Bool} (hbc : b ≠ c) :
    ¬ List.IsPrefix (p ++ (b :: s)) (p ++ (c :: t)) := by
  rintro ⟨u,hu⟩
  rw [List.append_assoc,List.cons_append] at hu
  have he := List.append_inj_right hu rfl
  exact hbc (List.cons.inj he).1

private theorem infinite_subbranch_contains_late_atom_r11 {X : Set ℕ} (hX : X.Infinite)
    {x : ℕ → Bool} (hsub : X ⊆ branchLargeSet x) (d : ℕ) :
    ∃ m ∈ X, ∃ i > d, inCodedBlock m (binaryPrefixList x i) := by
  let E : Set ℕ := ⋃ i ∈ (Finset.range (d+1) : Set ℕ),
    (justSourceBlock (binaryPrefixIndex x i) : Set ℕ)
  have hE : E.Finite := (Finset.range (d+1)).finite_toSet.biUnion
    (fun i _ => (justSourceBlock (binaryPrefixIndex x i)).finite_toSet)
  have hnot : ¬ X ⊆ E := fun h => hX (hE.subset h)
  obtain ⟨m,hm,hn⟩ := Set.not_subset.mp hnot
  obtain ⟨i,hi⟩ := hsub hm
  have hlt : d < i := by
    by_contra hc
    exact hn (Set.mem_iUnion₂.mpr ⟨i,Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_not_gt hc)),hi⟩)
  exact ⟨m,hm,i,hlt,hi⟩

theorem incompatible_labels_of_infinite_distinct_subbranches {x y : ℕ → Bool} (hxy : x ≠ y)
    {P Q : Set ℕ} (hP : P.Infinite) (hQ : Q.Infinite)
    (hp : P ⊆ branchLargeSet x) (hq : Q ⊆ branchLargeSet y) :
    ∃ m ∈ P, ∃ n ∈ Q,
      (¬ List.IsPrefix (neatBlockLabel m) (neatBlockLabel n)) ∧
      (¬ List.IsPrefix (neatBlockLabel n) (neatBlockLabel m)) := by
  classical
  have he : ∃ i, x i ≠ y i := by
    by_contra hn
    apply hxy
    funext i
    by_contra hi
    exact hn ⟨i,hi⟩
  let d := Nat.find he
  have hd : x d ≠ y d := Nat.find_spec he
  have hs : binaryPrefixList x d = binaryPrefixList y d := by
    unfold binaryPrefixList
    apply congrArg (fun f : Fin d → Bool => List.ofFn f)
    funext i
    exact not_not.mp (Nat.find_min he (show i.1 < d from i.2))
  obtain ⟨m,hm,i,hi,hmB⟩ := infinite_subbranch_contains_late_atom_r11 hP hp d
  obtain ⟨n,hn,j,hj,hnB⟩ := infinite_subbranch_contains_late_atom_r11 hQ hq d
  obtain ⟨t,ht⟩ := split_binaryPrefix_at_bit_r11 x hi
  obtain ⟨u,hu⟩ := split_binaryPrefix_at_bit_r11 y hj
  let s := binaryPrefixList x d
  let pad := true :: (stem 0 s ++ List.replicate (corridorWidth s.length) false)
  let trailM := stem (s.length+1) t ++ List.replicate (offsetOf (binaryPrefixList x i) m) false
  let trailN := stem (s.length+1) u ++ List.replicate (offsetOf (binaryPrefixList y j) n) false
  have hm' : neatBlockLabel m = pad ++ (x d :: trailM) := by
    rw [neatBlockLabel_of_coded hmB]
    have hh := atomTag_split_bit_r11 s (x d) t (offsetOf (binaryPrefixList x i) m)
    have hT : binaryPrefixList x i = s ++ (x d :: t) := ht
    rw [← hT] at hh
    rw [hh] <;> rfl
  have hn' : neatBlockLabel n = pad ++ (y d :: trailN) := by
    rw [neatBlockLabel_of_coded hnB]
    have hU : binaryPrefixList y j = s ++ (y d :: u) := by rw [hu,← hs] <;> rfl
    have hh := atomTag_split_bit_r11 s (y d) u (offsetOf (binaryPrefixList y j) n)
    rw [← hU] at hh
    rw [hh] <;> rfl
  refine ⟨m,hm,n,hn,?_,?_⟩ <;> rw [hm',hn']
  · exact no_prefix_of_different_head_r11 pad trailM trailN hd
  · exact no_prefix_of_different_head_r11 pad trailN trailM hd.symm

theorem incompatible_labels_of_coded_late_words_r269
    {u v : List Bool} {m n j : ℕ}
    (hm : m∈justSourceBlock (Encodable.encode u)) (hn : n∈justSourceBlock (Encodable.encode v))
    (hx : j<u.length) (hy : j<v.length) (hne : u[j]'hx ≠ v[j]'hy) :
    (¬ List.IsPrefix (neatBlockLabel m) (neatBlockLabel n)) ∧
    (¬ List.IsPrefix (neatBlockLabel n) (neatBlockLabel m)) := by
  classical
  let x (k : ℕ) : Bool := if h : k<u.length then u[k]'h else false
  let y (k : ℕ) : Bool := if h : k<v.length then v[k]'h else false
  have hj : x j ≠ y j := by simpa only [x,y,dite_eq_left hx,dite_eq_left hy] using hne
  have he : ∃ d, x d ≠ y d := ⟨j,hj⟩
  let d := Nat.find he
  have hd : x d ≠ y d := Nat.find_spec he
  have hdj : d≤j := Nat.find_min' he hj
  have hs : binaryPrefixList x d = binaryPrefixList y d := by
    unfold binaryPrefixList
    apply congrArg (fun f : Fin d → Bool => List.ofFn f)
    funext i
    exact not_not.mp (Nat.find_min he (show i.val<d from i.isLt))
  have hU : binaryPrefixList x u.length = u := by
    unfold binaryPrefixList
    refine Eq.trans ?_ (List.ofFn_getElem (xs := u))
    exact congrArg (fun f : Fin u.length → Bool => List.ofFn f)
      (funext fun i => dite_eq_left i.isLt)
  have hV : binaryPrefixList y v.length = v := by
    unfold binaryPrefixList
    refine Eq.trans ?_ (List.ofFn_getElem (xs := v))
    exact congrArg (fun f : Fin v.length → Bool => List.ofFn f)
      (funext fun i => dite_eq_left i.isLt)
  obtain ⟨t,ht⟩ := split_binaryPrefix_at_bit_r11 x (hdj.trans_lt hx)
  obtain ⟨w,hw⟩ := split_binaryPrefix_at_bit_r11 y (hdj.trans_lt hy)
  let s := binaryPrefixList x d
  let pad := true :: (stem 0 s ++ List.replicate (corridorWidth s.length) false)
  let trailM := stem (s.length+1) t ++ List.replicate (offsetOf u m) false
  let trailN := stem (s.length+1) w ++ List.replicate (offsetOf v n) false
  have hM : u = s ++ (x d :: t) := hU.symm.trans ht
  have hN : v = s ++ (y d :: w) :=
    hV.symm.trans (hw.trans (congrArg (fun a => a ++ (y d :: w)) hs.symm))
  have hm' : neatBlockLabel m = pad ++ (x d :: trailM) := by
    rw [neatBlockLabel_of_coded (show inCodedBlock m u from hm)]
    have hh := atomTag_split_bit_r11 s (x d) t (offsetOf u m)
    rw [← hM] at hh
    rw [hh] <;> rfl
  have hn' : neatBlockLabel n = pad ++ (y d :: trailN) := by
    rw [neatBlockLabel_of_coded (show inCodedBlock n v from hn)]
    have hh := atomTag_split_bit_r11 s (y d) w (offsetOf v n)
    rw [← hN] at hh
    rw [hh] <;> rfl
  refine ⟨?_,?_⟩ <;> rw [hm',hn']
  · exact no_prefix_of_different_head_r11 pad trailM trailN hd
  · exact no_prefix_of_different_head_r11 pad trailN trailM hd.symm

end

end JSP000933
