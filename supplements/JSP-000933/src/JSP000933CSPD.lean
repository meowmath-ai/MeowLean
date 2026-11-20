import JSP000933Lemma8

open scoped BigOperators Topology
open Filter

namespace JSP000933

noncomputable section

@[simp] theorem restrictSet_empty_r4 (s : Finset ℕ) : restrictSet s (∅ : Set ℕ) = ∅ := by
  ext m
  simp

theorem restrictSet_inter_r4 (s : Finset ℕ) (X Y : Set ℕ) :
    restrictSet s (X ∩ Y) = restrictSet s X ∩ restrictSet s Y := by
  ext m
  simp only [mem_restrictSet, Finset.mem_inter, Set.mem_inter_iff]
  tauto

theorem weightedClass_empty_r4 (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) :
    weightedClass a ha (∅ : Set ℕ) = 0 := by
  unfold weightedClass
  change Ideal.Quotient.mk (weightedNullIdeal a ha) (toBoolRing (⊥ : Set ℕ)) = 0
  rw [toBoolRing_bot, map_zero]

theorem weightedNull_iff_class_zero_r4 (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (X : Set ℕ) :
    WeightedNull a X ↔ weightedClass a ha X = 0 := by
  have hx : xorSet X ∅ = X := by ext m; simp [xorSet]
  simpa only [weightedClass_empty_r4, hx] using (weightedClass_eq_iff a ha X ∅).symm

def IsBlockLift (f g : EUWeight)
    (F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg)
    (B : FiniteBlockMap) : Prop :=
  ∀ X : Set ℕ, X ⊆ glueBlocks B.dom →
    F (weightedClass f.weight f.nonneg X) = weightedClass g.weight g.nonneg (B.eval X)

namespace FiniteBlockMap

private theorem restrict_dom_glue_r4 (B : FiniteBlockMap) (x : ℕ → Finset ℕ)
    (hx : ∀ k, x k ⊆ B.dom k) (k : ℕ) :
    restrictSet (B.dom k) (glueBlocks x) = x k := by
  rw [restrictSet_glueBlocks B.dom x B.dom_disjoint hx k (by rfl),
    Finset.inter_eq_left.mpr (hx k)]

private theorem restrict_ran_eval_r4 (B : FiniteBlockMap) (X : Set ℕ) (k : ℕ) :
    restrictSet (B.ran k) (B.eval X) = B.act k (restrictSet (B.dom k) X) := by
  rw [B.restrict_eval X k (by rfl)]
  apply Finset.inter_eq_left.mpr
  apply B.act_subset
  exact fun _ hm => (mem_restrictSet.mp hm).1

theorem eval_empty_weightedNull (B : FiniteBlockMap) {f g : EUWeight}
    {F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg}
    (hL : IsBlockLift f g F B) : WeightedNull g.weight (B.eval ∅) := by
  apply (weightedNull_iff_class_zero_r4 g.weight g.nonneg _).mpr
  have hw := hL ∅ (Set.empty_subset _)
  rw [weightedClass_empty_r4, map_zero] at hw
  exact hw.symm

theorem eventually_small_empty_images (B : FiniteBlockMap) {f : EUWeight}
    {F : WeightedRing f.weight f.nonneg →+* WeightedRing harmonicEU.weight harmonicEU.nonneg}
    (hL : IsBlockLift f harmonicEU F B) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k ≥ N, logConcentration (B.act k ∅) ≤ ε := by
  have hnull : HarmonicNull (B.eval ∅) := B.eval_empty_weightedNull (f := f) (g := harmonicEU) hL
  obtain ⟨N,hN⟩ := harmonicNull_eventually_small_block B.ran B.ran_disjoint hnull hε
  refine ⟨N, fun k hk => ?_⟩
  simpa only [restrict_ran_eval_r4, restrictSet_empty_r4] using hN k hk

theorem inter_error_weightedNull (B : FiniteBlockMap) {f g : EUWeight}
    {F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg}
    (hL : IsBlockLift f g F B) {X Y : Set ℕ}
    (hX : X ⊆ glueBlocks B.dom) (hY : Y ⊆ glueBlocks B.dom) :
    WeightedNull g.weight (xorSet (B.eval X ∩ B.eval Y) (B.eval (X ∩ Y))) := by
  have hi : X ∩ Y ⊆ glueBlocks B.dom := Set.inter_subset_left.trans hX
  have h₁ := hL X hX
  have h₂ := hL Y hY
  have h₃ := hL (X ∩ Y) hi
  apply (weightedClass_eq_iff g.weight g.nonneg _ _).mp
  rw [weightedClass_inter, ← h₁, ← h₂, ← map_mul, ← weightedClass_inter, h₃]

theorem eventually_small_meet_error (B : FiniteBlockMap) {f : EUWeight}
    {F : WeightedRing f.weight f.nonneg →+* WeightedRing harmonicEU.weight harmonicEU.nonneg}
    (hL : IsBlockLift f harmonicEU F B) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ x y : Finset ℕ, x ⊆ B.dom k → y ⊆ B.dom k →
      logConcentration (xorFinset (B.act k x ∩ B.act k y) (B.act k (x ∩ y))) ≤ ε := by
  classical
  let error (k : ℕ) (x y : Finset ℕ) := xorFinset (B.act k x ∩ B.act k y) (B.act k (x ∩ y))
  let Good (k : ℕ) : Prop :=
    ∀ x y : Finset ℕ, x ⊆ B.dom k → y ⊆ B.dom k → logConcentration (error k x y) ≤ ε
  change ∃ N : ℕ, ∀ k ≥ N, Good k
  by_contra hNo
  have hbad (N : ℕ) : ∃ k ≥ N, ¬ Good k := by
    by_contra h
    apply hNo
    refine ⟨N, fun k hk => ?_⟩
    by_contra hn
    exact h ⟨k, hk, hn⟩
  have hpairs (k : ℕ) (h : ¬ Good k) : ∃ p : Finset ℕ × Finset ℕ,
      p.1 ⊆ B.dom k ∧ p.2 ⊆ B.dom k ∧ ε < logConcentration (error k p.1 p.2) := by
    by_contra hn
    apply h
    intro x y hx hy
    by_contra hbad
    exact hn ⟨(x,y), hx, hy, lt_of_not_ge hbad⟩
  let p (k : ℕ) := if h : Good k then (∅, ∅) else Classical.choose (hpairs k h)
  let x (k : ℕ) := (p k).1
  let y (k : ℕ) := (p k).2
  have hx (k : ℕ) : x k ⊆ B.dom k := by
    by_cases hk : Good k
    · simp [x, p, hk]
    · simpa only [x, p, dite_eq_right hk] using (Classical.choose_spec (hpairs k hk)).1
  have hy (k : ℕ) : y k ⊆ B.dom k := by
    by_cases hk : Good k
    · simp [y, p, hk]
    · simpa only [y, p, dite_eq_right hk] using (Classical.choose_spec (hpairs k hk)).2.1
  have he (k : ℕ) (hk : ¬ Good k) : ε < logConcentration (error k (x k) (y k)) := by
    simpa only [x, y, p, dite_eq_right hk] using (Classical.choose_spec (hpairs k hk)).2.2
  let X := glueBlocks x
  let Y := glueBlocks y
  have hX : X ⊆ glueBlocks B.dom := by rintro m ⟨k, hm⟩; exact ⟨k, hx k hm⟩
  have hY : Y ⊆ glueBlocks B.dom := by rintro m ⟨k, hm⟩; exact ⟨k, hy k hm⟩
  have hnull : HarmonicNull (xorSet (B.eval X ∩ B.eval Y) (B.eval (X ∩ Y))) :=
    B.inter_error_weightedNull (f := f) (g := harmonicEU) hL hX hY
  obtain ⟨N,hN⟩ := harmonicNull_eventually_small_block B.ran B.ran_disjoint hnull hε
  obtain ⟨k,hk,hkb⟩ := hbad N
  have hsmall := hN k hk
  rw [restrictSet_xorSet, restrictSet_inter_r4 (B.ran k),
    restrict_ran_eval_r4, restrict_ran_eval_r4, restrict_ran_eval_r4,
    restrictSet_inter_r4 (B.dom k),
    B.restrict_dom_glue_r4 x hx k, B.restrict_dom_glue_r4 y hy k] at hsmall
  exact (not_lt_of_ge hsmall) (he k hkb)

end FiniteBlockMap

def PrefixExceeds (f : EUWeight) (s : Finset ℕ) (ε : ℝ) : Prop :=
  ∃ n : ℕ, ε < weightedSetDensity f.weight (s : Set ℕ) n

theorem weightedNull_eventually_small_piece (f : EUWeight) (v : ℕ → Finset ℕ)
    (hpair : Pairwise (fun i j => Disjoint (v i) (v j))) {X : Set ℕ}
    (hX : WeightedNull f.weight X) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ p,
      weightedSetDensity f.weight (restrictSet (v k) X : Set ℕ) p ≤ ε := by
  obtain ⟨P,hP⟩ := hX ε hε
  obtain ⟨N,hN⟩ := eventually_disjoint_finset_of_pairwise v hpair (Finset.range P)
  refine ⟨N, fun k hk p => ?_⟩
  by_cases hp : P ≤ p
  · have hsub : (restrictSet (v k) X : Set ℕ) ⊆ X := fun _ hm => (mem_restrictSet.mp hm).2
    exact (weightedSetDensity_mono f.weight f.nonneg hsub p).trans (hP p hp)
  · have hnone : restrictSet (Finset.range p) (restrictSet (v k) X : Set ℕ) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      obtain ⟨hmr,hmv⟩ := mem_restrictSet.mp hm
      exact Finset.disjoint_left.mp (hN k hk) (mem_restrictSet.mp hmv).1
        (Finset.mem_range.mpr ((Finset.mem_range.mp hmr).trans (lt_of_not_ge hp)))
    simp [weightedSetDensity, hnone, hε.le]

namespace FiniteBlockMap

theorem eventually_no_collapse (B : FiniteBlockMap) {f g : EUWeight}
    {F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg}
    (hL : IsBlockLift f g F B) (hF : Function.Injective F) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ x : Finset ℕ, x ⊆ B.dom k →
      PrefixExceeds f x ε → PrefixExceeds g (B.act k x) δ := by
  classical
  by_contra hNo
  let Bad (j k : ℕ) (x : Finset ℕ) : Prop :=
    x ⊆ B.dom k ∧ PrefixExceeds f x ε ∧
      ∀ p, weightedSetDensity g.weight (B.act k x : Set ℕ) p ≤ blockErrorRate j
  have hSelect (j N : ℕ) : ∃ k ≥ N, ∃ x : Finset ℕ, Bad j k x := by
    by_contra hh
    apply hNo
    have hpos : 0 < blockErrorRate j := by unfold blockErrorRate; positivity
    refine ⟨blockErrorRate j, hpos, N, fun k hk x hx hlarge => ?_⟩
    by_contra hsmall
    apply hh
    refine ⟨k, hk, x, hx, hlarge, fun p => le_of_not_gt ?_⟩
    intro hp
    exact hsmall ⟨p, hp⟩
  have hPick (j N : ℕ) :
      ∃ z : ℕ × Finset ℕ, N ≤ z.1 ∧ Bad j z.1 z.2 := by
    obtain ⟨k, hk, x, hx⟩ := hSelect j N
    exact ⟨(k,x), hk, hx⟩
  let pick (j N : ℕ) : ℕ × Finset ℕ := Classical.choose (hPick j N)
  have hpick (j N : ℕ) : N ≤ (pick j N).1 ∧ Bad j (pick j N).1 (pick j N).2 :=
    Classical.choose_spec (hPick j N)
  let seq : ℕ → ℕ × Finset ℕ := Nat.rec (pick 0 0) (fun j z => pick (j + 1) (z.1 + 1))
  let φ (j : ℕ) := (seq j).1
  let x (j : ℕ) := (seq j).2
  have hbad (j : ℕ) : Bad j (φ j) (x j) := by
    cases j with
    | zero => exact (hpick 0 0).2
    | succ j => exact (hpick (j + 1) (φ j + 1)).2
  have hmono : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro j
    exact (Nat.lt_succ_self (φ j)).trans_le (hpick (j + 1) (φ j + 1)).1
  have hφ (j : ℕ) : j ≤ φ j := by
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have hj : φ j < φ (j + 1) := hmono (Nat.lt_succ_self j)
      change j + 1 ≤ φ (j + 1)
      omega
  have hx (j : ℕ) : x j ⊆ B.dom (φ j) := (hbad j).1
  let X := glueBlocks x
  have hXsub : X ⊆ glueBlocks B.dom := by
    rintro m ⟨j, hm⟩
    exact ⟨φ j, hx j hm⟩
  have hXcut (j : ℕ) : restrictSet (B.dom (φ j)) X = x j := by
    have hd : Pairwise (fun i j => Disjoint (B.dom (φ i)) (B.dom (φ j))) := by
      intro i j hij
      exact B.dom_disjoint (fun h => hij (hmono.injective h))
    change restrictSet (B.dom (φ j)) (glueBlocks x) = x j
    rw [restrictSet_glueBlocks (fun j => B.dom (φ j)) x hd hx j (by rfl),
      Finset.inter_eq_left.mpr (hx j)]
  let D (j : ℕ) := B.act (φ j) (x j)
  have hDsub (j : ℕ) : D j ⊆ B.ran (φ j) := B.act_subset _ (hx j)
  have hDdis : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j hij
    exact Disjoint.mono (hDsub i) (hDsub j)
      (B.ran_disjoint (fun h => hij (hmono.injective h)))
  have hDnull : WeightedNull g.weight (glueBlocks D) :=
    weightedNull_glue_of_dyadic_bounds g D hDdis (fun j p => (hbad j).2.2 p)
  have hEmpty : WeightedNull g.weight (B.eval ∅) :=
    B.eval_empty_weightedNull (f := f) (g := g) hL
  have hcontain : B.eval X ⊆ glueBlocks D ∪ B.eval ∅ := by
    rintro m ⟨k, hm⟩
    by_cases hk : ∃ j, φ j = k
    · obtain ⟨j,rfl⟩ := hk
      change m ∈ B.act (φ j) (restrictSet (B.dom (φ j)) X) at hm
      rw [hXcut j] at hm
      exact Or.inl ⟨j, hm⟩
    · have he : restrictSet (B.dom k) X = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro b hb
        obtain ⟨hdom, ⟨j, hxj⟩⟩ := mem_restrictSet.mp hb
        exact Finset.disjoint_left.mp (B.dom_disjoint (fun h => hk ⟨j,h⟩)) (hx j hxj) hdom
      change m ∈ B.act k (restrictSet (B.dom k) X) at hm
      rw [he] at hm
      apply Or.inr
      refine ⟨k, ?_⟩
      simpa only [restrictSet_empty_r4] using hm
  have hEvalNull : WeightedNull g.weight (B.eval X) :=
    weightedNull_mono g.weight g.nonneg hcontain (weightedNull_union g.weight g.nonneg hDnull hEmpty)
  have hclass : weightedClass f.weight f.nonneg X = 0 := by
    apply hF
    rw [hL X hXsub, map_zero]
    exact (weightedNull_iff_class_zero_r4 g.weight g.nonneg _).mp hEvalNull
  have hXnull : WeightedNull f.weight X :=
    (weightedNull_iff_class_zero_r4 f.weight f.nonneg _).mpr hclass
  obtain ⟨N, hN⟩ := weightedNull_eventually_small_piece f B.dom B.dom_disjoint hXnull hε
  obtain ⟨p, hp⟩ := (hbad N).2.1
  have hs := hN (φ N) (hφ N) p
  rw [hXcut N] at hs
  exact (not_lt_of_ge hs) hp

end FiniteBlockMap

private def windowWord (S y : Finset ℕ) : Word ↥S := fun i => decide (i.1 ∈ y)

private def windowWordSupport (S : Finset ℕ) (x : Word ↥S) : Finset ℕ := by
  classical
  exact S.filter (fun m => if h : m ∈ S then x ⟨m,h⟩ = true else False)

private theorem windowWord_support (S : Finset ℕ) (x : Word ↥S) :
    windowWord S (windowWordSupport S x) = x := by
  classical
  funext i
  cases hi : x i <;> simp [windowWord, windowWordSupport, i.2, hi]

private theorem windowWordSupport_subset (S : Finset ℕ) (x : Word ↥S) :
    windowWordSupport S x ⊆ S := by
  classical
  unfold windowWordSupport
  exact Finset.filter_subset _ _

private theorem harmonicWeight_sum_on_carrier (S : Finset ℕ) :
    totalWeight (fun i : ↥S => harmonicAtom i.1) = ∑ i ∈ S, harmonicAtom i := by
  unfold totalWeight
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach S harmonicAtom

private theorem harmonicDistance_window (w z y : Finset ℕ) (p : ℕ)
    (hz : z ⊆ w) (hy : y ⊆ w) :
    weightedDist (fun i : ↥(prefixBlock w p) => harmonicAtom i.1)
        (windowWord (prefixBlock w p) z) (windowWord (prefixBlock w p) y) =
      logPrefixMass (xorFinset z y) p := by
  have hsub : xorFinset z y ⊆ w := by
    intro m hm
    simp only [xorFinset, Finset.mem_union, Finset.mem_sdiff] at hm
    exact hm.elim (fun h => hz h.1) (fun h => hy h.1)
  have hcut : prefixBlock (xorFinset z y) p =
      (prefixBlock w p).filter (fun i => i ∈ xorFinset z y) := by
    ext m
    simp only [prefixBlock, Finset.mem_filter]
    exact ⟨fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  unfold weightedDist logPrefixMass
  rw [hcut, Finset.sum_filter, Finset.univ_eq_attach]
  calc
    _ = ∑ i ∈ (prefixBlock w p).attach,
        (if i.1 ∈ xorFinset z y then harmonicAtom i.1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hz' : i.1 ∈ z <;> by_cases hy' : i.1 ∈ y <;>
        simp [windowWord, xorFinset, Finset.mem_union, Finset.mem_sdiff, hz', hy']
    _ = _ := Finset.sum_attach (prefixBlock w p)
      (fun i => if i ∈ xorFinset z y then harmonicAtom i else 0)

private theorem one_le_harmonicSum_r4 {p : ℕ} (hp : 0 < p) : 1 ≤ harmonicSum p := by
  unfold harmonicSum
  have h := Finset.single_le_sum (f := harmonicAtom)
    (fun i _ => by unfold harmonicAtom; positivity) (Finset.mem_range.mpr hp)
  simpa [harmonicAtom] using h

theorem no_small_cover_on_linear_escape (w : Finset ℕ) (C : Finset (Finset ℕ)) (n : ℕ)
    {μ : ℝ} (hμ : 0 < μ) (hmass : μ < logConcentration w)
    (hmin : ∀ m ∈ w, 16 * ((n : ℝ) + 1) / μ ≤ (m : ℝ) + 1)
    (hcard : C.card ≤ 2 ^ n) (hsub : ∀ y ∈ C, y ⊆ w) :
    ∃ z : Finset ℕ, z ⊆ w ∧
      ∀ y ∈ C, μ / 4 < logConcentration (xorFinset z y) := by
  classical
  obtain ⟨p,hp⟩ := (lt_logConcentration_iff w μ).mp hmass
  have hp0 : 0 < p := by
    by_contra hn
    have he : p = 0 := by omega
    subst p
    have hfalse : μ < 0 := by simpa [logPrefixDensity, harmonicSum] using hp
    exact (not_lt_of_ge hμ.le) hfalse
  have hsum := one_le_harmonicSum_r4 hp0
  have hsum0 : 0 < harmonicSum p := zero_lt_one.trans_le hsum
  let S := prefixBlock w p
  let a : ↥S → ℝ := fun i => harmonicAtom i.1
  let A : ℝ := (16 * ((n : ℝ) + 1) / μ)⁻¹
  let D : Finset (Word ↥S) := C.image (windowWord S)
  have hA : 0 < A := by dsimp [A]; positivity
  have hbound (i : ↥S) : a i ≤ A := by
    have hs : S ⊆ w := Finset.filter_subset _ _
    change ((i.1 : ℝ) + 1)⁻¹ ≤ (16 * ((n : ℝ) + 1) / μ)⁻¹
    exact inv_anti₀ (by positivity) (hmin i.1 (hs i.2))
  have hM : μ * harmonicSum p < totalWeight a := by
    have hh := (lt_div_iff₀ hsum0).mp hp
    simpa only [a, S, harmonicWeight_sum_on_carrier, logPrefixMass] using hh
  have hMμ : μ < totalWeight a := by
    calc
      μ = μ * 1 := (mul_one μ).symm
      _ ≤ μ * harmonicSum p := mul_le_mul_of_nonneg_left hsum hμ.le
      _ < _ := hM
  have hA' : 16 * A = μ / ((n : ℝ) + 1) := by
    dsimp [A]
    have hn0 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [ne_of_gt hμ, hn0] <;> ring
  have hrate : (n : ℝ) < totalWeight a / (16 * A) := by
    have hnc : 0 < (n : ℝ) + 1 := by positivity
    have hmul : (n : ℝ) * (μ / ((n : ℝ) + 1)) ≤ μ := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hnc).mpr
      nlinarith only [hμ]
    apply (lt_div_iff₀ (by positivity : 0 < 16 * A)).mpr
    rw [hA']
    exact hmul.trans_lt hMμ
  have hsizeNat : D.card ≤ 2 ^ n := by
    have hi : D.card ≤ C.card := Finset.card_image_le
    exact hi.trans hcard
  have hsizeReal : (D.card : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hsizeNat
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
      convert Real.add_one_le_exp (1 : ℝ) using 1 <;> norm_num
  have hexp : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
    calc
      _ ≤ Real.exp 1 ^ n := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul, mul_one]
  have hd : (D.card : ℝ) < Real.exp (totalWeight a / (16 * A)) :=
    (hsizeReal.trans hexp).trans_lt (Real.exp_lt_exp.mpr hrate)
  obtain ⟨x,hx⟩ := far_word_quarter a D hA (fun i => by dsimp [a, harmonicAtom]; positivity) hbound hd
  let z := windowWordSupport S x
  have hz : z ⊆ w := (windowWordSupport_subset S x).trans (Finset.filter_subset _ _)
  refine ⟨z, hz, fun y hy => (lt_logConcentration_iff _ _).mpr ⟨p, ?_⟩⟩
  have hyD : windowWord S y ∈ D := Finset.mem_image.mpr ⟨y,hy,rfl⟩
  have hfar := hx (windowWord S y) hyD
  have heq := harmonicDistance_window w z y p hz (hsub y hy)
  have hzword : windowWord S z = x := windowWord_support S x
  change weightedDist a (windowWord S z) (windowWord S y) = _ at heq
  rw [hzword] at heq
  rw [heq] at hfar
  apply (lt_div_iff₀ hsum0).mpr
  linarith only [hM, hfar]

private def normalizedHarmonicAtom (p m : ℕ) : ℝ := harmonicAtom m / harmonicSum p

private theorem normalizedHarmonicAtom_nonneg (p m : ℕ) : 0 ≤ normalizedHarmonicAtom p m := by
  unfold normalizedHarmonicAtom harmonicSum
  exact div_nonneg (by unfold harmonicAtom; positivity)
    (Finset.sum_nonneg (fun i _ => by unfold harmonicAtom; positivity))

private theorem normalizedHarmonicAtom_sum (p : ℕ) (hp : 0 < p) :
    ∑ m ∈ Finset.range p, normalizedHarmonicAtom p m = 1 := by
  unfold normalizedHarmonicAtom
  rw [← Finset.sum_div]
  change harmonicSum p / harmonicSum p = 1
  exact div_self (zero_lt_one.trans_le (one_le_harmonicSum_r4 hp)).ne'

private def setBit (s : Finset ℕ) (m : ℕ) : ℝ := if m ∈ s then 1 else 0

private theorem harmonicDensity_sum_bit (s : Finset ℕ) (p : ℕ) :
    logPrefixDensity s p =
      ∑ m ∈ Finset.range p, normalizedHarmonicAtom p m * setBit s m := by
  rw [logPrefixDensity_eq_weightedSetDensity]
  unfold weightedSetDensity restrictSet
  rw [Finset.sum_div, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : m ∈ s <;>
    simp [setBit, normalizedHarmonicAtom, weightedPrefixSum, harmonicSum, hm]

private theorem harmonicDensity_inter_sum_bit (s t : Finset ℕ) (p : ℕ) :
    logPrefixDensity (s ∩ t) p =
      ∑ m ∈ Finset.range p, normalizedHarmonicAtom p m * (setBit s m * setBit t m) := by
  rw [harmonicDensity_sum_bit]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hs : m ∈ s <;> by_cases ht : m ∈ t <;> simp [setBit, Finset.mem_inter, hs, ht]

private theorem harmonicDensity_sum_le_one_r4 (s : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    logPrefixDensity s p ≤ 1 := by
  rw [harmonicDensity_sum_bit, ← normalizedHarmonicAtom_sum p hp]
  apply Finset.sum_le_sum
  intro m _
  by_cases hm : m ∈ s
  · simp [setBit, hm]
  · simpa [setBit, hm] using normalizedHarmonicAtom_nonneg p m

theorem harmonic_prefix_second_moment {ι : Type*} [Fintype ι]
    (s : ι → Finset ℕ) (p : ℕ) (hp : 0 < p) :
    (∑ i : ι, logPrefixDensity (s i) p) ^ 2 ≤
      ∑ i : ι, ∑ j : ι, logPrefixDensity (s i ∩ s j) p := by
  classical
  let W := Finset.range p
  let w : ℕ → ℝ := normalizedHarmonicAtom p
  let c (m : ℕ) := ∑ i : ι, setBit (s i) m
  have hfirst : (∑ i : ι, logPrefixDensity (s i) p) = ∑ m ∈ W, w m * c m := by
    simp_rw [harmonicDensity_sum_bit]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    change (∑ i : ι, w m * setBit (s i) m) = w m * c m
    change (∑ i : ι, w m * setBit (s i) m) = w m * (∑ i : ι, setBit (s i) m)
    rw [Finset.mul_sum]
  have hsecond : (∑ i : ι, ∑ j : ι, logPrefixDensity (s i ∩ s j) p) =
      ∑ m ∈ W, w m * (c m) ^ 2 := by
    simp_rw [harmonicDensity_inter_sum_bit]
    calc
      _ = ∑ i : ι, ∑ m ∈ W, ∑ j : ι, w m * (setBit (s i) m * setBit (s j) m) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ m ∈ W, ∑ i : ι, ∑ j : ι, w m * (setBit (s i) m * setBit (s j) m) := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m _
        dsimp only [c]
        rw [pow_two, Fintype.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
  have hsum : (∑ m ∈ W, w m) = 1 := normalizedHarmonicAtom_sum p hp
  rw [hfirst, hsecond, ← one_mul (∑ m ∈ W, w m * (c m) ^ 2), ← hsum]
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul W
    (fun m _ => normalizedHarmonicAtom_nonneg p m)
    (fun m _ => mul_nonneg (normalizedHarmonicAtom_nonneg p m) (sq_nonneg _))
    (fun m _ => le_of_eq (by ring))

theorem harmonic_packing_count {ι : Type*} [Fintype ι] (s : ι → Finset ℕ)
    (p : ℕ) (hp : 0 < p) {α η : ℝ} (hα : 0 < α) (hη : 0 ≤ η)
    (hsmall : η ≤ α ^ 2 / 4)
    (hlarge : ∀ i, α ≤ logPrefixDensity (s i) p)
    (hpair : ∀ i j, i ≠ j → logPrefixDensity (s i ∩ s j) p ≤ η) :
    (Fintype.card ι : ℝ) * α ^ 2 < 2 := by
  classical
  let Q : ℝ := Fintype.card ι
  let T := ∑ i : ι, logPrefixDensity (s i) p
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hT : Q * α ≤ T := by
    calc
      Q * α = ∑ _ : ι, α := by simp [Q, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hlarge i)
  have hl : (Q * α) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (mul_nonneg hQ0 hα.le) hT _
  have hr (i : ι) : (∑ j : ι, logPrefixDensity (s i ∩ s j) p) ≤ 1 + Q * η := by
    calc
      _ ≤ ∑ j : ι, ((if j = i then (1 : ℝ) else 0) + η) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j = i
        · rw [ite_eq_left hj]
          exact (harmonicDensity_sum_le_one_r4 _ _ hp).trans (le_add_of_nonneg_right hη)
        · rw [ite_eq_right hj, zero_add]
          exact hpair i j (Ne.symm hj)
      _ = _ := by rw [Finset.sum_add_distrib]; simp [Q, nsmul_eq_mul]
  have hu : T ^ 2 ≤ Q + Q ^ 2 * η := by
    calc
      _ ≤ ∑ i : ι, ∑ j : ι, logPrefixDensity (s i ∩ s j) p :=
        harmonic_prefix_second_moment s p hp
      _ ≤ ∑ _i : ι, (1 + Q * η) := Finset.sum_le_sum (fun i _ => hr i)
      _ = _ := by simp [Q, nsmul_eq_mul] <;> ring
  change Q * α ^ 2 < 2
  by_contra hh
  have hbig : 2 ≤ Q * α ^ 2 := le_of_not_gt hh
  have hQpos : 0 < Q := by
    by_contra hn
    have hQzero : Q = 0 := le_antisymm (le_of_not_gt hn) hQ0
    rw [hQzero, zero_mul] at hbig
    norm_num at hbig
  have hb := mul_le_mul_of_nonneg_left hbig hQ0
  have hc := mul_le_mul_of_nonneg_left hsmall (sq_nonneg Q)
  have hd := hl.trans hu
  have hpos : 0 < Q ^ 2 * α ^ 2 := mul_pos (pow_pos hQpos _) (pow_pos hα _)
  nlinarith only [hb, hc, hd, hpos]

private theorem harmonicMass_mono_prefix_r4 (s : Finset ℕ) {p q : ℕ} (hpq : p ≤ q) :
    logPrefixMass s p ≤ logPrefixMass s q := by
  unfold logPrefixMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    obtain ⟨hms, hmp⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨hms, hmp.trans_le hpq⟩
  · intro m _ _
    unfold harmonicAtom
    positivity

theorem harmonic_density_of_nearby_later_prefix (s : Finset ℕ) {p q : ℕ} {α : ℝ}
    (hα : 0 < α) (hp : 0 < p) (hpq : p ≤ q)
    (hsize : harmonicSum q ≤ 2 * harmonicSum p)
    (h : 2 * α < logPrefixDensity s p) :
    α < logPrefixDensity s q := by
  have hP := zero_lt_one.trans_le (one_le_harmonicSum_r4 hp)
  have hQ := zero_lt_one.trans_le (one_le_harmonicSum_r4 (hp.trans_le hpq))
  have hstart : (2 * α) * harmonicSum p < logPrefixMass s p :=
    (lt_div_iff₀ hP).mp h
  apply (lt_div_iff₀ hQ).mpr
  calc
    α * harmonicSum q ≤ (2 * α) * harmonicSum p := by
      have hh := mul_le_mul_of_nonneg_left hsize hα.le
      nlinarith only [hh]
    _ < logPrefixMass s p := hstart
    _ ≤ logPrefixMass s q := harmonicMass_mono_prefix_r4 s hpq

private theorem exists_dyadic_band {x : ℝ} {J : ℕ} (hx : 1 ≤ x)
    (hJ : x < (2 : ℝ) ^ J) :
    ∃ j < J, (2 : ℝ) ^ j ≤ x ∧ x < (2 : ℝ) ^ (j + 1) := by
  classical
  have hex : ∃ n : ℕ, x < (2 : ℝ) ^ n := ⟨J,hJ⟩
  let n := Nat.find hex
  have hbound : n ≤ J := Nat.find_min' hex hJ
  have hp : x < (2 : ℝ) ^ n := Nat.find_spec hex
  have hn : n ≠ 0 := by
    intro hn
    rw [hn, pow_zero] at hp
    exact (not_lt_of_ge hx) hp
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hjn : j < n := by omega
  refine ⟨j, hjn.trans_le hbound, le_of_not_gt (Nat.find_min hex hjn), ?_⟩
  simpa only [hj] using hp

theorem exists_large_harmonic_witness_of_many_images {ι : Type*} [Fintype ι]
    (s : ι → Finset ℕ) (p : ι → ℕ) {α η : ℝ} (hα : 0 < α)
    (hη : 0 ≤ η) (hsmall : η ≤ α ^ 2 / 4)
    (hp : ∀ i, 0 < p i) (hlarge : ∀ i, 2 * α < logPrefixDensity (s i) (p i))
    (hpair : ∀ i j, i ≠ j → ∀ q, logPrefixDensity (s i ∩ s j) q ≤ η)
    (R J : ℕ) (hR : 2 ≤ (R : ℝ) * α ^ 2)
    (hMany : R * J < Fintype.card ι) :
    ∃ i, (2 : ℝ) ^ J ≤ harmonicSum (p i) := by
  classical
  by_contra hn
  have hall (i : ι) : harmonicSum (p i) < (2 : ℝ) ^ J :=
    lt_of_not_ge (fun h => hn ⟨i,h⟩)
  have hbin (i : ι) := exists_dyadic_band (one_le_harmonicSum_r4 (hp i)) (hall i)
  choose bin hbinSpec using hbin
  have hJ (i : ι) := (hbinSpec i).1
  have hL (i : ι) := (hbinSpec i).2.1
  have hU (i : ι) := (hbinSpec i).2.2
  let fiber (j : ℕ) : Finset ι := Finset.univ.filter (fun i => bin i = j)
  have memFiber {j : ℕ} {i : ι} : i ∈ fiber j ↔ bin i = j := by simp [fiber]
  have hcount (j : ℕ) : (fiber j).card ≤ R := by
    by_cases hf : (fiber j).Nonempty
    · let v := (fiber j).image p
      have hv : v.Nonempty := hf.image p
      let q := v.max' hv
      have hqv : q ∈ v := Finset.max'_mem _ _
      obtain ⟨i₀, hi₀, hiq⟩ := Finset.mem_image.mp hqv
      have hi₀bin := memFiber.mp hi₀
      have hq0 : 0 < q := by rw [← hiq]; exact hp i₀
      have hQ : harmonicSum q < (2 : ℝ) ^ (j + 1) := by
        rw [← hiq, ← hi₀bin]
        exact hU i₀
      have hl (i : ↥(fiber j)) : α ≤ logPrefixDensity (s i.1) q := by
        have hip : p i.1 ∈ v := Finset.mem_image.mpr ⟨i.1,i.2,rfl⟩
        have hmax : p i.1 ≤ q := Finset.le_max' _ _ hip
        have hlow : (2 : ℝ) ^ j ≤ harmonicSum (p i.1) := by
          simpa only [memFiber.mp i.2] using hL i.1
        have hnear : harmonicSum q ≤ 2 * harmonicSum (p i.1) := by
          have h2 : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := pow_succ' _ _
          rw [h2] at hQ
          exact hQ.le.trans (mul_le_mul_of_nonneg_left hlow (by norm_num))
        exact (harmonic_density_of_nearby_later_prefix (s i.1) hα (hp i.1) hmax hnear
          (hlarge i.1)).le
      have hh : (Fintype.card ↥(fiber j) : ℝ) * α ^ 2 < 2 :=
        harmonic_packing_count (fun i : ↥(fiber j) => s i.1) q hq0 hα hη hsmall hl
          (fun i l hne => hpair i.1 l.1 (fun he => hne (Subtype.ext he)) q)
      rw [Fintype.card_coe] at hh
      have hcast : ((fiber j).card : ℝ) < R :=
        (mul_lt_mul_iff_left₀ (pow_pos hα _)).mp (hh.trans_le hR)
      exact_mod_cast hcast.le
    · have hempty : fiber j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hf
      simp [hempty]
  have hcover : (Finset.range J).biUnion fiber = (Finset.univ : Finset ι) := by
    ext i
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      exact Finset.mem_biUnion.mpr ⟨bin i, Finset.mem_range.mpr (hJ i), memFiber.mpr rfl⟩
  have hc : Fintype.card ι ≤ J * R := by
    calc
      _ = ((Finset.range J).biUnion fiber).card := by simp only [hcover, Finset.card_univ]
      _ ≤ ∑ j ∈ Finset.range J, (fiber j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Finset.range J, R := Finset.sum_le_sum (fun j _ => hcount j)
      _ = _ := by simp
  exact (not_le_of_gt hMany) (by simpa only [Nat.mul_comm] using hc)

private theorem logPrefixDensity_mono_finset_r4 {s t : Finset ℕ} (hst : s ⊆ t) (p : ℕ) :
    logPrefixDensity s p ≤ logPrefixDensity t p := by
  simp only [logPrefixDensity_eq_weightedSetDensity]
  exact weightedSetDensity_mono harmonicAtom harmonicEU.nonneg (fun _ hm => hst hm) p

private theorem logPrefixDensity_union_le_r4 (s t : Finset ℕ) (p : ℕ) :
    logPrefixDensity (s ∪ t) p ≤ logPrefixDensity s p + logPrefixDensity t p := by
  simp only [logPrefixDensity_eq_weightedSetDensity, Finset.coe_union]
  exact weightedSetDensity_union_le harmonicAtom harmonicEU.nonneg (s : Set ℕ) t p

theorem FiniteBlockMap.eventually_small_disjoint_overlaps (B : FiniteBlockMap) {f : EUWeight}
    {F : WeightedRing f.weight f.nonneg →+* WeightedRing harmonicEU.weight harmonicEU.nonneg}
    (hL : IsBlockLift f harmonicEU F B) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ x y : Finset ℕ, x ⊆ B.dom k → y ⊆ B.dom k → Disjoint x y →
      ∀ p, logPrefixDensity (B.act k x ∩ B.act k y) p ≤ η := by
  obtain ⟨N₁,h₁⟩ := B.eventually_small_empty_images hL (show 0 < η / 2 by positivity)
  obtain ⟨N₂,h₂⟩ := B.eventually_small_meet_error hL (show 0 < η / 2 by positivity)
  refine ⟨max N₁ N₂, fun k hk x y hx hy hxy p => ?_⟩
  have hxy' : x ∩ y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    exact Finset.disjoint_left.mp hxy (Finset.mem_inter.mp hm).1 (Finset.mem_inter.mp hm).2
  let s := B.act k x ∩ B.act k y
  let t := B.act k ∅
  have hsub : s ⊆ xorFinset s t ∪ t := by
    intro m hm
    by_cases ht : m ∈ t
    · exact Finset.mem_union.mpr (Or.inr ht)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_sdiff.mpr ⟨hm,ht⟩))))
  have he := h₂ k ((le_max_right N₁ N₂).trans hk) x y hx hy
  rw [hxy'] at he
  have ha : logPrefixDensity (xorFinset s t) p ≤ η / 2 :=
    (logConcentration_le_iff _ _).mp he p
  have hb : logPrefixDensity t p ≤ η / 2 :=
    (logConcentration_le_iff _ _).mp (h₁ k ((le_max_left N₁ N₂).trans hk)) p
  calc
    logPrefixDensity s p ≤ logPrefixDensity (xorFinset s t ∪ t) p :=
      logPrefixDensity_mono_finset_r4 hsub p
    _ ≤ logPrefixDensity (xorFinset s t) p + logPrefixDensity t p :=
      logPrefixDensity_union_le_r4 _ _ _
    _ ≤ η := by linarith only [ha,hb]

def ordinaryHalfWindow (t j : ℕ) : Finset ℕ :=
  Finset.Ico (t * 2 ^ j) (t * 2 ^ (j + 1))

theorem ordinaryHalfWindow_subset_justSourceBlock (i : ℕ) (j : Fin (justSourceStart i)) :
    ordinaryHalfWindow (justSourceStart i) j.1 ⊆ justSourceBlock i := by
  let t := justSourceStart i
  intro m hm
  change m ∈ Finset.Ico (t * 2 ^ j.1) (t * 2 ^ (j.1 + 1)) at hm
  have hmt := Finset.mem_Ico.mp hm
  change m ∈ Finset.Ico t (t * 2 ^ t)
  apply Finset.mem_Ico.mpr
  have hp : 1 ≤ (2 : ℕ) ^ j.1 := Nat.one_le_pow _ _ (by decide)
  have hleft : t ≤ t * 2 ^ j.1 := by
    simpa only [mul_one] using Nat.mul_le_mul_left t hp
  have hright : t * 2 ^ (j.1 + 1) ≤ t * 2 ^ t :=
    Nat.mul_le_mul_left t (Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt j.2))
  exact ⟨hleft.trans hmt.1, hmt.2.trans_le hright⟩

theorem ordinaryHalfWindow_disjoint (t : ℕ) :
    Pairwise (fun j l : ℕ => Disjoint (ordinaryHalfWindow t j) (ordinaryHalfWindow t l)) := by
  have h (j l : ℕ) (hjl : j < l) : Disjoint (ordinaryHalfWindow t j) (ordinaryHalfWindow t l) := by
    rw [Finset.disjoint_left]
    intro m hj hl
    change m ∈ Finset.Ico (t * 2 ^ j) (t * 2 ^ (j + 1)) at hj
    change m ∈ Finset.Ico (t * 2 ^ l) (t * 2 ^ (l + 1)) at hl
    have hj' := (Finset.mem_Ico.mp hj).2
    have hl' := (Finset.mem_Ico.mp hl).1
    have hnext : t * 2 ^ (j + 1) ≤ t * 2 ^ l :=
      Nat.mul_le_mul_left t (Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt hjl))
    exact (not_lt_of_ge (hnext.trans hl')) hj'
  intro j l hjl
  rcases lt_or_gt_of_ne hjl with hjl | hjl
  · exact h j l hjl
  · exact (h l j hjl).symm

private theorem ordinaryWeightedDensity_eq_r4 (s : Finset ℕ) (p : ℕ) :
    weightedSetDensity ordinaryEU.weight (s : Set ℕ) p =
      ((restrictSet (Finset.range p) (s : Set ℕ)).card : ℝ) / p := by
  simp [weightedSetDensity, weightedPrefixSum, ordinaryEU]

theorem ordinaryHalfWindow_prefixExceeds {t : ℕ} (ht : 0 < t) (j : ℕ) :
    PrefixExceeds ordinaryEU (ordinaryHalfWindow t j) (1 / 4) := by
  let a : ℕ := t * 2 ^ j
  have ha : 0 < a := Nat.mul_pos ht (pow_pos (by decide : 0 < (2 : ℕ)) _)
  have he : t * 2 ^ (j + 1) = a + a := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
  let p := t * 2 ^ (j + 1)
  let s := ordinaryHalfWindow t j
  refine ⟨p, ?_⟩
  have hr : restrictSet (Finset.range p) (s : Set ℕ) = s := by
    ext m
    simp only [mem_restrictSet, Finset.mem_range, Finset.mem_coe]
    refine ⟨And.right, fun hm => ⟨?_,hm⟩⟩
    exact (Finset.mem_Ico.mp (show m ∈ Finset.Ico a p from hm)).2
  have hc : s.card = a := by
    change (Finset.Ico a (t * 2 ^ (j + 1))).card = a
    rw [Nat.card_Ico, he]
    omega
  rw [ordinaryWeightedDensity_eq_r4, hr, hc]
  change (1 / 4 : ℝ) < (a : ℝ) / ((t * 2 ^ (j + 1) : ℕ) : ℝ)
  rw [he, Nat.cast_add]
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  apply (lt_div_iff₀ (show 0 < (a : ℝ) + a by positivity)).mpr
  linarith only [ha']

private theorem harmonicSum_mono_r4 {p q : ℕ} (hpq : p ≤ q) : harmonicSum p ≤ harmonicSum q := by
  unfold harmonicSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hm).trans_le hpq)
  · intro m _ _
    unfold harmonicAtom
    positivity

theorem logPrefixMass_le_initial_add_tail (s : Finset ℕ) (T p : ℕ) :
    logPrefixMass s p ≤ harmonicSum T + logPrefixMass (s.filter (fun m => T ≤ m)) p := by
  let L := (prefixBlock s p).filter (fun m => m < T)
  let U := prefixBlock (s.filter (fun m => T ≤ m)) p
  have hsplit : prefixBlock s p = L ∪ U := by
    ext m
    simp only [L, U, prefixBlock, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hms,hmp⟩
      rcases lt_or_ge m T with h | h
      · exact Or.inl ⟨⟨hms,hmp⟩,h⟩
      · exact Or.inr ⟨⟨hms,h⟩,hmp⟩
    · rintro (⟨⟨hms,hmp⟩,_⟩ | ⟨⟨hms,_⟩,hmp⟩) <;> exact ⟨hms,hmp⟩
  have hdis : Disjoint L U := by
    rw [Finset.disjoint_left]
    intro m hm hn
    change m ∈ (prefixBlock s p).filter (fun m => m < T) at hm
    change m ∈ (s.filter (fun m => T ≤ m)).filter (fun m => m < p) at hn
    have hlt : m < T := (Finset.mem_filter.mp hm).2
    have hge : T ≤ m := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
    omega
  have hL : L ⊆ Finset.range T := by
    intro m hm
    change m ∈ (prefixBlock s p).filter (fun m => m < T) at hm
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hm).2
  have hmass : ∑ m ∈ L, harmonicAtom m ≤ harmonicSum T := by
    unfold harmonicSum
    apply Finset.sum_le_sum_of_subset_of_nonneg hL
    intro m _ _
    unfold harmonicAtom
    positivity
  change (∑ m ∈ prefixBlock s p, harmonicAtom m) ≤ harmonicSum T + ∑ m ∈ U, harmonicAtom m
  rw [hsplit, Finset.sum_union hdis]
  exact add_le_add hmass le_rfl

theorem tail_concentration_of_large_prefix (s : Finset ℕ) (T : ℕ) {p : ℕ} {α : ℝ}
    (hp : 0 < p) (hsize : harmonicSum T ≤ α * harmonicSum p)
    (hlarge : 2 * α < logPrefixDensity s p) :
    α < logConcentration (s.filter (fun m => T ≤ m)) := by
  have hP := zero_lt_one.trans_le (one_le_harmonicSum_r4 hp)
  have h₁ : (2 * α) * harmonicSum p < logPrefixMass s p := (lt_div_iff₀ hP).mp hlarge
  have h₂ := logPrefixMass_le_initial_add_tail s T p
  have h₃ : α * harmonicSum p < logPrefixMass (s.filter (fun m => T ≤ m)) p := by
    nlinarith only [hsize,h₁,h₂]
  have h₄ : α < logPrefixDensity (s.filter (fun m => T ≤ m)) p := (lt_div_iff₀ hP).mpr h₃
  exact (lt_logConcentration_iff _ _).mpr ⟨p,h₄⟩

private theorem succ_le_twoPow_r4 (j : ℕ) : j + 1 ≤ (2 : ℕ) ^ j := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Nat.two_pow_succ]
    omega

private theorem harmonicSum_twoPow_le_r4 (l : ℕ) :
    harmonicSum (2 ^ l) ≤ (l : ℝ) + 1 := by
  induction l with
  | zero => norm_num [harmonicSum, harmonicAtom]
  | succ l ih =>
    let n : ℕ := 2 ^ l
    have hn : 0 < n := pow_pos (by decide : 0 < (2 : ℕ)) _
    have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
    have he : (2 : ℕ) ^ (l + 1) = n + n := Nat.two_pow_succ l
    have hs : (∑ m ∈ Finset.Ico n (n + n), harmonicAtom m) ≤ 1 := by
      calc
        _ ≤ ∑ _m ∈ Finset.Ico n (n + n), (n : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro m hm
          have hnm : n ≤ m := (Finset.mem_Ico.mp hm).1
          have hnr' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
          unfold harmonicAtom
          exact inv_anti₀ hnr (by linarith only [hnr'])
        _ = 1 := by
          simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
          have hsub : n + n - n = n := by omega
          rw [hsub, mul_inv_cancel₀ hnr.ne']
    have hsum : harmonicSum (n + n) =
        harmonicSum n + ∑ m ∈ Finset.Ico n (n + n), harmonicAtom m := by
      unfold harmonicSum
      exact (Finset.sum_range_add_sum_Ico harmonicAtom (by omega : n ≤ n + n)).symm
    rw [he, hsum, Nat.cast_succ]
    have hh : harmonicSum n ≤ (l : ℝ) + 1 := ih
    linarith only [hh,hs]

private theorem harmonicSum_linear_cutoff_le_r4 (K n t : ℕ) (hn : n ≤ t * 2 ^ t) :
    harmonicSum (K * (n + 1)) ≤ (K : ℝ) + 1 + 2 * (t : ℝ) := by
  have hp : 1 ≤ (2 : ℕ) ^ t := Nat.one_le_pow _ _ (by decide)
  have hb : n + 1 ≤ (t + 1) * 2 ^ t := by
    rw [Nat.add_mul, one_mul]
    omega
  have hK : K ≤ (2 : ℕ) ^ K := (Nat.le_succ K).trans (succ_le_twoPow_r4 K)
  have hT : K * (n + 1) ≤ (2 : ℕ) ^ (K + t + t) := by
    rw [pow_add, pow_add]
    calc
      K * (n + 1) ≤ K * ((t + 1) * 2 ^ t) := Nat.mul_le_mul_left K hb
      _ ≤ (2 : ℕ) ^ K * ((2 : ℕ) ^ t * 2 ^ t) :=
        Nat.mul_le_mul hK (Nat.mul_le_mul_right _ (succ_le_twoPow_r4 t))
      _ = _ := by rw [Nat.mul_assoc]
  have h := (harmonicSum_mono_r4 hT).trans (harmonicSum_twoPow_le_r4 (K + t + t))
  push_cast at h
  linarith only [h]

private theorem realSquare_le_twoPow_offset_r4 (j : ℕ) :
    ((j : ℝ) + 4) ^ 2 ≤ (2 : ℝ) ^ (j + 4) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have hj : (4 : ℝ) ≤ (j : ℝ) + 4 := by
      have h0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
      linarith only [h0]
    have hp : 4 * ((j : ℝ) + 4) ≤ ((j : ℝ) + 4) * ((j : ℝ) + 4) :=
      mul_le_mul_of_nonneg_right hj (by positivity)
    have he : (j + 1) + 4 = (j + 4) + 1 := by omega
    change (((j + 1 : ℕ) : ℝ) + 4) ^ 2 ≤ (2 : ℝ) ^ ((j + 1) + 4)
    rw [Nat.cast_add, Nat.cast_one, he]
    calc
      ((j : ℝ) + 1 + 4) ^ 2 ≤ 2 * ((j : ℝ) + 4) ^ 2 := by
        nlinarith only [hj,hp]
      _ ≤ 2 * (2 : ℝ) ^ (j + 4) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := (pow_succ' _ _).symm

private theorem realSquare_le_twoPow_r4 (j : ℕ) (hj : 4 ≤ j) :
    (j : ℝ) ^ 2 ≤ (2 : ℝ) ^ j := by
  have hd : (j - 4) + 4 = j := Nat.sub_add_cancel hj
  have hd' : ((j - 4 : ℕ) : ℝ) + 4 = (j : ℝ) := by exact_mod_cast hd
  simpa only [hd,hd'] using realSquare_le_twoPow_offset_r4 (j - 4)

private theorem eventually_linear_le_scaled_twoPow_r4 {α : ℝ} (hα : 0 < α) (C : ℝ) :
    ∃ L : ℕ, ∀ J ≥ L, C * ((J : ℝ) + 1) ≤ α * (2 : ℝ) ^ J := by
  obtain ⟨M,hM⟩ := exists_nat_gt (2 * C / α)
  refine ⟨max M 4, fun J hJ => ?_⟩
  have hJM : M ≤ J := (le_max_left _ _).trans hJ
  have hJ4 : 4 ≤ J := (le_max_right _ _).trans hJ
  have hJr : (4 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ4
  have hM' : 2 * C / α ≤ (J : ℝ) := hM.le.trans (by exact_mod_cast hJM)
  have hC : C ≤ (α / 2) * (J : ℝ) := by
    have h := (div_le_iff₀ hα).mp hM'
    nlinarith only [h]
  calc
    C * ((J : ℝ) + 1) ≤ (α / 2 * (J : ℝ)) * ((J : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ (α / 2 * (J : ℝ)) * (2 * (J : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith only [hJr]
    _ = α * (J : ℝ) ^ 2 := by ring
    _ ≤ α * (2 : ℝ) ^ J := mul_le_mul_of_nonneg_left (realSquare_le_twoPow_r4 J hJ4) hα.le

theorem exists_dyadic_budget_for_linear_cutoff (K R : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ n ≤ t * 2 ^ t,
      ∃ J : ℕ, R * J < t ∧ harmonicSum (K * (n + 1)) ≤ α * (2 : ℝ) ^ J := by
  let C : ℝ := (K : ℝ) + 1 + 2 * ((R : ℝ) + 1)
  obtain ⟨L,hL⟩ := eventually_linear_le_scaled_twoPow_r4 hα C
  refine ⟨(L + 1) * (R + 1), fun t ht n hn => ?_⟩
  let J := t / (R + 1)
  have hR : 0 < R + 1 := Nat.succ_pos R
  have hJL : L + 1 ≤ J := (Nat.le_div_iff_mul_le hR).mpr ht
  have hlow : J * (R + 1) ≤ t := Nat.div_mul_le_self _ _
  have hhigh : t < (J + 1) * (R + 1) :=
    (Nat.div_lt_iff_lt_mul hR).mp (Nat.lt_succ_self J)
  have hRJ : R * J < t := by
    rw [Nat.mul_add, mul_one, Nat.mul_comm J R] at hlow
    omega
  have hhigh' : (t : ℝ) ≤ ((J : ℝ) + 1) * ((R : ℝ) + 1) := by
    exact_mod_cast hhigh.le
  have hbasic := harmonicSum_linear_cutoff_le_r4 K n t hn
  have hC : (K : ℝ) + 1 + 2 * (t : ℝ) ≤ C * ((J : ℝ) + 1) := by
    dsimp only [C]
    have hmul : 0 ≤ ((K : ℝ) + 1) * (J : ℝ) := by positivity
    nlinarith only [hhigh',hmul]
  exact ⟨J,hRJ,hbasic.trans (hC.trans (hL J (by omega)))⟩

private theorem justSourceBlock_card_le_r4 (i : ℕ) :
    (justSourceBlock i).card ≤ justSourceStart i * 2 ^ justSourceStart i := by
  change (Finset.Ico (justSourceStart i) (justSourceStart i * 2 ^ justSourceStart i)).card ≤ _
  rw [Nat.card_Ico]
  omega

private theorem linear_escape_of_cutoff_r4 {K n m : ℕ} {α : ℝ}
    (hK : 16 / α ≤ (K : ℝ)) (hm : K * (n + 1) ≤ m) :
    16 * ((n : ℝ) + 1) / α ≤ (m : ℝ) + 1 := by
  have hmr : (K : ℝ) * ((n : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hm
  calc
    _ = (16 / α) * ((n : ℝ) + 1) := by ring
    _ ≤ (K : ℝ) * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ ≤ (m : ℝ) := hmr
    _ ≤ _ := le_add_of_nonneg_right zero_le_one

theorem FiniteBlockMap.eventually_exists_concentrated_late_window (B : FiniteBlockMap)
    {F : WeightedRing ordinaryEU.weight ordinaryEU.nonneg →+*
      WeightedRing harmonicEU.weight harmonicEU.nonneg}
    (hL : IsBlockLift ordinaryEU harmonicEU F B) (hFi : Function.Injective F)
    (hsource : ∀ k, ∃ i ≥ k, B.dom k = justSourceBlock i) :
    ∃ α : ℝ, 0 < α ∧ ∃ N : ℕ, ∀ k ≥ N, ∃ w : Finset ℕ,
      w ⊆ B.ran k ∧ α < logConcentration w ∧
        ∀ m ∈ w, 16 * (((B.dom k).card : ℝ) + 1) / α ≤ (m : ℝ) + 1 := by
  classical
  obtain ⟨δ,hδ,N₁,hN₁⟩ := B.eventually_no_collapse hL hFi (show (0 : ℝ) < 1 / 4 by norm_num)
  let α : ℝ := δ / 4
  have hα : 0 < α := by dsimp [α]; positivity
  let η : ℝ := α ^ 2 / 4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N₂,hN₂⟩ := B.eventually_small_disjoint_overlaps hL hη
  obtain ⟨R,hR⟩ := exists_nat_gt (2 / α ^ 2)
  have hR' : 2 ≤ (R : ℝ) * α ^ 2 :=
    (div_le_iff₀ (pow_pos hα _)).mp hR.le
  obtain ⟨K,hK⟩ := exists_nat_gt (16 / α)
  obtain ⟨N₃,hN₃⟩ := exists_dyadic_budget_for_linear_cutoff K R hα
  refine ⟨α,hα,max N₁ (max N₂ N₃), fun k hk => ?_⟩
  obtain ⟨i,hik,hDi⟩ := hsource k
  let t := justSourceStart i
  have ht : 0 < t := by have h := justSourceStart_growth i; dsimp [t]; omega
  have htN : N₃ ≤ t := by
    have h₁ : N₃ ≤ k := (le_max_right N₂ N₃).trans ((le_max_right N₁ (max N₂ N₃)).trans hk)
    have h₂ := justSourceStart_growth i
    dsimp [t]
    omega
  let n := (B.dom k).card
  have hn : n ≤ t * 2 ^ t := by
    dsimp [n,t]
    rw [hDi]
    exact justSourceBlock_card_le_r4 i
  obtain ⟨J,hJ,hbudget⟩ := hN₃ t htN n hn
  let x (j : Fin t) := ordinaryHalfWindow t j.1
  let s (j : Fin t) := B.act k (x j)
  have hx (j : Fin t) : x j ⊆ B.dom k := by
    rw [hDi]
    exact ordinaryHalfWindow_subset_justSourceBlock i j
  have hW (j : Fin t) : ∃ p : ℕ, 0 < p ∧ 2 * α < logPrefixDensity (s j) p := by
    have hk₁ := (le_max_left N₁ (max N₂ N₃)).trans hk
    obtain ⟨p,hp⟩ := hN₁ k hk₁ (x j) (hx j) (ordinaryHalfWindow_prefixExceeds ht j.1)
    have hP : δ < logPrefixDensity (s j) p := by
      rw [logPrefixDensity_eq_weightedSetDensity]
      exact hp
    have hp₀ : 0 < p := by
      by_contra hp₀
      have he : p = 0 := by omega
      have hfalse : δ < 0 := by simpa [logPrefixDensity, harmonicSum, he] using hP
      exact (not_lt_of_ge hδ.le) hfalse
    refine ⟨p,hp₀,?_⟩
    have hh : 2 * α ≤ δ := by dsimp [α]; linarith only [hδ]
    exact hh.trans_lt hP
  choose p hpSpec using hW
  have hp (j : Fin t) := (hpSpec j).1
  have hD (j : Fin t) := (hpSpec j).2
  have hpair (j l : Fin t) (hjl : j ≠ l) (q : ℕ) :
      logPrefixDensity (s j ∩ s l) q ≤ η := by
    have hk₂ := (le_max_left N₂ N₃).trans ((le_max_right N₁ (max N₂ N₃)).trans hk)
    have hdis : Disjoint (x j) (x l) :=
      ordinaryHalfWindow_disjoint t (fun h => hjl (Fin.ext h))
    exact hN₂ k hk₂ (x j) (x l) (hx j) (hx l) hdis q
  have hMany : R * J < Fintype.card (Fin t) := by simpa only [Fintype.card_fin] using hJ
  obtain ⟨j,hbig⟩ :=
    exists_large_harmonic_witness_of_many_images s p hα hη.le le_rfl hp hD hpair R J hR' hMany
  let T := K * (n + 1)
  let w := (s j).filter (fun m => T ≤ m)
  refine ⟨w, (Finset.filter_subset _ _).trans (B.act_subset k (hx j)), ?_, ?_⟩
  · have hsize : harmonicSum T ≤ α * harmonicSum (p j) :=
      hbudget.trans (mul_le_mul_of_nonneg_left hbig hα.le)
    exact tail_concentration_of_large_prefix (s j) T (hp j) hsize (hD j)
  · intro m hm
    change m ∈ (s j).filter (fun m => T ≤ m) at hm
    exact linear_escape_of_cutoff_r4 hK.le (Finset.mem_filter.mp hm).2

theorem CSPD.not_orderIso_ordinary_harmonic (hC : CSPD) :
    ¬ Nonempty (WeightedAlgebra ordinaryEU.weight ordinaryEU.nonneg ≃o
      WeightedAlgebra harmonicEU.weight harmonicEU.nonneg) := by
  classical
  rintro ⟨e⟩
  obtain ⟨B,hsource,hB⟩ := hC.exists_finiteBlockMap_on_long_source_blocks e
  let E := ringEquivOfBoolAlgebraOrderIso e
  let F := E.toRingHom
  have hL : IsBlockLift ordinaryEU harmonicEU F B := hB
  have hi : Function.Injective F := E.injective
  have hs : Function.Surjective F := E.surjective
  have honto := B.surjectiveOnSupport_of_quotientLift ordinaryEU.nonneg F hs hL
  obtain ⟨α,hα,N,hN⟩ := B.eventually_exists_concentrated_late_window hL hi hsource
  let w (k : ℕ) : Finset ℕ := if h : N ≤ k then Classical.choose (hN k h) else ∅
  have hw (k : ℕ) : w k ⊆ B.ran k := by
    by_cases hk : N ≤ k
    · simpa only [w,dite_eq_left hk] using (Classical.choose_spec (hN k hk)).1
    · simp [w,hk]
  obtain ⟨M,hM⟩ := B.eventually_approx_every_subset honto w hw (show 0 < α / 4 by positivity)
  let k := max N M
  have hkN : N ≤ k := le_max_left _ _
  have hkM : M ≤ k := le_max_right _ _
  have hwSpec := Classical.choose_spec (hN k hkN)
  have hmass : α < logConcentration (w k) := by
    simpa only [w,dite_eq_left hkN] using hwSpec.2.1
  have hfar : ∀ m ∈ w k, 16 * (((B.dom k).card : ℝ) + 1) / α ≤ (m : ℝ) + 1 := by
    simpa only [w,dite_eq_left hkN] using hwSpec.2.2
  obtain ⟨z,hz,hfar_all⟩ :=
    no_small_cover_on_linear_escape (w k) (B.centers k (w k)) (B.dom k).card hα hmass hfar
      (B.centers_card k (w k)) (fun y hy => B.centers_subset k (w k) y hy)
  obtain ⟨x,hx',hx⟩ := hM k hkM z hz
  have hcenter : B.act k x ∩ w k ∈ B.centers k (w k) :=
    Finset.mem_image.mpr ⟨x,Finset.mem_powerset.mpr hx',rfl⟩
  exact (not_lt_of_ge hx) (hfar_all _ hcenter)

end

end JSP000933
