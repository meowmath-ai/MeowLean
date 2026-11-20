import JSP000933CSPD

namespace JSP000933

noncomputable section

theorem FiniteBlockMap.no_bijective_quotient_lift_on_long_source_blocks (B : FiniteBlockMap)
    {F : WeightedRing ordinaryEU.weight ordinaryEU.nonneg →+*
      WeightedRing harmonicEU.weight harmonicEU.nonneg}
    (hsource : ∀ k, ∃ i ≥ k, B.dom k = justSourceBlock i)
    (hFi : Function.Injective F) (hFs : Function.Surjective F)
    (hL : IsBlockLift ordinaryEU harmonicEU F B) : False := by
  classical
  have honto := B.surjectiveOnSupport_of_quotientLift ordinaryEU.nonneg F hFs hL
  obtain ⟨α,hα,N,hN⟩ := B.eventually_exists_concentrated_late_window hL hFi hsource
  let w (k : ℕ) : Finset ℕ := if h : N ≤ k then Classical.choose (hN k h) else ∅
  have hw (k : ℕ) : w k ⊆ B.ran k := by
    by_cases hk : N ≤ k
    · simpa only [w,dite_eq_left hk] using (Classical.choose_spec (hN k hk)).1
    · simp [w,hk]
  obtain ⟨M,hM⟩ := B.eventually_approx_every_subset honto w hw (show 0 < α / 4 by positivity)
  let k := max N M
  have hkN : N ≤ k := le_max_left _ _
  have hkM : M ≤ k := le_max_right _ _
  have hspec := Classical.choose_spec (hN k hkN)
  have hmass : α < logConcentration (w k) := by
    simpa only [w,dite_eq_left hkN] using hspec.2.1
  have hfar : ∀ m ∈ w k, 16 * (((B.dom k).card : ℝ) + 1) / α ≤ (m : ℝ) + 1 := by
    simpa only [w,dite_eq_left hkN] using hspec.2.2
  obtain ⟨z,hz,hfarAll⟩ :=
    no_small_cover_on_linear_escape (w k) (B.centers k (w k)) (B.dom k).card hα hmass hfar
      (B.centers_card k (w k)) (fun y hy => B.centers_subset k (w k) y hy)
  obtain ⟨x,hx,hclose⟩ := hM k hkM z hz
  have hcenter : B.act k x ∩ w k ∈ B.centers k (w k) :=
    Finset.mem_image.mpr ⟨x,Finset.mem_powerset.mpr hx,rfl⟩
  exact (not_lt_of_ge hclose) (hfarAll _ hcenter)

theorem no_localized_continuous_lift_of_ordinary_harmonic_orderIso
    (e : WeightedAlgebra ordinaryEU.weight ordinaryEU.nonneg ≃o
      WeightedAlgebra harmonicEU.weight harmonicEU.nonneg)
    (A : Set ℕ)
    (hA : Set.Infinite {i | (justSourceBlock i : Set ℕ) ⊆ A}) :
    ¬ HasContinuousLift (f := ordinaryEU) (g := harmonicEU)
      (ringEquivOfBoolAlgebraOrderIso e).toRingHom A := by
  intro hL
  let E := ringEquivOfBoolAlgebraOrderIso e
  let F := E.toRingHom
  obtain ⟨B,hsource,hBlock⟩ :=
    exists_finiteBlockMap_of_continuousLift (f := ordinaryEU) (g := harmonicEU)
      F hL justSourceBlock justSourceBlock_pairwise hA
  exact B.no_bijective_quotient_lift_on_long_source_blocks hsource E.injective E.surjective hBlock

def LongBlockLarge (A : Set ℕ) : Prop :=
  Set.Infinite {i | (justSourceBlock i : Set ℕ) ⊆ A}

theorem LongBlockLarge.exists_block_from_index {A : Set ℕ} (hA : LongBlockLarge A)
    (N : ℕ) : ∃ i ≥ N, (justSourceBlock i : Set ℕ) ⊆ A := by
  change Set.Infinite {i | (justSourceBlock i : Set ℕ) ⊆ A} at hA
  obtain ⟨i,hi,hnot⟩ := hA.exists_notMem_finset (Finset.range N)
  exact ⟨i, Nat.le_of_not_lt (fun hh => hnot (Finset.mem_range.mpr hh)), hi⟩

theorem LongBlockLarge.of_almost_subset {A B : Set ℕ} (hA : LongBlockLarge A)
    (hfinite : (A \ B).Finite) : LongBlockLarge B := by
  classical
  let s := hfinite.toFinset
  obtain ⟨N,havoid⟩ :=
    eventually_disjoint_finset_of_pairwise justSourceBlock justSourceBlock_pairwise s
  unfold LongBlockLarge at hA ⊢
  intro hBfin
  apply hA
  apply (hBfin.union (Finset.range N).finite_toSet).subset
  intro i hi
  change (justSourceBlock i : Set ℕ) ⊆ A at hi
  by_cases hNi : N ≤ i
  · apply Or.inl
    intro m hm
    by_contra hmB
    have he : m ∈ s := by
      simpa [s] using (show m ∈ A \ B from ⟨hi hm,hmB⟩)
    exact Finset.disjoint_left.mp (havoid i hNi) hm he
  · exact Or.inr (Finset.mem_range.mpr (Nat.lt_of_not_ge hNi))

theorem exists_large_pseudointersection (b : ℕ → Set ℕ) (hb : Antitone b)
    (hlarge : ∀ k, LongBlockLarge (b k)) :
    ∃ A : Set ℕ, LongBlockLarge A ∧ ∀ k : ℕ, (A \ b k).Finite := by
  classical
  have hchoice (k N : ℕ) : ∃ i ≥ N, (justSourceBlock i : Set ℕ) ⊆ b k :=
    (hlarge k).exists_block_from_index N
  let chooseAt (k N : ℕ) := Classical.choose (hchoice k N)
  have hchoose (k N : ℕ) : N ≤ chooseAt k N ∧
      (justSourceBlock (chooseAt k N) : Set ℕ) ⊆ b k :=
    Classical.choose_spec (hchoice k N)
  let seq : ℕ → ℕ := Nat.rec (chooseAt 0 0) (fun k x => chooseAt (k + 1) (x + 1))
  have hwhole (k : ℕ) : (justSourceBlock (seq k) : Set ℕ) ⊆ b k := by
    cases k with
    | zero => exact (hchoose 0 0).2
    | succ k => exact (hchoose (k + 1) (seq k + 1)).2
  have hmono : StrictMono seq := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact (Nat.lt_succ_self (seq k)).trans_le (hchoose (k + 1) (seq k + 1)).1
  let A := glueBlocks (fun k => justSourceBlock (seq k))
  refine ⟨A, ?_, fun k => ?_⟩
  · unfold LongBlockLarge
    apply (Set.infinite_range_of_injective hmono.injective).mono
    rintro _ ⟨i,rfl⟩ m hm
    exact ⟨i,hm⟩
  · have hf : (⋃ i ∈ (Finset.range k : Set ℕ), (justSourceBlock (seq i) : Set ℕ)).Finite :=
      (Finset.range k).finite_toSet.biUnion (fun i _ => (justSourceBlock (seq i)).finite_toSet)
    apply hf.subset
    intro m hm
    obtain ⟨i,hi⟩ := hm.1
    have hik : i < k := by
      by_contra h
      exact hm.2 (hb (Nat.le_of_not_lt h) (hwhole i hi))
    exact Set.mem_iUnion₂.mpr ⟨i,Finset.mem_range.mpr hik,hi⟩

end

end JSP000933
