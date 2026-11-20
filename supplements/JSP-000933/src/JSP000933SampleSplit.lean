import JSP000933SecondCover

open Filter
open scoped Topology

namespace JSP000933

noncomputable section

abbrev QuadPrefix (p : ℕ) :=
  (Fin p → Bool) × (Fin p → Bool) × (Fin p → Bool) × (Fin p → Bool)

def restrictCrossingCube (p : ℕ) (z : CrossingCube) : QuadPrefix p :=
  (fun i => z.1 i.1, fun i => z.2.1 i.1, fun i => z.2.2.1 i.1, fun i => z.2.2.2 i.1)

theorem continuous_restrictCrossingCube [TopologicalSpace Bool] (p : ℕ) :
    Continuous (restrictCrossingCube p) := by
  have h₁ : Continuous (fun z : CrossingCube => fun i : Fin p => z.1 i.1) := by
    exact continuous_pi (fun i => (continuous_apply i.1).comp continuous_fst)
  have h₂ : Continuous (fun z : CrossingCube => fun i : Fin p => z.2.1 i.1) := by
    exact continuous_pi (fun i => (continuous_apply i.1).comp continuous_snd.fst)
  have h₃ : Continuous (fun z : CrossingCube => fun i : Fin p => z.2.2.1 i.1) := by
    exact continuous_pi (fun i => (continuous_apply i.1).comp continuous_snd.snd.fst)
  have h₄ : Continuous (fun z : CrossingCube => fun i : Fin p => z.2.2.2 i.1) := by
    exact continuous_pi (fun i => (continuous_apply i.1).comp continuous_snd.snd.snd)
  exact h₁.prodMk (h₂.prodMk (h₃.prodMk h₄))

private theorem exact_prefix_sample_r18 [TopologicalSpace Bool] [DiscreteTopology Bool]
    {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ} {D : Set (CrossPoint A F)}
    {x : CrossPoint A F} (hx : x ∈ closure D) (p : ℕ) :
    ∃ y ∈ D, restrictCrossingCube p y.1 = restrictCrossingCube p x.1 := by
  let U : Set (CrossPoint A F) := {z | restrictCrossingCube p z.1 = restrictCrossingCube p x.1}
  have hU : IsOpen U := (isOpen_discrete ({restrictCrossingCube p x.1} : Set (QuadPrefix p))).preimage
    ((continuous_restrictCrossingCube p).comp continuous_subtype_val)
  have hxU : x ∈ U := rfl
  obtain ⟨y,hyU,hyD⟩ := (mem_closure_iff.mp hx) U hU hxU
  exact ⟨y,hyD,hyU⟩

private theorem finite_subset_some_initial_r18 {s : Set ℕ} (hs : s.Finite) :
    ∃ B : ℕ, s ⊆ Set.Iio B := by
  classical
  refine ⟨hs.toFinset.sup id + 1,fun i hi => ?_⟩
  have hm : i ∈ hs.toFinset := by simpa using hi
  have hle : i ≤ hs.toFinset.sup id := Finset.le_sup (f := id) hm
  exact Nat.lt_succ_of_le hle

theorem exists_finite_sample_bound [TopologicalSpace Bool] [DiscreteTopology Bool]
    {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ} (V D : ℕ → Set (CrossPoint A F)) (c : Set ℕ)
    (hdense : ∀ n, V n ⊆ closure (D n))
    (hfinite : ∀ n, ∀ q ∈ D n, (capOf q ∩ c).Finite)
    (n p : ℕ) :
    ∃ B : ℕ, ∀ l ≤ n, ∀ x ∈ V l, ∃ y ∈ D l,
      restrictCrossingCube p y.1 = restrictCrossingCube p x.1 ∧ capOf y ∩ c ⊆ Set.Iio B := by
  classical
  let I := Fin (n+1) × QuadPrefix p
  let Possible (i : I) : Prop := ∃ y ∈ D i.1.1, restrictCrossingCube p y.1 = i.2
  let pick (i : I) (h : Possible i) := Classical.choose h
  have pickSpec (i : I) (h : Possible i) :
      pick i h ∈ D i.1.1 ∧ restrictCrossingCube p (pick i h).1 = i.2 :=
    Classical.choose_spec h
  have boundFor (i : I) (h : Possible i) :
      ∃ B : ℕ, capOf (pick i h) ∩ c ⊆ Set.Iio B :=
    finite_subset_some_initial_r18 (hfinite i.1.1 (pick i h) (pickSpec i h).1)
  let cost (i : I) : ℕ := if h : Possible i then Classical.choose (boundFor i h) else 0
  let N := Finset.univ.sup cost
  refine ⟨N,fun l hl x hx => ?_⟩
  let i : I := (⟨l,Nat.lt_succ_of_le hl⟩,restrictCrossingCube p x.1)
  have hi : Possible i := exact_prefix_sample_r18 (hdense l hx) p
  have hN : cost i ≤ N := Finset.le_sup (Finset.mem_univ i)
  have hh : capOf (pick i hi) ∩ c ⊆ Set.Iio (cost i) := by
    simpa only [cost,dite_eq_left hi] using Classical.choose_spec (boundFor i hi)
  refine ⟨pick i hi,(pickSpec i hi).1,(pickSpec i hi).2,?_⟩
  intro m hm
  exact (hh hm).trans_le hN

def colorParity (b : Bool) : ℕ := if b then 1 else 0

def parityPiece (c : Set ℕ) (cut : ℕ → ℕ) (b : Bool) : Set ℕ :=
  {m | m ∈ c ∧ ∃ k : ℕ, k % 2 = colorParity b ∧ cut k ≤ m ∧ m < cut (k+1)}

theorem exists_two_infinite_pieces_with_sample_prefixes
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ} (V D : ℕ → Set (CrossPoint A F))
    {c : Set ℕ} (hc : c.Infinite)
    (hdense : ∀ n, V n ⊆ closure (D n))
    (hfinite : ∀ n, ∀ q ∈ D n, (capOf q ∩ c).Finite) :
    ∃ cut : ℕ → ℕ, StrictMono cut ∧ cut 0 = 0 ∧
      parityPiece c cut false ∪ parityPiece c cut true = c ∧
      Disjoint (parityPiece c cut false) (parityPiece c cut true) ∧
      (∀ b : Bool, (parityPiece c cut b).Infinite) ∧
      ∀ b : Bool, ∀ l k : ℕ, l ≤ k → k % 2 ≠ colorParity b → ∀ x ∈ V l,
        ∃ y ∈ D l, restrictCrossingCube (cut k) y.1 = restrictCrossingCube (cut k) x.1 ∧
          capOf y ∩ parityPiece c cut b ⊆ Set.Iio (cut k) := by
  classical
  choose look hLook using (fun n p => exists_finite_sample_bound V D c hdense hfinite n p)
  have hchoose (p : ℕ) : ∃ m ∈ c, p ≤ m := by
    obtain ⟨m,hm,hn⟩ := hc.exists_notMem_finset (Finset.range p)
    exact ⟨m,hm,Nat.le_of_not_lt (fun h => hn (Finset.mem_range.mpr h))⟩
  choose point hPoint using hchoose
  let cut : ℕ → ℕ := Nat.rec 0
    (fun k p => max (p+1) (max (look k p) (point p+1)))
  have hNext (k : ℕ) : cut (k+1) =
      max (cut k+1) (max (look k (cut k)) (point (cut k)+1)) := rfl
  have h0 : cut 0 = 0 := rfl
  have hcut : StrictMono cut := by
    apply strictMono_nat_of_lt_succ
    intro k
    rw [hNext]
    exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  have hlook (k : ℕ) : look k (cut k) ≤ cut (k+1) := by
    rw [hNext]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hpointCut (k : ℕ) : cut k ≤ point (cut k) ∧ point (cut k) < cut (k+1) := by
    refine ⟨(hPoint (cut k)).2,?_⟩
    rw [hNext]
    exact (Nat.lt_succ_self _).trans_le ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨cut,hcut,h0,?_,?_,?_,?_⟩
  · ext m
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro hm
      let k := hybridBand cut hcut m
      have hk : cut k ≤ m ∧ m < cut (k+1) := hybridBand_spec cut hcut h0 m
      have hmod : k % 2 < 2 := Nat.mod_lt _ (by decide)
      by_cases h : k % 2 = 0
      · exact Or.inl ⟨hm,k,h,hk.1,hk.2⟩
      · have h1 : k % 2 = 1 := by omega
        exact Or.inr ⟨hm,k,h1,hk.1,hk.2⟩
  · rw [Set.disjoint_left]
    intro m hm hn
    obtain ⟨_,i,hi,hlo,hhi⟩ := hm
    obtain ⟨_,j,hj,jlo,jhi⟩ := hn
    have hI := (hybridBand_eq_iff cut hcut h0 m i).mpr ⟨hlo,hhi⟩
    have hJ := (hybridBand_eq_iff cut hcut h0 m j).mpr ⟨jlo,jhi⟩
    have hEq : i = j := hI.symm.trans hJ
    have hj' : i % 2 = colorParity true := by rwa [hEq]
    have hbad : (0 : ℕ) = 1 := hi.symm.trans hj'
    omega
  · intro b
    let i (n : ℕ) := 2*n + colorParity b
    let p (n : ℕ) := point (cut (i n))
    have hInject : Function.Injective p := by
      apply StrictMono.injective
      intro a d had
      have hii : i a + 1 ≤ i d := by dsimp [i]; omega
      exact ((hpointCut (i a)).2.trans_le (hcut.monotone hii)).trans_le (hpointCut (i d)).1
    apply (Set.infinite_range_of_injective hInject).mono
    rintro _ ⟨n,rfl⟩
    refine ⟨(hPoint (cut (i n))).1,i n,?_,(hpointCut (i n)).1,(hpointCut (i n)).2⟩
    cases b <;> simp [i,colorParity] <;> omega
  · intro b l k hl hk x hx
    obtain ⟨y,hy,hpre,hbound⟩ := hLook k (cut k) l hl x hx
    refine ⟨y,hy,hpre,?_⟩
    intro m hm
    obtain ⟨hmcap,hmPart⟩ := hm
    obtain ⟨hmc,j,hjp,hjl,hjh⟩ := hmPart
    have ht : m < cut (k+1) := (hbound ⟨hmcap,hmc⟩).trans_le (hlook k)
    change m < cut k
    apply Nat.lt_of_not_ge
    intro hlow
    have hK := (hybridBand_eq_iff cut hcut h0 m k).mpr ⟨hlow,ht⟩
    have hJ := (hybridBand_eq_iff cut hcut h0 m j).mpr ⟨hjl,hjh⟩
    rw [hK.symm.trans hJ] at hk
    exact hk hjp

end

end JSP000933
