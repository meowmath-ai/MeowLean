import JSP000930AnalyticOrderedCut

open Fol JSP000933.SetLanguage

namespace JSP000930.AnalyticSyntax

def complex_f {n : ℕ} (z : STerm n) : SForm n :=
  sEx (fun x => sEx (fun y => bd_and (realCut_f (lift_bounded_term x 1)) (bd_and (realCut_f y) (bd_and (bd_equal (lift_bounded_term z 2) (pair' (lift_bounded_term x 1) y)) (bd_equal (lift_bounded_term x 1) (lift_bounded_term x 1))))))

def unpackComplex_f {n k : ℕ} (z : STerm n) (ps : Fin k → STerm n)
    (body : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → STerm d → SForm d) : SForm n :=
  sEx fun x => sEx fun y =>
    bd_and (bd_equal (up2 z) (pair' (up x) y))
      (bd_and (realCut_f (up x))
        (bd_and (realCut_f y) (body (fun i => up2 (ps i)) (up x) y)))

def complexNat_f {n : ℕ} (n0 z : STerm n) : SForm n :=
  unpackComplex_f z (fun _ : Fin 1 => n0) (fun p x y =>
    bd_and (realNat_f (p 0) x) (realNat_f zero y))

def complexNeg_f {n : ℕ} (a b : STerm n) : SForm n :=
  unpackComplex_f a (fun _ : Fin 1 => b) (fun p ax ay =>
    unpackComplex_f (p 0) (fun i => ![ax,ay] i) (fun t bx by0 =>
      bd_and (realNeg_f (t 0) bx) (realNeg_f (t 1) by0)))

def complexTriple_f {n : ℕ} (a b c : STerm n)
    (body : ∀ {d : ℕ}, (Fin 6 → STerm d) → SForm d) : SForm n :=
  unpackComplex_f a (fun i => ![b,c] i) (fun p ax ay =>
    unpackComplex_f (p 0) (fun i => ![ax,ay,p 1] i) (fun r bx by0 =>
      unpackComplex_f (r 2) (fun i => ![r 0,r 1,bx,by0] i) (fun s cx cy =>
        body (fun i => ![s 0,s 1,s 2,s 3,cx,cy] i))))

def complexAdd_f {n : ℕ} (a b c : STerm n) : SForm n :=
  complexTriple_f a b c (fun t =>
    bd_and (realAdd_f (t 0) (t 2) (t 4)) (realAdd_f (t 1) (t 3) (t 5)))

def selectReal_f {n k : ℕ} (p : Fin k → STerm n)
    (rel body : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → SForm d) : SForm n :=
  sEx fun x => bd_and (realCut_f x)
    (bd_and (rel (fun i => up (p i)) x) (body (fun i => up (p i)) x))

def complexMulCore_f {n : ℕ} (t : Fin 6 → STerm n) : SForm n :=
  selectReal_f t (fun p ac => realMul_f (p 0) (p 2) ac) (fun p ac =>
    selectReal_f (fun i => ![p 0,p 1,p 2,p 3,p 4,p 5,ac] i)
      (fun r bd => realMul_f (r 1) (r 3) bd) (fun r bd =>
        selectReal_f (fun i => ![r 0,r 1,r 2,r 3,r 4,r 5,r 6,bd] i)
          (fun s nbd => realNeg_f (s 7) nbd) (fun s nbd =>
            selectReal_f (fun i => ![s 0,s 1,s 2,s 3,s 4,s 5,s 6,nbd] i)
              (fun w ad => realMul_f (w 0) (w 3) ad) (fun w ad =>
                selectReal_f (fun i => ![w 0,w 1,w 2,w 3,w 4,w 5,w 6,w 7,ad] i)
                (fun p0 bc => realMul_f (p0 1) (p0 2) bc)
                (fun p0 bc => bd_and (realAdd_f (p0 6) (p0 7) (p0 4))
                  (realAdd_f (p0 8) bc (p0 5)))))))

def complexMul_f {n : ℕ} (a b c : STerm n) : SForm n :=
  complexTriple_f a b c complexMulCore_f

def complexSub_f {n : ℕ} (a b c : STerm n) : SForm n :=
  sEx (fun nb => bd_and (complexNeg_f (lift_bounded_term b 1) nb) (complexAdd_f (lift_bounded_term a 1) nb (lift_bounded_term c 1)))

def complexNormSq_f {n : ℕ} (z r : STerm n) : SForm n :=
  unpackComplex_f z (fun _ : Fin 1 => r) (fun p x y =>
    selectReal_f (fun i => ![x,y,p 0] i) (fun t xx => realMul_f (t 0) (t 0) xx)
      (fun t xx => selectReal_f (fun i => ![t 1,t 2,xx] i)
        (fun w yy => realMul_f (w 0) (w 0) yy)
        (fun w yy => realAdd_f (w 2) yy (w 1))))

def typedComplexFunctionOn_f {n : ℕ} (g A : STerm n) : SForm n :=
  bd_and (allIn g (fun q => exIn (lift_bounded_term A 1) (fun i => sEx (fun z => bd_and (complex_f z) (bd_equal (lift_bounded_term q 2) (pair' (lift_bounded_term i 1) z)))))) (allIn A (fun i => sEx (fun z => bd_and (complex_f z) (bd_and (value_f (lift_bounded_term g 2) (lift_bounded_term i 1) z) (sAll (fun w => bd_imp (value_f (lift_bounded_term g 3) (lift_bounded_term i 2) w) (bd_equal (lift_bounded_term z 1) w)))))))

def sequence_f {n : ℕ} (a : STerm n) : SForm n :=
  typedComplexFunctionOn_f a omega

def complexRecursion_f {n k : ℕ} (m base result : STerm n)
    (param : Fin k → STerm n)
    (step : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → STerm d → STerm d → SForm d) :
    SForm n :=
  exIn omega fun endIndex =>
    bd_and (successor_f (up m) endIndex) (sEx fun g =>
      bd_and (typedComplexFunctionOn_f g (up endIndex))
        (bd_and (value_f g zero (up2 base))
          (bd_and (value_f g (up2 m) (up2 result))
            (allIn (up2 m) fun i =>
              allIn omega fun j =>
                sAll fun cur =>
                  sAll fun next =>
                    bd_imp (bd_and (successor_f (up3 i) (up2 j))
                      (bd_and (value_f (up4 g) (up3 i) (up cur))
                        (value_f (up4 g) (up2 j) next)))
                      (step (fun a => up2 (up2 (up2 (param a))))
                        (up3 i) (up cur) next)))))

def complexPow_f {n : ℕ} (z m w : STerm n) : SForm n :=
  exIn omega fun one =>
    bd_and (successor_f zero one) (sEx fun base =>
      bd_and (complexNat_f (up one) base)
        (complexRecursion_f (up2 m) base (up2 w) (fun _ : Fin 1 => up2 z)
          (fun prm _ cur next => complexMul_f cur (prm 0) next)))

def partialTaylorStep_f {n : ℕ} (prm : Fin 2 → STerm n) (i cur next : STerm n) : SForm n :=
  sEx fun a => sEx fun p => sEx fun t =>
    bd_and (value_f (up3 (prm 0)) (up3 i) (up2 a))
      (bd_and (complexPow_f (up3 (prm 1)) (up3 i) (up p))
        (bd_and (complex_f t)
          (bd_and (complexMul_f (up2 a) (up p) t)
            (complexAdd_f (up3 cur) t (up3 next)))))

def partialTaylorSum_f {n : ℕ} (A z m w : STerm n) : SForm n :=
  sEx fun base =>
    bd_and (complexNat_f zero base)
      (complexRecursion_f (up m) base (up w) (fun j : Fin 2 => if j = 0 then up A else up z)
        partialTaylorStep_f)

def natExprSelect_f {n k l : ℕ} (e : NatExpr k)
    (natParams : Fin k → STerm n) (args : Fin l → STerm n)
    (body : ∀ {d : ℕ}, (Fin l → STerm d) → STerm d → SForm d) : SForm n :=
  exIn omega fun h => bd_and (e.rel_f (fun i => up (natParams i)) h)
    (body (fun i => up (args i)) h)

def squareNatExpr : NatExpr 1 := .mul (.var 0) (.var 0)

def powSquareNatExpr : NatExpr 2 :=
  .mul (.pow (.var 0) (.var 1)) (.pow (.var 0) (.var 1))

def scaledNormCompare_f {n : ℕ} (strict : Bool) (C RP KQ : STerm n) : SForm n :=
  selectReal_f (fun i => ![C,RP,KQ] i) (fun t S => complexNormSq_f (t 0) S)
    (fun t S => selectReal_f (fun i => ![t 1,t 2,S] i)
      (fun u P => realNat_f (u 0) P)
      (fun u P => selectReal_f (fun i => ![u 1,u 2,P] i)
        (fun w U => realMul_f (w 1) (w 2) U)
        (fun w U => selectReal_f (fun i => ![w 0,U] i)
          (fun q V => realNat_f (q 0) V)
          (fun q V => if strict then realLT_f (q 1) V else realLE_f (q 1) V))))

def radiusSquared_f {n : ℕ} (C RP KQ : STerm n) : SForm n :=
  scaledNormCompare_f false C RP KQ

def radiusCoefficient_f {n : ℕ} (C R K N : STerm n) : SForm n :=
  natExprSelect_f powSquareNatExpr (fun i => ![R,N] i) (fun i => ![C,K] i)
    (fun t r => natExprSelect_f squareNatExpr (fun _ : Fin 1 => t 1)
      (fun i => ![t 0,r] i) (fun u k => radiusSquared_f (u 0) (u 1) k))

def radiusBudget_f {n : ℕ} (A R K N : STerm n) : SForm n :=
  sEx fun C => bd_and (complex_f C)
    (bd_and (value_f (up A) (up N) C) (radiusCoefficient_f C (up R) (up K) (up N)))

def radiusAt_f {n : ℕ} (A R : STerm n) : SForm n :=
  exIn omega fun K => allIn omega fun i => radiusBudget_f (up2 A) (up2 R) (up K) i

def entireRadii_f {n : ℕ} (A : STerm n) : SForm n :=
  allIn omega fun R => bd_imp (bd_not (bd_equal R zero)) (radiusAt_f (up A) R)

def isEntireCode_f {n : ℕ} (A : STerm n) : SForm n :=
  bd_and (sequence_f A) (entireRadii_f A)

def selectComplex_f {n k : ℕ} (p : Fin k → STerm n)
    (rel body : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → SForm d) : SForm n :=
  sEx fun x => bd_and (complex_f x)
    (bd_and (rel (fun i => up (p i)) x) (body (fun i => up (p i)) x))

def normError_f {n : ℕ} (D K : STerm n) : SForm n :=
  natExprSelect_f squareNatExpr (fun _ : Fin 1 => K) (fun _ : Fin 1 => D)
    (fun q kk => exIn omega fun one => bd_and (successor_f zero one)
      (scaledNormCompare_f true (up (q 0)) (up kk) one))

def evaluationBudget_f {n : ℕ} (A Z W K N : STerm n) : SForm n :=
  selectComplex_f (fun i => ![A,Z,W,K,N] i)
    (fun q P => partialTaylorSum_f (q 0) (q 1) (q 4) P)
    (fun q P => selectComplex_f (fun i => ![q 2,q 3,P] i)
      (fun r NW => complexNeg_f (r 0) NW)
      (fun r NW => selectComplex_f (fun i => ![r 1,r 2,NW] i)
        (fun w D => complexAdd_f (w 1) (w 2) D)
        (fun w D => normError_f D (w 0))))

def evalTail_f {n : ℕ} (A Z W K N : STerm n) : SForm n :=
  allIn omega fun i => bd_imp (natLE_f (up N) i)
    (evaluationBudget_f (up A) (up Z) (up W) (up K) i)

def evalAllTail_f {n : ℕ} (A Z W : STerm n) : SForm n :=
  allIn omega fun k => bd_imp (bd_not (bd_equal k zero)) (exIn omega fun N =>
    evalTail_f (up2 A) (up2 Z) (up2 W) (up k) N)

def evalAt_f {n : ℕ} (a z w : STerm n) : SForm n :=
  bd_and (isEntireCode_f a) (bd_and (complex_f z) (bd_and (complex_f w) (evalAllTail_f a z w)))

end JSP000930.AnalyticSyntax
