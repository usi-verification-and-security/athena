(set-logic HORN)


(declare-fun |fibo2| ( Bool Bool Bool Int Int ) Bool)
(declare-fun |main@entry| ( ) Bool)
(declare-fun |main@entry.split| ( ) Bool)
(declare-fun |fibo2@_tail| ( Int ) Bool)
(declare-fun |fibo2@.split| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (v_2 Bool) (v_3 Bool) (v_4 Bool) ) 
    (=>
      (and
        (and true (= v_2 true) (= v_3 true) (= v_4 true))
      )
      (fibo2 v_2 v_3 v_4 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Bool) (v_3 Bool) (v_4 Bool) ) 
    (=>
      (and
        (and true (= v_2 false) (= v_3 true) (= v_4 true))
      )
      (fibo2 v_2 v_3 v_4 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Bool) (v_3 Bool) (v_4 Bool) ) 
    (=>
      (and
        (and true (= v_2 false) (= v_3 false) (= v_4 false))
      )
      (fibo2 v_2 v_3 v_4 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Bool) (v_3 Bool) (v_4 Bool) ) 
    (=>
      (and
        (fibo2@.split B A)
        (and (= v_2 true) (= v_3 false) (= v_4 false))
      )
      (fibo2 v_2 v_3 v_4 A B)
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (and
        true
      )
      (fibo2@_tail A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Bool) (L Int) (M Bool) (N Bool) (O Int) (P Int) (Q Bool) (R Int) (S Int) (T Bool) (U Bool) (V Int) (W Int) (X Bool) (Y Bool) (Z Int) (A1 Int) (B1 Bool) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Int) (K1 Bool) (L1 Bool) (M1 Int) (N1 Bool) (O1 Bool) (P1 Int) (Q1 Bool) (R1 Bool) (S1 Int) (T1 Int) (v_46 Bool) (v_47 Bool) (v_48 Bool) (v_49 Bool) (v_50 Bool) (v_51 Bool) (v_52 Bool) (v_53 Bool) ) 
    (=>
      (and
        (fibo2@_tail T1)
        (fibo2 X v_46 v_47 A D)
        (fibo2 X v_48 v_49 B C)
        (fibo2 Q v_50 v_51 F I)
        (fibo2 Q v_52 v_53 G H)
        (let ((a!1 (or (not X) (not (= (<= 1 E) N)))))
  (and (= v_46 false)
       (= v_47 false)
       (= v_48 false)
       (= v_49 false)
       (= v_50 false)
       (= v_51 false)
       (= v_52 false)
       (= v_53 false)
       (or (not I1) (and I1 B1) (and I1 Q) (and Y X) (and U T))
       (or (not Q1) (and Q1 I1) (and O1 N1) (and L1 K1))
       (or (not T) (not Q) (not M))
       (or (not U) (not T) (= S O))
       (or (not U) (not T) (= V 1))
       (or (not U) (not T) (= D1 V))
       (or (not U) (not T) (= E1 S))
       (or (not U) (not T) M)
       (or (not X) (not K) (not J))
       (or (not X) (not T) (not N))
       (or (not Y) (not X) (= W O))
       (or (not Y) (not X) (= Z 0))
       (or (not Y) (not X) (= D1 Z))
       (or (not Y) (not X) (= E1 W))
       (or (not Y) (not X) N)
       (or (not B1) (not J) K)
       (or (not I1) (not Q) (= P O))
       (or (not I1) (not Q) (= R L))
       (or (not I1) (not Q) (= D1 R))
       (or (not I1) (not Q) (= E1 P))
       (or (not I1) (not B1) (= A1 1))
       (or (not I1) (not B1) (= C1 0))
       (or (not I1) (not B1) (= D1 C1))
       (or (not I1) (not B1) (= E1 A1))
       (or (not K1) (not G1) (not J))
       (or (not L1) (not K1) (= M1 1))
       (or (not L1) (not K1) (= S1 M1))
       (or (not L1) (not K1) G1)
       (or (not N1) (not K1) (not H1))
       (or (not O1) (not N1) (= P1 0))
       (or (not O1) (not N1) (= S1 P1))
       (or (not O1) (not N1) H1)
       (or (not Q1) (not I1) (= J1 F1))
       (or (not Q1) (not I1) (= S1 J1))
       (or (not J) (= K (= T1 2)))
       (or (not J) (and K1 J))
       (or (not Q) (= F (+ (- 3) T1)))
       (or (not Q) (= G (+ (- 4) T1)))
       (or (not Q) (= L (+ H I)))
       (or (not Q) (and T Q))
       (or (not T) (= M (= E 1)))
       (or (not T) (and X T))
       (or (not U) T)
       (or (not X) (= A (+ (- 2) T1)))
       (or (not X) (= B (+ (- 3) T1)))
       (or (not X) (= E (+ (- 2) T1)))
       (or (not X) (= O (+ C D)))
       a!1
       (or (not X) (and X J))
       (or (not Y) X)
       (or (not B1) (and B1 J))
       (or (not I1) (= F1 (+ D1 E1)))
       (or (not K1) (= G1 (= T1 1)))
       (or (not K1) (and N1 K1))
       (or (not L1) K1)
       (or (not O1) N1)
       (or (not R1) (and R1 Q1))
       (= R1 true)
       (not (= (<= 1 T1) H1))))
      )
      (fibo2@.split S1 T1)
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        true
      )
      main@entry
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Bool) (v_6 Bool) (v_7 Bool) (v_8 Bool) (v_9 Int) (v_10 Bool) (v_11 Bool) (v_12 Bool) (v_13 Int) ) 
    (=>
      (and
        main@entry
        (fibo2 v_6 v_7 v_8 v_9 B)
        (fibo2 v_10 v_11 v_12 v_13 A)
        (and (= v_6 true)
     (= v_7 false)
     (= v_8 false)
     (= 19 v_9)
     (= v_10 true)
     (= v_11 false)
     (= v_12 false)
     (= 18 v_13)
     (= D (= C 6765))
     (or (not F) (and F E))
     (not D)
     (= F true)
     (= C (+ A B)))
      )
      main@entry.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@entry.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
