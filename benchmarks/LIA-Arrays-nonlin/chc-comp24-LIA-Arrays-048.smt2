(set-logic HORN)


(declare-fun |funcS1__syn| ( (Array Int Int) Int Bool Bool Bool Int Int Int Int Int Int Int (Array Int Int) Int Int Int Int Int Int Int ) Bool)
(declare-fun |funcE__syn| ( (Array Int Int) Int Bool Bool Bool Int Int Int Int Int Int Int (Array Int Int) Int Int Int Int ) Bool)
(declare-fun |funcE1__sem| ( (Array Int Int) Int Bool Bool Bool Int Int Int Int Int Int Int (Array Int Int) Int Int Int Int ) Bool)
(declare-fun |funcStart__sem| ( (Array Int Int) Int Bool Bool Bool Int Int Int Int Int Int Int (Array Int Int) Int Int Int Int Int Int Int ) Bool)
(declare-fun |funcE__sem| ( (Array Int Int) Int Bool Bool Bool Int Int Int Int Int Int Int (Array Int Int) Int Int Int Int ) Bool)
(declare-fun |funcS1__sem| ( (Array Int Int) Int Bool Bool Bool Int Int Int Int Int Int Int (Array Int Int) Int Int Int Int Int Int Int ) Bool)
(declare-fun |funcStart__syn| ( (Array Int Int) Int Bool Bool Bool Int Int Int Int Int Int Int (Array Int Int) Int Int Int Int Int Int Int ) Bool)
(declare-fun |funcB__sem| ( (Array Int Int) Int Bool Bool Bool Int Int Int Int Int Int Int (Array Int Int) Int Bool Bool Bool ) Bool)
(declare-fun |realizable| ( ) Bool)
(declare-fun |funcE1__syn| ( (Array Int Int) Int Bool Bool Bool Int Int Int Int Int Int Int (Array Int Int) Int Int Int Int ) Bool)
(declare-fun |funcB__syn| ( (Array Int Int) Int Bool Bool Bool Int Int Int Int Int Int Int (Array Int Int) Int Bool Bool Bool ) Bool)

(assert
  (forall ( (A (Array Int Int)) (B Int) (C Bool) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) (M Int) (N Int) (v_14 Int) (v_15 Int) (v_16 Int) ) 
    (=>
      (and
        (and (= (store A B 4) J) (= B (+ (- 1) K)) (= v_14 L) (= v_15 M) (= v_16 N))
      )
      (funcE__syn A B C D E L F M G N H I J K v_14 v_15 v_16)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E Int) (F (Array Int Int)) (G Int) (H Int) (I (Array Int Int)) (J Int) (K Bool) (L Int) (M Int) (N Int) (O Bool) (P Int) (Q Int) (R Int) (S Bool) (T Int) (U Int) (V Int) (v_22 Int) (v_23 Int) (v_24 Int) ) 
    (=>
      (and
        (funcE1__syn B A K O S M N Q R U V H I J L P T)
        (and (= D (ite O P Q))
     (= E (ite K L M))
     (= C (ite S T U))
     (= B (store F G 0))
     (= A (+ 1 G))
     (= v_22 N)
     (= v_23 R)
     (= v_24 V))
      )
      (funcS1__syn F G K O S M N Q R U V H I J E v_22 D v_23 C v_24)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Int) (I (Array Int Int)) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P (Array Int Int)) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X (Array Int Int)) (Y Int) (Z (Array Int Int)) (A1 Int) (B1 Int) (C1 (Array Int Int)) (D1 Int) (E1 Int) (F1 Int) (G1 Bool) (H1 Bool) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Bool) (N1 Bool) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Bool) (T1 Bool) (U1 Int) (V1 Int) ) 
    (=>
      (and
        (funcB__syn I H H1 N1 T1 F1 J1 L1 P1 R1 V1 B1 P Q G1 M1 S1)
        (funcS1__syn P Q G F E F1 J1 L1 P1 R1 V1 B1 C1 D1 R S T U V W)
        (funcStart__sem C1 A1 D C B R S T U V W A X Y E1 I1 K1 O1 Q1 U1)
        (and (= N (ite (and H1 G1) I1 J1))
     (= M (ite (and M1 N1) K1 L1))
     (= L (ite (and M1 N1) O1 P1))
     (= K (ite (and S1 T1) Q1 R1))
     (= J (ite (and S1 T1) U1 V1))
     (= H (+ 1 A1))
     (= A (+ (- 1) B1))
     (= I (store Z A1 2))
     (= G (and H1 G1))
     (= F (and M1 N1))
     (= E (and S1 T1))
     (= D (and H1 G1))
     (= C (and M1 N1))
     (= B (and S1 T1))
     (not (<= B1 0))
     (= O (ite (and H1 G1) E1 F1)))
      )
      (funcStart__syn Z A1 H1 N1 T1 F1 J1 L1 P1 R1 V1 B1 C1 D1 O N M L K J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F (Array Int Int)) (G Int) (H Bool) (I Bool) (J Bool) (K Int) (L Int) (M Int) (N Int) (O (Array Int Int)) (P Int) (Q Int) (R Int) (S Int) ) 
    (=>
      (and
        (and (= B (+ 1 R))
     (= C (+ 1 Q))
     (= E P)
     (= G (+ (- 1) E))
     (= (store F G 5) D)
     (= D O)
     (= A (+ 1 S)))
      )
      (funcE1__syn F G H I J Q K R L S M N O P C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Bool) (D Bool) (E Bool) (F (Array Int Int)) (G Int) (H (Array Int Int)) (I Int) (J Bool) (K Bool) (L Bool) (M Int) (N Int) (O Int) (P Int) (Q (Array Int Int)) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) ) 
    (=>
      (and
        (funcE__syn B A J K L M T N V O X P F G S U W)
        (and (= G R)
     (= F Q)
     (= B (store H I 3))
     (not (= (<= T S) E))
     (not (= (<= V U) D))
     (not (= (<= X W) C))
     (= A (+ 1 I)))
      )
      (funcB__syn H I J K L M T N V O X P Q R E D C)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Bool) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) (J (Array Int Int)) (K Int) (L Int) (M Int) (N Int) (v_14 Int) (v_15 Int) (v_16 Int) ) 
    (=>
      (and
        (and (= B (+ (- 1) K))
     (= A J)
     (= 4 (select A B))
     (= v_14 L)
     (= v_15 M)
     (= v_16 N))
      )
      (funcE__sem A B C D E L F M G N H I J K v_14 v_15 v_16)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G Int) (H (Array Int Int)) (I Int) (J Bool) (K Int) (L Int) (M Int) (N Bool) (O Int) (P Int) (Q Int) (R Bool) (S Int) (T Int) (U Int) (v_21 Int) (v_22 Int) (v_23 Int) ) 
    (=>
      (and
        (funcE1__sem E A J N R L M P Q T U G H I K O S)
        (and (= A (+ 1 F))
     (= C (ite N O P))
     (= D (ite J K L))
     (= B (ite R S T))
     (= 0 (select E F))
     (= v_21 M)
     (= v_22 Q)
     (= v_23 U))
      )
      (funcS1__sem E F J N R L M P Q T U G H I D v_21 C v_22 B v_23)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Int) (E Int) (F Bool) (G Bool) (H Bool) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O (Array Int Int)) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W (Array Int Int)) (X Int) (Y (Array Int Int)) (Z Int) (A1 Int) (B1 (Array Int Int)) (C1 Int) (D1 Int) (E1 Int) (F1 Bool) (G1 Bool) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Bool) (M1 Bool) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Bool) (S1 Bool) (T1 Int) (U1 Int) ) 
    (=>
      (and
        (funcStart__sem B1 Z H G F Q R S T U V E W X D1 H1 J1 N1 P1 T1)
        (funcB__sem Y D G1 M1 S1 E1 I1 K1 O1 Q1 U1 A1 O P F1 L1 R1)
        (funcS1__sem O P C B A E1 I1 K1 O1 Q1 U1 A1 B1 C1 Q R S T U V)
        (and (= D (+ 1 Z))
     (= E (+ (- 1) A1))
     (= N (ite (and G1 F1) D1 E1))
     (= M (ite (and G1 F1) H1 I1))
     (= L (ite (and L1 M1) J1 K1))
     (= K (ite (and L1 M1) N1 O1))
     (= J (ite (and R1 S1) P1 Q1))
     (= I (ite (and R1 S1) T1 U1))
     (= G (and L1 M1))
     (= H (and G1 F1))
     (= F (and R1 S1))
     (= C (and G1 F1))
     (= B (and L1 M1))
     (= A (and R1 S1))
     (not (<= A1 0))
     (= 2 (select Y Z)))
      )
      (funcStart__sem Y Z G1 M1 S1 E1 I1 K1 O1 Q1 U1 A1 B1 C1 N M L K J I)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (v_9 Bool) (v_10 Bool) (v_11 Bool) (v_12 (Array Int Int)) (v_13 Int) (v_14 Int) (v_15 Int) (v_16 Int) (v_17 Int) (v_18 Int) (v_19 Int) ) 
    (=>
      (and
        (and (not (<= A 0))
     (= 2 (select B C))
     (= v_9 false)
     (= v_10 false)
     (= v_11 false)
     (= v_12 B)
     (= v_13 C)
     (= v_14 D)
     (= v_15 E)
     (= v_16 F)
     (= v_17 G)
     (= v_18 H)
     (= v_19 I))
      )
      (funcStart__sem B
                C
                v_9
                v_10
                v_11
                D
                E
                F
                G
                H
                I
                A
                v_12
                v_13
                v_14
                v_15
                v_16
                v_17
                v_18
                v_19)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (Array Int Int)) (E Int) (F (Array Int Int)) (G Int) (H Bool) (I Bool) (J Bool) (K Int) (L Int) (M Int) (N Int) (O (Array Int Int)) (P Int) (Q Int) (R Int) (S Int) ) 
    (=>
      (and
        (and (= A (+ 1 S))
     (= B (+ 1 R))
     (= C (+ 1 Q))
     (= E P)
     (= G (+ (- 1) E))
     (= D O)
     (= F D)
     (= 5 (select F G)))
      )
      (funcE1__sem F G H I J Q K R L S M N O P C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E (Array Int Int)) (F Int) (G (Array Int Int)) (H Int) (I Bool) (J Bool) (K Bool) (L Int) (M Int) (N Int) (O Int) (P (Array Int Int)) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) ) 
    (=>
      (and
        (funcE__sem G A I J K L S M U N W O E F R T V)
        (and (= A (+ 1 H))
     (= F Q)
     (= E P)
     (not (= (<= S R) D))
     (not (= (<= U T) C))
     (not (= (<= W V) B))
     (= 3 (select G H)))
      )
      (funcB__sem G H I J K L S M U N W O P Q D C B)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (v_3 Int) (v_4 Bool) (v_5 Bool) (v_6 Bool) (v_7 Int) (v_8 Int) (v_9 Int) (v_10 Int) (v_11 Int) (v_12 Int) (v_13 Int) (v_14 Int) (v_15 Int) (v_16 Int) (v_17 Int) (v_18 Int) (v_19 Int) ) 
    (=>
      (and
        (funcStart__syn A
                v_3
                v_4
                v_5
                v_6
                v_7
                v_8
                v_9
                v_10
                v_11
                v_12
                v_13
                B
                C
                v_14
                v_15
                v_16
                v_17
                v_18
                v_19)
        (and (= 0 v_3)
     (= v_4 true)
     (= v_5 true)
     (= v_6 true)
     (= 4 v_7)
     (= 10 v_8)
     (= 12 v_9)
     (= 20 v_10)
     (= 20 v_11)
     (= 12 v_12)
     (= 100 v_13)
     (= 10 v_14)
     (= 10 v_15)
     (= 20 v_16)
     (= 20 v_17)
     (= 12 v_18)
     (= 12 v_19))
      )
      realizable
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        realizable
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
