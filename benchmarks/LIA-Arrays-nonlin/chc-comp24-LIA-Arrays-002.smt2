(set-logic HORN)


(declare-fun |__VERIFIER_assert@_1| ( (Array Int Int) (Array Int Int) Int ) Bool)
(declare-fun |main@verifier.error.split| ( ) Bool)
(declare-fun |__VERIFIER_assert@_call3| ( (Array Int Int) (Array Int Int) Int ) Bool)
(declare-fun |main@_bb2| ( (Array Int Int) (Array Int Int) Int Int Int ) Bool)
(declare-fun |main@entry| ( (Array Int Int) (Array Int Int) ) Bool)
(declare-fun |__VERIFIER_assert| ( Bool Bool Bool (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) Int ) Bool)

(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (v_3 Bool) (v_4 Bool) (v_5 Bool) (v_6 (Array Int Int)) (v_7 (Array Int Int)) ) 
    (=>
      (and
        (and true (= v_3 true) (= v_4 true) (= v_5 true) (= v_6 A) (= v_7 B))
      )
      (__VERIFIER_assert v_3 v_4 v_5 A v_6 B v_7 C)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (v_3 Bool) (v_4 Bool) (v_5 Bool) (v_6 (Array Int Int)) (v_7 (Array Int Int)) ) 
    (=>
      (and
        (and true (= v_3 false) (= v_4 true) (= v_5 true) (= v_6 A) (= v_7 B))
      )
      (__VERIFIER_assert v_3 v_4 v_5 A v_6 B v_7 C)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (v_3 Bool) (v_4 Bool) (v_5 Bool) (v_6 (Array Int Int)) (v_7 (Array Int Int)) ) 
    (=>
      (and
        (and true (= v_3 false) (= v_4 false) (= v_5 false) (= v_6 A) (= v_7 B))
      )
      (__VERIFIER_assert v_3 v_4 v_5 A v_6 B v_7 C)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (v_3 Bool) (v_4 Bool) (v_5 Bool) (v_6 (Array Int Int)) (v_7 (Array Int Int)) ) 
    (=>
      (and
        (__VERIFIER_assert@_call3 A B C)
        (and (= v_3 true) (= v_4 false) (= v_5 false) (= v_6 A) (= v_7 B))
      )
      (__VERIFIER_assert v_3 v_4 v_5 A v_6 B v_7 C)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) ) 
    (=>
      (and
        true
      )
      (__VERIFIER_assert@_1 A B C)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D (Array Int Int)) (E (Array Int Int)) (F Int) ) 
    (=>
      (and
        (__VERIFIER_assert@_1 D E F)
        (and (or (not C) (and C B)) (not A) (= C true) (= A (= F 0)))
      )
      (__VERIFIER_assert@_call3 D E F)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) ) 
    (=>
      (and
        true
      )
      (main@entry A B)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B (Array Int Int)) (C Int) (D Int) (E Bool) (F Bool) (G Bool) (H (Array Int Int)) (I (Array Int Int)) (J Int) (K (Array Int Int)) (L (Array Int Int)) (M Bool) (N Bool) (O Int) (P (Array Int Int)) (Q (Array Int Int)) (R Int) (S Int) (T Int) ) 
    (=>
      (and
        (main@entry I A)
        (and (= H (store B S C))
     (= C (+ 4 D))
     (= J D)
     (= T (+ 28 D))
     (not (<= D 0))
     (or (not N) (not M) (= K H))
     (or (not N) (not M) (= L I))
     (or (not N) (not M) (= P L))
     (or (not N) (not M) (= Q K))
     (or (not N) (not M) (= O J))
     (or (not N) (not M) (= R O))
     (or (not (<= C 0)) (<= D 0))
     (or (not (<= J 0)) (<= D 0))
     (or (not (<= T 0)) (<= D 0))
     (or (not G) (and G F))
     (or (not M) (and N M))
     (or (not N) (and N G))
     (not E)
     (= M true)
     (= B (store A S 0)))
      )
      (main@_bb2 P Q R S T)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Bool) (E Bool) (F Bool) (G (Array Int Int)) (H (Array Int Int)) (I Int) (J (Array Int Int)) (K Int) (L (Array Int Int)) (M (Array Int Int)) (N Int) (O (Array Int Int)) (P (Array Int Int)) (Q Bool) (R Bool) (S Int) (T (Array Int Int)) (U (Array Int Int)) (V Int) (W Int) (X Int) (v_24 Bool) (v_25 Bool) ) 
    (=>
      (and
        (main@_bb2 G H K W X)
        (__VERIFIER_assert R v_24 v_25 G J H L I)
        (let ((a!1 (ite (>= K 0)
                (or (not (<= C K)) (not (>= C 0)))
                (and (not (<= C K)) (not (<= 0 C)))))
      (a!2 (ite (>= X 0)
                (or (not (<= K X)) (not (>= K 0)))
                (and (not (<= K X)) (not (<= 0 K))))))
  (and (= v_24 false)
       (= v_25 false)
       (or (not E) (= D (= K C)) (= D a!1))
       (or (not R) (not (<= N 0)) (<= K 0))
       (or (not R) (not E) F)
       (or (not R) (not Q) (= O L))
       (or (not R) (not Q) (= P M))
       (or (not R) (not Q) (= T P))
       (or (not R) (not Q) (= U O))
       (or (not R) (not Q) (= S N))
       (or (not R) (not Q) (= V S))
       (or (not E) (= C (select H W)))
       (or (not E) (= I (ite D 1 0)))
       (or (not E) (and E B))
       (or (not Q) (and R Q))
       (or (not R) (= M (store J K 1)))
       (or (not R) (= N (+ 4 K)))
       (or (not R) (and R E))
       (not A)
       (= Q true)
       (= A a!2)))
      )
      (main@_bb2 T U V W X)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Bool) (D Bool) (E (Array Int Int)) (F Int) (G Int) (H Int) (I Bool) (J Bool) (K Bool) (L Bool) (M Int) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) ) 
    (=>
      (and
        (main@_bb2 A E G F B)
        (let ((a!1 (ite (>= G 0)
                (or (not (<= H G)) (not (>= H 0)))
                (and (not (<= H G)) (not (<= 0 H)))))
      (a!2 (ite (>= B 0)
                (or (not (<= G B)) (not (>= G 0)))
                (and (not (<= G B)) (not (<= 0 G))))))
  (and (or (not J) (= I (= G H)) (= I a!1))
       (or (not L) (not K) (not J))
       (or (not J) (= H (select E F)))
       (or (not J) (= M (ite I 1 0)))
       (or (not J) (and D J))
       (or (not P) (and O P))
       (or (not Q) (and Q P))
       (or (not R) (and R Q))
       (or (not L) (and L J))
       (or (not O) (= N (= M 0)))
       (or (not O) (and O L))
       (or (not O) N)
       (= R true)
       (not C)
       (= C a!2)))
      )
      main@verifier.error.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@verifier.error.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
