; ./kind2/./data/traffic_e7_46_e7_171_000.smt2
(set-logic HORN)

(declare-fun |ERR| ( ) Bool)
(declare-fun |Store_step| ( Int Int Int Bool Int Bool ) Bool)
(declare-fun |MAIN| ( Int Bool Bool Bool Bool ) Bool)
(declare-fun |INIT_STATE| ( ) Bool)
(declare-fun |Sofar_step| ( Bool Bool Bool Bool Bool Bool ) Bool)
(declare-fun |top_reset| ( Int Bool Bool Bool Int Bool Bool Bool ) Bool)
(declare-fun |Store_reset| ( Int Bool Int Bool ) Bool)
(declare-fun |top_step| ( Int Bool Int Bool Bool Bool Int Bool Bool Bool ) Bool)
(declare-fun |Sofar_reset| ( Bool Bool Bool Bool ) Bool)

(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) ) 
    (=>
      (and
        (and (= D true) (= C A))
      )
      (Sofar_reset A B C D)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) ) 
    (=>
      (and
        (and (= B A)
     (= E (or D C))
     (= H E)
     (or (= C F) B)
     (or (not B) C)
     (not I)
     (= A G))
      )
      (Sofar_step D E F G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) ) 
    (=>
      (and
        (and (= D true) (= C A))
      )
      (Store_reset A B C D)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Int) (E Int) (F Int) (G Bool) (H Int) (I Bool) ) 
    (=>
      (and
        (let ((a!1 (or (and (not (<= D 0)) (not (<= 10 C))) (= E C))))
(let ((a!2 (and a!1 (or (<= 10 C) (<= D 0) (= E (+ C D))))))
  (and (= A G)
       (= B A)
       (or (not (<= C 0)) (not (<= 0 D)) a!2)
       (or (and (<= C 0) (<= 0 D)) (= E (+ C D)))
       (or (not B) (= C 0))
       (or B (= C F))
       (not I)
       (= H E))))
      )
      (Store_step D E F G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Int) (F Bool) (G Bool) (H Bool) ) 
    (=>
      (and
        (Store_reset A B E F)
        (Sofar_reset C D G H)
        true
      )
      (top_reset A B C D E F G H)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Int) (E Bool) (F Bool) (G Int) (H Int) (I Bool) (J Int) (K Bool) (L Bool) (M Bool) (N Int) (O Bool) (P Bool) (Q Bool) ) 
    (=>
      (and
        (Sofar_step A F B C P Q)
        (Store_step H G D E N O)
        (let ((a!1 (= I (or (not F) (and (<= G 20) (<= 0 G))))))
  (and (= B L) (= C M) (= E K) (= A (and (<= H 1) (<= (- 1) H))) a!1 (= D J)))
      )
      (top_step H I J K L M N O P Q)
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        true
      )
      INIT_STATE
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Int) (F Int) (G Bool) (H Bool) (I Bool) (J Int) (K Bool) (L Bool) (M Bool) (N Bool) ) 
    (=>
      (and
        (top_step E N F G H I J K L M)
        INIT_STATE
        (top_reset A B C D F G H I)
        true
      )
      (MAIN J K L M N)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) (D Bool) (E Bool) (F Bool) (G Int) (H Bool) (I Bool) (J Bool) (K Bool) ) 
    (=>
      (and
        (top_step B K C D E F G H I J)
        (MAIN C D E F A)
        true
      )
      (MAIN G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Bool) (E Bool) ) 
    (=>
      (and
        (MAIN A B C D E)
        (not E)
      )
      ERR
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        ERR
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
