; ./kind2/./data/car_4_e8_118_000.smt2
(set-logic HORN)

(declare-fun |top_reset| ( Int Int Int Bool Bool Bool Bool Int Int Int Bool Bool Bool Bool ) Bool)
(declare-fun |ERR| ( ) Bool)
(declare-fun |excludes2_fun| ( Bool Bool Bool ) Bool)
(declare-fun |voiture_reset| ( Int Int Int Bool Bool Int Int Int Bool Bool ) Bool)
(declare-fun |voiture_step| ( Bool Bool Bool Bool Bool Int Int Int Bool Bool Bool Int Int Int Bool Bool Int Int Int Bool Bool ) Bool)
(declare-fun |INIT_STATE| ( ) Bool)
(declare-fun |Sofar_step| ( Bool Bool Bool Bool Bool Bool ) Bool)
(declare-fun |top_step| ( Bool Bool Bool Int Int Int Bool Bool Bool Bool Int Int Int Bool Bool Bool Bool ) Bool)
(declare-fun |MAIN| ( Int Int Int Bool Bool Bool Bool Bool ) Bool)
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
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) ) 
    (=>
      (and
        (and (= B A)
     (= G D)
     (or B (= D (and E C)))
     (or (not B) (= D C))
     (not H)
     (= A F))
      )
      (Sofar_step C D E F G H)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) ) 
    (=>
      (and
        (not (= (and B A) C))
      )
      (excludes2_fun A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Bool) (J Bool) ) 
    (=>
      (and
        (and (= G B) (= H C) (= I D) (= J true) (= F A))
      )
      (voiture_reset A B C D E F G H I J)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Int) (P Int) (Q Int) (R Bool) (S Bool) (T Int) (U Int) (V Int) (W Bool) (X Bool) ) 
    (=>
      (and
        (let ((a!1 (and (= N (and (not E) D)) (= M E) (= L R)))
      (a!2 (and (or C (= J P)) (or (not C) (= J (+ 1 P)))))
      (a!4 (and (or (= I Q) C) (or (not C) (= I (+ 1 Q)))))
      (a!5 (and (or M (= K O)) (or (not M) (= K (+ 1 O))))))
(let ((a!3 (and (or (and M (not L)) a!2) (or (not M) L (= J 0)))))
  (and (= U J)
       (= V I)
       (= A S)
       (= B A)
       (= C (and N L))
       (= F (>= J 3))
       (= G (>= K 4))
       (= H (= I 10))
       (= W (and L (not H) (not G) (not F)))
       (or (not B) (= I 0))
       (or (not B) (= J 0))
       (or (not B) (= K 0))
       (or a!1 B)
       (or (not B) (and (not N) (not M) L))
       (or B a!3)
       (or a!4 B)
       (or a!5 B)
       (not X)
       (= T K))))
      )
      (voiture_step D E F G H I J K L M N O P Q R S T U V W X)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Bool) (G Bool) (H Int) (I Int) (J Int) (K Bool) (L Bool) (M Bool) (N Bool) ) 
    (=>
      (and
        (voiture_reset A B C D E H I J K L)
        (Sofar_reset F G M N)
        true
      )
      (top_reset A B C D E F G H I J K L M N)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Int) (H Int) (I Bool) (J Bool) (K Bool) (L Int) (M Int) (N Int) (O Bool) (P Bool) (Q Bool) (R Int) (S Bool) (T Bool) (U Bool) (V Int) (W Int) (X Int) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Int) (D1 Int) (E1 Int) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) ) 
    (=>
      (and
        (excludes2_fun S T A)
        (Sofar_step A Q B C H1 I1)
        (voiture_step S T D E F G R H I J K L M N O P C1 D1 E1 F1 G1)
        (and (= M W)
     (= N X)
     (= B A1)
     (= C B1)
     (= O Y)
     (= P Z)
     (= U (or (not Q) (>= R 0)))
     (= L V))
      )
      (top_step S T U V W X Y Z A1 B1 C1 D1 E1 F1 G1 H1 I1)
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
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Int) (K Int) (L Int) (M Bool) (N Bool) (O Bool) (P Bool) (Q Int) (R Int) (S Int) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) ) 
    (=>
      (and
        (top_step H I X J K L M N O P Q R S T U V W)
        INIT_STATE
        (top_reset A B C D E F G J K L M N O P)
        true
      )
      (MAIN Q R S T U V W X)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Int) (E Int) (F Int) (G Bool) (H Bool) (I Bool) (J Bool) (K Int) (L Int) (M Int) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) ) 
    (=>
      (and
        (top_step B C R D E F G H I J K L M N O P Q)
        (MAIN D E F G H I J A)
        true
      )
      (MAIN K L M N O P Q R)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) ) 
    (=>
      (and
        (MAIN A B C D E F G H)
        (not H)
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
