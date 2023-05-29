; ./sv-comp/./2015-05-26/LIA/Eldarica/RECUR/countZero.nts_000.smt2
(set-logic HORN)

(declare-fun |countZero_q6| ( Int Int Int Int Int Int ) Bool)
(declare-fun |countZero_q5| ( Int Int Int Int Int Int ) Bool)
(declare-fun |main_q1| ( Int Int Int Int ) Bool)
(declare-fun |countZero_q1| ( Int Int Int Int Int Int ) Bool)
(declare-fun |countZero_q0| ( Int Int Int Int Int Int ) Bool)
(declare-fun |main_q0| ( Int Int Int Int ) Bool)
(declare-fun |main_q2| ( Int Int Int Int ) Bool)
(declare-fun |countZero_q4| ( Int Int Int Int Int Int ) Bool)
(declare-fun |countZero_q3| ( Int Int Int Int Int Int ) Bool)
(declare-fun |countZero_q2| ( Int Int Int Int Int Int ) Bool)
(declare-fun |countZero_q7| ( Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (main_q0 A B E F)
        (not (<= D 0))
      )
      (main_q1 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (and (= A C) (= B D))
      )
      (main_q0 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (countZero_q6 A E B F G H)
        (and (= H D) (= G I) (= C 1))
      )
      (countZero_q7 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (countZero_q4 A E B F G H)
        (and (= H D) (= G I) (= C (+ 1 G)))
      )
      (countZero_q7 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (countZero_q2 A B C G H I)
        (and (= I F) (= H E) (not (= (mod I 10) 0)))
      )
      (countZero_q5 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (countZero_q2 A B C G H I)
        (and (= I F) (= H E) (= G D) (= (mod I 10) 0))
      )
      (countZero_q3 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (countZero_q1 A E B F G H)
        (and (= H D) (= G I) (= C 0))
      )
      (countZero_q7 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (countZero_q0 A B C G H I)
        (and (= H E) (= G D) (or (= I 0) (= I 10)) (= I F))
      )
      (countZero_q6 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (countZero_q0 A B C G H I)
        (and (= H E) (= G D) (not (<= I 10)) (= I F))
      )
      (countZero_q2 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (countZero_q0 A B C G H I)
        (and (= I F) (= H E) (= G D) (not (<= 10 I)) (not (= I 0)))
      )
      (countZero_q1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) ) 
    (=>
      (and
        (countZero_q3 A B C G H I)
        (countZero_q7 K J L M)
        (and (= I F) (= L E) (= J (div I 10)) (= G D))
      )
      (countZero_q4 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (countZero_q3 G H I J K L)
        (and (= C F) (= A D) (= C (div L 10)))
      )
      (countZero_q0 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) ) 
    (=>
      (and
        (countZero_q5 A E B F G H)
        (countZero_q7 J I K L)
        (and (= I (div H 10)) (= H D) (= K C) (= G M))
      )
      (countZero_q7 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (countZero_q5 G H I J K L)
        (and (= C F) (= A D) (= C (div L 10)))
      )
      (countZero_q0 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (main_q1 A B E F)
        (countZero_q7 H G I J)
        (and (= I C) (= G F) (= F D))
      )
      (main_q2 A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (main_q1 G H I J)
        (and (= C F) (= C J) (= A D))
      )
      (countZero_q0 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (main_q2 A B C D)
        (not (<= C D))
      )
      false
    )
  )
)

(check-sat)
(exit)
