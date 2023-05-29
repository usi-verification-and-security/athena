; ./synth/nay-horn/./CONST_example3_000.smt2
(set-logic HORN)

(declare-fun |Start| ( Int ) Bool)
(declare-fun |StartBool| ( Bool ) Bool)

(assert
  (forall ( (v_0 Int) ) 
    (=>
      (and
        (and true (= 0 v_0))
      )
      (Start v_0)
    )
  )
)
(assert
  (forall ( (v_0 Int) ) 
    (=>
      (and
        (and true (= 0 v_0))
      )
      (Start v_0)
    )
  )
)
(assert
  (forall ( (v_0 Int) ) 
    (=>
      (and
        (and true (= 0 v_0))
      )
      (Start v_0)
    )
  )
)
(assert
  (forall ( (v_0 Int) ) 
    (=>
      (and
        (and true (= 10 v_0))
      )
      (Start v_0)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (Start C)
        (Start B)
        (= A (+ B C))
      )
      (Start A)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Int) ) 
    (=>
      (and
        (Start D)
        (StartBool B)
        (Start C)
        (= A (ite B C D))
      )
      (Start A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) ) 
    (=>
      (and
        (StartBool B)
        (not (= B A))
      )
      (StartBool A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) ) 
    (=>
      (and
        (StartBool B)
        (= A B)
      )
      (StartBool A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Int) (C Int) ) 
    (=>
      (and
        (Start C)
        (Start B)
        (= A (>= B C))
      )
      (StartBool A)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) ) 
    (=>
      (and
        (StartBool C)
        (StartBool B)
        (= A (and C B))
      )
      (StartBool A)
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (and
        (Start A)
        (= A 9)
      )
      false
    )
  )
)

(check-sat)
(exit)
