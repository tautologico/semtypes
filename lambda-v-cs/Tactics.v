Ltac contra_equality := 
  repeat match goal with
    | [ H1 : ?X = ?Y, H2 : ?X <> ?Y |- _ ] => specialize (H2 H1); apply False_rec; exact H2
    | [ H1 : ?X = ?Y, H2 : ?Y <> ?X |- _ ] => apply eq_sym in H1 
  end.

