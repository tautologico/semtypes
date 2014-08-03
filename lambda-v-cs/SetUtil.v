(** Utility theorems to deal with sets (represented as lists) *)

Require Import List.
Require Export ListSet. 
Require Import Tactics. 

Set Implicit Arguments. 

Section theorems. 
  Variable A : Set. 
  Hypothesis Aeq_dec : forall x y : A, {x = y} + {x <> y}. 

  Lemma diff_head_in_tail_in_set : forall x y (S : set A),
                                   x <> y -> set_In x (y :: S) -> set_In x S. 
  Proof. 
    intros x y S Hneq Hin. simpl in Hin. 
    inversion Hin; [ contra_equality | assumption ]. 
  Qed. 

  Lemma remove_diff : forall x v (S : set A),
                        x <> v -> set_In x S -> set_In x (set_remove Aeq_dec v S). 
  Proof. 
    intros x v S Hneq Hin. induction S. 

    (* Case S = empty_set (nil) *) inversion Hin.  

    (* Case S = a :: S' *)
    simpl. destruct (Aeq_dec v a). 
      (* Case v = a *)
      rewrite e in Hneq. 
      apply diff_head_in_tail_in_set with (y := a); assumption. 

      (* Case v <> a *)
      simpl.
      destruct (Aeq_dec x a) as [ Eq | Neq ]. 
        (* Case x = a *) intuition. 
        (* Case x <> a *)
        right. apply IHS. apply diff_head_in_tail_in_set with (y := a); assumption. 
  Qed. 

  Lemma diff_head_not_in_tail : forall x y (S : set A),
                                  x <> y -> ~(set_In x (y :: S)) -> 
                                  ~(set_In x S). 
  Proof. 
    intros x y S Hneq Hnin.
    intro Hcontra; apply Hnin. 
    simpl. right. apply Hcontra. 
  Qed. 

  Lemma diff_head_not_tail_not_set : forall x y (S : set A),
                                       x <> y -> 
                                       ~(set_In x S) -> 
                                       ~(set_In x (y :: S)).
  Proof. 
    intros x y S Hneq Hnin. 
    intro Hcontra; apply Hnin. simpl in Hcontra.  
    inversion Hcontra; [ contra_equality |  assumption ]. 
  Qed. 

  Lemma not_in_diff_head : forall x y (S : set A),
                             ~(set_In x (y :: S)) -> 
                             x <> y. 
  Proof. 
    intros x y S Hnin Hcontra. apply Hnin. simpl. intuition.
  Qed. 


  Lemma not_in_remove_not_in_set : forall x y (S : set A),
                                     x <> y -> 
                                     ~(set_In x (set_remove Aeq_dec y S)) -> 
                                     ~(set_In x S). 
  Proof. 
    intros x y S Hneq Hnin.
    induction S. 
    (* Case S = nil *) intuition. 

    (* Case S = a :: S *)
    simpl in Hnin.  
    destruct (Aeq_dec y a) in Hnin.
      (* Case y = a *) 
      rewrite -> e in Hneq. 
      apply (diff_head_not_tail_not_set Hneq). assumption. 
      (* Case v <> a *)
      simpl. intro Hcontra; apply Hnin. simpl. inversion Hcontra. 
        (* Case a = x *) 
        left; assumption. 
        (* Case set_In x (set_remove v S) *) 
        right. apply not_in_diff_head in Hnin. apply remove_diff; assumption. 
  Qed. 

End theorems. 