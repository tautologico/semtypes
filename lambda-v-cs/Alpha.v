Require Import LambdaSyntax.
Require Import DBVar. 

(** Convert term [t], considered the body of an abstraction bound,
 to use variable [v2] in place of [v1]. *)

Fixpoint alpha_convert {A : Type} (t : term A) (v1 v2 : var) : term A := 
  match t with
    | Const _ => t
    | Var x => if beq_nat x v1 then Var v2 else t
    | Abs x body => if beq_nat x v1 then t else Abs x (alpha_convert body v1 v2)
    | App m n => App (alpha_convert m v1 v2) (alpha_convert n v1 v2)
  end. 

Example alpha_convert1 : alpha_convert nat_term_3 X Y = (Var Y). 
Proof. reflexivity. Qed. 

(** We define alpha equivalence (equivalence of terms up to names of bound variables) 
    by translating terms to our variation of De Bruijn representation and checking if 
    they're equal. *)

Definition alpha_equiv {A : Type} (t1 t2 : term A) : Prop := 
  convert_to_dbv t1 = convert_to_dbv t2. 

(** printing == %\ensuremath{\equiv}% *)

(** If [t1] and [t2] are terms, we note equivalence up to names of bound 
 variables as [t1 == t2]. This is an equivalence relation. *)

(* begin hide *)
Notation "t1 == t2" := (alpha_equiv t1 t2) (at level 20, no associativity). 
(* end hide *)

Theorem alpha_equiv_refl : forall (A : Type) (t : term A), t == t. 
Proof. 
  reflexivity. 
Qed. 

Theorem alpha_equiv_sym : forall (A : Type) (t1 t2 : term A), 
                            t1 == t2 -> t2 == t1. 
Proof. 
  intros A t1 t2 H12; unfold alpha_equiv in H12; apply eq_sym in H12; assumption. 
Qed. 

Theorem alpha_equiv_trans : forall (A : Type) (t1 t2 t3 : term A),
                              t1 == t2 -> t2 == t3 -> t1 == t3. 
Proof. 
  intros A t1 t2 t3 H12 H23. 
  unfold alpha_equiv in H12. unfold alpha_equiv in H23. rewrite H23 in H12. assumption. 
Qed. 

Theorem equal_alpha_eq : forall (A : Type) (t1 t2 : term A),
                                t1 = t2 -> t1 == t2. 
Proof. 
  intros A t1 t2 Heq. rewrite Heq. apply alpha_equiv_refl. 
Qed. 

