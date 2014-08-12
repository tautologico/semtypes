
Require Import List. 
Require Import LambdaSyntax. 

(** A representation that's a variation of De Bruijn indices, avoiding the 
  shifting of free variables. Shifting is only used to preserve the identity 
  of free variables when under binders, but here we distinguish free and 
  bound variables in a term explicitly. *)

Set Implicit Arguments. 

Inductive dbv_var : Set := 
| Free : nat -> dbv_var
| Bound : nat -> dbv_var. 

Inductive dbv_term (A : Type) : Type := 
| DBV_const : A -> dbv_term A
| DBV_var : dbv_var -> dbv_term A
| DBV_abs : dbv_term A -> dbv_term A
| DBV_app : dbv_term A -> dbv_term A -> dbv_term A.

Notation "\\ M" := (DBV_abs M) (at level 60, right associativity). 
Notation "M $$ N" := (DBV_app M N) (at level 60, right associativity). 
Notation "[ v ]" := (DBV_var (Free v)) (at level 40, no associativity). 
Notation "[ v # T ]" := (DBV_var T (Free v)) (at level 40, no associativity). 
Notation "[| v |]" := (DBV_var (Bound v)) (at level 40, no associativity). 
Notation "[| v # T |]" := (DBV_var T (Bound v)) (at level 40, no associativity). 

Definition binders := list var.

Fixpoint find_var_in_binders (bs : binders) (v : var) (i : nat) : option nat := 
  match bs with
    | nil => None
    | v' :: bs' => if beq_nat v v' then Some i 
                   else find_var_in_binders bs' v (S i)
  end.

Definition var_to_dbv_var (v : var) (bs : binders) : dbv_var := 
  match find_var_in_binders bs v 0 with
    | None => Free v
    | Some i => Bound i
  end. 

Fixpoint term_to_dbv_aux {A : Type} (t : term A) (bs : binders) : dbv_term A := 
  match t with
    | Const a => DBV_const a
    | Var v => DBV_var A (var_to_dbv_var v bs)
    | Abs x body => DBV_abs (term_to_dbv_aux body (x :: bs))
    | App m n => DBV_app (term_to_dbv_aux m bs) (term_to_dbv_aux n bs)
  end. 

Definition term_to_dbv {A : Type} (t : term A) : dbv_term A := 
  term_to_dbv_aux t nil. 

Example dbv_conv_ex1 : 
  term_to_dbv (\X # nat --> Var X) = (\\ (DBV_var nat (Bound 0))).
Proof. reflexivity. Qed. 

Example dbv_conv_ex2 : 
  term_to_dbv (\X # nat --> (Var X) $ (Var Y)) = 
  \\ ((DBV_var nat (Bound 0)) $$ (DBV_var nat (Free 1))).
Proof. reflexivity. Qed. 

Example dbv_conv_ex3 : 
  term_to_dbv (\Y # nat --> Var Y) = (DBV_abs (DBV_var nat (Bound 0))).
Proof. reflexivity. Qed. 

Example dbv_conv_ex4 : 
  term_to_dbv (\Y # nat --> (Var Y) $ (Var Z)) = 
  (DBV_abs (DBV_app (DBV_var nat (Bound 0)) (DBV_var nat (Free Z)))).
Proof. reflexivity. Qed. 

Fixpoint dbv_var_to_var (ix : nat) (bs : binders) : var :=
  match ix, bs with
    | 0, v :: bs' => v
    | S i, v :: bs' => dbv_var_to_var i bs'
    | _, _ => 666
  end. 

Fixpoint dbv_to_term_aux {A : Type} (dt : dbv_term A) (bs : binders) (v : var) : term A := 
  match dt with
    | DBV_const c => Const c
    | DBV_var (Free n) => Var n
    | DBV_var (Bound n) => Var (dbv_var_to_var n bs)
    | DBV_abs body => Abs v (dbv_to_term_aux body (v :: bs) (S v))
    | DBV_app m n => App (dbv_to_term_aux m bs v) (dbv_to_term_aux n bs v)
  end. 

Fixpoint max_free_var {A : Type} (dt : dbv_term A) : nat := 
  match dt with
    | DBV_const _ => 0
    | DBV_var (Bound _) => 0
    | DBV_var (Free n) => n
    | DBV_abs body => max_free_var body
    | DBV_app m n => max (max_free_var m) (max_free_var n)
  end. 

Definition dbv_to_term {A : Type} (dt : dbv_term A) : term A := 
  dbv_to_term_aux dt nil (S (max_free_var dt)). 

Example dbv_to_term_1 : dbv_to_term (\\ (DBV_var nat (Bound 0))) = (Abs 1 (Var 1)).
Proof. reflexivity. Qed. 

Example dbv_to_term_2 : 
  dbv_to_term (\\ ((DBV_var nat (Bound 0)) $$ (DBV_var nat (Free Z)))) = 
  (\3 --> (Var 3) $ (Var Z)). 
Proof. reflexivity. Qed. 

Example dbv_to_term_3 : 
  dbv_to_term (\\ (\\ ((DBV_var nat (Bound 0)) $$ (DBV_var nat (Bound 1))))) =
  \1 --> \2 --> Var 2 $ Var 1. 
Proof. reflexivity. Qed. 

(** Verifying if a DBV term is well-formed.  *)

Fixpoint well_formed_aux {A : Type} (dt : dbv_term A) (b : nat) : bool := 
  match dt with
    | DBV_const _ => true
    | DBV_var (Free _) => true
    | DBV_var (Bound n) => leb (S n) b
    | DBV_abs body => well_formed_aux body (S b)
    | DBV_app m n => andb (well_formed_aux m b) (well_formed_aux n b)
  end. 

Lemma well_formed_var : forall (A : Type) (v n : nat),
                          well_formed_aux (DBV_var A (Bound v)) n = true -> 
                          v < n.
Proof. 
  intros A v n H. 
  simpl in H. destruct n. inversion H. apply le_lt_n_Sm. apply leb_complete. assumption. 
Qed. 
