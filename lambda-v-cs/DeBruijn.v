
Require Import List.
Require Import LambdaSyntax.

(** Representation using DeBruijn indices. *)

Set Implicit Arguments. 

Inductive db_term (A : Type) : Type := 
| db_const : A -> db_term A
| db_var : var -> db_term A
| db_app : db_term A -> db_term A -> db_term A
| db_abs : db_term A -> db_term A.

Arguments db_var [A] _. 

Notation "\\ M" := (db_abs M) (at level 60, right associativity). 
Notation "M $$ N" := (db_app M N) (at level 60, right associativity). 
Notation "[ v ]" := (db_var v) (at level 40, no associativity). 
Notation "[ v # T ]" := (db_var (A := T) v) (at level 40, no associativity). 

Definition binders := list var.

Fixpoint find_var_in_binders (bs : binders) (v : var) (i : nat) : option nat := 
  match bs with
    | nil => None
    | v' :: bs' => if beq_nat v v' then Some i 
                   else find_var_in_binders bs' v (S i)
  end.

Definition map_var (v : var) (lv : nat) (bs : binders) : var := 
  match find_var_in_binders bs v 0 with
    | None => v + lv
    | Some i => i
  end. 

Fixpoint term_to_db_aux {A : Type} (t : term A) (bs : binders) (lv : nat) : db_term A := 
  match t with
    | Const a => db_const a 
    | Var v => db_var (map_var v lv bs)
    | App m n => db_app (term_to_db_aux m bs lv) (term_to_db_aux n bs lv)
    | Abs x body => db_abs (term_to_db_aux body (x::bs) (S lv))
  end.

Definition term_to_db {A : Type} (t : term A) : db_term A := 
  term_to_db_aux t nil 0.

Example term_to_db_ex1 : 
  term_to_db (\X # nat --> Var X) = (\\ (db_var 0)).
Proof. reflexivity. Qed. 

Example term_to_db_ex2 : 
  term_to_db (\X # nat --> (Var X) $ (Var Y)) = 
  \\ ((db_var 0) $$ (db_var 2)).
Proof. reflexivity. Qed. 

Example term_to_db_ex3 : 
  term_to_db (\Y # nat --> Var Y) = (\\ (db_var 0)).
Proof. reflexivity. Qed. 

Example term_to_db_ex4 : 
  term_to_db (\Y # nat --> (Var Y) $ (Var Z)) = 
  (\\ ((db_var 0) $$ (db_var (S Z)))).
Proof. reflexivity. Qed. 

Example term_to_db_ex5 : 
  term_to_db ((Var 4) $ ((Var 3) $ (Var 2))) =
  ((db_var 4) $$ ((db_var 3) $$ [2 # nat])).
Proof. reflexivity. Qed. 

Example term_to_db_ex6 : 
  term_to_db (\ 7 --> (Var 3) $ (Var 7)) = 
  (\\ [4 # nat] $$ [0]).
Proof. reflexivity. Qed. 

Example term_to_db_ex7 : 
  term_to_db (\ 7 --> (\ 8 --> (Var 4))) = 
  (\\ (\\ [6 # nat])). 
Proof. reflexivity. Qed. 

Definition db_var_to_var (n i v : var) : var := 
  if leb (S n) i then (v + i - n) else (n - i). 

Fixpoint db_to_term_aux {A : Type} (dt : db_term A) (i v : var) : term A := 
  match dt with
    | db_const a => Const a
    | db_var n => Var (db_var_to_var n i v)
    | db_app m n => App (db_to_term_aux m i v) (db_to_term_aux n i v)
    | db_abs body => Abs (v + (S i)) (db_to_term_aux body (S i) v)
  end. 

Fixpoint max_free_var {A : Type} (dt : db_term A) (lv : nat) : nat := 
  match dt with
    | db_const _ => 0
    | db_var v => (v - lv)
    | db_app m n => max (max_free_var m lv) (max_free_var n lv) 
    | db_abs body => max_free_var body (S lv)
  end. 

Definition db_to_term {A : Type} (dt : db_term A) : term A := 
  db_to_term_aux dt 0 (max_free_var dt 0).

Example dbv_to_term_1 : db_to_term (\\ [0 # nat]) = (Abs 1 (Var 1)).
Proof. reflexivity. Qed. 

Example dbv_to_term_2 : 
  db_to_term (\\ ([0 # nat] $$ [2])) = 
  (\2 --> (Var 2) $ (Var 1)). 
Proof. reflexivity. Qed. 


