
Require Import LambdaSyntax. 

(** A representation that's a variation of De Bruijn indices, avoiding the 
  shifting of free variables. Shifting is only used to preserve the identity 
  of free variables when under binders, but here we distinguish free and 
  bound variables in a term explicitly. *)

Inductive dbv_var : Set := 
| Free : nat -> dbv_var
| Bound : nat -> dbv_var. 

Inductive dbv_term (A : Type) : Type := 
| DBV_const : A -> dbv_term A
| DBV_var : dbv_var -> dbv_term A
| DBV_abs : dbv_term A -> dbv_term A
| DBV_app : dbv_term A -> dbv_term A -> dbv_term A.

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

Fixpoint convert_to_dbv_aux {A : Type} (t : term A) (bs : binders) : dbv_term A := 
  match t with
    | Const a => DBV_const a
    | Var v => DBV_var A (var_to_dbv_var v bs)
    | Abs x body => DBV_abs (convert_to_dbv_aux body (x :: bs))
    | App m n => DBV_app (convert_to_dbv_aux m bs) (convert_to_dbv_aux n bs)
  end. 

Definition convert_to_dbv {A : Type} (t : term A) : dbv_term A := 
  convert_to_dbv_aux t nil. 

Example dbv_conv_ex1 : 
  convert_to_dbv (\X # nat --> Var X) = (DBV_abs (DBV_var nat (Bound 0))).
Proof. reflexivity. Qed. 

Example dbv_conv_ex2 : 
  convert_to_dbv (\X # nat --> (Var X) $ (Var Y)) = 
  (DBV_abs (DBV_app (DBV_var nat (Bound 0)) (DBV_var nat (Free 1)))).
Proof. reflexivity. Qed. 

Example dbv_conv_ex3 : 
  convert_to_dbv (\Y # nat --> Var Y) = (DBV_abs (DBV_var nat (Bound 0))).
Proof. reflexivity. Qed. 

Example dbv_conv_ex4 : 
  convert_to_dbv (\Y # nat --> (Var Y) $ (Var Z)) = 
  (DBV_abs (DBV_app (DBV_var nat (Bound 0)) (DBV_var nat (Free Z)))).
Proof. reflexivity. Qed. 

