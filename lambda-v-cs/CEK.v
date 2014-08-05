(** * The CEK Machine *)

Require Import LambdaSyntax. 

Set Implicit Arguments. 

(** Control strings. *)

Inductive control (A : Type) : Type := 
| CTerm : term A -> control A
| CCont : control A. 

(** Values, closures and environments. *)

Inductive value (A : Type) : Type := 
| VConst : A -> value A
| VClos : term A -> env A -> value A  (* the term is an abstraction, abstraction body? *)
with env (A : Type) : Type := 
| Env : list (var * value A) -> env A. 

(** Continuations. *)

Inductive pcont (A : Type) : Type := 
| PCStop : pcont A
| PCFun : pcont A -> value A -> pcont A
| PCArg: pcont A -> term A -> env A -> pcont A. 

Definition retcont (A : Type) : Type := (pcont A * value A)%type. 

Inductive cont (A : Type) : Type := 
| PCont : pcont A -> cont A
| RetCont : retcont A -> cont A. 

(** A CEK-machine state is either a triple of the form 
    $\langle \ddagger, \emptyset, \kappa \rangle$ where $\kappa$ is a ret-continuation, 
    or a triple of the form $\langle M, \rho, \kappa \rangle$ where $M$ is a 
    $\Lambda$-term, $\rho$ is an environment that provides a meaning for all 
    variables in $M$, and $\kappa$ is a p-continuation. *)

Inductive state (A : Type) : Type := 
| SRet : pcont A -> state A
| STerm : term A -> env A -> retcont A -> state A. 
