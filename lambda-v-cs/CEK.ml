(* 
 * CEK.ml
 * Implementation of a CEK machine for a specific language
 *
 * Andrei de A. Formiga - 2014-08-20
 *
 *)

(* The lambda term syntax *)
type intconst = Num of int | Fun of (int -> intconst)

type var = int

type term = 
  | Const of intconst 
  | Var of var
  | Abs of var * term
  | App of term * term

type control = CntStop | CntTerm of term

type value = Val of intconst | Closure of term * env
and env = (var * value) list

let lookup e v = 
  List.assoc v e

let extend e vr vl = 
  (vr, vl) :: e

type pcont = 
  | PStop
  | PFun of pcont * value
  | PArg of pcont * term * env

type retcont = pcont * value

type cont = PCont of pcont | RetCont of retcont

type state = 
  | SRet of retcont
  | STerm of term * env * pcont

(* the transition function *)
let rec cek_trans s = 
  match s with
  | STerm (Const c, env, pc) -> SRet (pc, Val c)
  | STerm (Var v, env, pc) -> SRet (pc, lookup env v)
  | STerm (Abs (v, body), env, pc) -> SRet (pc, Closure (Abs (v, body), env))
  | STerm (App (m, n), env, pc) -> STerm (m, env, PArg (pc, n, env))
  | SRet (PArg (pc, n, env), v) -> STerm (n, env, PFun (pc, v))
  | SRet (PFun (pc, Closure (Abs (x, m), env)), v) -> STerm (m, extend env x v, pc)
  | SRet (PFun (pc, Val (Fun f)), Val (Num a)) -> SRet (pc, Val (f a))
  | _ -> failwith "Unknown transition"

(* example functions *) 
let succ = Fun (fun x -> Num (x + 1))
let pred = Fun (fun x -> Num (x - 1))


(* example terms *)
let ex1 = Abs (0, App (Const succ, App (Const succ, Var 0)))
let ex2 = App (ex1, Const (Num 0))


