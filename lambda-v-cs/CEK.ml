(* 
 * CEK.ml
 * Implementation of a CEK machine for a specific language
 *
 * Andrei de A. Formiga - 2014-08-20
 *
 *)

(* The lambda term syntax *)
type intconst = Num of int | Fun of string * (int -> intconst)

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
  | Stuck

(* the transition function *)
let rec cek_trans s = 
  match s with
  | STerm (Const c, env, k) -> SRet (k, Val c)
  | STerm (Var v, env, k) -> SRet (k, lookup env v)
  | STerm (Abs (v, body), env, k) -> SRet (k, Closure (Abs (v, body), env))
  | STerm (App (m, n), env, k) -> STerm (m, env, PArg (k, n, env))
  | SRet (PArg (k, n, env), v) -> STerm (n, env, PFun (k, v))
  | SRet (PFun (k, Closure (Abs (x, m), env)), v) -> STerm (m, extend env x v, k)
  | SRet (PFun (k, Val (Fun (_, f))), Val (Num a)) -> SRet (k, Val (f a))
  | _ -> Stuck

(* example functions *) 
let succ = Fun ("1+", fun x -> Num (x + 1))
let pred = Fun ("1-", fun x -> Num (x - 1))

(* example terms *)
let ex1 = Abs (0, App (Const succ, App (Const succ, Var 0)))
let ex2 = App (ex1, Const (Num 0))
let ex3 = App (Const (Num 0), Const succ)   (* gets stuck *)

(* printing functions to display machine states in the style of 
   Felleisen's dissertation *)
let show_var v = Printf.sprintf "V%d" v

let show_intconst c = 
  match c with
    Num n -> string_of_int n
  | Fun (name, f) -> name

let rec show_term t = 
  match t with
  | Const c -> show_intconst c
  | Var v -> show_var v 
  | Abs (v, body) -> Printf.sprintf "\\%s.%s" (show_var v) (show_term body)
  | App (m, n) -> Printf.sprintf "(%s %s)" (show_term m) (show_term n)

let rec show_value v = 
  match v with
  | Val c -> show_intconst c
  | Closure (t, env) -> Printf.sprintf "[%s, %s]" (show_term t) (show_env env)
and show_env env = 
  let rec print_loop l = 
    match l with
    | [] -> ""
    | (vr, vl) :: [] -> Printf.sprintf "(%s, %s)" (show_var vr) (show_value vl)
    | (vr, vl) :: l' -> Printf.sprintf "(%s, %s), %s" (show_var vr) (show_value vl) (print_loop l')
  in
  Printf.sprintf "{%s}" (print_loop env)

let rec show_pcont k = 
  match k with
  | PStop -> "(stop)"
  | PFun (k', v) -> Printf.sprintf "(%s fun %s)" (show_pcont k') (show_value v)
  | PArg (k', t, env) -> 
     Printf.sprintf "(%s arg %s %s)" (show_pcont k') (show_term t) (show_env env)

let show_retcont k v = 
  Printf.sprintf "(%s ret %s)" (show_pcont k) (show_value v)

let show_state s = 
  match s with
  | Stuck -> "STUCK"
  | SRet (k, v) -> Printf.sprintf "(++, [], %s)" (show_retcont k v)
  | STerm (t, env, k) -> 
     Printf.sprintf "(%s, %s, %s)" (show_term t) (show_pcont k) (show_env env)

(* Execution and evaluation *)

type exec_result = ExStuck | ExVal of value 

let exec t = 
  let rec exec_loop s = 
    match s with 
    | Stuck -> ExStuck
    | SRet (PStop, v) -> ExVal v
    | _ -> exec_loop (cek_trans s)
  in 
  exec_loop (STerm (t, [], PStop))

let exec_trace t = 
  let rec exec_loop s =     
    let () = print_endline @@ show_state s in
    match (cek_trans s) with
    | Stuck -> print_endline "STUCK"
    | SRet (PStop, v) -> Printf.printf "*** Final value: %s\n" (show_value v)
    | s' -> exec_loop s'
  in    
  exec_loop (STerm (t, [], PStop))

let rec unload_closure t env = 
  match t with
  | Const _ -> t
  | Var v -> if List.mem_assoc v env then unload @@ List.assoc v env else Var v
  | Abs (x, body) -> Abs (x, unload_closure body env)
  | App (m, n) -> App (unload_closure m env, unload_closure n env)
and unload v = 
  match v with
  | Val v -> Const v
  | Closure (t, env) -> unload_closure t env

let eval_cek t = 
  match exec t with
  | ExStuck -> failwith "Evaluation of an ill-formed expression"
  | ExVal v -> unload v

let eval_show t = 
  t |> eval_cek |> show_term
