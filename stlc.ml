(* this implmentation of STLC is intended to be an extension of mine ULC/Mumei implem, I heavily reuse the code *)

type typ = 
  | TypBool
  | TypFun of typ * typ 


  
type context = (int * typ) list

type term =
  | Var of int  
  | Abs of term * typ 
  | App of term * term
  | True 
  | False 
  | If of term * term * term 

exception IsNotBind
let rec lookup_cxt cxt k = match cxt with  
  | [] -> false
  | hd :: tl -> if fst(hd) = k then true else lookup_cxt tl k  

let shift_left_typing_cxt (a,b) = (a+1,b)

exception IsNotGood
(* typing rules in stlc are heavy syntax directed, then I see the typechecker as an implementation of inversion lemma *)
let rec typechecker ctx t = match t with 
  | Var(k) ->  
        (match ctx with  
          | [] -> raise IsNotBind
          | hd :: tl -> if fst(hd) = k then snd(hd) else typechecker tl t)
  | Abs(t1,typof0) ->  (* the type will be typeof0 -> T1 , where T1 stands for type of t1*)
    (TypFun (typof0,typechecker ((0,typof0)::(List.map shift_left_typing_cxt ctx)) t1))
  | App(t1,t2) -> (match typechecker ctx t1 with 
    | TypFun (dom, codom) -> if typechecker ctx t2 = dom then codom else raise IsNotGood    
    | TypBool -> raise IsNotGood
    )
  | True -> TypBool
  | False -> TypBool
  | If (t1,t2,t3) when (typechecker ctx t1 = TypBool) -> if typechecker ctx t2 = typechecker ctx t3 
    then typechecker ctx t2 
    else raise IsNotGood
  | _ -> raise IsNotGood (* the yellow lines upset me *)
  


let rec shift d c = function 
  | Var (k) -> if k < c then Var k else Var (k + d) 
  | Abs (t1,typoft1) -> Abs (shift d (c+1) t1,typoft1) 
  | App (t1,t2) -> App (shift d c t1, shift d c t2) 
  | _ -> raise IsNotGood (* the yellow lines upset me *)
  
(* wrapper to initialize the cutoff at 0, hence ease the term shifting *)
let term_shift d t = shift d 0 t 

(* substitution lying on shifting *)
let rec substitution j s = function 
  | Var (k) -> if k = j then s else Var k 
  | App (t1,t2) -> App (substitution j s t1, substitution j s t2)
  | Abs (t1,typoft1) -> Abs(substitution (j+1) (term_shift 1 s) t1,typoft1)
  | _ -> raise IsNotGood (* the yellow lines upset me *)

(* only abstraction are values *)
let is_a_value = function | Abs (t1,typoft1) -> true | _ -> false 
exception NotaValue

(* beta reduction lying on down shift, with a call by value approach *)
let rec b_step t v = if is_a_value v then 
    term_shift (-1) (substitution 0 (term_shift 1 v) t)
  else raise NotaValue   

exception NoRuleApplies
let rec eval_one_step = function  
  | App (Abs (t1,typoft1), v1) when is_a_value v1 -> b_step t1 v1 
  | App (t1,t2) when not (is_a_value t1) -> App (eval_one_step t1,t2)
  | App (v1,t2) when is_a_value v1 -> App (v1, eval_one_step t2)
  | _ -> raise NoRuleApplies 

let rec eval_multi_step t = try eval_multi_step (eval_one_step t) with | NoRuleApplies -> t 

let rec big_step = function
  | Abs (t1,typoft1) ->
      Abs (t1,typoft1)
  | App (t1, t2) ->
      let v1 = big_step t1 in
      let v2 = big_step t2 in
      (match v1 with
       | Abs (t12,typoft12) -> big_step (b_step t12 v2)
       | _ -> raise NoRuleApplies)
  | Var _ -> raise NoRuleApplies
  | _ -> raise IsNotGood (* the yellow lines upset me *)

