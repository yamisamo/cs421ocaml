open List
open Minijavaast
open Mp7common

(* MP7 interpreter - no objects, arrays, or floats; just one class;
   limited set of statements.  See MP6 write-up for details. *)

(* Utility functions *)

let rec asgn (id:id) (v:stackvalue) (env:environment) : environment =
  match env with
     [] -> raise (TypeError ("Assignment to unbound variable " ^ id))
  | (id1,v1) :: t -> if id = id1 then (id,v) :: t
                     else (id1,v1) :: asgn id v t

let rec binds (id:id) (env:environment) : bool =
  match env with
    [] -> false
  | (id', _)::t -> id=id' || binds id t

let rec fetch (id:id) (env:environment) : stackvalue =
  match env with
    [] -> raise (TypeError ("Unbound variable: "^id))
  | (id', v)::t -> if id=id' then v else fetch id t

let rec mklist (i:int) (v:stackvalue) : stackvalue list =
       if i=0 then [] else v :: mklist (i-1) v

let rec zip (lis1:id list) (lis2:stackvalue list) : environment =
  match (lis1, lis2) with
    ([], []) -> [] | (h1::t1, h2::t2) -> (h1,h2) :: zip t1 t2
  | _ -> raise (TypeError ("Mismatched formal and actual param lists"))

let zipscalar (lis:id list) (v:stackvalue) : environment =
                                zip lis (mklist (length lis) v)

let rec varnames (varlis:var_decl list) : id list =
   match varlis with
     [] -> [] | (Var(_, s))::t -> s :: varnames t

let getMethodInClass (id:id) (Class(_, _, _, methlis)) : method_decl =
  let rec aux methlis = match methlis with
      [] -> raise (TypeError ("No such method: "^id))
    | (Method(_, m, _, _, _, _) as themethod) :: t ->
        if id=m then themethod else aux t
  in aux methlis

let extend (st:store) (hval:heapvalue) : store = st @ [hval]

let storefetch (st:store) (loc:int) : heapvalue = List.nth st loc

let asgn_fld (obj:heapvalue) (id:varname) (sv:stackvalue) : heapvalue =
  let Object(c,flds) = obj
  in Object(c, asgn id sv flds)

let rec replace_nth i x lis = match (i, lis) with
    (0, _::t) -> x :: t
  | (n, h::t) -> h :: replace_nth (n-1) x t

let asgn_sto (sto:store) (loc:int) (obj:heapvalue) =
  replace_nth loc obj sto;;

let getClass (c:id) (Program classlis) : class_decl =
  let rec aux classlis = match classlis with
      [] -> raise (TypeError ("No such class: "^c))
    | (Class(c', _, _, _) as theclass) :: t ->
          if c=c' then theclass else aux t
  in aux classlis

(* Note: modify the following two helper functions to support inheritance *)

let getMethod (id:id) (c:id) (prog:program) : method_decl =
     getMethodInClass id (getClass c prog)

let fields (c:id) (prog:program) : string list =
  let rec aux flds = match flds with
      [] -> []
    | (_, Var(_,id))::t -> id :: aux t
  in let Class(_,_,flds,_) = getClass c prog
     in aux flds


(* START HERE *)

let applyOp (bop:binary_operation)
            (v1:stackvalue) (v2:stackvalue) : stackvalue =
    match (bop,v1,v2) with 
  (*Plus, Minus, Mult,Div,lessThan,eq*)
    (Plus,IntV i1, IntV i2) -> IntV(i1+i2)
    |(Plus,StringV s1, _) -> StringV(s1^string_of_value v2)
    |(Plus,_,StringV s2) -> StringV(string_of_value v1^s2)
    |(Minus, IntV i1, IntV i2) -> IntV(i1-i2)
    |(Multiplication,IntV i1, IntV i2) -> IntV(i1*i2)
    |(Division,IntV i1, IntV i2) -> 
      if(i2 = 0) then raise (RuntimeError("DivisionByZero"))
      else IntV(i1/i2)
    |(LessThan, IntV i1, IntV i2) -> BoolV(i1<i2)
    |(GreaterThan, IntV i1, IntV i2) -> BoolV(i1>i2)
    |(Equal, StringV s1, StringV s2) -> BoolV(s1=s2)
    |(Equal, IntV i1, IntV i2) -> BoolV(i1=i2)
    |(Equal, BoolV b1, BoolV b2) -> BoolV(b1=b2)
    |(Equal, NullV, NullV) -> BoolV(true)
    |(Equal, NullV, _) -> BoolV(false)
    |(Equal, _,NullV) -> BoolV(false)
    |_-> raise (TypeError("Everything else isn't implemented"));;
  

(* Main interpreter code *)

let rec eval (e:exp) ((env,sto) as sigma:state) (prog:program)
       : stackvalue * store =
     match e with
       Integer i -> (IntV i,sto)
      |True -> (BoolV(true),sto)
      |False -> (BoolV(false),sto)
      |Id(id) -> if(binds id env) then fetch id env else match (storefetch sto (fetch "this" env)) with Object(_,envThis) -> if(binds id envThis) then fetch id envThis else
        raise(TypeError("Identifier not found"))
      |Not(e) -> let (val1,stoNot) = eval e sigma prog in if(val1 = BoolV(true)) then (BoolV(false),stoNot)
        else (BoolV(true),stoNot)
      |Null -> NullV
      |String(s) -> StringV(s)
      |MethodCall(e,id,elist) -> (match getMethod id prog with
        Method(_,id,args,vdec,sl,re) -> 
        evalMethodCall sl re ((zip (varnames (args)) (evallist elist sigma prog))
        @ (zipscalar (varnames (vdec)) NullV)) prog
        |_-> raise(TypeError("Method Call didn't work")))
      
      |Operation(e1,bop,e2)-> 
      (let (val1,sto1) = eval e1 sigma prog and (val2,sto2) = eval e2 (env,sto1) prog in (* Test the short circuit of and and ors*)
        match bop with 
          And -> (match (val1,val2) with 
                    BoolV(_),BoolV(_)-> if(val1 = BoolV(true)) 
                      then (val2,sto2) else (val1,sto1) 
                    |_,_ -> raise(TypeError("And evals not boolean")))
          |Or -> (match (ev1,ev2) with 
                    BoolV(_),BoolV(_)-> if(val1 = BoolV(true)) then (val1,sto1) 
                      else (val2,sto2)
                    |_,_ -> raise(TypeError("Or evals not boolean")))
          |Equal -> ((applyOp bop (val1) (val2)),sto2)
          |LessThan -> ((applyOp bop (val1) (val2)),sto2)
          |LessThanEq -> 
            if(applyOp LessThan (val1) (val2) = BoolV(true)) then (BoolV(true),sto2)
            else ((applyOp Equal (val1) (val2)),sto2)
          |GreaterThan -> ((applyOp bop (val1) (val2)),sto2)
          |GreaterThanEq -> 
            if(applyOp GreaterThan (val1) (val2) = BoolV(true)) then (BoolV(true),sto2)
            else ((applyOp Equal (val1) (val2)),sto2)
          |Plus -> ((applyOp bop (val1) (val2)),sto2)
          |Minus -> ((applyOp bop (val1) (val2)),sto2)
          |Multiplication -> ((applyOp bop (val1) (val2)),sto2)
          |Division -> ((applyOp bop (val1) (val2)),sto2)
          |_-> raise(TypeError("Operation not implemented")))
     | _ -> raise (NotImplemented "eval")

and evallist (el:exp list) ((env,sto) as sigma:state) (prog:program)
          : stackvalue list * store = 
    match el with
    h::tt -> let(nVal,nSto) = (eval h sigma prog) and (tVal,tSto) = (eval tt (nVal,nSto) prog) in ((nVal::tVal),tSto)
    |[] -> ([],sto)

and evalMethodCall (stms:statement list) (retval:exp) (sigma:state)
                 (prog:program) : stackvalue * store =
  eval retval (execstmtlis stms sigma prog) prog

and execstmt (s:statement) ((env,sto) as sigma:state) (prog:program) : state =
    match s with 
  If(e,s1,s2) -> (match (eval e sigma prog) with 
                    (BoolV(b),nSto) -> if(b) then execstmt s1 (env,nSto) prog 
                                  else execstmt s2 (env,nSto) prog
                    |_-> raise(TypeError("Eval didn't return correct type")))
  |Assignment(id,e) -> let (val1,nSto) = (eval e sigma prog) in if(binds id sigma) then (asgn id val1 env) else let obj = (storefetch sto (fetch "this" env)) in
      match obj with Object(_,envThis) -> if(binds id envThis) then asgn_sto nSto (fetch "this" env) (asgn_fld obj id val1)
	  else raise(TypeError("Variable not included"))
  |Block(sl) -> execstmtlis sl sigma prog

and execstmtlis (sl:statement list) (sigma:state) (prog:program) : state =
    match sl with 
    h::tt -> execstmtlis tt (execstmt h sigma prog) prog
    |[] -> sigma;;

let run_with_args (Program(Class(cname,_,_,_) :: _) as prog)
                  (args:exp list) : string =
   let env = [("this", Location 0)]
   and sto = [Object(cname, [])]
   in let (v,_) = eval (MethodCall(Id "this", "main", args))
                       (env,sto) prog
      in string_of_stackval v

let run (prog:program) : string = run_with_args prog []

let eval_exp (prog:program) : string =
   let Program [Class(_, _, _, [meth])] = prog
   in let Method(_,_,_,_,_,retval) = meth
      in string_of_stackval (fst (eval retval ([],[]) prog))

