exception UndefSemantics

type program = exp
and exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | READ
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
  | CALLREF of exp * var
  | SET of var * exp
  | SEQ of exp * exp
  | BEGIN of exp
and var = string

type value = 
    Int of int 
  | Bool of bool 
  | Closure of var * exp * env 
  | RecClosure of var * var * exp * env
and env = var -> loc
and loc = int
and mem = loc -> value

(*********************************)
(* implementation of environment *)
(*********************************)
(* empty env *)
let empty_env = fun x -> raise (Failure "Environment is empty")
(* extend the environment e with the binding (x,v), where x is a varaible and v is a value *)
let extend_env (x,v) e = fun y -> if x = y then v else (e y)
(* look up the environment e for the variable x *)
let apply_env e x = e x

(*********************************)
(* implementation of memory      *)
(*********************************)
let empty_mem = fun _ -> raise (Failure "Memory is empty")
let extend_mem (l,v) m = fun y -> if l = y then v else (m y)
let apply_mem m l = m l

(* NOTE: you don't need to understand how env and mem work *)

let counter = ref 0

(* calling 'new_location' produces a fresh memory location *)
let new_location () = counter:=!counter+1;!counter

let value2str v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | Closure (x,e,env) -> "Closure "
  | RecClosure (f,x,e,env) -> "RecClosure "^f

(* TODO: Implement this function *)
let rec eval : exp -> env -> mem -> value * mem
=fun exp env mem -> 
  match exp with
  | CONST n -> (Int n, mem)

  | VAR x -> (mem (env x) , mem)

  | ADD (e1, e2) -> let t1 = eval e1 env mem in
                  begin 
                    match t1 with
                    | (n1, s1) -> let tmp1 = n1 in 
                            let t2 = eval e2 env s1 in
                                        begin
                                          match t2 with
                                          | (n2, s2) -> let tmp2 = n2 in
                                                    begin
                                                      match (tmp1, tmp2) with
                                                          | (Int a1, Int b1) -> (Int (a1 + b1), s2)
                                                          | _ -> raise (Failure "Unimplemented") 
                                                    end
                                        end
                  end

  | SUB (e1, e2) -> let t1 = eval e1 env mem in
                  begin 
                    match t1 with
                    | (n1, s1) -> let tmp1 = n1 in 
                            let t2 = eval e2 env s1 in
                                        begin
                                          match t2 with
                                          | (n2, s2) -> let tmp2 = n2 in
                                                    begin
                                                      match (tmp1, tmp2) with
                                                          | (Int a1, Int b1) -> (Int (a1 - b1), s2)
                                                          | _ -> raise (Failure "Unimplemented") 
                                                    end
                                        end
                  end
  | MUL (e1, e2) -> let t1 = eval e1 env mem in
                  begin 
                    match t1 with
                    | (n1, s1) -> let tmp1 = n1 in 
                            let t2 = eval e2 env s1 in
                                        begin
                                          match t2 with
                                          | (n2, s2) -> let tmp2 = n2 in
                                                    begin
                                                      match (tmp1, tmp2) with
                                                          | (Int a1, Int b1) -> (Int (a1 * b1), s2)
                                                          | _ -> raise (Failure "Unimplemented") 
                                                    end
                                        end
                  end

  | DIV (e1, e2) -> let t1 = eval e1 env mem in
                  begin 
                    match t1 with
                    | (n1, s1) -> let tmp1 = n1 in 
                            let t2 = eval e2 env s1 in
                                        begin
                                          match t2 with
                                          | (n2, s2) -> let tmp2 = n2 in
                                                    begin
                                                      match (tmp1, tmp2) with
                                                          | (Int a1, Int b1) -> (Int (a1 / b1), s2)
                                                          | _ -> raise (Failure "Unimplemented") 
                                                    end
                                        end
                  end

  | ISZERO (e) -> let t = eval e env mem in 
                begin
                  match  t with
                  | (Int n, s1) -> if (n=0) then (Bool true, s1) else (Bool false, s1)
                  | _ -> raise UndefSemantics
                end

  | READ -> (Int  (read_int()), mem)

  | IF (e1, e2, e3) -> let t = eval e1 env mem in
                begin
                  match t with
                  | (Bool true, s1) -> let t2 = eval e2 env s1 in
                      begin
                        match t2 with
                        | (v2, s2) -> (v2, s2)
                      end
                  | (Bool false, s1) -> let t3 = eval e3 env s1 in
                      begin
                        match t3 with
                        | (v3, s3) -> (v3, s3)
                      end
                  | _->raise UndefSemantics
                end

  | LET (v, e1, e2) -> let t1 = eval e1 env mem in 
                              begin
                                match t1 with
                                |(v1, s1) -> let l = new_location() in
                                      let t2 = eval e2 (extend_env (v, l) env) (extend_mem (l, v1) s1) in
                                        begin
                                          match t2 with
                                          |(v2, s2) -> (v2,s2)
                                        end
                              end

  | LETREC(f,x,e1,e2) -> (let l = new_location() in
                          eval e2 (extend_env (f,l)env) (extend_mem(l,RecClosure(f,x,e1,env))mem))

  | PROC (v, e) -> ( Closure(v, e, env), mem )

  | CALL(e1,e2) ->let l = new_location() in 
                         let ev = eval e1 env mem in
                               (match ev with
                               |(Closure(x,e,env'),m1) -> 
                          let ev2 = eval e2 env m1 in
                                  (match ev2 with
                                  |(v,m2)-> eval e (extend_env(x, l) env') (extend_mem (l,v) m2)
                                  )   
                               |(RecClosure(f,x,e,env'),m1)->
                         let ev2 = eval e2 env m1 in
                         let l2 = new_location() in
                         let env'2 = extend_env(f,l) env' in
                             (match ev2 with
                         |(v,m2)->   
                            let em = extend_mem (l2,v) m2 in
                            eval e (extend_env(x,l2) env'2) (extend_mem (l, RecClosure(f,x,e,env'))em)
                               )
                               |_-> raise UndefSemantics
                               )

 | CALLREF(e1,y) -> let ev = eval e1 env mem in
                               (match ev with
                            
                            |(Closure(x,e,env'),m1)->
                         (eval e (extend_env(x,(apply_env env y)) env') m1)
                            |(RecClosure(f,x,e,env'),m1)->
                      (   let l = new_location() in
                   let env'2 = extend_env (f,l) env' in
                   
                eval e (extend_env(x, (apply_env env y))env'2)  (extend_mem (l,RecClosure(f,x,e,env')) m1))
                            |_-> raise UndefSemantics)
      

  | SET (var, e) -> let t = eval e env mem in
                    begin
                      match t with
                        | (v, s1) ->  (v, (extend_mem ((apply_env env var), v) s1))
                    end
  
  | SEQ (e1, e2) -> let t = eval e1 env mem in
                    begin
                      match t with
                      | (v1, s1) -> eval e2 env s1
                    end

  | BEGIN (e) -> eval e env mem

  | _ -> raise (Failure "Unimplemented")

let run : program -> value
=fun pgm -> 
  let (v,m) = eval pgm empty_env empty_mem in
    v