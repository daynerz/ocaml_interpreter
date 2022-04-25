(* Grammar types *)
(* 
digit ::= 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
int ::= [−] digit {digit}
bool ::= True | False
const ::= int | bool | () 
letter ::= a...z | A...Z
name ::= letter{letter | digit | _ | ´}
const ::= ... | name
*)

type const =
  | I of int
  | B of bool 
  | U
  | N of string

type com = 
  | Push of const
  | Pop of int 
  | Trace of int 
  | Add of int
  | Sub of int
  | Mul of int
  | Div of int
  | And | Or | Not 
  | Equal 
  | Lte 
  | Local 
  | Global 
  | Lookup
  | BeginEnd of coms
  | IfElseEnd of coms * coms

and coms = com list 

type value = const

type stack = const list

(* Local and Global - (Name, Value) tuples *)
type env = (string * value) list

(* parsing util functions *)

let is_lower_case c = 'a' <= c && c <= 'z'

let is_upper_case c = 'A' <= c && c <= 'Z'

let is_alpha c = is_lower_case c || is_upper_case c

let is_digit c = '0' <= c && c <= '9'

let is_alphanum c = is_lower_case c || is_upper_case c || is_digit c

let is_blank c = String.contains " \012\n\r\t" c

let explode s = List.of_seq (String.to_seq s)

let implode ls = String.of_seq (List.to_seq ls)

let readlines (file : string) : string =
  let fp = open_in file in
  let rec loop () =
    match input_line fp with
    | s -> s ^ "\n" ^ loop ()
    | exception End_of_file -> ""
  in
  let res = loop () in
  let () = close_in fp in
  res

(* end of util functions *)

(* parser combinators *)

type 'a parser = char list -> ('a * char list) option

let parse (p : 'a parser) (s : string) : ('a * char list) option = p (explode s)

let pure (x : 'a) : 'a parser = fun ls -> Some (x, ls)
let return = pure

let fail : 'a parser = fun ls -> None

let bind (p : 'a parser) (q : 'a -> 'b parser) : 'b parser =
  fun ls ->
  match p ls with
  | Some (a, ls) -> q a ls
  | None -> None

let ( >>= ) = bind

let ( let* ) = bind

let read : char parser =
  fun ls ->
  match ls with
  | x :: ls -> Some (x, ls)
  | _ -> None

let satisfy (f : char -> bool) : char parser =
  fun ls ->
  match ls with
  | x :: ls ->
    if f x then
      Some (x, ls)
    else
      None
  | _ -> None

let char (c : char) : char parser = satisfy (fun x -> x = c)

let seq (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
  fun ls ->
  match p1 ls with
  | Some (_, ls) -> p2 ls
  | None -> None

let ( >> ) = seq

let seq' (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls) -> (
      match p2 ls with
      | Some (_, ls) -> Some (x, ls)
      | None -> None)
  | None -> None

let ( << ) = seq'

let alt (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls) -> Some (x, ls)
  | None -> p2 ls

let ( <|> ) = alt

let map (p : 'a parser) (f : 'a -> 'b) : 'b parser =
  fun ls ->
  match p ls with
  | Some (a, ls) -> Some (f a, ls)
  | None -> None

let ( >|= ) = map

let ( >| ) p c = map p (fun _ -> c)

let rec many (p : 'a parser) : 'a list parser =
  fun ls ->
  match p ls with
  | Some (x, ls) -> (
      match many p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
  | None -> Some ([], ls)

let rec many1 (p : 'a parser) : 'a list parser =
  fun ls ->
  match p ls with
  | Some (x, ls) -> (
      match many p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
  | None -> None

let rec many' (p : unit -> 'a parser) : 'a list parser =
  fun ls ->
  match p () ls with
  | Some (x, ls) -> (
      match many' p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
  | None -> Some ([], ls)

let rec many1' (p : unit -> 'a parser) : 'a list parser =
  fun ls ->
  match p () ls with
  | Some (x, ls) -> (
      match many' p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
  | None -> None

let whitespace : unit parser =
  fun ls ->
  match ls with
  | c :: ls ->
    if String.contains " \012\n\r\t" c then
      Some ((), ls)
    else
      None
  | _ -> None

let ws : unit parser = many whitespace >| ()

let ws1 : unit parser = many1 whitespace >| ()

let digit : char parser = satisfy is_digit

let natural : int parser =
  fun ls ->
  match many1 digit ls with
  | Some (xs, ls) -> Some (int_of_string (implode xs), ls)
  | _ -> None

let literal (s : string) : unit parser =
  fun ls ->
  let cs = explode s in
  let rec loop cs ls =
    match (cs, ls) with
    | [], _ -> Some ((), ls)
    | c :: cs, x :: xs ->
      if x = c then
        loop cs xs
      else
        None
    | _ -> None
  in
  loop cs ls

let keyword (s : string) : unit parser = literal s >> ws >| ()


(* Constant parsers = int, bool, (), name *)
let integerParser : int parser = 
  natural <|> 
  (
    satisfy (fun x-> x='-') >>= fun c1 ->
    natural >>= fun n ->
    return (-1*n)
  )

let boolParser : bool parser = 
  (keyword "True" >>= fun t -> return true) <|> 
  (keyword "False" >>= fun t -> return false)

let unitParser : const parser = 
  keyword "()" >>= fun c1 -> return U

let nameParser : string parser =
  let* c = satisfy is_alpha in
  let* cs = many (satisfy (fun c -> is_alphanum c || c = '_' || c = '\'')) in
  let s = implode (c :: cs) in
  return s << ws

let constParser : const parser = 
  (integerParser >>= fun i -> return (I i)) <|>
  (boolParser >>= fun b -> return (B b)) <|>
  (unitParser >>= fun u -> return (U)) <|>
  (nameParser >>= fun n -> return (N n))

(* Part 1 Command Parsers = Push, Pop, Trace, Add, Sub, Mul, Div 
   prog ::= coms
   com ::= Push const | Pop int | Trace int
   | Add int | Sub int | Mul int | Div int
   coms ::= com {com} 
*)

let pushParser : com parser = 
  keyword "Push" >>= fun _ ->
  ws >>= fun _ ->
  constParser >>= fun c ->
  ws >>= fun _ ->
  return (Push c)

let traceParser : com parser = 
  keyword "Trace" >>= fun _ ->
  ws >>= fun _ ->
  natural >>= fun n ->
  ws >>= fun _ ->
  return (Trace n)

let popParser : com parser = 
  keyword "Pop" >>= fun _ ->
  ws >>= fun _ ->
  natural >>= fun n ->
  ws >>= fun _ ->
  return (Pop n)

let addParser : com parser = 
  keyword "Add" >>= fun _ ->
  ws >>= fun _ ->
  natural >>= fun n ->
  ws >>= fun _ ->
  return (Add n)

let subParser : com parser = 
  keyword "Sub" >>= fun _ ->
  ws >>= fun _ ->
  natural >>= fun n ->
  ws >>= fun _ ->
  return (Sub n)

let mulParser : com parser =
  keyword "Mul" >>= fun _ ->
  ws >>= fun _ ->
  natural >>= fun n ->
  ws >>= fun _ ->
  return (Mul n)

let divParser : com parser =
  keyword "Div" >>= fun _ ->
  ws >>= fun _ ->
  natural >>= fun n ->
  ws >>= fun _ ->
  return (Div n)


(* Part 2 commands - And, Or, Not, Equal, Lte, Local, Global, Lookup, BeginEnd, IfElseEnd *)
let andParser : com parser =
  keyword "And" >>= fun _ ->
  ws >>= fun _ ->
  return (And)

let orParser : com parser =
  keyword "Or" >>= fun _ ->
  ws >>= fun _ ->
  return (Or)

let notParser : com parser = 
  keyword "Not" >>= fun _ ->
  ws >>= fun _ ->
  return (Not)

let equalParser : com parser = 
  keyword "Equal" >>= fun _ ->
  ws >>= fun _ ->
  return (Equal)

let lteParser : com parser = 
  keyword "Lte" >>= fun _ ->
  ws >>= fun _ ->
  return (Lte)

let localParser : com parser =
  keyword "Local" >>= fun _ ->
  ws >>= fun _ ->
  return (Local)

let globalParser : com parser =
  keyword "Global" >>= fun _ ->
  ws >>= fun _ ->
  return (Global)

let lookupParser : com parser =
  keyword "Lookup" >>= fun _ ->
  ws >>= fun _ ->
  return (Lookup)

let rec beginEndParser () =
  let* _ = keyword "Begin" in
  let* commands = commandParsers() in 
  let* _ = keyword "End" in 
  return (BeginEnd commands)

and ifElseEndParser () = 
  let* _ = keyword "If" in
  let* if_commands = commandParsers() in 
  let* _ = keyword "Else" in 
  let* else_commands = commandParsers() in 
  let* _ = keyword "End" in 
  return (IfElseEnd (if_commands, else_commands))

and commandParser () : com parser = 
  pushParser <|>
  traceParser <|>
  popParser <|>
  addParser <|>
  subParser <|>
  mulParser <|>
  divParser <|>
  andParser <|>
  orParser <|>
  notParser <|>
  equalParser <|>
  lteParser <|>
  localParser <|>
  globalParser <|>
  lookupParser <|>
  beginEndParser() <|>
  ifElseEndParser()

and commandParsers () = many (commandParser ())

(* end of parser combinators *)

(* Turn const to string bc log is a string list*)
let constToString (c: const) : string = 
  match c with 
  | I (i) -> string_of_int (i)
  | B b -> (match b with 
      | true -> "True"
      | false -> "False")
  | U -> "()"
  | N n -> n

(* Performs add, sub, mul, div on integers in the stack, returns new stack *)
let opsOnStack (n: int) (st: stack) (str: string): stack option =
  let rec helper x st1 accum =
    match x with 
    | 0 -> Some ((I accum)::st1)
    | x -> 
      if str="add" then (match st1 with 
          | (I i)::tl -> helper (x-1) (tl) (accum+i) 
          | _ -> None)
      else if str="sub" then (match st1 with 
          | (I i)::tl -> if x==n then helper (x-1) (tl) (i) else helper (x-1) (tl) (accum-i)
          | _ -> None)
      else if str="mul" then (match st1 with 
          | (I i)::tl -> if x==n then helper (x-1) (tl) (i) else helper (x-1) (tl) (accum*i)
          | _ -> None)
      else if str="div" then (match st1 with 
          | (I i)::tl -> if x==n then helper (x-1) (tl) (i) else (match i with 
              | 0 -> None     (* Will output program as Error, divided by 0*)
              | i -> helper (x-1) (tl) (accum/i))
          | _ -> None)
      else None
  in helper n st 0

(* Performs: and, or, not, equal, lte *)
let logicalOps (n: int) (st: stack) (str: string): stack option = 
  let rec helper x st1 accum = 
    match x with 
    | 0 -> Some ((B accum)::st1)
    | x -> 
      if str="and" then (match st1 with 
          | (B b1)::(B b2)::tl -> helper 0 tl (b1 && b2)
          | _ -> None)
      else if str="or" then (match st1 with 
          | (B b1)::(B b2)::tl -> helper 0 tl (b1 || b2)
          | _ -> None)
      else if str="not" then (match st1 with 
          | (B b)::tl -> helper 0 (tl) (not b)
          | _ -> None)
      else if str="equal" then (match st1 with 
          | (I n1)::(I n2)::tl -> helper 0 (tl) (n1==n2)
          | _ -> None)
      else if str="lte" then (match st1 with 
          | (I n1)::(I n2)::tl -> helper 0 (tl) (n1<=n2)
          | _ -> None)
      else None
  in helper n st true

(* Performs Local and Global bindings, adds name*value pair to envs *)
let envOps (st: stack) (env: env) : env option = 
  match st with 
  | N name :: y :: st1 -> Some ((name, y)::env)
  | _ -> None

let rec lookupLocal (name: string) (local: env) : const option =
  match local with 
  | (n, value)::tl -> if n=name then Some(value) else lookupLocal name tl
  | [] -> None

let rec lookupGlobal (name: string) (global: env) : const option =
  match global with 
  | (n, value)::tl -> if n=name then Some(value) else lookupGlobal name tl
  | [] -> None

(* Look up in local env first, then global env, then return as error if none found *)
let lookupName (st: stack) (local: env) (global: env) : stack option =
  match st with 
  | N name :: tl -> (match lookupLocal name local with 
      | Some res -> Some(res :: tl)
      | _ -> (match lookupGlobal name global with 
          | Some res -> Some(res :: tl)
          | _ -> None
        ) 
    )
  | _ -> None

(* 
Evaluator.
coms = described below in interp. 
st = [I 5; B true; I 4; U; B false]
log = ["5"; "True"; "4"; "()"; "False"] 
Part 2 - Add stack and global env as outputs for BeginEnd scope.
*)
let rec eval (coms: coms) (st: stack) (log: string list) (local: env) (global: env): stack * env * string list = 
  match coms, st with 
  | Push c :: comsrest, _ -> eval comsrest (c::st) log local global
  | Trace n :: comsrest, [] -> if n=0 then eval comsrest st log local global else (st, global, ["Error"])  
  | Trace n :: comsrest, c::stackrest -> (match n with 
      | 0 -> eval comsrest st log local global
      | n -> eval ((Trace (n-1))::comsrest) stackrest ((constToString c)::log) local global ) 
  | Pop n :: comsrest, [] -> if n=0 then eval comsrest st log local global else (st, global, ["Error"]) 
  | Pop n :: comsrest, c::stackrest -> (match n with 
      | 0 -> eval comsrest st log local global
      | n -> eval ((Pop (n-1))::comsrest) stackrest log local global )
  | Add 0 :: comsrest, _ -> eval comsrest ((I 0)::st) log local global
  | Add n :: comsrest, st1 -> (match (opsOnStack n st1 "add") with 
      | Some res -> eval comsrest res log local global
      | _ -> (st, global, ["Error"]) )
  | Sub 0 :: comsrest, _ -> eval comsrest ((I 0)::st) log local global
  | Sub n :: comsrest, st1 -> (match (opsOnStack n st1 "sub") with 
      | Some res -> eval comsrest res log local global
      | _ -> (st, global, ["Error"]) )
  | Mul 0 :: comsrest, _ -> eval comsrest ((I 1)::st) log local global
  | Mul n :: comsrest, st1 -> (match (opsOnStack n st1 "mul") with 
      | Some res -> eval comsrest res log local global
      | _ -> (st, global, ["Error"]) )
  | Div 0 :: comsrest, _ -> eval comsrest ((I 1)::st) log local global
  | Div n :: comsrest, st1 -> (match (opsOnStack n st1 "div") with 
      | Some res -> eval comsrest res log local global
      | _ -> (st,global, ["Error"]) )
  | And :: comsrest, [] -> (st, global, ["Error"]) 
  | And :: comsrest, st1 -> (match (logicalOps 2 st1 "and") with 
      | Some res -> eval comsrest res log local global
      | _ -> (st, global, ["Error"]) )
  | Or :: comsrest, [] -> (st, global, ["Error"]) 
  | Or :: comsrest, st1 -> (match (logicalOps 2 st1 "or") with 
      | Some res -> eval comsrest res log local global
      | _ -> (st, global, ["Error"]) )
  | Not :: comsrest, [] -> (st, global, ["Error"]) 
  | Not :: comsrest, st1 -> (match (logicalOps 1 st1 "not") with 
      | Some res -> eval comsrest res log local global
      | _ -> (st, global, ["Error"]) )
  | Equal :: comsrest, [] -> (st, global, ["Error"]) 
  | Equal :: comsrest, st1 -> (match (logicalOps 2 st1 "equal") with 
      | Some res -> eval comsrest res log local global
      | _ -> (st, global, ["Error"]))
  | Lte :: comsrest, [] -> (st, global, ["Error"]) 
  | Lte :: comsrest, st1 -> (match (logicalOps 2 st1 "lte") with 
      | Some res -> eval comsrest res log local global
      | _ -> (st, global, ["Error"]) )
  | Local :: comsrest, [] -> (st, global, ["Error"]) 
  | Local :: comsrest, st1 -> (match (envOps st1 local) with 
      | Some newlocal -> (match st1 with 
          | x::y::tl -> eval comsrest (U::tl) log newlocal global
          | _ -> (st, global, ["Error"]) )
      | _ -> (st, global, ["Error"]) )
  | Global :: comsrest, [] -> (st, global, ["Error"]) 
  | Global :: comsrest, st1 -> (match (envOps st1 global) with 
      | Some newglobal -> (match st1 with 
          | x::y::tl -> eval comsrest (U::tl) log local newglobal
          | _ -> (st, global, ["Error"]) )
      | _ -> (st, global, ["Error"]) )
  | Lookup :: comsrest, [] -> (st, global, ["Error"]) 
  | Lookup :: comsrest, st1 -> (match lookupName st1 local global with 
      | Some newstack -> eval comsrest newstack log local global
      | _ -> (st, global, ["Error"]))
  (* BeginEnd has new stack, log, global env that get added to the originals *)
  | BeginEnd commands :: comsrest, st1 -> (match eval commands [] [] local global with 
      | (st2, global2, log2) -> if log2=["Error"] then (st1, global, ["Error"]) else (match st2 with 
          | v::tl -> eval comsrest (v::st1) (log2 @ log) local (global2 @ global)
          | _ -> (st, global, ["Error"]))
    )
  | IfElseEnd (if_cmds, else_cmds) :: comsrest, [] -> (st, global, ["Error"]) 
  | IfElseEnd (if_cmds, else_cmds) :: comsrest, st1 -> (match st1 with 
      | B b :: stackrest -> 
        (if b=true then eval (if_cmds @ comsrest) stackrest log local global
         else if b=false then eval (else_cmds @ comsrest) stackrest log local global
         else (st, global, ["Error"])
        )
      | _ -> (st, global, ["Error"]))
  | [], _ -> (st, global, log)
  | _ -> (st, global, ["Error"]) 

(* TODO *)
(*
src = "Push 54\nPush 8\nPush False\nPush ()\nTrace 3\n"
coms = [Push (I 54); Push (I 8); Push (B false); Push U; Trace 3]
*)
let interp (src : string) : string list = 
  match parse (many(commandParser())) (src) with 
  | Some (coms, []) -> (match eval coms [] [] [] [] with 
      | (eval_stack, eval_globalenv, eval_log) -> eval_log) 
  | _ -> ["Error"]

(* Calling (main "test.txt") will read the file test.txt and run interp on it.
   This is only used for debugging and will not be used by the gradescope autograder. *)
let main fname =
  let src = readlines fname in
  interp src
