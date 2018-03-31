(* Mini BASIC Interpreter

   This file contains source code from the book:
   "Developing Applications with Objective Caml"

   The book is available at:
   https://caml.inria.fr/pub/docs/oreilly-book/html/

   The specific part of the book which descibes the
   basic interpreter implementation is available at
   https://caml.inria.fr/pub/docs/oreilly-book/html/book-ora058.html
*)

(* Abstract Syntax Types *)
type unary_op = | MINUS
                | NOT

type binary_op = | PLUS
                 | MINUS
                 | MULT
                 | DIV
                 | MOD
                 | EQ
                 | LT
                 | LE
                 | GT
                 | GE
                 | DIFF
                 | AND
                 | OR

type expression = | ExpInt of int
                  | ExpVar of string
                  | ExpStr of string
                  | ExpUnr of unary_op * expression
                  | ExpBin of expression * binary_op * expression

type command = | Rem of string
               | Goto of int
               | Print of expression
               | Input of string
               | If of expression * int
               | Let of string * expression

type line = {num : int ; cmd : command}

type program = line list

(* Program editor *)
type phrase = Line of line | List | Run | PEnd

let unary_pr = function
  | NOT -> 1
  | MINUS -> 7

let binary_pr = function
  | MULT | DIV -> 6
  | PLUS | MINUS -> 5
  | MOD -> 4
  | EQ | LT | LE | GT | GE | DIFF -> 3
  | AND | OR -> 2

(* Program pretty printing *)
let unary_pp = function
  | NOT -> "!"
  | MINUS -> "-"

let binary_pp = function
  | PLUS -> "+"
  | MULT -> "*"
  | MOD -> "%"
  | MINUS -> "-"
  | DIV -> "/"
  | EQ -> "="
  | LT -> "<"
  | LE -> "<="
  | GT -> ">"
  | GE -> ">="
  | DIFF -> "<>"
  | AND -> "&"
  | OR -> "|"

let parenthesis x = "(" ^ x ^ ")"

let expression_pp =
  let rec ppl pr = function
    | ExpInt n -> (string_of_int n)
    | ExpVar v -> v
    | ExpStr s -> "\"" ^ s ^ "\""
    | ExpUnr (op, e) ->
      let res = (unary_pp op)^(ppl (unary_pr op) e) in
      if (pr=0) then res else parenthesis res
    | ExpBin (e1, op, e2) ->
      let pr2 = binary_pr op in
      let res = (ppl pr2 e1)^(binary_pp op)^(ppr pr2 e2) in
      if (pr2 >= pr) then res else parenthesis res
  and ppr pr exp = match exp with
      ExpBin (e1,op,e2) ->
      let pr2 = binary_pr op in
      let res = (ppl pr2 e1)^(binary_pp op)^(ppr pr2 e2) in
      if (pr2 > pr) then res else parenthesis res
    | _ -> ppl pr exp
   in ppl 0

let command_pp = function
  | Rem s -> "REM " ^ s
  | Goto n -> "GOTO " ^ (string_of_int n)
  | Print e -> "PRINT " ^ (expression_pp e)
  | Input v -> "INPUT " ^ v
  | If (e,n) -> "IF "^(expression_pp e)^" THEN "^(string_of_int n)
  | Let (v,e) -> "LET "^ v ^ " = "^(expression_pp e)

let line_pp l = (string_of_int l.num) ^ " " ^ (command_pp l.cmd)

(* Lexing *)
type lexeme = Lint of int
            | Lident of string
            | Lsymbol of string
            | Lstring of string
            | Lend

type string_lexer = {string:string; mutable current:int; size:int }

let init_lex s = { string=s; current=0; size=String.length s}

let forward cl = cl.current <- cl.current + 1

let forward_n cl n = cl.current <- cl.current + n

let extract pred cl =
  let st = cl.string and pos = cl.current in
  let rec ext n = if (n<cl.size) && (pred st.[n]) then ext (n+1) else n in
  let res = ext pos in
  cl.current <- res;
  String.sub cl.string pos (res-pos)

let extract_int =
  let is_int = function '0'..'9' -> true | _ -> false in
  function cl -> int_of_string (extract is_int cl)

let extract_ident =
  let is_alpha_num = function 'a'..'z'|'A'..'Z'|'0'..'9'|'_' -> true | _ -> false in
  extract is_alpha_num

exception LexerError

let rec lexer cl =
  let lexer_char c = match c with
    | ' '
    | '\t' -> forward cl ; lexer cl
    | 'a'..'z'
    | 'A'..'Z' -> Lident (extract_ident cl)
    | '0'..'9' -> Lint (extract_int cl)
    | '"' -> forward cl;
      let res = Lstring (extract ((<>) '"') cl) in forward cl; res
    | '+' | '-' | '*' | '/' | '%' | '&' | '|' | '!' | '=' | '(' | ')' ->
      forward cl; Lsymbol (String.make 1 c)
    | '<' | '>' -> forward cl;
      if cl.current >= cl.size then Lsymbol (String.make 1 c)
      else let cs = cl.string.[cl.current]
        in (match (c,cs) with
            | ('<', '=') -> forward cl; Lsymbol "<="
            | ('>', '=') -> forward cl; Lsymbol ">="
            | ('<', '>') -> forward cl; Lsymbol "<>"
            | _ -> Lsymbol (String.make 1 c))
    | _ -> raise LexerError
  in
  if cl.current >= cl.size then Lend
  else lexer_char cl.string.[cl.current]

(* Parsing *)

type exp_elem =
  | Texp of expression
  | Tbin of binary_op
  | Tunr of unary_op
  | Tlp

exception ParseError

let unary_sym = function
  | "!" -> NOT
  | "-" -> MINUS
  | _ -> raise ParseError

let binary_sym = function
  | "+" -> PLUS
  | "-" -> MINUS
  | "*" -> MULT
  | "/" -> DIV
  | "%" -> MOD
  | "=" -> EQ
  | "<" -> LT
  | "<=" -> LE
  | ">" -> GT
  | ">=" -> GE
  | "<>" -> DIFF
  | "&" -> AND
  | "|" -> OR
  | _ -> raise ParseError

let tsymb s = try Tbin (binary_sym s) with ParseError -> Tunr (unary_sym s)

let reduce pr = function
  | (Texp e)::(Tunr op)::st when (unary_pr op) >= pr
    -> (Texp (ExpUnr (op,e)))::st
  | (Texp e1)::(Tbin op)::(Texp e2)::st when (binary_pr op) >= pr
    -> (Texp (ExpBin (e2,op,e1)))::st
  | _ -> raise ParseError

let rec stack_or_reduce lex stack = match lex, stack with
  | Lint n, _ -> (Texp (ExpInt n))::stack
  | Lident v, _ -> (Texp (ExpVar v))::stack
  | Lstring s, _ -> (Texp (ExpStr s))::stack
  | Lsymbol "(" , _ -> Tlp::stack
  | Lsymbol ")", (Texp e)::Tlp::st -> (Texp e)::st
  | Lsymbol ")", _ -> stack_or_reduce lex (reduce 0 stack)
  | Lsymbol s, _
    -> let symbol =
         if (s<>"-") then tsymb s
         else match stack with
           | (Texp _)::_ -> Tbin MINUS
           | _ -> Tunr MINUS
    in (match symbol with
        | Tunr op -> (Tunr op)::stack
        | Tbin op -> (try stack_or_reduce lex (reduce (binary_pr op)
                                                 stack)
                      with ParseError -> (Tbin op)::stack)
        | _ -> raise ParseError )
  | _, _ -> raise ParseError

let rec reduce_all = function
  | [] -> raise ParseError
  | [Texp x] -> x
  | st -> reduce_all (reduce 0 st)

let parse_exp stop cl =
  let p = ref 0 in
  let rec parse_one stack =
    let l = ( p:=cl.current ; lexer cl ) in
    if not (stop l) then parse_one (stack_or_reduce l stack)
    else (cl.current <- !p ; reduce_all stack )
  in parse_one []

let parse_cmd cl = match lexer cl with
    Lident s -> (match s with
      | "REM" -> Rem(extract (fun _ -> true) cl)
      | "GOTO" -> Goto (match lexer cl with
          | Lint p -> p
          | _ -> raise ParseError)
      | "INPUT" -> Input (match lexer cl with
          | Lident v -> v
          | _ -> raise ParseError)
      | "PRINT" -> Print (parse_exp ((=) Lend) cl)
      | "LET" ->
        let l2 = lexer cl and l3 = lexer cl in
        (match l2, l3 with
         | (Lident v, Lsymbol "=") -> Let(v, parse_exp ((=) Lend) cl)
         | _ -> raise ParseError)
      | "IF" ->
        let test = parse_exp ((=) (Lident "THEN")) cl in
        (match ignore (lexer cl) ; lexer cl with
         | Lint n -> If (test, n)
         | _ -> raise ParseError)
      | _ -> raise ParseError )
  | _ -> raise ParseError

let parse str =
  let cl = init_lex str in
  match lexer cl with
  | Lint n -> Line { num=n ; cmd=parse_cmd cl}
  | Lident "LIST" -> List
  | Lident "RUN" -> Run
  | Lident "END" -> PEnd
  | _ -> raise ParseError

(* Evaluation *)
type value = Vint of int | Vstr of string | Vbool of bool

type environment = (string * value) list

type code = line array

type state_exec = { line:int ; xprog:code ; xenv:environment }

exception RunError of int
let runerr n = raise (RunError n)

exception Result_lookup_index of int

let lookup_index tprog num_line =
  try
    for i=0 to (Array.length tprog) - 1 do
      let num_i = tprog.(i).num in
      if (num_i=num_line) then raise (Result_lookup_index i)
      else if num_i>num_line then raise (Result_lookup_index (-1))
    done ;
    (-1)
  with Result_lookup_index i -> i

let assemble prog =
  let tprog = Array.of_list prog in
  for i=0 to (Array.length tprog) - 1 do
    match tprog.(i).cmd with
    | Goto n -> let index = lookup_index tprog n in
      tprog.(i) <- { tprog.(i) with cmd = Goto index }
    | If(c,n) -> let index = lookup_index tprog n in
      tprog.(i) <- { tprog.(i) with cmd = If(c, index) }
    | _ -> ()
  done;
  tprog

let rec eval_exp n envt expr = match expr with
  | ExpInt p  ->  Vint p
  | ExpVar v  -> ( try List.assoc v envt with Not_found -> runerr n )
  | ExpUnr (MINUS,e) ->
    (match eval_exp n envt e with
      |  Vint p -> Vint (-p)
      | _ -> runerr n )
  | ExpUnr (NOT,e) ->
    (match eval_exp n envt e with
      | Vbool p -> Vbool (not p)
      | _ -> runerr n )
  | ExpStr s -> Vstr s  
  | ExpBin (e1,op,e2) ->
    match eval_exp n envt e1 , op , eval_exp n envt e2 with
    | Vint v1, PLUS, Vint v2 -> Vint (v1 + v2) 
    | Vint v1, MINUS, Vint v2 -> Vint (v1 - v2) 
    | Vint v1, MULT, Vint v2 -> Vint (v1 * v2) 
    | Vint v1, DIV, Vint v2 when v2<>0 -> Vint (v1 / v2) 
    | Vint v1, MOD, Vint v2 when v2<>0 -> Vint (v1 mod v2) 
    | Vint v1, EQ, Vint v2 -> Vbool (v1 = v2) 
    | Vint v1, DIFF, Vint v2 -> Vbool (v1 <> v2) 
    | Vint v1, LT, Vint v2 -> Vbool (v1 < v2) 
    | Vint v1, GT, Vint v2 -> Vbool (v1 > v2) 
    | Vint v1, LE, Vint v2 -> Vbool (v1 <= v2) 
    | Vint v1, GE, Vint v2 -> Vbool (v1 >= v2) 
    | Vbool v1, AND, Vbool v2 -> Vbool (v1 && v2) 
    | Vbool v1, OR, Vbool v2 -> Vbool (v1 || v2) 
    | Vstr v1, PLUS, Vstr v2 -> Vstr (v1 ^ v2) 
    | _ , _ , _ -> runerr n

let rec add v e env = match env with
  | [] -> [v,e]
  | (w,f)::l -> if w=v then (v,e)::l else (w,f)::(add v e l)

let print_value v = match v with
  | Vint n -> print_int n
  | Vbool true -> print_string "true"
  | Vbool false -> print_string "false"
  | Vstr s -> print_string s

let next_line state =
  let n = state.line+1 in
  if n < Array.length state.xprog then n else -1

let eval_cmd state =
  match state.xprog.(state.line).cmd with
  | Rem _ -> { state with line = next_line state }
  | Print e -> print_value (eval_exp state.line state.xenv e);
    print_newline () ;
    { state with line = next_line state }
  | Let(v,e) -> let ev = eval_exp state.line state.xenv e in
    { state with line = next_line state ; xenv = add v ev state.xenv }
  | Goto n -> { state with line = n }
  | Input v -> let x = try read_int ()
                 with Failure "int_of_string" -> 0 in
    { state with line = next_line state ; xenv = add v (Vint x) state.xenv }
  | If (t,n) -> match eval_exp state.line state.xenv t with
    | Vbool true -> { state with line = n }
    | Vbool false -> { state with line = next_line state }
    | _ -> runerr state.line

let rec run state =
  if state.line = -1 then state else run (eval_cmd state)

(* Finishing touches *)

let rec insert line p = match p with
  | [] -> [line]
  | l::prog ->
    if l.num < line.num then l::(insert line prog)
    else if l.num=line.num then line::prog
    else line::l::prog

let print_prog prog =
  let print_line x = print_string (line_pp x) ; print_newline () in
  print_newline () ;
  List.iter print_line prog ;
  print_newline ()

type loop_state = { prog:program ; env:environment }

exception End

let one_command state =
  print_string "> " ; flush stdout ;
  try
    match parse (input_line stdin) with
    | Line l -> { state with prog = insert l state.prog }
    | List -> (print_prog state.prog ; state)
    | Run -> let tprog = assemble state.prog in
      let xstate = run { line = 0 ; xprog = tprog ; xenv = state.env } in
      { state with env = xstate.xenv }
    | PEnd -> raise End
  with
  | LexerError -> print_string "Illegal character\n"; state
  | ParseError -> print_string "Syntax error\n"; state
  | RunError n ->
    print_string "Runtime error at line";
    print_int n;
    print_string "\n";
    state

let go () =
  try
    print_string "BASIC Interpreter\n\n";
    let rec loop state = loop (one_command state) in
    loop { prog = [] ; env=[] }
  with End -> print_string "See you later...\n"

let () = go ()
