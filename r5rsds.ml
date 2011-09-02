(*
  An OCaml implementation of R5RS denotational semantics.

  modifications are:
  * `wrong' function takes a store and objects to construct an error message.
  * some functions eta-converted to take a store.
  * store is not a function, but is a record.
*)

(* Domains *)
type scm_loc = int
type scm_bool = [`True | `False]
type scm_sym = [`Symbol of string]
type scm_char = [`Char of char]
type scm_num = [`Num of int]
type scm_pair = [`Pair of (scm_loc * scm_loc * bool)]
type scm_vec = [`Vec of (scm_loc list * bool)]
type scm_str = [`Str of (scm_loc list * bool)]
type scm_null = [`Null]
type scm_misc = [ scm_bool | scm_null | `Undefined | `Unspecified ]

type scm_proc_repr = scm_loc * (scm_expr list -> scm_econt -> scm_ccont)
and scm_proc = [`Proc of scm_proc_repr]
and scm_expr = [
| scm_sym
| scm_char
| scm_num
| scm_pair
| scm_vec
| scm_str
| scm_misc
| `Proc of scm_proc_repr
]
and scm_env = string -> scm_loc
and scm_store = { loc : scm_loc; find : scm_loc -> (scm_expr * bool) }
and scm_ccont = scm_store -> scm_answer
and scm_econt = scm_expr list -> scm_ccont
and scm_answer = scm_expr

(* Syntax *)
type scm_const = [ scm_sym | scm_num | scm_bool | scm_null | scm_char ]
type syn_const = [`K of scm_const]
type syn_expr = [
| `Id of string
| `App of (syn_expr * syn_expr list)
| `Lam of (string list * syn_cmd list * syn_expr)
| `LamO of (string list * string * syn_cmd list * syn_expr)
| `LamR of (string * syn_cmd list * syn_expr)
| `If of (syn_expr * syn_expr * syn_expr)
| `If1 of (syn_expr * syn_expr)
| `Set of (string * syn_expr)
| syn_const
]
and syn_cmd = syn_expr

(* Misc. *)
let null_loc : scm_loc = -1

let null_env (_name : string) : scm_loc =
  null_loc

let null_store =
  { loc = null_loc + 1
  ; find = fun _loc -> (`Undefined, false)
  }

exception Internal_error of string
exception Runtime_error of string * string list

let internal_error s =
  raise (Internal_error s)

let runtime_error s strs =
  raise (Runtime_error (s, strs))

let rec string_of_expr : scm_store -> scm_expr -> string =
  fun store e ->
    let resolve loc = fst (store.find loc) in
    let rec strings_of_pair = function
      | `Pair (a, d, _) ->
          string_of_expr store (resolve a)::strings_of_pair (resolve d)
      | `Null -> []
      | s -> ["."; string_of_expr store s]
    in
    let char_repr_in_string = function
      | `Char c -> Printf.sprintf "%c" c
      | obj ->
          internal_error (Printf.sprintf "non-character content in string: %s"
                            (string_of_expr store obj))
    in
      match e with
      | `True -> "#t"
      | `False -> "#f"
      | `Null -> "()"
      | `Undefined -> "#<undef>"
      | `Unspecified -> "#<unspecified>"
      | `Proc _ -> "#<procedure>"
      | `Symbol s -> s
      | `Num n -> string_of_int n
      | `Pair _ as p ->
          Printf.sprintf "(%s)" (String.concat " " (strings_of_pair p))
      | `Char c -> Printf.sprintf "#\\%c" c
      | `Vec (ps, _) ->
          Printf.sprintf "#(%s)" (String.concat " "
                                    (List.map
                                       (fun loc ->
                                          string_of_expr store (resolve loc))
                                       ps))
      | `Str (ps, _) ->
          Printf.sprintf "\"%s\"" (String.concat ""
                                     (List.map
                                        (fun loc ->
                                           char_repr_in_string (resolve loc))
                                        ps))

(* Auxiliary functions *)
let wrong msg s objs =
  runtime_error msg (List.map (string_of_expr s) objs)

let lookup : scm_env -> string -> scm_loc =
  fun rho name -> rho name

let rec extends : scm_env -> string list -> scm_loc list -> scm_env =
  fun rho names locs ->
    match names, locs with
    | [], [] -> rho
    | name::names, loc::locs ->
        extends (fun n ->
                   if n = name then
                     loc
                   else
                     rho n)
          names locs
    | _, _ -> internal_error "uneven name/loc pairs"

let send : scm_expr -> scm_econt -> scm_ccont =
  fun e k -> k [e]

let single : (scm_expr -> scm_ccont) -> scm_econt =
  fun psi es s ->
    match es with
    | [e] -> psi e s
    | _ -> wrong "wrong number of return values" s es

let newloc s =
  Some s.loc

let update : scm_loc -> scm_expr -> scm_store -> scm_store =
  fun loc e s ->
    if loc = null_loc then   (* avoid to set! to undefined variable *)
      s
    else
      { loc = s.loc + 1
      ; find = (fun l -> if l = loc then (e, true) else s.find l)
      }

let rec dropfirst l = function
  | 0 -> l
  | n -> dropfirst (List.tl l) (n - 1)

let rec takefirst l = function
  | 0 -> []
  | n -> List.hd l :: takefirst (List.tl l) (n - 1)

let onearg : (scm_expr -> scm_econt -> scm_ccont)
    -> (scm_expr list -> scm_econt -> scm_ccont) =
  fun z es k s ->
    match es with
    | [e] -> z e k s
    | _ -> wrong "number of arguments /= 1" s es

let twoarg : (scm_expr -> scm_expr -> scm_econt -> scm_ccont)
    -> (scm_expr list -> scm_econt -> scm_ccont) =
  fun z es k s ->
    match es with
    | [e1; e2] -> z e1 e2 k s
    | _ -> wrong "number of arguments /= 2" s es

let cons : scm_expr list -> scm_econt -> scm_ccont =
  twoarg (fun e1 e2 k s ->
            match newloc s with
            | Some loc ->
                (fun s' ->
                   match newloc s' with
                   | Some loc' ->
                       send (`Pair (loc, loc', true))
                         k
                         (update loc' e2 s')
                   | None -> wrong "out of memory" s' [])
                  (update loc e1 s)
            | None -> wrong "out of memory" s [])

let rec list : scm_expr list -> scm_econt -> scm_ccont =
  fun es k ->
    match es with
    | [] ->
        send `Null k
    | e::es ->
        list es (single (fun lis -> cons [e; lis] k))

let rec tievals : (scm_loc list -> scm_ccont) -> scm_expr list -> scm_ccont =
  fun psi es s ->
    match es with
    | [] ->
      psi [] s
    | e::es ->
        match newloc s with
        | Some loc ->
            tievals (fun locs -> psi (loc :: locs))
              es
              (update loc e s)
        | None -> wrong "out of memory" s []

let tievalsrest : (scm_loc list -> scm_ccont) -> scm_expr list -> int -> scm_ccont =
  fun psi es n ->
    list (dropfirst es n)
      (single (fun e -> tievals psi ((takefirst es n) @ [e])))

let assign : scm_loc -> scm_expr -> scm_ccont -> scm_ccont =
  fun loc e theta s ->
    theta (update loc e s)

let hold : scm_loc -> scm_econt -> scm_ccont =
  fun l k s -> send (fst (s.find l)) k s

let truish : scm_expr -> bool = function
  | `False -> false
  | _ -> true

let permute exprs = exprs

let unpermute exprs = exprs

let applicate e es k s =
  match e with
  | `Proc (_loc, body) -> body es k s
  | _ -> wrong "bad procedure" s [e]

let car : scm_expr list -> scm_econt -> scm_ccont =
  onearg (fun e k s ->
            match e with
            | `Pair (a, _, _) -> hold a k s
            | _ -> wrong "non-pair argument to car" s [e])

let cdr : scm_expr list -> scm_econt -> scm_ccont =
  onearg (fun e k s ->
            match e with
            | `Pair (_, d, _) -> hold d k s
            | _ -> wrong "non-pair argument to cdr" s [e])

let scm_bool_of_bool = function
  | true -> `True
  | false -> `False

let less : scm_expr list -> scm_econt -> scm_ccont =
  twoarg (fun e1 e2 k s ->
            match e1, e2 with
            | `Num a, `Num b ->
                send (scm_bool_of_bool (a < b)) k s
            | _, _ -> wrong "non-numeric argument to <" s [e1; e2])

let add : scm_expr list -> scm_econt -> scm_ccont =
  twoarg (fun e1 e2 k s ->
            match e1, e2 with
            | `Num a, `Num b ->
                send (`Num (a + b)) k s
            | _, _ -> wrong "non-numeric argument to +" s [e1; e2])

let setcar : scm_expr list -> scm_econt -> scm_ccont =
  twoarg (fun e1 e2 k s ->
            match e1 with
            | `Pair (a, _, true) ->
                assign a e2 (send `Unspecified k) s
            | `Pair (_, _, false) ->
                wrong "immutable argument to set-car!" s [e1]
            | _ ->
                wrong "non-pair argument to set-car!" s [e1])

let eqv : scm_expr list -> scm_econt -> scm_ccont =
  twoarg (fun e1 e2 k ->
            match e1, e2 with
            | `True, `True
            | `False, `False
            | `Null, `Null
            | `Undefined, `Undefined
            | `Unspecified, `Unspecified ->
                send `True k
            | `Num m, `Num n ->
                send (scm_bool_of_bool (m = n)) k
            | `Pair (a1, d1, _), `Pair(a2, d2, _) ->
                send (scm_bool_of_bool (a1 = a2 && d1 = d2)) k
            | `Char c, `Char d ->
                send (scm_bool_of_bool (c = d)) k
            | `Str (ls1, _), `Str (ls2, _)
            | `Vec (ls1, _), `Vec (ls2, _) ->
                send (scm_bool_of_bool (ls1 = ls2)) k
            | _, _ -> send `False k)

let rec valuelist : unit -> scm_expr list -> scm_econt -> scm_ccont =
  fun () -> (* for let rec rhs restriction *)
    onearg (fun e k s ->
              match e with
              | `Pair (_, _, _) as e ->
                  cdr [e]
                    (fun es ->
                       valuelist () es
                         (fun es ->
                            car [e]
                              (single (fun e -> k (e::es)))))
                    s
              | `Null -> k [] s
              | _ ->
                  wrong "non list argument to apply" s [e])

let apply : scm_expr list -> scm_econt -> scm_ccont =
  twoarg (fun e1 e2 k s ->
            match e1 with
            | `Proc (_, _) as f ->
                valuelist () [e2] (fun es -> applicate f es k) s
            | _ ->
                wrong "bad procedure argument to apply" s [e1])

let cwcc : scm_expr list -> scm_econt -> scm_ccont =
  onearg (fun e k s ->
            match e with
            | `Proc (_, _) as f ->
                begin
                  match newloc s with
                  | Some loc ->
                      applicate f
                        [`Proc (loc, fun es _k' -> k es)]
                        k
                        (update loc
                           `Unspecified
                           s)
                  | None -> wrong "out of memory" s []
                end
            | _ ->
                wrong "bad procedure argument" s [e])

let values : scm_expr list -> scm_econt -> scm_ccont =
  fun es k -> k es

let cwv : scm_expr list -> scm_econt -> scm_ccont =
  (* R5RS misses `apllicate e2 es >>k<<' *)
  twoarg (fun e1 e2 k -> applicate e1 [] (fun es -> applicate e2 es k))

(* Semantic functions *)
let sem_K : syn_const -> scm_expr = function
  | `K n -> (n :> scm_expr)

let rec sem_E : syn_expr -> scm_env -> scm_econt -> scm_ccont = function
  | `K _ as c ->
      (fun _rho k -> send (sem_K c) k)
  | `Id name ->
      (fun rho k s ->
         hold (lookup rho name)
           (single (function
                      | `Undefined ->
                          wrong ("Undefined variable: " ^ name) s []
                      | e -> send e k))
           s)
  | `App (e, es) ->
      (fun rho k ->
         sem_Es (permute (e::es))
           rho
           (fun es ->
              match unpermute es with
              | e::es -> applicate e es k
              | _ -> internal_error "should not occure"))
  | `Lam (names, cmds, e) ->
      (fun rho k s ->
         match newloc s with
         | Some loc ->
             send (`Proc (loc,
                          (fun es k' ->
                             if List.length es = List.length names then
                               tievals (fun locs ->
                                          (fun rho' ->
                                             sem_C cmds rho'
                                               (sem_E e rho' k'))
                                            (extends rho names locs))
                                 es
                             else
                               wrong "wrong number of arguments" s es)))
               k (update loc `Unspecified s)
         | None -> wrong "out of memory" s [])
  | `LamO (names, name, cmds, e) ->
      (fun rho k s ->
         match newloc s with
         | Some loc ->
             send (`Proc (loc,
                          (fun es k' ->
                             if List.length es >= List.length names then
                               tievalsrest
                                 (fun locs ->
                                    (fun rho' ->
                                       sem_C cmds rho' (sem_E e rho' k'))
                                      (extends rho (names @ [name]) locs))
                                 es
                                 (List.length names)
                             else
                               wrong "too few arguments" s es)))
               k (update loc `Unspecified s)
         | None -> wrong "out of memory" s [])
  | `LamR (name, cmds, e) ->
      sem_E (`LamO ([], name, cmds, e))
  | `If (e0, e1, e2) ->
      (fun rho k ->
         sem_E e0 rho
           (single (fun e ->
                      if truish e then
                        sem_E e1 rho k
                      else
                        sem_E e2 rho k)))
  | `If1 (e0, e1) ->
      (fun rho k ->
         sem_E e0 rho
           (single (fun e ->
                      if truish e then
                        sem_E e1 rho k
                      else
                        send `Unspecified k)))
  | `Set (name, expr) ->
      (fun rho k ->
         sem_E expr rho
           (single (fun e ->
                      assign (lookup rho name)
                        e
                        (send `Unspecified k))))
and sem_Es = function
  | [] -> (fun _rho k -> k [])
  | e::es ->
      (fun rho k ->
         sem_E e rho (single (fun e -> sem_Es es rho
                                (fun es -> k (e::es)))))
and sem_C = function
  | [] -> (fun _rho theta -> theta)
  | c::cs ->
      (fun rho theta ->
         sem_E c rho
           (fun _es -> sem_C cs rho theta))

(* evaluator + printer *)
let make_env nvs =
  let names, vals = List.split nvs in
  let rec loop store locs = function
    | [] -> (store, List.rev locs)
    | v::vs ->
        match newloc store with
        | Some loc ->
            loop (update loc (`Proc (loc, v)) store) (loc::locs) vs
        | None -> wrong "out of memory" store []
  in
  let (initial_store, locs) = loop null_store [] vals in
  let initial_env = extends null_env names locs in
    (initial_store, initial_env)

let (store0, env0) = make_env [
  ("cons", cons)
  ; ("list", list)
  ; ("car", car)
  ; ("cdr", cdr)
  ; ("<", less)
  ; ("+", add)
  ; ("set-car!", setcar)
  ; ("apply", apply)
  ; ("call-with-current-continuation", cwcc)
  ; ("call/cc", cwcc)
  ; ("values", values)
  ; ("call-with-values", cwv)
]

let eval expr cont =
  (sem_E expr) env0 cont store0

let eval_to_string expr =
  let printer exprs s =
    `Symbol (String.concat "\n" (List.map (string_of_expr s) exprs))
  in
  match eval expr printer with
  | `Symbol s -> s
  | _ -> internal_error "printer bug. should not occure"
