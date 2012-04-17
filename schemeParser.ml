open R5rsds
open Util

include P.CharParser

let identifier =
  let initp = function
    |'a'..'z'|'A'..'Z'
    |'!'|'$'|'%'|'&'|'*'|'/'|':'|'<'|'='|'>'|'?'|'_'|'~' -> true
    | _ -> false
  in
  let digitp = function '0'..'9' -> true | _ -> false in
  let special_subseq_p = function '+'|'-'|'.'|'@' -> true | _ -> false in
  let subseqp c = initp c || digitp c || special_subseq_p c in
    begin
      (List.cons <$> satisfy initp <*> many (satisfy subseqp) >>= fun cs ->
       pure @@ String.of_list cs)
      <|> string "+"
      <|> string "-"
      <|> string "..."
    end <?> "parse error: identifier"


let number =
  let digitp = function '0'..'9' -> true | _ -> false in
  let digit1p = function '1'..'9' -> true | _ -> false in
  let nat =
    satisfy digit1p >>= fun c ->
    many (satisfy digitp) >>= fun cs ->
    pure @@ String.of_list (c::cs)
  in
  let opt_minus = maybe "" <$> opt (string "-") in
    (((^) <$> opt_minus <*> nat) >>= fun s ->
     pure @@ int_of_string @@ s)
    <|> (char '0' >> pure 0)

let wsp = char ' ' <|> char '\n' <|> char '\t'
let sps0 = many wsp
let sps = many1 wsp

let lparen = char '(' << sps0
let rparen = sps0 >> char ')'

let formals =
  let dot = sps >> char '.' >> sps in
    begin
      (identifier >>= fun rest -> pure ([], Some rest))
      <|> (lparen >>= fun _ -> rparen >> pure ([], None))
      <|> begin
        lparen >>= fun _ ->
        sep_by1 sps identifier >>= fun names ->
        opt (dot >> identifier) >>= fun rest ->
        rparen >>
        pure (names, rest)
      end
    end <?> "parse error: formals"

(*
  [x1; x2; ...; xn-1; xn] -> ([x1; x2; ...; xn-1], xn)
*)
let unsnoc xs =
  let rec loop hs = function
    | [x] -> (List.rev hs, x)
    | (x::xs) -> loop (x::hs) xs
    | _ -> failwith "empty list"
  in loop [] xs

let kw_if = string "if"
let kw_lambda = string "lambda"
let kw_quote = string "quote"
let kw_set = string "set!"

let rec syn_lambda () =
  begin
    lparen >>= fun _ ->
    kw_lambda >>
    sps >> formals >>= fun formals ->
    sps >> sep_by1 sps (syn_sexp ()) >>= fun exprs ->
    rparen >>
    let (cmds, expr) = unsnoc exprs in
      match formals with
      | (args, None) -> pure @@ `Lam (args, cmds, expr)
      | ([], Some name) -> pure @@ `LamR (name, cmds, expr)
      | (args, Some rest) -> pure @@ `LamO (args, rest, cmds, expr)
  end <?> "parse error: lambda"
and syn_if () =
  begin
    lparen >>= fun _ ->
    kw_if >>
    sps >> syn_sexp () >>= fun c ->
    sps >> syn_sexp () >>= fun t ->
    opt (sps >> syn_sexp ()) <<
    rparen >>= function
    | Some e -> pure @@ `If (c, t, e)
    | None -> pure @@ `If1 (c, t)
  end <?> "parse error: if"
and syn_set () =
  begin
    lparen >>= fun _ ->
    kw_set >>
    sps >> identifier >>= fun name ->
    sps >> syn_sexp () >>= fun exp ->
    rparen >>
    pure @@ `Set (name, exp)
  end <?> "parse error: set!"
and syn_quotable () =
  syn_num ()
  <|> syn_bool ()
  <|> (lparen >> rparen >> pure @@ `K `Null)
  <|> (identifier >>= fun s -> pure @@ `K (`Symbol s))
and syn_quoted () =
  (* NB: you cannot quote pairs *)
  (char '\'' >> syn_quotable ())
  <|> begin
    lparen >>= fun _ ->
    kw_quote >> sps >> syn_quotable () << rparen
  end
and syn_app () =
  begin
    lparen >>= fun _ ->
    sep_by1 sps (syn_sexp ()) <<
    rparen >>= function
      | e::es -> pure @@ `App (e, es)
      | _ -> fail "parse error: app: should not occure"
  end <?> "parse error: app"
and syn_id () =
  identifier >>= (fun sym -> pure @@ `Id sym)
and syn_num () =
  number >>= fun n -> pure @@ `K (`Num n)
and syn_bool () =
  (string "#t" >> pure @@ `K `True)
  <|> (string "#f" >> pure @@ `K `False)
and syn_sexp () =
  syn_lambda ()
  <|> syn_if ()
  <|> syn_set ()
  <|> syn_quoted ()
  <|> syn_app ()
  <|> syn_num ()
  <|> syn_id ()
  <|> syn_bool ()

let sexp = sps0 >> (syn_sexp ())

let end_of_input = sps0 >> eof >>= (fun _ -> raise End_of_file)

let read chan  =
  let input = P.LazyList.of_char_channel chan in
    parse_llist (sexp <|> end_of_input) input

let read_from_string str =
  parse_string sexp str
