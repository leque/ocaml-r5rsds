open Util

exception ParseError of string

module Parser = struct
  module type Spec = sig
    type input
    type state
    val error_message : state -> string -> string
  end

  module Make(S : Spec) = struct
    type state = S.state

    type input = S.input

    type 'a t =
        state -> input -> (state * string, 'a * state * input) either

    let run_parser : 'a t -> state -> input -> 'a =
      fun p state input ->
        match p state input with
        | Right (res, state, input) -> res
        | Left (state, msg) -> raise (ParseError (S.error_message state msg))

    let pure : 'a -> 'a t =
      fun x ->
        fun state input ->
          Right (x, state, input)

    let put_state : state -> unit t =
      fun st ->
        fun state input ->
          Right ((), st, input)

    let get_state : state t =
      fun state input ->
        Right (state, state, input)

    let update_state : (state -> state) -> unit t =
      fun f ->
        fun state input ->
          Right ((), f state, input)

    let fail : string -> 'a t =
      fun msg ->
        fun state input ->
          Left (state, msg)

    let (>>=) : 'a t -> ('a -> 'b t) -> 'b t =
      fun p1 f ->
        fun state input ->
          match p1 state input with
          | Right (x, st, rest) -> f x st rest
          | Left _ as res -> res

    let (<|>) : 'a t -> 'a t -> 'a t =
      fun p1 p2 ->
        fun state input ->
          match p1 state input with
          | Right _ as res -> res
          | Left _ -> p2 state input

    let (<?>) : 'a t -> string -> 'a t =
      fun p msg ->
        fun state input ->
          match p state input with
          | Right _ as res -> res
          | Left (state, _) -> Left (state, msg)

    let (>>) p1 p2 =
      p1 >>= (fun _ -> p2)

    let (<<) p1 p2 =
      p1 >>= (fun x -> p2 >> (pure x))

    let (<$>) f p =
      p >>= (fun x -> pure (f x))

    let (<*>) p1 p2 =
      p1 >>= (fun f -> p2 >>= (fun x -> pure (f x)))

    let opt p =
      (fun x -> Some x) <$> p
      <|> pure None

    let rec count n p =
      if n = 0 then
        pure []
      else
        List.cons <$> p <*> count (n - 1) p

    let rec many p =
      p >>= (fun x -> List.cons x <$> many p)
      <|> pure []

    let many1 p =
      List.cons <$> p <*> many p

    let between op cl p =
      op >> p << cl

    let surround p q =
      between p p q

    let sep_by1 sep p =
      List.cons <$> p <*> many (sep >> p)

    let sep_by sep p = sep_by1 sep p <|> pure []
  end
end

module LazyList = struct
  type 'a t = Nil | Cons of 'a * 'a t Lazy.t

  let hd = function
    | Nil -> failwith "empty list"
    | Cons (x, _) -> x

  let tl = function
    | Nil -> failwith "empty list"
    | Cons (_, lazy xs) -> xs

  let rec of_list = function
    | [] -> Nil
    | (x::xs) ->
        Cons (x, lazy (of_list xs))

  let of_string str =
    let len = String.length str in
    let rec loop i =
      if i >= len then
        Nil
      else
        Cons (String.get str i, lazy (loop (i + 1)))
    in loop 0

  let rec from_generator gen =
    match gen () with
    | None -> Nil
    | Some x -> Cons (x, lazy (from_generator gen))

  let of_char_channel ch =
    from_generator (fun () ->
                      try
                        Some (input_char ch)
                      with
                      | End_of_file -> None)
end

module CharParser = struct
  include Parser.Make(
    struct
      type input = char LazyList.t
      type state = int * char list * input
      let error_message (pos, _, _) msg =
        Printf.sprintf "%d: %s" pos msg
    end
  )

  let eof : unit t = fun state input ->
    match input with
    | LazyList.Nil ->
        Right ((), state, input)
    | LazyList.Cons (_, _) ->
        Left (state, "not eof")

  let satisfy p : char t = fun state input ->
    match state, input with
    | state, LazyList.Nil ->
        Left (state, "end of input")
    | (n, cs, _) as state, LazyList.Cons (c, rest) ->
        if p c then
          let rest = Lazy.force rest in
            Right (c, (n + 1, c::cs, rest), rest)
        else
          Left (state, "satisfy")

  let one_of xs = satisfy (fun c -> List.mem c xs)

  let none_of xs = satisfy (fun c -> not @@ List.mem c xs)

  let one_of_s str = satisfy (String.contains str)

  let none_of_s str = satisfy (complement @@ String.contains str)

  let char c =
    satisfy (fun d -> c = d)
    <?> (Printf.sprintf "char: `%c'" c)

  let any_char =
    satisfy (fun _ -> true)

  let string str =
    let len = String.length str in
    let rec loop i =
      if i >= len then
        pure str
      else
        char (String.get str i) >>= fun _ -> loop (i + 1)
    in loop 0 <?> (Printf.sprintf "string: %s" str)

  let parse_llist (p : 'a t) input =
    run_parser p (0, [], input) input

  let parse_string (p : 'a t) str =
    let input = LazyList.of_string str in
      parse_llist p input

  let parse_file (p : 'a t) file =
    protect (open_in file)
      (fun ch ->
         let input = LazyList.of_char_channel ch in
           parse_llist p input)
      ~finally:close_in
end
