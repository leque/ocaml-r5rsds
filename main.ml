open Util

let rec repl () =
  print_string "> ";
  flush stdout;
  begin
    try
      let line = read_line () in
        print_endline
          @@ R5rsds.eval_to_string
          @@ SchemeParser.read_from_string line
    with
    | R5rsds.Runtime_error (msg, objs) ->
        print_string ("*** ERROR: " ^ msg);
        begin
          match objs with
          | [] -> print_newline ()
          | ss ->
              Printf.fprintf stdout ": (%s)\n" (String.concat " " ss)
        end
    | P.ParseError msg ->
        print_endline ("parse error: " ^ msg)
    | End_of_file -> exit 0
  end;
  repl ()

let _ = repl ()
