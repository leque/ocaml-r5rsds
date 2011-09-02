type ('a, 'b) either = Left of 'a | Right of 'b

let (@@) f x = f x

let complement f x = not @@ f x

let maybe default = function
  | Some x -> x
  | None -> default

let protect x f ~(finally : _ -> unit) =
  try
    let r = f x in
      finally x; r
  with exc -> finally x; raise exc

module S = struct
  include String

  let of_char c =
    String.make 1 c

  let of_list cs =
    let buf = Buffer.create 32 in
      List.iter (Buffer.add_char buf) cs;
      Buffer.contents buf
end

module String = S

module L = struct
  include List

  let pure x = [x]

  let cons x xs = x::xs
end

module List = L
