(* ========================================================================= *)
(* Oracle machines.                      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Library.                                          *)
(* ------------------------------------------------------------------------- *)
type ('a,'b)func =
   Empty
 | Leaf of int * ('a*'b)list
 | Branch of int * int * ('a,'b)func * ('a,'b)func;;

let applyd =
  let rec apply_listd l d x =
    match l with
      (a,b)::t -> let c = Pervasives.compare x a in
                  if c = 0 then b else if c > 0 then apply_listd t d x else d x
    | [] -> d x in
  fun f d x ->
    let k = Hashtbl.hash x in
    let rec look t =
      match t with
        Leaf(h,l) when h = k -> apply_listd l d x
      | Branch(p,b,l,r) when (k lxor p) land (b - 1) = 0
                -> look (if k land b = 0 then l else r)
      | _ -> d x in
    look f;;

let (|->),combine =
  let newbranch p1 t1 p2 t2 =
    let zp = p1 lxor p2 in
    let b = zp land (-zp) in
    let p = p1 land (b - 1) in
    if p1 land b = 0 then Branch(p,b,t1,t2)
    else Branch(p,b,t2,t1) in
  let rec define_list (x,y as xy) l =
    match l with
      (a,b as ab)::t ->
          let c = Pervasives.compare x a in
          if c = 0 then xy::t
          else if c < 0 then xy::l
          else ab::(define_list xy t)
    | [] -> [xy]
  and combine_list op z l1 l2 =
    match (l1,l2) with
      [],_ -> l2
    | _,[] -> l1
    | ((x1,y1 as xy1)::t1,(x2,y2 as xy2)::t2) ->
          let c = Pervasives.compare x1 x2 in
          if c < 0 then xy1::(combine_list op z t1 l2)
          else if c > 0 then xy2::(combine_list op z l1 t2) else
          let y = op y1 y2 and l = combine_list op z t1 t2 in
          if z(y) then l else (x1,y)::l in
  let (|->) x y =
    let k = Hashtbl.hash x in
    let rec upd t =
      match t with
        Empty -> Leaf (k,[x,y])
      | Leaf(h,l) ->
           if h = k then Leaf(h,define_list (x,y) l)
           else newbranch h t k (Leaf(k,[x,y]))
      | Branch(p,b,l,r) ->
          if k land (b - 1) <> p then newbranch p t k (Leaf(k,[x,y]))
          else if k land b = 0 then Branch(p,b,upd l,r)
          else Branch(p,b,l,upd r) in
    upd in
  let rec combine op z t1 t2 =
    match (t1,t2) with
      Empty,_ -> t2
    | _,Empty -> t1
    | Leaf(h1,l1),Leaf(h2,l2) ->
          if h1 = h2 then
            let l = combine_list op z l1 l2 in
            if l = [] then Empty else Leaf(h1,l)
          else newbranch h1 t1 h2 t2
    | (Leaf(k,lis) as lf),(Branch(p,b,l,r) as br) ->
          if k land (b - 1) = p then
            if k land b = 0 then
              (match combine op z lf l with
                 Empty -> r | l' -> Branch(p,b,l',r))
            else
              (match combine op z lf r with
                 Empty -> l | r' -> Branch(p,b,l,r'))
          else
            newbranch k lf p br
    | (Branch(p,b,l,r) as br),(Leaf(k,lis) as lf) ->
          if k land (b - 1) = p then
            if k land b = 0 then
              (match combine op z l lf with
                Empty -> r | l' -> Branch(p,b,l',r))
            else
              (match combine op z r lf with
                 Empty -> l | r' -> Branch(p,b,l,r'))
          else
            newbranch p br k lf
    | Branch(p1,b1,l1,r1),Branch(p2,b2,l2,r2) ->
          if b1 < b2 then
            if p2 land (b1 - 1) <> p1 then newbranch p1 t1 p2 t2
            else if p2 land b1 = 0 then
              (match combine op z l1 t2 with
                 Empty -> r1 | l -> Branch(p1,b1,l,r1))
            else
              (match combine op z r1 t2 with
                 Empty -> l1 | r -> Branch(p1,b1,l1,r))
          else if b2 < b1 then
            if p1 land (b2 - 1) <> p2 then newbranch p1 t1 p2 t2
            else if p1 land b2 = 0 then
              (match combine op z t1 l2 with
                 Empty -> r2 | l -> Branch(p2,b2,l,r2))
            else
              (match combine op z t1 r2 with
                 Empty -> l2 | r -> Branch(p2,b2,l2,r))
          else if p1 = p2 then
           (match (combine op z l1 l2,combine op z r1 r2) with
              (Empty,r) -> r | (l,Empty) -> l | (l,r) -> Branch(p1,b1,l,r))
          else
            newbranch p1 t1 p2 t2 in
  (|->),combine;;

let apply f = applyd f (fun x -> failwith "apply");;

let tryapplyd f a d = applyd f (fun x -> d) a;;

let defined f x = try apply f x; true with Failure _ -> false;;

let undefined = Empty;;

let ( ** ) = fun f g x -> f(g x);;

let rec funpow n f x =
  if n < 1 then x else funpow (n-1) f (f x);;

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

(* ------------------------------------------------------------------------- *)
(* Fundamental types.                                          *)
(* ------------------------------------------------------------------------- *)

type symbol = Blank | One;;

type direction = Left | Right;;

type tape = Tape of int * (int,symbol)func;;

(* ------------------------------------------------------------------------- *)
(* Oracle tapes are functions from integers to symbols                                          *)
(* ------------------------------------------------------------------------- *)

type config = Config of int * (int -> symbol) * tape * int;;

(* ------------------------------------------------------------------------- *)
(* Actions of Turing machines.                                          *)
(* ------------------------------------------------------------------------- *)

let look (Tape(r,f)) = tryapplyd f r Blank;;

let write s (Tape(r,f)) = Tape (r,(r |-> s) f);;

let move dir (Tape(r,f)) =
  let d = if dir = Left then -1 else 1 in
  Tape(r+d,f);;

(* ------------------------------------------------------------------------- *)
(* Keep running till we get to the specified stage or an undefined state.                           *)
(* ------------------------------------------------------------------------- *)

let rec run prog (Config (state, oracle, tape, use) as config) stage =
  let  position (Tape(r,f)) = r in
  let stt = (state, oracle(position tape), look tape) in
  if defined prog stt && stage <> 0 then
  let next_state, char, dir = apply prog stt in 
  let count_down x = x - 1 in
  let confirm_use x = if position (move dir tape) > x - 1 then
  position (move dir tape) +1 else x in
  run prog (Config(next_state, oracle, move dir (write char tape), confirm_use use)) (count_down stage)
  else config;;

(* ------------------------------------------------------------------------- *)
(* Tape with set of canonical input arguments.                               *)
(* ------------------------------------------------------------------------- *)

let input_tape args=
  let writen n =
  move Right ** write Blank ** funpow (n+1) (move Right ** write One) in
  let reset_head (Tape(r,f)) = (Tape(0,f)) in
  reset_head (itlist writen args (Tape(0,undefined)));;

(*let rec go_left (Tape(r,f) as tape) = if look tape = One then
  go_left (Tape(r - 1,f)) else *)

(* ------------------------------------------------------------------------- *)
(* Test whether the machine halts on the given configuration.                               *)
(* ------------------------------------------------------------------------- *)

let halted (Config (state, oracle, tape, use)) = 
  if state = 0 then true else false;;

(* ------------------------------------------------------------------------- *)
(* Read the result of the tape.                                              *)
(* ------------------------------------------------------------------------- *)

(*let rec output_tape tape config = 
  if not (halted config) then -1 else 
  let tape' = move Right tape in
  if look tape' = Blank then 0
  else 2 + (output_tape tape' config);;*)

let rec output_tape tape config = 
  if not (halted config) then -1 else 
  let tape' = move Right tape in
  if look tape' = Blank then 0
  else 1 + (output_tape tape' config);;

(* ------------------------------------------------------------------------- *)
(* Overall program execution.                                                *)
(* ------------------------------------------------------------------------- *)

let exec prog args oracle stage=
  let c = Config(1,oracle, input_tape args, 1) in
  let (Config(_, o, t, u) as config) = run prog c stage in
  let print_out x = if x = -1 then 
  print_string "Not halted" else Printf.printf "result = %d" x in
  print_newline (); print_out (output_tape t config); 
  print_newline (); Printf.printf "use = %d" u;;

(* ------------------------------------------------------------------------- *)
(* Example program (current state, oracle, symbol -> next state, action, direction).                                              *)
(* ------------------------------------------------------------------------- *)

let oracle x = if x = 2 then One else Blank;;

let prog = itlist (fun m -> m)
[(1,One,One) |-> (1, One,Right); (1,Blank,One) |-> (1, One,Right);
(1, One, Blank) |-> (2, Blank, Left); (1, Blank, Blank) |-> (2, Blank, Left);
(2,One, One) |-> (3,Blank,Left); (2,Blank, One) |-> (4,Blank,Left);
(3,One, One) |-> (3, One,Left); (3,Blank, One) |-> (3,One,Left);
(3,One, Blank) |-> (5, Blank,Right); (3,Blank, Blank) |-> (5, Blank,Right);
(5,One, One) |-> (0, One,Left); (5,Blank, One) |-> (0, One,Left);
(4,One, One) |-> (4,Blank,Left); (4,Blank, One) |-> (4,Blank,Left);
(4,One, Blank) |-> (0,Blank,Right); (4,Blank, Blank) |-> (0,Blank,Right);]
undefined;;

exec prog [2] oracle 100;;

let var(s) = expr
(*Debugging*)

(*let tconfig = Config(0,testo, input_tape [1], 1);;

output_tape (input_tape [1]) ttape;;

let ttape = Tape(0, undefined);;

write One ttape;;

output_tape ttape tconfig;;*)

(*let testo x = if true then One else Blank;;

let prog_test = itlist (fun m -> m)
[(1,One,One) |-> (2, One,Right);
(2, One, Blank) |-> (3,One,Right);
(3,One, Blank) |-> (3,Blank,Left);
(3,One, One) |-> (4,One,Left);
(4,One, One) |-> (0,One,Left)]
undefined;;

exec prog_test [0] testo 10;;*)
