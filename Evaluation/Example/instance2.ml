
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _ :: l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type _ _ =
  compareSpec2Type

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

(** val add : nat -> nat -> nat **)

let rec add n0 m =
  match n0 with
  | O -> m
  | S p -> S (add p m)

(** val sub : nat -> nat -> nat **)

let rec sub n0 m =
  match n0 with
  | O -> n0
  | S k -> (match m with
            | O -> n0
            | S l -> sub k l)

(** val max : nat -> nat -> nat **)

let rec max n0 m =
  match n0 with
  | O -> m
  | S n' -> (match m with
             | O -> n0
             | S m' -> S (max n' m'))

(** val min : nat -> nat -> nat **)

let rec min n0 m =
  match n0 with
  | O -> O
  | S n' -> (match m with
             | O -> O
             | S m' -> S (min n' m'))

(** val tail_add : nat -> nat -> nat **)

let rec tail_add n0 m =
  match n0 with
  | O -> m
  | S n1 -> tail_add n1 (S m)

(** val tail_addmul : nat -> nat -> nat -> nat **)

let rec tail_addmul r n0 m =
  match n0 with
  | O -> r
  | S n1 -> tail_addmul (tail_add m r) n1 m

(** val tail_mul : nat -> nat -> nat **)

let tail_mul n0 m =
  tail_addmul O n0 m

(** val of_uint_acc : uint -> nat -> nat **)

let rec of_uint_acc d acc =
  match d with
  | Nil -> acc
  | D0 d0 ->
    of_uint_acc d0 (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)
  | D1 d0 ->
    of_uint_acc d0 (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))
  | D2 d0 ->
    of_uint_acc d0 (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))
  | D3 d0 ->
    of_uint_acc d0 (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))
  | D4 d0 ->
    of_uint_acc d0 (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))
  | D5 d0 ->
    of_uint_acc d0 (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))
  | D6 d0 ->
    of_uint_acc d0 (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))))
  | D7 d0 ->
    of_uint_acc d0 (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))))
  | D8 d0 ->
    of_uint_acc d0 (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))))))
  | D9 d0 ->
    of_uint_acc d0 (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))))))

(** val of_uint : uint -> nat **)

let of_uint d =
  of_uint_acc d O

module type DecidableTypeOrig =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type EqLtLe =
 sig
  type t
 end

module type OrderedType =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module type OrderedType' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module OT_to_Full =
 functor (O:OrderedType') ->
 struct
  type t = O.t

  (** val compare : t -> t -> comparison **)

  let compare =
    O.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    O.eq_dec
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module OT_to_OrderTac =
 functor (OT:OrderedType) ->
 struct
  module OTF = OT_to_Full(OT)

  module TO =
   struct
    type t = OTF.t

    (** val compare : t -> t -> comparison **)

    let compare =
      OTF.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      OTF.eq_dec
   end
 end

module OrderedTypeFacts =
 functor (O:OrderedType') ->
 struct
  module OrderTac = OT_to_OrderTac(O)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    let c = compSpec2Type x y (O.compare x y) in
    (match c with
     | CompLtT -> true
     | _ -> false)

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n0 m =
    match n0 with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n' -> (match m with
               | O -> false
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n0 m =
    match n0 with
    | O -> true
    | S n' -> (match m with
               | O -> false
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n0 m =
    leb (S n0) m
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t0 -> (f a) :: (map f t0)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t0 -> f b (fold_right f a0 t0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)

  (** val eq_dec : positive -> positive -> bool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> false)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> false)
    | XH -> (match x0 with
             | XH -> true
             | _ -> false)
 end

module N =
 struct
  (** val of_nat : nat -> n **)

  let of_nat = function
  | O -> N0
  | S n' -> Npos (Pos.of_succ_nat n')
 end

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : positive -> char **)

let ascii_of_pos =
  let rec loop n0 p =
    match n0 with
    | O -> zero
    | S n' ->
      (match p with
       | XI p' -> shift true (loop n' p')
       | XO p' -> shift false (loop n' p')
       | XH -> one)
  in loop (S (S (S (S (S (S (S (S O))))))))

(** val ascii_of_N : n -> char **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : nat -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let rec eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> false)

  (** val max : z -> z -> z **)

  let max n0 m =
    match compare n0 m with
    | Lt -> m
    | _ -> n0

  (** val eq_dec : z -> z -> bool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos x0 -> (match y with
                  | Zpos p0 -> Pos.eq_dec x0 p0
                  | _ -> false)
    | Zneg x0 -> (match y with
                  | Zneg p0 -> Pos.eq_dec x0 p0
                  | _ -> false)
 end

(** val list_ascii_of_string : char list -> char list **)

let rec list_ascii_of_string = function
| [] -> []
| ch::s0 -> ch :: (list_ascii_of_string s0)

type 'x compare0 =
| LT
| EQ
| GT

module type Coq_OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module Coq_OrderedTypeFacts =
 functor (O:Coq_OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> bool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> true
    | _ -> false

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    if eq_dec x y then true else false
 end

module KeyOrderedType =
 functor (O:Coq_OrderedType) ->
 struct
  module MO = Coq_OrderedTypeFacts(O)
 end

module type UsualOrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> bool
 end

module type DecidableType =
 DecidableTypeOrig

module type WS =
 sig
  module E :
   DecidableType

  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val eq_dec : t -> t -> bool

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option
 end

module WFacts_fun =
 functor (E:DecidableType) ->
 functor (M:sig
  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val eq_dec : t -> t -> bool

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option
 end) ->
 struct
  (** val eqb : E.t -> E.t -> bool **)

  let eqb x y =
    if E.eq_dec x y then true else false
 end

module WFacts =
 functor (M:WS) ->
 WFacts_fun(M.E)(M)

module Facts = WFacts

module MakeListOrdering =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module type OrderedTypeOrig =
 Coq_OrderedType

module Update_OT =
 functor (O:OrderedTypeOrig) ->
 struct
  type t = O.t

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    O.eq_dec

  (** val compare : O.t -> O.t -> comparison **)

  let compare x y =
    match O.compare x y with
    | LT -> Lt
    | EQ -> Eq
    | GT -> Gt
 end

module type Int =
 sig
  type t

  val i2z : t -> z

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int =
 struct
  type t = z

  (** val _0 : z **)

  let _0 =
    Z0

  (** val _1 : z **)

  let _1 =
    Zpos XH

  (** val _2 : z **)

  let _2 =
    Zpos (XO XH)

  (** val _3 : z **)

  let _3 =
    Zpos (XI XH)

  (** val add : z -> z -> z **)

  let add =
    Z.add

  (** val opp : z -> z **)

  let opp =
    Z.opp

  (** val sub : z -> z -> z **)

  let sub =
    Z.sub

  (** val mul : z -> z -> z **)

  let mul =
    Z.mul

  (** val max : z -> z -> z **)

  let max =
    Z.max

  (** val eqb : z -> z -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : z -> z -> bool **)

  let ltb =
    Z.ltb

  (** val leb : z -> z -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : z -> z -> bool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : z -> z -> bool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in if b then true else false

  (** val ge_lt_dec : z -> z -> bool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in if b then false else true

  (** val i2z : t -> z **)

  let i2z n0 =
    n0
 end

module MakeRaw =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  type elt = X.t

  type tree =
  | Leaf
  | Node of I.t * tree * X.t * tree

  (** val empty : tree **)

  let empty =
    Leaf

  (** val is_empty : tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _) -> false

  (** val mem : X.t -> tree -> bool **)

  let rec mem x = function
  | Leaf -> false
  | Node (_, l, k, r) ->
    (match X.compare x k with
     | Eq -> true
     | Lt -> mem x l
     | Gt -> mem x r)

  (** val min_elt : tree -> elt option **)

  let rec min_elt = function
  | Leaf -> None
  | Node (_, l, x, _) ->
    (match l with
     | Leaf -> Some x
     | Node (_, _, _, _) -> min_elt l)

  (** val max_elt : tree -> elt option **)

  let rec max_elt = function
  | Leaf -> None
  | Node (_, _, x, r) ->
    (match r with
     | Leaf -> Some x
     | Node (_, _, _, _) -> max_elt r)

  (** val choose : tree -> elt option **)

  let choose =
    min_elt

  (** val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1 **)

  let rec fold f t0 base =
    match t0 with
    | Leaf -> base
    | Node (_, l, x, r) -> fold f r (f x (fold f l base))

  (** val elements_aux : X.t list -> tree -> X.t list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (_, l, x, r) -> elements_aux (x :: (elements_aux acc r)) l

  (** val elements : tree -> X.t list **)

  let elements =
    elements_aux []

  (** val rev_elements_aux : X.t list -> tree -> X.t list **)

  let rec rev_elements_aux acc = function
  | Leaf -> acc
  | Node (_, l, x, r) -> rev_elements_aux (x :: (rev_elements_aux acc l)) r

  (** val rev_elements : tree -> X.t list **)

  let rev_elements =
    rev_elements_aux []

  (** val cardinal : tree -> nat **)

  let rec cardinal = function
  | Leaf -> O
  | Node (_, l, _, r) -> S (add (cardinal l) (cardinal r))

  (** val maxdepth : tree -> nat **)

  let rec maxdepth = function
  | Leaf -> O
  | Node (_, l, _, r) -> S (max (maxdepth l) (maxdepth r))

  (** val mindepth : tree -> nat **)

  let rec mindepth = function
  | Leaf -> O
  | Node (_, l, _, r) -> S (min (mindepth l) (mindepth r))

  (** val for_all : (elt -> bool) -> tree -> bool **)

  let rec for_all f = function
  | Leaf -> true
  | Node (_, l, x, r) ->
    if if f x then for_all f l else false then for_all f r else false

  (** val exists_ : (elt -> bool) -> tree -> bool **)

  let rec exists_ f = function
  | Leaf -> false
  | Node (_, l, x, r) ->
    if if f x then true else exists_ f l then true else exists_ f r

  type enumeration =
  | End
  | More of elt * tree * enumeration

  (** val cons : tree -> enumeration -> enumeration **)

  let rec cons s e =
    match s with
    | Leaf -> e
    | Node (_, l, x, r) -> cons l (More (x, r, e))

  (** val compare_more :
      X.t -> (enumeration -> comparison) -> enumeration -> comparison **)

  let compare_more x1 cont = function
  | End -> Gt
  | More (x2, r2, e3) ->
    (match X.compare x1 x2 with
     | Eq -> cont (cons r2 e3)
     | x -> x)

  (** val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison **)

  let rec compare_cont s1 cont e2 =
    match s1 with
    | Leaf -> cont e2
    | Node (_, l1, x1, r1) ->
      compare_cont l1 (compare_more x1 (compare_cont r1 cont)) e2

  (** val compare_end : enumeration -> comparison **)

  let compare_end = function
  | End -> Eq
  | More (_, _, _) -> Lt

  (** val compare : tree -> tree -> comparison **)

  let compare s1 s2 =
    compare_cont s1 compare_end (cons s2 End)

  (** val equal : tree -> tree -> bool **)

  let equal s1 s2 =
    match compare s1 s2 with
    | Eq -> true
    | _ -> false

  (** val subsetl : (tree -> bool) -> X.t -> tree -> bool **)

  let rec subsetl subset_l1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (_, l2, x2, r2) ->
    (match X.compare x1 x2 with
     | Eq -> subset_l1 l2
     | Lt -> subsetl subset_l1 x1 l2
     | Gt -> if mem x1 r2 then subset_l1 s2 else false)

  (** val subsetr : (tree -> bool) -> X.t -> tree -> bool **)

  let rec subsetr subset_r1 x1 s2 = match s2 with
  | Leaf -> false
  | Node (_, l2, x2, r2) ->
    (match X.compare x1 x2 with
     | Eq -> subset_r1 r2
     | Lt -> if mem x1 l2 then subset_r1 s2 else false
     | Gt -> subsetr subset_r1 x1 r2)

  (** val subset : tree -> tree -> bool **)

  let rec subset s1 s2 =
    match s1 with
    | Leaf -> true
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> false
       | Node (_, l2, x2, r2) ->
         (match X.compare x1 x2 with
          | Eq -> if subset l1 l2 then subset r1 r2 else false
          | Lt -> if subsetl (subset l1) x1 l2 then subset r1 s2 else false
          | Gt -> if subsetr (subset r1) x1 r2 then subset l1 s2 else false))

  type t = tree

  (** val height : t -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (h, _, _, _) -> h

  (** val singleton : X.t -> tree **)

  let singleton x =
    Node (I._1, Leaf, x, Leaf)

  (** val create : t -> X.t -> t -> tree **)

  let create l x r =
    Node ((I.add (I.max (height l) (height r)) I._1), l, x, r)

  (** val assert_false : t -> X.t -> t -> tree **)

  let assert_false =
    create

  (** val bal : t -> X.t -> t -> tree **)

  let bal l x r =
    let hl = height l in
    let hr = height r in
    if I.ltb (I.add hr I._2) hl
    then (match l with
          | Leaf -> assert_false l x r
          | Node (_, ll, lx, lr) ->
            if I.leb (height lr) (height ll)
            then create ll lx (create lr x r)
            else (match lr with
                  | Leaf -> assert_false l x r
                  | Node (_, lrl, lrx, lrr) ->
                    create (create ll lx lrl) lrx (create lrr x r)))
    else if I.ltb (I.add hl I._2) hr
         then (match r with
               | Leaf -> assert_false l x r
               | Node (_, rl, rx, rr) ->
                 if I.leb (height rl) (height rr)
                 then create (create l x rl) rx rr
                 else (match rl with
                       | Leaf -> assert_false l x r
                       | Node (_, rll, rlx, rlr) ->
                         create (create l x rll) rlx (create rlr rx rr)))
         else create l x r

  (** val add : X.t -> tree -> tree **)

  let rec add x = function
  | Leaf -> Node (I._1, Leaf, x, Leaf)
  | Node (h, l, y, r) ->
    (match X.compare x y with
     | Eq -> Node (h, l, y, r)
     | Lt -> bal (add x l) y r
     | Gt -> bal l y (add x r))

  (** val join : tree -> elt -> t -> t **)

  let rec join l = match l with
  | Leaf -> add
  | Node (lh, ll, lx, lr) ->
    (fun x ->
      let rec join_aux r = match r with
      | Leaf -> add x l
      | Node (rh, rl, rx, rr) ->
        if I.ltb (I.add rh I._2) lh
        then bal ll lx (join lr x r)
        else if I.ltb (I.add lh I._2) rh
             then bal (join_aux rl) rx rr
             else create l x r
      in join_aux)

  (** val remove_min : tree -> elt -> t -> t * elt **)

  let rec remove_min l x r =
    match l with
    | Leaf -> (r, x)
    | Node (_, ll, lx, lr) ->
      let (l', m) = remove_min ll lx lr in ((bal l' x r), m)

  (** val merge : tree -> tree -> tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, l2, x2, r2) ->
         let (s2', m) = remove_min l2 x2 r2 in bal s1 m s2')

  (** val remove : X.t -> tree -> tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (_, l, y, r) ->
    (match X.compare x y with
     | Eq -> merge l r
     | Lt -> bal (remove x l) y r
     | Gt -> bal l y (remove x r))

  (** val concat : tree -> tree -> tree **)

  let concat s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, l2, x2, r2) ->
         let (s2', m) = remove_min l2 x2 r2 in join s1 m s2')

  type triple = { t_left : t; t_in : bool; t_right : t }

  (** val t_left : triple -> t **)

  let t_left t0 =
    t0.t_left

  (** val t_in : triple -> bool **)

  let t_in t0 =
    t0.t_in

  (** val t_right : triple -> t **)

  let t_right t0 =
    t0.t_right

  (** val split : X.t -> tree -> triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_in = false; t_right = Leaf }
  | Node (_, l, y, r) ->
    (match X.compare x y with
     | Eq -> { t_left = l; t_in = true; t_right = r }
     | Lt ->
       let { t_left = ll; t_in = b; t_right = rl } = split x l in
       { t_left = ll; t_in = b; t_right = (join rl y r) }
     | Gt ->
       let { t_left = rl; t_in = b; t_right = rr } = split x r in
       { t_left = (join l y rl); t_in = b; t_right = rr })

  (** val inter : tree -> tree -> tree **)

  let rec inter s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> Leaf
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
         if pres
         then join (inter l1 l2') x1 (inter r1 r2')
         else concat (inter l1 l2') (inter r1 r2'))

  (** val diff : tree -> tree -> tree **)

  let rec diff s1 s2 =
    match s1 with
    | Leaf -> Leaf
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = pres; t_right = r2' } = split x1 s2 in
         if pres
         then concat (diff l1 l2') (diff r1 r2')
         else join (diff l1 l2') x1 (diff r1 r2'))

  (** val union : tree -> tree -> tree **)

  let rec union s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, l1, x1, r1) ->
      (match s2 with
       | Leaf -> s1
       | Node (_, _, _, _) ->
         let { t_left = l2'; t_in = _; t_right = r2' } = split x1 s2 in
         join (union l1 l2') x1 (union r1 r2'))

  (** val filter : (elt -> bool) -> tree -> tree **)

  let rec filter f = function
  | Leaf -> Leaf
  | Node (_, l, x, r) ->
    let l' = filter f l in
    let r' = filter f r in if f x then join l' x r' else concat l' r'

  (** val partition : (elt -> bool) -> t -> t * t **)

  let rec partition f = function
  | Leaf -> (Leaf, Leaf)
  | Node (_, l, x, r) ->
    let (l1, l2) = partition f l in
    let (r1, r2) = partition f r in
    if f x
    then ((join l1 x r1), (concat l2 r2))
    else ((concat l1 r1), (join l2 x r2))

  (** val ltb_tree : X.t -> tree -> bool **)

  let rec ltb_tree x = function
  | Leaf -> true
  | Node (_, l, y, r) ->
    (match X.compare x y with
     | Gt -> (&&) (ltb_tree x l) (ltb_tree x r)
     | _ -> false)

  (** val gtb_tree : X.t -> tree -> bool **)

  let rec gtb_tree x = function
  | Leaf -> true
  | Node (_, l, y, r) ->
    (match X.compare x y with
     | Lt -> (&&) (gtb_tree x l) (gtb_tree x r)
     | _ -> false)

  (** val isok : tree -> bool **)

  let rec isok = function
  | Leaf -> true
  | Node (_, l, x, r) ->
    (&&) ((&&) ((&&) (isok l) (isok r)) (ltb_tree x l)) (gtb_tree x r)

  module MX = OrderedTypeFacts(X)

  type coq_R_min_elt =
  | R_min_elt_0 of tree
  | R_min_elt_1 of tree * I.t * tree * X.t * tree
  | R_min_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * X.t *
     tree * elt option * coq_R_min_elt

  type coq_R_max_elt =
  | R_max_elt_0 of tree
  | R_max_elt_1 of tree * I.t * tree * X.t * tree
  | R_max_elt_2 of tree * I.t * tree * X.t * tree * I.t * tree * X.t *
     tree * elt option * coq_R_max_elt

  module L = MakeListOrdering(X)

  (** val flatten_e : enumeration -> elt list **)

  let rec flatten_e = function
  | End -> []
  | More (x, t0, r) -> x :: (app (elements t0) (flatten_e r))

  type coq_R_bal =
  | R_bal_0 of t * X.t * t
  | R_bal_1 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_2 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_3 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * X.t * tree
  | R_bal_4 of t * X.t * t
  | R_bal_5 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_6 of t * X.t * t * I.t * tree * X.t * tree
  | R_bal_7 of t * X.t * t * I.t * tree * X.t * tree * I.t * tree * X.t * tree
  | R_bal_8 of t * X.t * t

  type coq_R_remove_min =
  | R_remove_min_0 of tree * elt * t
  | R_remove_min_1 of tree * elt * t * I.t * tree * X.t * tree * (t * elt)
     * coq_R_remove_min * t * elt

  type coq_R_merge =
  | R_merge_0 of tree * tree
  | R_merge_1 of tree * tree * I.t * tree * X.t * tree
  | R_merge_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree *
     X.t * tree * t * elt

  type coq_R_concat =
  | R_concat_0 of tree * tree
  | R_concat_1 of tree * tree * I.t * tree * X.t * tree
  | R_concat_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree *
     X.t * tree * t * elt

  type coq_R_inter =
  | R_inter_0 of tree * tree
  | R_inter_1 of tree * tree * I.t * tree * X.t * tree
  | R_inter_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree *
     X.t * tree * t * bool * t * tree * coq_R_inter * tree * coq_R_inter
  | R_inter_3 of tree * tree * I.t * tree * X.t * tree * I.t * tree *
     X.t * tree * t * bool * t * tree * coq_R_inter * tree * coq_R_inter

  type coq_R_diff =
  | R_diff_0 of tree * tree
  | R_diff_1 of tree * tree * I.t * tree * X.t * tree
  | R_diff_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree *
     X.t * tree * t * bool * t * tree * coq_R_diff * tree * coq_R_diff
  | R_diff_3 of tree * tree * I.t * tree * X.t * tree * I.t * tree *
     X.t * tree * t * bool * t * tree * coq_R_diff * tree * coq_R_diff

  type coq_R_union =
  | R_union_0 of tree * tree
  | R_union_1 of tree * tree * I.t * tree * X.t * tree
  | R_union_2 of tree * tree * I.t * tree * X.t * tree * I.t * tree *
     X.t * tree * t * bool * t * tree * coq_R_union * tree * coq_R_union
 end

module IntMake =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  module Raw = MakeRaw(I)(X)

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> comparison **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x s =
    Raw.mem x (this s)

  (** val add : elt -> t -> t **)

  let add x s =
    Raw.add x (this s)

  (** val remove : elt -> t -> t **)

  let remove x s =
    Raw.remove x (this s)

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> nat **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    Raw.filter f (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition f s =
    let p = Raw.partition f (this s) in ((fst p), (snd p))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in if b then true else false

  (** val compare : t -> t -> comparison **)

  let compare s s' =
    Raw.compare (this s) (this s')

  (** val min_elt : t -> elt option **)

  let min_elt s =
    Raw.min_elt (this s)

  (** val max_elt : t -> elt option **)

  let max_elt s =
    Raw.max_elt (this s)
 end

module Coq_IntMake =
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct
  module X' = Update_OT(X)

  module MSet = IntMake(I)(X')

  type elt = X.t

  type t = MSet.t

  (** val empty : t **)

  let empty =
    MSet.empty

  (** val is_empty : t -> bool **)

  let is_empty =
    MSet.is_empty

  (** val mem : elt -> t -> bool **)

  let mem =
    MSet.mem

  (** val add : elt -> t -> t **)

  let add =
    MSet.add

  (** val singleton : elt -> t **)

  let singleton =
    MSet.singleton

  (** val remove : elt -> t -> t **)

  let remove =
    MSet.remove

  (** val union : t -> t -> t **)

  let union =
    MSet.union

  (** val inter : t -> t -> t **)

  let inter =
    MSet.inter

  (** val diff : t -> t -> t **)

  let diff =
    MSet.diff

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    MSet.eq_dec

  (** val equal : t -> t -> bool **)

  let equal =
    MSet.equal

  (** val subset : t -> t -> bool **)

  let subset =
    MSet.subset

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold =
    MSet.fold

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all =
    MSet.for_all

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ =
    MSet.exists_

  (** val filter : (elt -> bool) -> t -> t **)

  let filter =
    MSet.filter

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition =
    MSet.partition

  (** val cardinal : t -> nat **)

  let cardinal =
    MSet.cardinal

  (** val elements : t -> elt list **)

  let elements =
    MSet.elements

  (** val choose : t -> elt option **)

  let choose =
    MSet.choose

  module MF =
   struct
    (** val eqb : X.t -> X.t -> bool **)

    let eqb x y =
      if MSet.E.eq_dec x y then true else false
   end

  (** val min_elt : t -> elt option **)

  let min_elt =
    MSet.min_elt

  (** val max_elt : t -> elt option **)

  let max_elt =
    MSet.max_elt

  (** val compare : t -> t -> t compare0 **)

  let compare s s' =
    let c = compSpec2Type s s' (MSet.compare s s') in
    (match c with
     | CompEqT -> EQ
     | CompLtT -> LT
     | CompGtT -> GT)

  module E =
   struct
    type t = X.t

    (** val compare : t -> t -> t compare0 **)

    let compare =
      X.compare

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      X.eq_dec
   end
 end

module Make =
 functor (X:Coq_OrderedType) ->
 Coq_IntMake(Z_as_Int)(X)

module type Coq_WS =
 sig
  module E :
   DecidableType

  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Raw =
 functor (X:Coq_OrderedType) ->
 struct
  module MX = Coq_OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  (** val empty : 'a1 t **)

  let empty =
    []

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | [] -> false
  | p :: l ->
    let (k', _) = p in
    (match X.compare k k' with
     | LT -> false
     | EQ -> true
     | GT -> mem k l)

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_mem

  (** val coq_R_mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rect k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rec k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rec k f f0 f1 f2 l _res r0)

  (** val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec mem_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t0, e) = p in
       let f7 = f6 t0 e l __ in
       let f8 = fun _ _ -> let hrec = mem_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match X.compare k t0 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let mem_rec =
    mem_rect

  (** val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem **)

  let coq_R_mem_correct k s _res =
    Obj.magic mem_rect k (fun y _ _ _ -> R_mem_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_mem_3 (y, y0, y1, y2, (mem k y2),
      (y6 (mem k y2) __))) s _res __

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | [] -> None
  | p :: s' ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x
     | GT -> find k s')

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
     * 'elt coq_R_find

  (** val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rect k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s') -> f1 s k' x s' __ __ __
  | R_find_3 (s, k', x, s', _res, r0) ->
    f2 s k' x s' __ __ __ _res r0 (coq_R_find_rect k f f0 f1 f2 s' _res r0)

  (** val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rec k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s') -> f1 s k' x s' __ __ __
  | R_find_3 (s, k', x, s', _res, r0) ->
    f2 s k' x s' __ __ __ _res r0 (coq_R_find_rec k f f0 f1 f2 s' _res r0)

  (** val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec find_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t0, e) = p in
       let f7 = f6 t0 e l __ in
       let f8 = fun _ _ ->
         let hrec = find_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match X.compare k t0 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let find_rec =
    find_rect

  (** val coq_R_find_correct :
      key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find **)

  let coq_R_find_correct k s _res =
    Obj.magic find_rect k (fun y _ _ _ -> R_find_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_find_3 (y, y0, y1, y2, (find k y2),
      (y6 (find k y2) __))) s _res __

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x s = match s with
  | [] -> (k, x) :: []
  | p :: l ->
    let (k', y) = p in
    (match X.compare k k' with
     | LT -> (k, x) :: s
     | EQ -> (k, x) :: l
     | GT -> (k', y) :: (add k x l))

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_add

  (** val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rect k x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rect k x f f0 f1 f2 l _res r0)

  (** val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rec k x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rec k x f f0 f1 f2 l _res r0)

  (** val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec add_rect k x f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t0, e) = p in
       let f7 = f6 t0 e l __ in
       let f8 = fun _ _ ->
         let hrec = add_rect k x f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match X.compare k t0 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let add_rec =
    add_rect

  (** val coq_R_add_correct :
      key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add **)

  let coq_R_add_correct k x s _res =
    add_rect k x (fun y _ _ _ -> R_add_0 y) (fun y y0 y1 y2 _ _ _ _ _ ->
      R_add_1 (y, y0, y1, y2)) (fun y y0 y1 y2 _ _ _ _ _ -> R_add_2 (y, y0,
      y1, y2)) (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_add_3 (y, y0, y1, y2,
      (add k x y2), (y6 (add k x y2) __))) s _res __

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | [] -> []
  | p :: l ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> (k', x) :: (remove k l))

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_remove

  (** val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rect k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l) -> f1 s k' x l __ __ __
  | R_remove_3 (s, k', x, l, _res, r0) ->
    f2 s k' x l __ __ __ _res r0 (coq_R_remove_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rec k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l) -> f1 s k' x l __ __ __
  | R_remove_3 (s, k', x, l, _res, r0) ->
    f2 s k' x l __ __ __ _res r0 (coq_R_remove_rec k f f0 f1 f2 l _res r0)

  (** val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec remove_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | [] -> f3 __
     | p :: l ->
       let (t0, e) = p in
       let f7 = f6 t0 e l __ in
       let f8 = fun _ _ ->
         let hrec = remove_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match X.compare k t0 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let remove_rec =
    remove_rect

  (** val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove **)

  let coq_R_remove_correct k s _res =
    Obj.magic remove_rect k (fun y _ _ _ -> R_remove_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_remove_3 (y, y0, y1, y2,
      (remove k y2), (y6 (remove k y2) __))) s _res __

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | [] -> acc
    | p :: m' -> let (k, e) = p in fold f m' (f k e acc)

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
     * ('elt, 'a) coq_R_fold

  (** val coq_R_fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rect f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0
      (coq_R_fold_rect f f0 f1 m' (f k e acc) _res r0)

  (** val coq_R_fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rec f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0 (coq_R_fold_rec f f0 f1 m' (f k e acc) _res r0)

  (** val fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let rec fold_rect f1 f0 f m acc =
    let f2 = f0 m acc in
    let f3 = f m acc in
    (match m with
     | [] -> f2 __
     | p :: l ->
       let (t0, e) = p in
       let f4 = f3 t0 e l __ in
       let hrec = fold_rect f1 f0 f l (f1 t0 e acc) in f4 hrec)

  (** val fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let fold_rec =
    fold_rect

  (** val coq_R_fold_correct :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold **)

  let coq_R_fold_correct f m acc _res =
    fold_rect f (fun y y0 _ _ _ -> R_fold_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 _ _ -> R_fold_1 (y, y0, y1, y2, y3,
      (fold f y3 (f y1 y2 y0)), (y5 (fold f y3 (f y1 y2 y0)) __))) m acc _res
      __

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m m' =
    match m with
    | [] -> (match m' with
             | [] -> true
             | _ :: _ -> false)
    | p :: l ->
      let (x, e) = p in
      (match m' with
       | [] -> false
       | p0 :: l' ->
         let (x', e') = p0 in
         (match X.compare x x' with
          | EQ -> (&&) (cmp e e') (equal cmp l l')
          | _ -> false))

  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * X.t compare0
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

  (** val coq_R_equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
      ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
      'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rect cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x, e, l, x', e', l', _res, r0) ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rect cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x, e, l, x', e', l', _x) ->
    f1 m m' x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val coq_R_equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare0 -> __ -> __ -> 'a2) ->
      ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
      'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rec cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x, e, l, x', e', l', _res, r0) ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rec cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x, e, l, x', e', l', _x) ->
    f1 m m' x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let rec equal_rect cmp f2 f1 f0 f m m' =
    let f3 = f2 m m' in
    let f4 = f1 m m' in
    let f5 = f0 m m' in
    let f6 = f m m' in
    let f7 = f6 m __ in
    let f8 = f7 m' __ in
    (match m with
     | [] -> let f9 = f3 __ in (match m' with
                                | [] -> f9 __
                                | _ :: _ -> f8 __)
     | p :: l ->
       let (t0, e) = p in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match m' with
        | [] -> f8 __
        | p0 :: l0 ->
          let (t1, e0) = p0 in
          let f11 = f9 t1 e0 l0 __ in
          let f12 = let _x = X.compare t0 t1 in f11 _x __ in
          let f13 = f10 t1 e0 l0 __ in
          let f14 = fun _ _ ->
            let hrec = equal_rect cmp f2 f1 f0 f l l0 in f13 __ __ hrec
          in
          (match X.compare t0 t1 with
           | EQ -> f14 __ __
           | _ -> f12 __)))

  (** val equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let equal_rec =
    equal_rect

  (** val coq_R_equal_correct :
      ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal **)

  let coq_R_equal_correct cmp m m' _res =
    equal_rect cmp (fun y y0 _ _ _ _ -> R_equal_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 _ _ -> R_equal_1 (y, y0, y1,
      y2, y3, y5, y6, y7, (equal cmp y3 y7), (y11 (equal cmp y3 y7) __)))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ _ _ -> R_equal_2 (y, y0, y1, y2,
      y3, y5, y6, y7, y9)) (fun y y0 y1 _ y3 _ _ _ _ -> R_equal_3 (y, y0, y1,
      y3)) m m' _res __

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f e)) :: (map f m')

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f k e)) :: (mapi f m')

  (** val option_cons :
      key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list **)

  let option_cons k o l =
    match o with
    | Some e -> (k, e) :: l
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | [] -> []
  | p :: l -> let (k, e) = p in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | [] -> []
  | p :: l' ->
    let (k, e') = p in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | [] -> map2_r f
  | p :: l ->
    let (k, e) = p in
    let rec map2_aux m' = match m' with
    | [] -> map2_l f m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e) None) (map2 f l m')
       | EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let rec combine m = match m with
  | [] -> map (fun e' -> (None, (Some e')))
  | p :: l ->
    let (k, e) = p in
    let rec combine_aux m' = match m' with
    | [] -> map (fun e0 -> ((Some e0), None)) m
    | p0 :: l' ->
      let (k', e') = p0 in
      (match X.compare k k' with
       | LT -> (k, ((Some e), None)) :: (combine l m')
       | EQ -> (k, ((Some e), (Some e'))) :: (combine l l')
       | GT -> (k', (None, (Some e'))) :: (combine_aux l'))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
      (key * 'a3) list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 []

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (o, o')
    | None -> (match o' with
               | Some _ -> Some (o, o')
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rect f f0 t1) k y t2 (tree_rect f f0 t2) t3

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rec f f0 t1) k y t2 (tree_rec f f0 t2) t3

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h) -> h

  (** val cardinal : 'a1 tree -> nat **)

  let rec cardinal = function
  | Leaf -> O
  | Node (l, _, _, r, _) -> S (add (cardinal l) (cardinal r))

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _, _) -> false

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x = function
  | Leaf -> false
  | Node (l, y, _, r, _) ->
    (match X.compare x y with
     | LT -> mem x l
     | EQ -> true
     | GT -> mem x r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x = function
  | Leaf -> None
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> find x l
     | EQ -> Some d
     | GT -> find x r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x e r =
    Node (l, x, e, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x d r =
    let hl = height l in
    let hr = height r in
    if I.gt_le_dec hl (I.add hr I._2)
    then (match l with
          | Leaf -> assert_false l x d r
          | Node (ll, lx, ld, lr, _) ->
            if I.ge_lt_dec (height ll) (height lr)
            then create ll lx ld (create lr x d r)
            else (match lr with
                  | Leaf -> assert_false l x d r
                  | Node (lrl, lrx, lrd, lrr, _) ->
                    create (create ll lx ld lrl) lrx lrd (create lrr x d r)))
    else if I.gt_le_dec hr (I.add hl I._2)
         then (match r with
               | Leaf -> assert_false l x d r
               | Node (rl, rx, rd, rr, _) ->
                 if I.ge_lt_dec (height rr) (height rl)
                 then create (create l x d rl) rx rd rr
                 else (match rl with
                       | Leaf -> assert_false l x d r
                       | Node (rll, rlx, rld, rlr, _) ->
                         create (create l x d rll) rlx rld
                           (create rlr rx rd rr)))
         else create l x d r

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x d = function
  | Leaf -> Node (Leaf, x, d, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | LT -> bal (add x d l) y d' r
     | EQ -> Node (l, y, d, r, h)
     | GT -> bal l y d' (add x d r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1) **)

  let rec remove_min l x d r =
    match l with
    | Leaf -> (r, (x, d))
    | Node (ll, lx, ld, lr, _) ->
      let (l', m) = remove_min ll lx ld lr in ((bal l' x d r), m)

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let (s2', p) = remove_min l2 x2 d2 r2 in
         let (x, d) = p in bal s1 x d s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> bal (remove x l) y d r
     | EQ -> merge l r
     | GT -> bal l y d (remove x r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d ->
      let rec join_aux r = match r with
      | Leaf -> add x d l
      | Node (rl, rx, rd, rr, rh) ->
        if I.gt_le_dec lh (I.add rh I._2)
        then bal ll lx ld (join lr x d r)
        else if I.gt_le_dec rh (I.add lh I._2)
             then bal (join_aux rl) rx rd rr
             else create l x d r
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t0 =
    t0.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t0 =
    t0.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t0 =
    t0.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | EQ -> { t_left = l; t_opt = (Some d); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')

  (** val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d, r, _) -> elements_aux ((x, d) :: (elements_aux acc r)) l

  (** val elements : 'a1 tree -> (key * 'a1) list **)

  let elements m =
    elements_aux [] m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x, d, r, _) -> fold f r (f x d (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rect f f0 e1)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rec f f0 e1)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x, d, r, _) -> cons l (More (x, d, r, e))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp x1 d1 cont = function
  | End -> false
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> if cmp d1 d2 then cont (cons r2 e3) else false
     | _ -> false)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, _) ->
      equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> true
  | More (_, _, _, _) -> false

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp m1 m2 =
    equal_cont cmp m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((map f l), x, (f d), (map f r), h)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((mapi f l), x, (f x d), (mapi f r), h)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, _) ->
    (match f x d with
     | Some d' -> join (map_option f l) x d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d o -> f (Some d) o)
      (map_option (fun _ d -> f (Some d) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = Coq_OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t *
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t *
       bool * 'elt coq_R_mem

    (** val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rect x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rec x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find

    (** val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rect x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rec x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key *
       'elt * 'elt tree * I.t
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key *
       'elt * 'elt tree * I.t
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key *
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree *
       I.t
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key *
       'elt * 'elt tree * I.t
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key *
       'elt * 'elt tree * I.t
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key *
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree *
       I.t
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

    (** val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rect f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (x, x0, x1, x2) -> f x x0 x1 x2 __ __ __
    | R_bal_1 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_2 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_3 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_4 (x, x0, x1, x2) -> f3 x x0 x1 x2 __ __ __ __ __
    | R_bal_5 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_6 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_7 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_8 (x, x0, x1, x2) -> f7 x x0 x1 x2 __ __ __ __

    (** val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rec f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (x, x0, x1, x2) -> f x x0 x1 x2 __ __ __
    | R_bal_1 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_2 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_3 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_4 (x, x0, x1, x2) -> f3 x x0 x1 x2 __ __ __ __ __
    | R_bal_5 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_6 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_7 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_8 (x, x0, x1, x2) -> f7 x x0 x1 x2 __ __ __ __

    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add

    (** val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rect x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 r0 _res r1)

    (** val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rec x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
       key * 'elt * 'elt tree * I.t * ('elt tree * (key * 'elt))
       * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

    (** val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rect f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r0) -> f l x d r0 __
    | R_remove_min_1 (l, x, d, r0, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r0 ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rect f f0 ll lx ld lr _res r1) l' m __

    (** val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rec f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r0) -> f l x d r0 __
    | R_remove_min_1 (l, x, d, r0, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r0 ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rec f f0 ll lx ld lr _res r1) l' m __

    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key * 'elt) * key * 'elt

    (** val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rect f f0 f1 _ _ _ = function
    | R_merge_0 (x, x0) -> f x x0 __
    | R_merge_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
                 x13, x14) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __

    (** val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rec f f0 f1 _ _ _ = function
    | R_merge_0 (x, x0) -> f x x0 __
    | R_merge_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
                 x13, x14) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree *
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree *
       I.t * 'elt tree * 'elt coq_R_remove

    (** val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rect x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rec x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key * 'elt)

    (** val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rect f f0 f1 _ _ _ = function
    | R_concat_0 (x, x0) -> f x x0 __
    | R_concat_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __

    (** val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rec f f0 f1 _ _ _ = function
    | R_concat_0 (x, x0) -> f x x0 __
    | R_concat_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __

    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree

    (** val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rect x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 r0 _res r1) rl o rr __

    (** val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rec x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 r0 _res r1) rl o rr __

    type ('elt, 'x) coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree *
       I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree *
       I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option

    (** val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rect f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)

    (** val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rec f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)

    type ('elt, 'x0, 'x) coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'x0 tree
    | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
       * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt

    (** val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key * 'a1) list **)

    let rec flatten_e = function
    | End -> []
    | More (x, e0, t0, r) -> (x, e0) :: (app (elements t0) (flatten_e r))
   end
 end

module Coq0_IntMake =
 functor (I:Int) ->
 functor (X:Coq_OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty m =
    Raw.is_empty (this m)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add x e m =
    Raw.add x e (this m)

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove x m =
    Raw.remove x (this m)

  (** val mem : key -> 'a1 t -> bool **)

  let mem x m =
    Raw.mem x (this m)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find x m =
    Raw.find x (this m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Raw.map f (this m)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    Raw.mapi f (this m)

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 f m m' =
    Raw.map2 f (this m) (this m')

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements m =
    Raw.elements (this m)

  (** val cardinal : 'a1 t -> nat **)

  let cardinal m =
    Raw.cardinal (this m)

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    Raw.fold f (this m) i

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp m m' =
    Raw.equal cmp (this m) (this m')
 end

module Coq_Make =
 functor (X:Coq_OrderedType) ->
 Coq0_IntMake(Z_as_Int)(X)

module Coq_WFacts_fun =
 functor (E:DecidableType) ->
 functor (M:sig
  type key = E.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end) ->
 struct
  (** val eqb : E.t -> E.t -> bool **)

  let eqb x y =
    if E.eq_dec x y then true else false

  (** val coq_In_dec : 'a1 M.t -> M.key -> bool **)

  let coq_In_dec m x =
    let b = M.mem x m in if b then true else false
 end

module Coq_WFacts =
 functor (M:Coq_WS) ->
 Coq_WFacts_fun(M.E)(M)

module Coq_Facts = Coq_WFacts

module UOT_Facts =
 functor (U:UsualOrderedType) ->
 struct
 end

module type UsualComparableType =
 sig
  type t

  val compare : t -> t -> comparison
 end

module UOT_from_UCT =
 functor (C:UsualComparableType) ->
 struct
  type t = C.t

  (** val compare : t -> t -> t compare0 **)

  let compare x y =
    let c = C.compare x y in (match c with
                              | Eq -> EQ
                              | Lt -> LT
                              | Gt -> GT)

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    let c = C.compare x y in (match c with
                              | Eq -> true
                              | _ -> false)
 end

module List_as_UOT =
 functor (E:UsualOrderedType) ->
 struct
  module F = UOT_Facts(E)

  type t = E.t list

  (** val compare : E.t list -> E.t list -> E.t list compare0 **)

  let rec compare xs ys =
    match xs with
    | [] -> (match ys with
             | [] -> EQ
             | _ :: _ -> LT)
    | x :: xs' ->
      (match ys with
       | [] -> GT
       | y :: ys' ->
         (match E.compare x y with
          | LT -> LT
          | EQ -> compare xs' ys'
          | GT -> GT))

  (** val eq_dec : t -> t -> bool **)

  let rec eq_dec xs ys =
    match xs with
    | [] -> (match ys with
             | [] -> true
             | _ :: _ -> false)
    | x :: xs' ->
      (match ys with
       | [] -> false
       | y :: ys' -> if E.eq_dec x y then eq_dec xs' ys' else false)
 end

module Pair_as_UOT =
 functor (A:UsualOrderedType) ->
 functor (B:UsualOrderedType) ->
 struct
  module FA = UOT_Facts(A)

  module FB = UOT_Facts(B)

  type t = A.t * B.t

  (** val compare : t -> t -> (A.t * B.t) compare0 **)

  let compare x y =
    let (a, b) = x in
    let (a', b') = y in
    (match A.compare a a' with
     | LT -> LT
     | EQ -> (match B.compare b b' with
              | LT -> LT
              | EQ -> EQ
              | GT -> GT)
     | GT -> GT)

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    let (a, b) = x in
    let (a', b') = y in if A.eq_dec a a' then B.eq_dec b b' else false
 end

module type SIGMA =
 sig
  type coq_Sigma

  val coq_SigmaEnum : coq_Sigma list

  val coq_Sigma_dec : coq_Sigma -> coq_Sigma -> bool

  val compareT : coq_Sigma -> coq_Sigma -> comparison
 end

module DefsFn =
 functor (Ty:SIGMA) ->
 struct
  module T_as_UCT =
   struct
    type t = Ty.coq_Sigma

    (** val compare : Ty.coq_Sigma -> Ty.coq_Sigma -> comparison **)

    let compare =
      Ty.compareT
   end

  module T_as_UOT = UOT_from_UCT(T_as_UCT)

  module SigFS = Make(T_as_UOT)

  module SigFSF = Facts(SigFS)

  module SigFM = Coq_Make(T_as_UOT)

  module SigFMF = Coq_Facts(SigFM)

  module Strings =
   struct
    type coq_String = Ty.coq_Sigma list

    (** val coq_String_dec : coq_String -> coq_String -> bool **)

    let rec coq_String_dec l x =
      match l with
      | [] -> (match x with
               | [] -> true
               | _ :: _ -> false)
      | y :: l0 ->
        (match x with
         | [] -> false
         | s0 :: l1 ->
           if Ty.coq_Sigma_dec y s0 then coq_String_dec l0 l1 else false)

    (** val rm_empty : coq_String list -> Ty.coq_Sigma list list **)

    let rm_empty yss =
      filter (fun l -> match l with
                       | [] -> false
                       | _ :: _ -> true) yss
   end

  module Regexes =
   struct
    type regex =
    | EmptySet
    | EmptyStr
    | Char of Ty.coq_Sigma
    | App of regex * regex
    | Union of regex * regex
    | Star of regex

    (** val regex_rect :
        'a1 -> 'a1 -> (Ty.coq_Sigma -> 'a1) -> (regex -> 'a1 -> regex -> 'a1
        -> 'a1) -> (regex -> 'a1 -> regex -> 'a1 -> 'a1) -> (regex -> 'a1 ->
        'a1) -> regex -> 'a1 **)

    let rec regex_rect f f0 f1 f2 f3 f4 = function
    | EmptySet -> f
    | EmptyStr -> f0
    | Char t0 -> f1 t0
    | App (r1, r2) ->
      f2 r1 (regex_rect f f0 f1 f2 f3 f4 r1) r2
        (regex_rect f f0 f1 f2 f3 f4 r2)
    | Union (r1, r2) ->
      f3 r1 (regex_rect f f0 f1 f2 f3 f4 r1) r2
        (regex_rect f f0 f1 f2 f3 f4 r2)
    | Star r0 -> f4 r0 (regex_rect f f0 f1 f2 f3 f4 r0)

    (** val regex_rec :
        'a1 -> 'a1 -> (Ty.coq_Sigma -> 'a1) -> (regex -> 'a1 -> regex -> 'a1
        -> 'a1) -> (regex -> 'a1 -> regex -> 'a1 -> 'a1) -> (regex -> 'a1 ->
        'a1) -> regex -> 'a1 **)

    let rec regex_rec f f0 f1 f2 f3 f4 = function
    | EmptySet -> f
    | EmptyStr -> f0
    | Char t0 -> f1 t0
    | App (r1, r2) ->
      f2 r1 (regex_rec f f0 f1 f2 f3 f4 r1) r2 (regex_rec f f0 f1 f2 f3 f4 r2)
    | Union (r1, r2) ->
      f3 r1 (regex_rec f f0 f1 f2 f3 f4 r1) r2 (regex_rec f f0 f1 f2 f3 f4 r2)
    | Star r0 -> f4 r0 (regex_rec f f0 f1 f2 f3 f4 r0)

    (** val regex_dec : regex -> regex -> bool **)

    let rec regex_dec r x =
      match r with
      | EmptySet -> (match x with
                     | EmptySet -> true
                     | _ -> false)
      | EmptyStr -> (match x with
                     | EmptyStr -> true
                     | _ -> false)
      | Char t0 ->
        (match x with
         | Char t1 -> Ty.coq_Sigma_dec t0 t1
         | _ -> false)
      | App (r1, r2) ->
        (match x with
         | App (r0, r3) -> if regex_dec r1 r0 then regex_dec r2 r3 else false
         | _ -> false)
      | Union (r1, r2) ->
        (match x with
         | Union (r0, r3) ->
           if regex_dec r1 r0 then regex_dec r2 r3 else false
         | _ -> false)
      | Star r0 -> (match x with
                    | Star r1 -> regex_dec r0 r1
                    | _ -> false)

    (** val regex_eq : regex -> regex -> bool **)

    let rec regex_eq r1 r2 =
      match r1 with
      | EmptySet -> (match r2 with
                     | EmptySet -> true
                     | _ -> false)
      | EmptyStr -> (match r2 with
                     | EmptyStr -> true
                     | _ -> false)
      | Char a ->
        (match r2 with
         | Char b -> if Ty.coq_Sigma_dec a b then true else false
         | _ -> false)
      | App (x1, y1) ->
        (match r2 with
         | App (x2, y2) -> (&&) (regex_eq x1 x2) (regex_eq y1 y2)
         | _ -> false)
      | Union (x1, y1) ->
        (match r2 with
         | Union (x2, y2) -> (&&) (regex_eq x1 x2) (regex_eq y1 y2)
         | _ -> false)
      | Star a -> (match r2 with
                   | Star b -> regex_eq a b
                   | _ -> false)

    (** val nullable' : regex -> bool **)

    let rec nullable' = function
    | EmptySet -> false
    | Char _ -> false
    | App (r1, r2) -> (&&) (nullable' r1) (nullable' r2)
    | Union (r1, r2) -> (||) (nullable' r1) (nullable' r2)
    | _ -> true

    (** val nullable : regex -> bool **)

    let rec nullable = function
    | EmptySet -> false
    | Char _ -> false
    | App (r1, r2) -> if negb (nullable r2) then false else nullable r1
    | Union (r1, r2) -> if nullable r2 then true else nullable r1
    | _ -> true

    (** val derivative : Ty.coq_Sigma -> regex -> regex **)

    let rec derivative a = function
    | Char x -> if Ty.coq_Sigma_dec x a then EmptyStr else EmptySet
    | App (r1, r2) ->
      if nullable r1
      then Union ((App ((derivative a r1), r2)), (derivative a r2))
      else App ((derivative a r1), r2)
    | Union (r1, r2) -> Union ((derivative a r1), (derivative a r2))
    | Star r0 -> App ((derivative a r0), (Star r0))
    | _ -> EmptySet

    (** val derivative_list : Ty.coq_Sigma list -> regex -> regex **)

    let rec derivative_list bs e =
      match bs with
      | [] -> e
      | c :: cs -> derivative_list cs (derivative c e)

    (** val re_compare : regex -> regex -> comparison **)

    let rec re_compare e1 e2 =
      match e1 with
      | EmptySet -> (match e2 with
                     | EmptySet -> Eq
                     | EmptyStr -> Gt
                     | _ -> Lt)
      | EmptyStr -> (match e2 with
                     | EmptyStr -> Eq
                     | _ -> Lt)
      | Char a ->
        (match e2 with
         | EmptySet -> Gt
         | EmptyStr -> Gt
         | Char b -> Ty.compareT a b
         | _ -> Lt)
      | App (e3, e4) ->
        (match e2 with
         | App (e5, e6) ->
           (match re_compare e3 e5 with
            | Eq -> re_compare e4 e6
            | x -> x)
         | Union (_, _) -> Lt
         | Star _ -> Lt
         | _ -> Gt)
      | Union (e3, e4) ->
        (match e2 with
         | Union (e5, e6) ->
           (match re_compare e3 e5 with
            | Eq -> re_compare e4 e6
            | x -> x)
         | _ -> Gt)
      | Star e3 ->
        (match e2 with
         | Union (_, _) -> Lt
         | Star e4 -> re_compare e3 e4
         | _ -> Gt)
   end

  module Coq_regex_as_UCT =
   struct
    type t = Regexes.regex

    (** val compare : Regexes.regex -> Regexes.regex -> comparison **)

    let compare =
      Regexes.re_compare
   end

  module Coq_regex_as_UOT = UOT_from_UCT(Coq_regex_as_UCT)

  module Coq_reFS = Make(Coq_regex_as_UOT)

  module Coq_reFSF = Facts(Coq_reFS)

  module Coq_reFM = Coq_Make(Coq_regex_as_UOT)

  module Coq_reFMF = Coq_Facts(Coq_reFM)

  module MatchSpec =
   struct
   end

  module MatchSpecLemmas =
   struct
   end

  module Notations =
   struct
   end

  module Helpers =
   struct
    (** val coq_Plus : Regexes.regex -> Regexes.regex **)

    let coq_Plus r =
      Regexes.App (r, (Regexes.Star r))

    (** val coq_IterUnion : Regexes.regex list -> Regexes.regex **)

    let rec coq_IterUnion = function
    | [] -> Regexes.EmptySet
    | h :: t0 ->
      (match t0 with
       | [] -> h
       | _ :: _ -> Regexes.Union (h, (coq_IterUnion t0)))

    (** val coq_IterApp : Regexes.regex list -> Regexes.regex **)

    let rec coq_IterApp = function
    | [] -> Regexes.EmptyStr
    | h :: t0 ->
      (match t0 with
       | [] -> h
       | _ :: _ -> Regexes.App (h, (coq_IterApp t0)))

    (** val coq_Optional : Regexes.regex -> Regexes.regex **)

    let coq_Optional r =
      Regexes.Union (Regexes.EmptyStr, r)

    (** val coq_REString : Strings.coq_String -> Regexes.regex **)

    let coq_REString z0 =
      coq_IterApp (map (fun x -> Regexes.Char x) z0)
   end
 end

module type T =
 sig
  module Ty :
   SIGMA

  module Defs :
   sig
    module T_as_UCT :
     sig
      type t = Ty.coq_Sigma

      val compare : Ty.coq_Sigma -> Ty.coq_Sigma -> comparison
     end

    module T_as_UOT :
     sig
      type t = T_as_UCT.t

      val compare : t -> t -> t compare0

      val eq_dec : t -> t -> bool
     end

    module SigFS :
     sig
      module X' :
       sig
        type t = T_as_UCT.t

        val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

        val compare : T_as_UCT.t -> T_as_UCT.t -> comparison
       end

      module MSet :
       sig
        module Raw :
         sig
          type elt = T_as_UCT.t

          type tree =
          | Leaf
          | Node of Z_as_Int.t * tree * T_as_UCT.t * tree

          val empty : tree

          val is_empty : tree -> bool

          val mem : T_as_UCT.t -> tree -> bool

          val min_elt : tree -> elt option

          val max_elt : tree -> elt option

          val choose : tree -> elt option

          val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

          val elements_aux : T_as_UCT.t list -> tree -> T_as_UCT.t list

          val elements : tree -> T_as_UCT.t list

          val rev_elements_aux : T_as_UCT.t list -> tree -> T_as_UCT.t list

          val rev_elements : tree -> T_as_UCT.t list

          val cardinal : tree -> nat

          val maxdepth : tree -> nat

          val mindepth : tree -> nat

          val for_all : (elt -> bool) -> tree -> bool

          val exists_ : (elt -> bool) -> tree -> bool

          type enumeration =
          | End
          | More of elt * tree * enumeration

          val cons : tree -> enumeration -> enumeration

          val compare_more :
            T_as_UCT.t -> (enumeration -> comparison) -> enumeration ->
            comparison

          val compare_cont :
            tree -> (enumeration -> comparison) -> enumeration -> comparison

          val compare_end : enumeration -> comparison

          val compare : tree -> tree -> comparison

          val equal : tree -> tree -> bool

          val subsetl : (tree -> bool) -> T_as_UCT.t -> tree -> bool

          val subsetr : (tree -> bool) -> T_as_UCT.t -> tree -> bool

          val subset : tree -> tree -> bool

          type t = tree

          val height : t -> Z_as_Int.t

          val singleton : T_as_UCT.t -> tree

          val create : t -> T_as_UCT.t -> t -> tree

          val assert_false : t -> T_as_UCT.t -> t -> tree

          val bal : t -> T_as_UCT.t -> t -> tree

          val add : T_as_UCT.t -> tree -> tree

          val join : tree -> elt -> t -> t

          val remove_min : tree -> elt -> t -> t * elt

          val merge : tree -> tree -> tree

          val remove : T_as_UCT.t -> tree -> tree

          val concat : tree -> tree -> tree

          type triple = { t_left : t; t_in : bool; t_right : t }

          val t_left : triple -> t

          val t_in : triple -> bool

          val t_right : triple -> t

          val split : T_as_UCT.t -> tree -> triple

          val inter : tree -> tree -> tree

          val diff : tree -> tree -> tree

          val union : tree -> tree -> tree

          val filter : (elt -> bool) -> tree -> tree

          val partition : (elt -> bool) -> t -> t * t

          val ltb_tree : T_as_UCT.t -> tree -> bool

          val gtb_tree : T_as_UCT.t -> tree -> bool

          val isok : tree -> bool

          module MX :
           sig
            module OrderTac :
             sig
              module OTF :
               sig
                type t = T_as_UCT.t

                val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

                val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
               end

              module TO :
               sig
                type t = T_as_UCT.t

                val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

                val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
               end
             end

            val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

            val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

            val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
           end

          type coq_R_min_elt =
          | R_min_elt_0 of tree
          | R_min_elt_1 of tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_min_elt_2 of tree * Z_as_Int.t * tree * T_as_UCT.t * tree
             * Z_as_Int.t * tree * T_as_UCT.t * tree * elt option
             * coq_R_min_elt

          type coq_R_max_elt =
          | R_max_elt_0 of tree
          | R_max_elt_1 of tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_max_elt_2 of tree * Z_as_Int.t * tree * T_as_UCT.t * tree
             * Z_as_Int.t * tree * T_as_UCT.t * tree * elt option
             * coq_R_max_elt

          module L :
           sig
            module MO :
             sig
              module OrderTac :
               sig
                module OTF :
                 sig
                  type t = T_as_UCT.t

                  val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

                  val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
                 end

                module TO :
                 sig
                  type t = T_as_UCT.t

                  val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

                  val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
                 end
               end

              val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
             end
           end

          val flatten_e : enumeration -> elt list

          type coq_R_bal =
          | R_bal_0 of t * T_as_UCT.t * t
          | R_bal_1 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
             * tree
          | R_bal_2 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
             * tree
          | R_bal_3 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
             * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_bal_4 of t * T_as_UCT.t * t
          | R_bal_5 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
             * tree
          | R_bal_6 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
             * tree
          | R_bal_7 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
             * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_bal_8 of t * T_as_UCT.t * t

          type coq_R_remove_min =
          | R_remove_min_0 of tree * elt * t
          | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree * T_as_UCT.t
             * tree * (t * elt) * coq_R_remove_min * t * elt

          type coq_R_merge =
          | R_merge_0 of tree * tree
          | R_merge_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_merge_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
             tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * elt

          type coq_R_concat =
          | R_concat_0 of tree * tree
          | R_concat_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_concat_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
             tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * elt

          type coq_R_inter =
          | R_inter_0 of tree * tree
          | R_inter_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_inter_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
             tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
             t * tree * coq_R_inter * tree * coq_R_inter
          | R_inter_3 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
             tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
             t * tree * coq_R_inter * tree * coq_R_inter

          type coq_R_diff =
          | R_diff_0 of tree * tree
          | R_diff_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_diff_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
             tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
             t * tree * coq_R_diff * tree * coq_R_diff
          | R_diff_3 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
             tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
             t * tree * coq_R_diff * tree * coq_R_diff

          type coq_R_union =
          | R_union_0 of tree * tree
          | R_union_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_union_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
             tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
             t * tree * coq_R_union * tree * coq_R_union
         end

        module E :
         sig
          type t = T_as_UCT.t

          val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

          val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
         end

        type elt = T_as_UCT.t

        type t_ = Raw.t
          (* singleton inductive, whose constructor was Mkt *)

        val this : t_ -> Raw.t

        type t = t_

        val mem : elt -> t -> bool

        val add : elt -> t -> t

        val remove : elt -> t -> t

        val singleton : elt -> t

        val union : t -> t -> t

        val inter : t -> t -> t

        val diff : t -> t -> t

        val equal : t -> t -> bool

        val subset : t -> t -> bool

        val empty : t

        val is_empty : t -> bool

        val elements : t -> elt list

        val choose : t -> elt option

        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

        val cardinal : t -> nat

        val filter : (elt -> bool) -> t -> t

        val for_all : (elt -> bool) -> t -> bool

        val exists_ : (elt -> bool) -> t -> bool

        val partition : (elt -> bool) -> t -> t * t

        val eq_dec : t -> t -> bool

        val compare : t -> t -> comparison

        val min_elt : t -> elt option

        val max_elt : t -> elt option
       end

      type elt = T_as_UCT.t

      type t = MSet.t

      val empty : t

      val is_empty : t -> bool

      val mem : elt -> t -> bool

      val add : elt -> t -> t

      val singleton : elt -> t

      val remove : elt -> t -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val eq_dec : t -> t -> bool

      val equal : t -> t -> bool

      val subset : t -> t -> bool

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val filter : (elt -> bool) -> t -> t

      val partition : (elt -> bool) -> t -> t * t

      val cardinal : t -> nat

      val elements : t -> elt list

      val choose : t -> elt option

      module MF :
       sig
        val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
       end

      val min_elt : t -> elt option

      val max_elt : t -> elt option

      val compare : t -> t -> t compare0

      module E :
       sig
        type t = T_as_UCT.t

        val compare : T_as_UCT.t -> T_as_UCT.t -> T_as_UCT.t compare0

        val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
       end
     end

    module SigFSF :
     sig
      val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
     end

    module SigFM :
     sig
      module E :
       sig
        type t = T_as_UCT.t

        val compare : T_as_UCT.t -> T_as_UCT.t -> T_as_UCT.t compare0

        val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
       end

      module Raw :
       sig
        type key = T_as_UCT.t

        type 'elt tree =
        | Leaf
        | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

        val tree_rect :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val tree_rec :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val height : 'a1 tree -> Z_as_Int.t

        val cardinal : 'a1 tree -> nat

        val empty : 'a1 tree

        val is_empty : 'a1 tree -> bool

        val mem : T_as_UCT.t -> 'a1 tree -> bool

        val find : T_as_UCT.t -> 'a1 tree -> 'a1 option

        val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

        val remove_min :
          'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

        val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

        val remove : T_as_UCT.t -> 'a1 tree -> 'a1 tree

        val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                             t_right : 'elt tree }

        val t_left : 'a1 triple -> 'a1 tree

        val t_opt : 'a1 triple -> 'a1 option

        val t_right : 'a1 triple -> 'a1 tree

        val split : T_as_UCT.t -> 'a1 tree -> 'a1 triple

        val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

        val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

        val elements : 'a1 tree -> (key * 'a1) list

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

        type 'elt enumeration =
        | End
        | More of key * 'elt * 'elt tree * 'elt enumeration

        val enumeration_rect :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val enumeration_rec :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

        val equal_more :
          ('a1 -> 'a1 -> bool) -> T_as_UCT.t -> 'a1 -> ('a1 enumeration ->
          bool) -> 'a1 enumeration -> bool

        val equal_cont :
          ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
          'a1 enumeration -> bool

        val equal_end : 'a1 enumeration -> bool

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

        val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

        val map2_opt :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
          'a3 tree

        module Proofs :
         sig
          module MX :
           sig
            module TO :
             sig
              type t = T_as_UCT.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

            val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

            val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
           end

          module PX :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = T_as_UCT.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
             end
           end

          module L :
           sig
            module MX :
             sig
              module TO :
               sig
                type t = T_as_UCT.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
             end

            module PX :
             sig
              module MO :
               sig
                module TO :
                 sig
                  type t = T_as_UCT.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

                val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

                val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
               end
             end

            type key = T_as_UCT.t

            type 'elt t = (T_as_UCT.t * 'elt) list

            val empty : 'a1 t

            val is_empty : 'a1 t -> bool

            val mem : key -> 'a1 t -> bool

            type 'elt coq_R_mem =
            | R_mem_0 of 'elt t
            | R_mem_1 of 'elt t * T_as_UCT.t * 'elt * (T_as_UCT.t * 'elt) list
            | R_mem_2 of 'elt t * T_as_UCT.t * 'elt * (T_as_UCT.t * 'elt) list
            | R_mem_3 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * bool * 'elt coq_R_mem

            val coq_R_mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
              -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

            val coq_R_mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
              -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

            val mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

            val find : key -> 'a1 t -> 'a1 option

            type 'elt coq_R_find =
            | R_find_0 of 'elt t
            | R_find_1 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list
            | R_find_2 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list
            | R_find_3 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * 'elt option * 'elt coq_R_find

            val coq_R_find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2
              -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

            val coq_R_find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2
              -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

            val find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val coq_R_find_correct :
              key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

            val add : key -> 'a1 -> 'a1 t -> 'a1 t

            type 'elt coq_R_add =
            | R_add_0 of 'elt t
            | R_add_1 of 'elt t * T_as_UCT.t * 'elt * (T_as_UCT.t * 'elt) list
            | R_add_2 of 'elt t * T_as_UCT.t * 'elt * (T_as_UCT.t * 'elt) list
            | R_add_3 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * 'elt t * 'elt coq_R_add

            val coq_R_add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t ->
              'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
              coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add ->
              'a2

            val coq_R_add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t ->
              'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
              coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add ->
              'a2

            val add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t ->
              'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
              t -> 'a2

            val add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t ->
              'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
              t -> 'a2

            val coq_R_add_correct :
              key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

            val remove : key -> 'a1 t -> 'a1 t

            type 'elt coq_R_remove =
            | R_remove_0 of 'elt t
            | R_remove_1 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list
            | R_remove_2 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list
            | R_remove_3 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * 'elt t * 'elt coq_R_remove

            val coq_R_remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 ->
              'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

            val coq_R_remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 ->
              'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

            val remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val coq_R_remove_correct :
              key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

            val elements : 'a1 t -> 'a1 t

            val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

            type ('elt, 'a) coq_R_fold =
            | R_fold_0 of 'elt t * 'a
            | R_fold_1 of 'elt t * 'a * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * 'a * ('elt, 'a) coq_R_fold

            val coq_R_fold_rect :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t
              -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

            val coq_R_fold_rec :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t
              -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

            val fold_rect :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

            val fold_rec :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

            val coq_R_fold_correct :
              (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
              coq_R_fold

            val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

            type 'elt coq_R_equal =
            | R_equal_0 of 'elt t * 'elt t
            | R_equal_1 of 'elt t * 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * bool * 'elt coq_R_equal
            | R_equal_2 of 'elt t * 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * T_as_UCT.t compare0
            | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

            val coq_R_equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t ->
              'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              T_as_UCT.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
              'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t ->
              bool -> 'a1 coq_R_equal -> 'a2

            val coq_R_equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t ->
              'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              T_as_UCT.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
              'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t ->
              bool -> 'a1 coq_R_equal -> 'a2

            val equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1
              -> (T_as_UCT.t * 'a1) list -> __ -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> T_as_UCT.t compare0 -> __ ->
              __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ ->
              __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

            val equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1
              -> (T_as_UCT.t * 'a1) list -> __ -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> T_as_UCT.t compare0 -> __ ->
              __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ ->
              __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

            val coq_R_equal_correct :
              ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
              coq_R_equal

            val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

            val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

            val option_cons :
              key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

            val map2_l :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

            val map2_r :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

            val map2 :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              'a3 t

            val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

            val fold_right_pair :
              ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

            val map2_alt :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              (key * 'a3) list

            val at_least_one :
              'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

            val at_least_one_then_f :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
              option -> 'a3 option
           end

          type 'elt coq_R_mem =
          | R_mem_0 of 'elt tree
          | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem
          | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem

          val coq_R_mem_rect :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool ->
            'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree ->
            bool -> 'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool ->
            'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree ->
            bool -> 'a1 coq_R_mem -> 'a2

          type 'elt coq_R_find =
          | R_find_0 of 'elt tree
          | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find
          | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find

          val coq_R_find_rect :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2)
            -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
            -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2)
            -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

          val coq_R_find_rec :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2)
            -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
            -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2)
            -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

          type 'elt coq_R_bal =
          | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

          val coq_R_bal_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          val coq_R_bal_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          type 'elt coq_R_add =
          | R_add_0 of 'elt tree
          | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add
          | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          type 'elt coq_R_remove_min =
          | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
          | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
             * key * 'elt * 'elt tree * Z_as_Int.t
             * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min * 'elt tree
             * (key * 'elt)

          val coq_R_remove_min_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          val coq_R_remove_min_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          type 'elt coq_R_merge =
          | R_merge_0 of 'elt tree * 'elt tree
          | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

          val coq_R_merge_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2

          val coq_R_merge_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt tree
          | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
          | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

          val coq_R_remove_rect :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2)
            -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
            -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2)
            -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

          val coq_R_remove_rec :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2)
            -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
            -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2)
            -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

          type 'elt coq_R_concat =
          | R_concat_0 of 'elt tree * 'elt tree
          | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt)

          val coq_R_concat_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

          val coq_R_concat_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

          type 'elt coq_R_split =
          | R_split_0 of 'elt tree
          | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree
          | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree

          val coq_R_split_rect :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
            tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option ->
            'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
            coq_R_split -> 'a2

          val coq_R_split_rec :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
            tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option ->
            'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
            coq_R_split -> 'a2

          type ('elt, 'x) coq_R_map_option =
          | R_map_option_0 of 'elt tree
          | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
             * 'x tree * ('elt, 'x) coq_R_map_option
          | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
             * ('elt, 'x) coq_R_map_option

          val coq_R_map_option_rect :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          val coq_R_map_option_rec :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          type ('elt, 'x0, 'x) coq_R_map2_opt =
          | R_map2_opt_0 of 'elt tree * 'x0 tree
          | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t
          | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
             * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt
          | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
             * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt

          val coq_R_map2_opt_rect :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val coq_R_map2_opt_rec :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

          val flatten_e : 'a1 enumeration -> (key * 'a1) list
         end
       end

      type 'elt bst =
        'elt Raw.tree
        (* singleton inductive, whose constructor was Bst *)

      val this : 'a1 bst -> 'a1 Raw.tree

      type 'elt t = 'elt bst

      type key = T_as_UCT.t

      val empty : 'a1 t

      val is_empty : 'a1 t -> bool

      val add : key -> 'a1 -> 'a1 t -> 'a1 t

      val remove : key -> 'a1 t -> 'a1 t

      val mem : key -> 'a1 t -> bool

      val find : key -> 'a1 t -> 'a1 option

      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

      val elements : 'a1 t -> (key * 'a1) list

      val cardinal : 'a1 t -> nat

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
     end

    module SigFMF :
     sig
      val eqb : T_as_UCT.t -> T_as_UCT.t -> bool

      val coq_In_dec : 'a1 SigFM.t -> SigFM.key -> bool
     end

    module Strings :
     sig
      type coq_String = Ty.coq_Sigma list

      val coq_String_dec : coq_String -> coq_String -> bool

      val rm_empty : coq_String list -> Ty.coq_Sigma list list
     end

    module Regexes :
     sig
      type regex =
      | EmptySet
      | EmptyStr
      | Char of Ty.coq_Sigma
      | App of regex * regex
      | Union of regex * regex
      | Star of regex

      val regex_rect :
        'a1 -> 'a1 -> (Ty.coq_Sigma -> 'a1) -> (regex -> 'a1 -> regex -> 'a1
        -> 'a1) -> (regex -> 'a1 -> regex -> 'a1 -> 'a1) -> (regex -> 'a1 ->
        'a1) -> regex -> 'a1

      val regex_rec :
        'a1 -> 'a1 -> (Ty.coq_Sigma -> 'a1) -> (regex -> 'a1 -> regex -> 'a1
        -> 'a1) -> (regex -> 'a1 -> regex -> 'a1 -> 'a1) -> (regex -> 'a1 ->
        'a1) -> regex -> 'a1

      val regex_dec : regex -> regex -> bool

      val regex_eq : regex -> regex -> bool

      val nullable' : regex -> bool

      val nullable : regex -> bool

      val derivative : Ty.coq_Sigma -> regex -> regex

      val derivative_list : Ty.coq_Sigma list -> regex -> regex

      val re_compare : regex -> regex -> comparison
     end

    module Coq_regex_as_UCT :
     sig
      type t = Regexes.regex

      val compare : Regexes.regex -> Regexes.regex -> comparison
     end

    module Coq_regex_as_UOT :
     sig
      type t = Coq_regex_as_UCT.t

      val compare : t -> t -> t compare0

      val eq_dec : t -> t -> bool
     end

    module Coq_reFS :
     sig
      module X' :
       sig
        type t = Coq_regex_as_UCT.t

        val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

        val compare : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison
       end

      module MSet :
       sig
        module Raw :
         sig
          type elt = Coq_regex_as_UCT.t

          type tree =
          | Leaf
          | Node of Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree

          val empty : tree

          val is_empty : tree -> bool

          val mem : Coq_regex_as_UCT.t -> tree -> bool

          val min_elt : tree -> elt option

          val max_elt : tree -> elt option

          val choose : tree -> elt option

          val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

          val elements_aux :
            Coq_regex_as_UCT.t list -> tree -> Coq_regex_as_UCT.t list

          val elements : tree -> Coq_regex_as_UCT.t list

          val rev_elements_aux :
            Coq_regex_as_UCT.t list -> tree -> Coq_regex_as_UCT.t list

          val rev_elements : tree -> Coq_regex_as_UCT.t list

          val cardinal : tree -> nat

          val maxdepth : tree -> nat

          val mindepth : tree -> nat

          val for_all : (elt -> bool) -> tree -> bool

          val exists_ : (elt -> bool) -> tree -> bool

          type enumeration =
          | End
          | More of elt * tree * enumeration

          val cons : tree -> enumeration -> enumeration

          val compare_more :
            Coq_regex_as_UCT.t -> (enumeration -> comparison) -> enumeration
            -> comparison

          val compare_cont :
            tree -> (enumeration -> comparison) -> enumeration -> comparison

          val compare_end : enumeration -> comparison

          val compare : tree -> tree -> comparison

          val equal : tree -> tree -> bool

          val subsetl : (tree -> bool) -> Coq_regex_as_UCT.t -> tree -> bool

          val subsetr : (tree -> bool) -> Coq_regex_as_UCT.t -> tree -> bool

          val subset : tree -> tree -> bool

          type t = tree

          val height : t -> Z_as_Int.t

          val singleton : Coq_regex_as_UCT.t -> tree

          val create : t -> Coq_regex_as_UCT.t -> t -> tree

          val assert_false : t -> Coq_regex_as_UCT.t -> t -> tree

          val bal : t -> Coq_regex_as_UCT.t -> t -> tree

          val add : Coq_regex_as_UCT.t -> tree -> tree

          val join : tree -> elt -> t -> t

          val remove_min : tree -> elt -> t -> t * elt

          val merge : tree -> tree -> tree

          val remove : Coq_regex_as_UCT.t -> tree -> tree

          val concat : tree -> tree -> tree

          type triple = { t_left : t; t_in : bool; t_right : t }

          val t_left : triple -> t

          val t_in : triple -> bool

          val t_right : triple -> t

          val split : Coq_regex_as_UCT.t -> tree -> triple

          val inter : tree -> tree -> tree

          val diff : tree -> tree -> tree

          val union : tree -> tree -> tree

          val filter : (elt -> bool) -> tree -> tree

          val partition : (elt -> bool) -> t -> t * t

          val ltb_tree : Coq_regex_as_UCT.t -> tree -> bool

          val gtb_tree : Coq_regex_as_UCT.t -> tree -> bool

          val isok : tree -> bool

          module MX :
           sig
            module OrderTac :
             sig
              module OTF :
               sig
                type t = Coq_regex_as_UCT.t

                val compare :
                  Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

                val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
               end

              module TO :
               sig
                type t = Coq_regex_as_UCT.t

                val compare :
                  Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

                val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
               end
             end

            val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

            val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

            val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
           end

          type coq_R_min_elt =
          | R_min_elt_0 of tree
          | R_min_elt_1 of tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree
          | R_min_elt_2 of tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree
             * elt option * coq_R_min_elt

          type coq_R_max_elt =
          | R_max_elt_0 of tree
          | R_max_elt_1 of tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree
          | R_max_elt_2 of tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree
             * elt option * coq_R_max_elt

          module L :
           sig
            module MO :
             sig
              module OrderTac :
               sig
                module OTF :
                 sig
                  type t = Coq_regex_as_UCT.t

                  val compare :
                    Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

                  val eq_dec :
                    Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
                 end

                module TO :
                 sig
                  type t = Coq_regex_as_UCT.t

                  val compare :
                    Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

                  val eq_dec :
                    Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
                 end
               end

              val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
             end
           end

          val flatten_e : enumeration -> elt list

          type coq_R_bal =
          | R_bal_0 of t * Coq_regex_as_UCT.t * t
          | R_bal_1 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree
          | R_bal_2 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree
          | R_bal_3 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree
          | R_bal_4 of t * Coq_regex_as_UCT.t * t
          | R_bal_5 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree
          | R_bal_6 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree
          | R_bal_7 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree
          | R_bal_8 of t * Coq_regex_as_UCT.t * t

          type coq_R_remove_min =
          | R_remove_min_0 of tree * elt * t
          | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree * (t * elt) * coq_R_remove_min *
             t * elt

          type coq_R_merge =
          | R_merge_0 of tree * tree
          | R_merge_1 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree
          | R_merge_2 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree *
             t * elt

          type coq_R_concat =
          | R_concat_0 of tree * tree
          | R_concat_1 of tree * tree * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree
          | R_concat_2 of tree * tree * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree * t * elt

          type coq_R_inter =
          | R_inter_0 of tree * tree
          | R_inter_1 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree
          | R_inter_2 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree *
             t * bool * t * tree * coq_R_inter * tree * coq_R_inter
          | R_inter_3 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree *
             t * bool * t * tree * coq_R_inter * tree * coq_R_inter

          type coq_R_diff =
          | R_diff_0 of tree * tree
          | R_diff_1 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree
          | R_diff_2 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree *
             t * bool * t * tree * coq_R_diff * tree * coq_R_diff
          | R_diff_3 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree *
             t * bool * t * tree * coq_R_diff * tree * coq_R_diff

          type coq_R_union =
          | R_union_0 of tree * tree
          | R_union_1 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree
          | R_union_2 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree *
             t * bool * t * tree * coq_R_union * tree * coq_R_union
         end

        module E :
         sig
          type t = Coq_regex_as_UCT.t

          val compare : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

          val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
         end

        type elt = Coq_regex_as_UCT.t

        type t_ = Raw.t
          (* singleton inductive, whose constructor was Mkt *)

        val this : t_ -> Raw.t

        type t = t_

        val mem : elt -> t -> bool

        val add : elt -> t -> t

        val remove : elt -> t -> t

        val singleton : elt -> t

        val union : t -> t -> t

        val inter : t -> t -> t

        val diff : t -> t -> t

        val equal : t -> t -> bool

        val subset : t -> t -> bool

        val empty : t

        val is_empty : t -> bool

        val elements : t -> elt list

        val choose : t -> elt option

        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

        val cardinal : t -> nat

        val filter : (elt -> bool) -> t -> t

        val for_all : (elt -> bool) -> t -> bool

        val exists_ : (elt -> bool) -> t -> bool

        val partition : (elt -> bool) -> t -> t * t

        val eq_dec : t -> t -> bool

        val compare : t -> t -> comparison

        val min_elt : t -> elt option

        val max_elt : t -> elt option
       end

      type elt = Coq_regex_as_UCT.t

      type t = MSet.t

      val empty : t

      val is_empty : t -> bool

      val mem : elt -> t -> bool

      val add : elt -> t -> t

      val singleton : elt -> t

      val remove : elt -> t -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val eq_dec : t -> t -> bool

      val equal : t -> t -> bool

      val subset : t -> t -> bool

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val filter : (elt -> bool) -> t -> t

      val partition : (elt -> bool) -> t -> t * t

      val cardinal : t -> nat

      val elements : t -> elt list

      val choose : t -> elt option

      module MF :
       sig
        val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
       end

      val min_elt : t -> elt option

      val max_elt : t -> elt option

      val compare : t -> t -> t compare0

      module E :
       sig
        type t = Coq_regex_as_UCT.t

        val compare :
          Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t
          compare0

        val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
       end
     end

    module Coq_reFSF :
     sig
      val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
     end

    module Coq_reFM :
     sig
      module E :
       sig
        type t = Coq_regex_as_UCT.t

        val compare :
          Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t
          compare0

        val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
       end

      module Raw :
       sig
        type key = Coq_regex_as_UCT.t

        type 'elt tree =
        | Leaf
        | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

        val tree_rect :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val tree_rec :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val height : 'a1 tree -> Z_as_Int.t

        val cardinal : 'a1 tree -> nat

        val empty : 'a1 tree

        val is_empty : 'a1 tree -> bool

        val mem : Coq_regex_as_UCT.t -> 'a1 tree -> bool

        val find : Coq_regex_as_UCT.t -> 'a1 tree -> 'a1 option

        val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

        val remove_min :
          'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

        val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

        val remove : Coq_regex_as_UCT.t -> 'a1 tree -> 'a1 tree

        val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                             t_right : 'elt tree }

        val t_left : 'a1 triple -> 'a1 tree

        val t_opt : 'a1 triple -> 'a1 option

        val t_right : 'a1 triple -> 'a1 tree

        val split : Coq_regex_as_UCT.t -> 'a1 tree -> 'a1 triple

        val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

        val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

        val elements : 'a1 tree -> (key * 'a1) list

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

        type 'elt enumeration =
        | End
        | More of key * 'elt * 'elt tree * 'elt enumeration

        val enumeration_rect :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val enumeration_rec :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

        val equal_more :
          ('a1 -> 'a1 -> bool) -> Coq_regex_as_UCT.t -> 'a1 -> ('a1
          enumeration -> bool) -> 'a1 enumeration -> bool

        val equal_cont :
          ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
          'a1 enumeration -> bool

        val equal_end : 'a1 enumeration -> bool

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

        val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

        val map2_opt :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
          'a3 tree

        module Proofs :
         sig
          module MX :
           sig
            module TO :
             sig
              type t = Coq_regex_as_UCT.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

            val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

            val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
           end

          module PX :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = Coq_regex_as_UCT.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
             end
           end

          module L :
           sig
            module MX :
             sig
              module TO :
               sig
                type t = Coq_regex_as_UCT.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
             end

            module PX :
             sig
              module MO :
               sig
                module TO :
                 sig
                  type t = Coq_regex_as_UCT.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

                val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

                val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
               end
             end

            type key = Coq_regex_as_UCT.t

            type 'elt t = (Coq_regex_as_UCT.t * 'elt) list

            val empty : 'a1 t

            val is_empty : 'a1 t -> bool

            val mem : key -> 'a1 t -> bool

            type 'elt coq_R_mem =
            | R_mem_0 of 'elt t
            | R_mem_1 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_mem_2 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_mem_3 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list * bool * 'elt coq_R_mem

            val coq_R_mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> bool ->
              'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem
              -> 'a2

            val coq_R_mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> bool ->
              'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem
              -> 'a2

            val mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

            val find : key -> 'a1 t -> 'a1 option

            type 'elt coq_R_find =
            | R_find_0 of 'elt t
            | R_find_1 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_find_2 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_find_3 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list * 'elt option
               * 'elt coq_R_find

            val coq_R_find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 option
              -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
              coq_R_find -> 'a2

            val coq_R_find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 option
              -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
              coq_R_find -> 'a2

            val find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val coq_R_find_correct :
              key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

            val add : key -> 'a1 -> 'a1 t -> 'a1 t

            type 'elt coq_R_add =
            | R_add_0 of 'elt t
            | R_add_1 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_add_2 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_add_3 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list * 'elt t * 'elt coq_R_add

            val coq_R_add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list ->
              __ -> __ -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1
              -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
              'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
              -> 'a2

            val coq_R_add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list ->
              __ -> __ -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1
              -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
              'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
              -> 'a2

            val add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list ->
              __ -> __ -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1
              -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list ->
              __ -> __ -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1
              -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val coq_R_add_correct :
              key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

            val remove : key -> 'a1 t -> 'a1 t

            type 'elt coq_R_remove =
            | R_remove_0 of 'elt t
            | R_remove_1 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_remove_2 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_remove_3 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list * 'elt t * 'elt coq_R_remove

            val coq_R_remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
              'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
              coq_R_remove -> 'a2

            val coq_R_remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
              'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
              coq_R_remove -> 'a2

            val remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val coq_R_remove_correct :
              key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

            val elements : 'a1 t -> 'a1 t

            val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

            type ('elt, 'a) coq_R_fold =
            | R_fold_0 of 'elt t * 'a
            | R_fold_1 of 'elt t * 'a * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list * 'a * ('elt, 'a) coq_R_fold

            val coq_R_fold_rect :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
              coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
              coq_R_fold -> 'a3

            val coq_R_fold_rec :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
              coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
              coq_R_fold -> 'a3

            val fold_rect :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t
              -> 'a2 -> 'a3

            val fold_rec :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t
              -> 'a2 -> 'a3

            val coq_R_fold_correct :
              (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
              coq_R_fold

            val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

            type 'elt coq_R_equal =
            | R_equal_0 of 'elt t * 'elt t
            | R_equal_1 of 'elt t * 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list * Coq_regex_as_UCT.t *
               'elt * (Coq_regex_as_UCT.t * 'elt) list * bool
               * 'elt coq_R_equal
            | R_equal_2 of 'elt t * 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list * Coq_regex_as_UCT.t *
               'elt * (Coq_regex_as_UCT.t * 'elt) list
               * Coq_regex_as_UCT.t compare0
            | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

            val coq_R_equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
              Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list ->
              __ -> Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1)
              list -> __ -> Coq_regex_as_UCT.t compare0 -> __ -> __ -> 'a2)
              -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
              -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

            val coq_R_equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
              Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list ->
              __ -> Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1)
              list -> __ -> Coq_regex_as_UCT.t compare0 -> __ -> __ -> 'a2)
              -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
              -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

            val equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2
              -> 'a2) -> ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ ->
              Coq_regex_as_UCT.t compare0 -> __ -> __ -> 'a2) -> ('a1 t ->
              'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
              'a1 t -> 'a2

            val equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2
              -> 'a2) -> ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ ->
              Coq_regex_as_UCT.t compare0 -> __ -> __ -> 'a2) -> ('a1 t ->
              'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
              'a1 t -> 'a2

            val coq_R_equal_correct :
              ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
              coq_R_equal

            val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

            val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

            val option_cons :
              key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

            val map2_l :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

            val map2_r :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

            val map2 :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              'a3 t

            val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

            val fold_right_pair :
              ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

            val map2_alt :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              (key * 'a3) list

            val at_least_one :
              'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

            val at_least_one_then_f :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
              option -> 'a3 option
           end

          type 'elt coq_R_mem =
          | R_mem_0 of 'elt tree
          | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem
          | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem

          val coq_R_mem_rect :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
            tree -> bool -> 'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
            tree -> bool -> 'a1 coq_R_mem -> 'a2

          type 'elt coq_R_find =
          | R_find_0 of 'elt tree
          | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find
          | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find

          val coq_R_find_rect :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
            'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

          val coq_R_find_rec :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
            'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

          type 'elt coq_R_bal =
          | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

          val coq_R_bal_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          val coq_R_bal_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          type 'elt coq_R_add =
          | R_add_0 of 'elt tree
          | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add
          | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          type 'elt coq_R_remove_min =
          | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
          | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
             * key * 'elt * 'elt tree * Z_as_Int.t
             * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min * 'elt tree
             * (key * 'elt)

          val coq_R_remove_min_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          val coq_R_remove_min_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          type 'elt coq_R_merge =
          | R_merge_0 of 'elt tree * 'elt tree
          | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

          val coq_R_merge_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2

          val coq_R_merge_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt tree
          | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
          | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

          val coq_R_remove_rect :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
            'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

          val coq_R_remove_rec :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
            'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

          type 'elt coq_R_concat =
          | R_concat_0 of 'elt tree * 'elt tree
          | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt)

          val coq_R_concat_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

          val coq_R_concat_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

          type 'elt coq_R_split =
          | R_split_0 of 'elt tree
          | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree
          | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree

          val coq_R_split_rect :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option ->
            'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
            'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
            option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
            coq_R_split -> 'a2

          val coq_R_split_rec :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option ->
            'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
            'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
            option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
            coq_R_split -> 'a2

          type ('elt, 'x) coq_R_map_option =
          | R_map_option_0 of 'elt tree
          | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
             * 'x tree * ('elt, 'x) coq_R_map_option
          | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
             * ('elt, 'x) coq_R_map_option

          val coq_R_map_option_rect :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          val coq_R_map_option_rec :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          type ('elt, 'x0, 'x) coq_R_map2_opt =
          | R_map2_opt_0 of 'elt tree * 'x0 tree
          | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t
          | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
             * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt
          | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
             * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt

          val coq_R_map2_opt_rect :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val coq_R_map2_opt_rec :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

          val flatten_e : 'a1 enumeration -> (key * 'a1) list
         end
       end

      type 'elt bst =
        'elt Raw.tree
        (* singleton inductive, whose constructor was Bst *)

      val this : 'a1 bst -> 'a1 Raw.tree

      type 'elt t = 'elt bst

      type key = Coq_regex_as_UCT.t

      val empty : 'a1 t

      val is_empty : 'a1 t -> bool

      val add : key -> 'a1 -> 'a1 t -> 'a1 t

      val remove : key -> 'a1 t -> 'a1 t

      val mem : key -> 'a1 t -> bool

      val find : key -> 'a1 t -> 'a1 option

      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

      val elements : 'a1 t -> (key * 'a1) list

      val cardinal : 'a1 t -> nat

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
     end

    module Coq_reFMF :
     sig
      val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

      val coq_In_dec : 'a1 Coq_reFM.t -> Coq_reFM.key -> bool
     end

    module MatchSpec :
     sig
     end

    module MatchSpecLemmas :
     sig
     end

    module Notations :
     sig
     end

    module Helpers :
     sig
      val coq_Plus : Regexes.regex -> Regexes.regex

      val coq_IterUnion : Regexes.regex list -> Regexes.regex

      val coq_IterApp : Regexes.regex list -> Regexes.regex

      val coq_Optional : Regexes.regex -> Regexes.regex

      val coq_REString : Strings.coq_String -> Regexes.regex
     end
   end
 end

module Coq_DefsFn =
 functor (R:T) ->
 functor (Ty:sig
  type coq_Pointer

  val defPointer : coq_Pointer

  type coq_Delta

  val defDelta : coq_Delta

  type coq_State = coq_Pointer * coq_Delta

  val defState : coq_State

  val transition : R.Ty.coq_Sigma -> coq_State -> coq_State

  val transition_list : R.Ty.coq_Sigma list -> coq_State -> coq_State

  val accepts : R.Defs.Strings.coq_String -> coq_State -> bool

  val accepting : coq_State -> bool

  val init_state : R.Defs.Regexes.regex -> coq_State

  val init_state_inv : coq_State -> R.Defs.Regexes.regex

  val pointer_compare : coq_Pointer -> coq_Pointer -> comparison
 end) ->
 struct
  module Pointer_as_UCT =
   struct
    type t = Ty.coq_Pointer

    (** val compare : Ty.coq_Pointer -> Ty.coq_Pointer -> comparison **)

    let compare =
      Ty.pointer_compare
   end

  module Coredefs =
   struct
    type coq_Label = R.Defs.Strings.coq_String

    type coq_Prefix = R.Defs.Strings.coq_String

    type coq_Suffix = R.Defs.Strings.coq_String

    type coq_Token = coq_Label * coq_Prefix

    type coq_Rule = coq_Label * R.Defs.Regexes.regex

    type sRule = coq_Label * Ty.coq_State
   end

  module MaxMunchSpec =
   struct
   end

  module Corollaries =
   struct
    (** val ru_dec : Coredefs.coq_Rule -> Coredefs.coq_Rule -> bool **)

    let ru_dec ru1 ru2 =
      let (l, r) = ru1 in
      let (l0, r0) = ru2 in
      let s = R.Defs.Strings.coq_String_dec l l0 in
      if s then R.Defs.Regexes.regex_dec r r0 else false
   end
 end

module type Coq_T =
 sig
  module R :
   T

  module Ty :
   sig
    type coq_Pointer

    val defPointer : coq_Pointer

    type coq_Delta

    val defDelta : coq_Delta

    type coq_State = coq_Pointer * coq_Delta

    val defState : coq_State

    val transition : R.Ty.coq_Sigma -> coq_State -> coq_State

    val transition_list : R.Ty.coq_Sigma list -> coq_State -> coq_State

    val accepts : R.Defs.Strings.coq_String -> coq_State -> bool

    val accepting : coq_State -> bool

    val init_state : R.Defs.Regexes.regex -> coq_State

    val init_state_inv : coq_State -> R.Defs.Regexes.regex

    val pointer_compare : coq_Pointer -> coq_Pointer -> comparison
   end

  module Defs :
   sig
    module Pointer_as_UCT :
     sig
      type t = Ty.coq_Pointer

      val compare : Ty.coq_Pointer -> Ty.coq_Pointer -> comparison
     end

    module Coredefs :
     sig
      type coq_Label = R.Defs.Strings.coq_String

      type coq_Prefix = R.Defs.Strings.coq_String

      type coq_Suffix = R.Defs.Strings.coq_String

      type coq_Token = coq_Label * coq_Prefix

      type coq_Rule = coq_Label * R.Defs.Regexes.regex

      type sRule = coq_Label * Ty.coq_State
     end

    module MaxMunchSpec :
     sig
     end

    module Corollaries :
     sig
      val ru_dec : Coredefs.coq_Rule -> Coredefs.coq_Rule -> bool
     end
   end
 end

module Coq0_DefsFn =
 functor (R:T) ->
 functor (TabTy:sig
  module DS :
   sig
    module T_as_UCT :
     sig
      type t = R.Ty.coq_Sigma

      val compare : R.Ty.coq_Sigma -> R.Ty.coq_Sigma -> comparison
     end

    module T_as_UOT :
     sig
      type t = T_as_UCT.t

      val compare : t -> t -> t compare0

      val eq_dec : t -> t -> bool
     end

    module SigFS :
     sig
      module X' :
       sig
        type t = T_as_UCT.t

        val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

        val compare : T_as_UCT.t -> T_as_UCT.t -> comparison
       end

      module MSet :
       sig
        module Raw :
         sig
          type elt = T_as_UCT.t

          type tree = R.Defs.SigFS.MSet.Raw.tree =
          | Leaf
          | Node of Z_as_Int.t * tree * T_as_UCT.t * tree

          val empty : tree

          val is_empty : tree -> bool

          val mem : T_as_UCT.t -> tree -> bool

          val min_elt : tree -> elt option

          val max_elt : tree -> elt option

          val choose : tree -> elt option

          val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

          val elements_aux : T_as_UCT.t list -> tree -> T_as_UCT.t list

          val elements : tree -> T_as_UCT.t list

          val rev_elements_aux : T_as_UCT.t list -> tree -> T_as_UCT.t list

          val rev_elements : tree -> T_as_UCT.t list

          val cardinal : tree -> nat

          val maxdepth : tree -> nat

          val mindepth : tree -> nat

          val for_all : (elt -> bool) -> tree -> bool

          val exists_ : (elt -> bool) -> tree -> bool

          type enumeration = R.Defs.SigFS.MSet.Raw.enumeration =
          | End
          | More of elt * tree * enumeration

          val cons : tree -> enumeration -> enumeration

          val compare_more :
            T_as_UCT.t -> (enumeration -> comparison) -> enumeration ->
            comparison

          val compare_cont :
            tree -> (enumeration -> comparison) -> enumeration -> comparison

          val compare_end : enumeration -> comparison

          val compare : tree -> tree -> comparison

          val equal : tree -> tree -> bool

          val subsetl : (tree -> bool) -> T_as_UCT.t -> tree -> bool

          val subsetr : (tree -> bool) -> T_as_UCT.t -> tree -> bool

          val subset : tree -> tree -> bool

          type t = tree

          val height : t -> Z_as_Int.t

          val singleton : T_as_UCT.t -> tree

          val create : t -> T_as_UCT.t -> t -> tree

          val assert_false : t -> T_as_UCT.t -> t -> tree

          val bal : t -> T_as_UCT.t -> t -> tree

          val add : T_as_UCT.t -> tree -> tree

          val join : tree -> elt -> t -> t

          val remove_min : tree -> elt -> t -> t * elt

          val merge : tree -> tree -> tree

          val remove : T_as_UCT.t -> tree -> tree

          val concat : tree -> tree -> tree

          type triple = R.Defs.SigFS.MSet.Raw.triple = { t_left : t;
                                                         t_in : bool;
                                                         t_right : t }

          val t_left : triple -> t

          val t_in : triple -> bool

          val t_right : triple -> t

          val split : T_as_UCT.t -> tree -> triple

          val inter : tree -> tree -> tree

          val diff : tree -> tree -> tree

          val union : tree -> tree -> tree

          val filter : (elt -> bool) -> tree -> tree

          val partition : (elt -> bool) -> t -> t * t

          val ltb_tree : T_as_UCT.t -> tree -> bool

          val gtb_tree : T_as_UCT.t -> tree -> bool

          val isok : tree -> bool

          module MX :
           sig
            module OrderTac :
             sig
              module OTF :
               sig
                type t = T_as_UCT.t

                val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

                val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
               end

              module TO :
               sig
                type t = T_as_UCT.t

                val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

                val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
               end
             end

            val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

            val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

            val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
           end

          type coq_R_min_elt = R.Defs.SigFS.MSet.Raw.coq_R_min_elt =
          | R_min_elt_0 of tree
          | R_min_elt_1 of tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_min_elt_2 of tree * Z_as_Int.t * tree * T_as_UCT.t * tree
             * Z_as_Int.t * tree * T_as_UCT.t * tree * elt option
             * coq_R_min_elt

          type coq_R_max_elt = R.Defs.SigFS.MSet.Raw.coq_R_max_elt =
          | R_max_elt_0 of tree
          | R_max_elt_1 of tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_max_elt_2 of tree * Z_as_Int.t * tree * T_as_UCT.t * tree
             * Z_as_Int.t * tree * T_as_UCT.t * tree * elt option
             * coq_R_max_elt

          module L :
           sig
            module MO :
             sig
              module OrderTac :
               sig
                module OTF :
                 sig
                  type t = T_as_UCT.t

                  val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

                  val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
                 end

                module TO :
                 sig
                  type t = T_as_UCT.t

                  val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

                  val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
                 end
               end

              val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
             end
           end

          val flatten_e : enumeration -> elt list

          type coq_R_bal = R.Defs.SigFS.MSet.Raw.coq_R_bal =
          | R_bal_0 of t * T_as_UCT.t * t
          | R_bal_1 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
             * tree
          | R_bal_2 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
             * tree
          | R_bal_3 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
             * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_bal_4 of t * T_as_UCT.t * t
          | R_bal_5 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
             * tree
          | R_bal_6 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
             * tree
          | R_bal_7 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
             * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_bal_8 of t * T_as_UCT.t * t

          type coq_R_remove_min = R.Defs.SigFS.MSet.Raw.coq_R_remove_min =
          | R_remove_min_0 of tree * elt * t
          | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree * T_as_UCT.t
             * tree * (t * elt) * coq_R_remove_min * t * elt

          type coq_R_merge = R.Defs.SigFS.MSet.Raw.coq_R_merge =
          | R_merge_0 of tree * tree
          | R_merge_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_merge_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
             tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * elt

          type coq_R_concat = R.Defs.SigFS.MSet.Raw.coq_R_concat =
          | R_concat_0 of tree * tree
          | R_concat_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_concat_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
             tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * elt

          type coq_R_inter = R.Defs.SigFS.MSet.Raw.coq_R_inter =
          | R_inter_0 of tree * tree
          | R_inter_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_inter_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
             tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
             t * tree * coq_R_inter * tree * coq_R_inter
          | R_inter_3 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
             tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
             t * tree * coq_R_inter * tree * coq_R_inter

          type coq_R_diff = R.Defs.SigFS.MSet.Raw.coq_R_diff =
          | R_diff_0 of tree * tree
          | R_diff_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_diff_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
             tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
             t * tree * coq_R_diff * tree * coq_R_diff
          | R_diff_3 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
             tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
             t * tree * coq_R_diff * tree * coq_R_diff

          type coq_R_union = R.Defs.SigFS.MSet.Raw.coq_R_union =
          | R_union_0 of tree * tree
          | R_union_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
          | R_union_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
             tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
             t * tree * coq_R_union * tree * coq_R_union
         end

        module E :
         sig
          type t = T_as_UCT.t

          val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

          val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
         end

        type elt = T_as_UCT.t

        type t_ = Raw.t
          (* singleton inductive, whose constructor was Mkt *)

        val this : t_ -> Raw.t

        type t = t_

        val mem : elt -> t -> bool

        val add : elt -> t -> t

        val remove : elt -> t -> t

        val singleton : elt -> t

        val union : t -> t -> t

        val inter : t -> t -> t

        val diff : t -> t -> t

        val equal : t -> t -> bool

        val subset : t -> t -> bool

        val empty : t

        val is_empty : t -> bool

        val elements : t -> elt list

        val choose : t -> elt option

        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

        val cardinal : t -> nat

        val filter : (elt -> bool) -> t -> t

        val for_all : (elt -> bool) -> t -> bool

        val exists_ : (elt -> bool) -> t -> bool

        val partition : (elt -> bool) -> t -> t * t

        val eq_dec : t -> t -> bool

        val compare : t -> t -> comparison

        val min_elt : t -> elt option

        val max_elt : t -> elt option
       end

      type elt = T_as_UCT.t

      type t = MSet.t

      val empty : t

      val is_empty : t -> bool

      val mem : elt -> t -> bool

      val add : elt -> t -> t

      val singleton : elt -> t

      val remove : elt -> t -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val eq_dec : t -> t -> bool

      val equal : t -> t -> bool

      val subset : t -> t -> bool

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val filter : (elt -> bool) -> t -> t

      val partition : (elt -> bool) -> t -> t * t

      val cardinal : t -> nat

      val elements : t -> elt list

      val choose : t -> elt option

      module MF :
       sig
        val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
       end

      val min_elt : t -> elt option

      val max_elt : t -> elt option

      val compare : t -> t -> t compare0

      module E :
       sig
        type t = T_as_UCT.t

        val compare : T_as_UCT.t -> T_as_UCT.t -> T_as_UCT.t compare0

        val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
       end
     end

    module SigFSF :
     sig
      val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
     end

    module SigFM :
     sig
      module E :
       sig
        type t = T_as_UCT.t

        val compare : T_as_UCT.t -> T_as_UCT.t -> T_as_UCT.t compare0

        val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
       end

      module Raw :
       sig
        type key = T_as_UCT.t

        type 'elt tree = 'elt R.Defs.SigFM.Raw.tree =
        | Leaf
        | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

        val tree_rect :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val tree_rec :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val height : 'a1 tree -> Z_as_Int.t

        val cardinal : 'a1 tree -> nat

        val empty : 'a1 tree

        val is_empty : 'a1 tree -> bool

        val mem : T_as_UCT.t -> 'a1 tree -> bool

        val find : T_as_UCT.t -> 'a1 tree -> 'a1 option

        val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

        val remove_min :
          'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

        val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

        val remove : T_as_UCT.t -> 'a1 tree -> 'a1 tree

        val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        type 'elt triple = 'elt R.Defs.SigFM.Raw.triple = { t_left :
                                                            'elt tree;
                                                            t_opt : 'elt
                                                                    option;
                                                            t_right :
                                                            'elt tree }

        val t_left : 'a1 triple -> 'a1 tree

        val t_opt : 'a1 triple -> 'a1 option

        val t_right : 'a1 triple -> 'a1 tree

        val split : T_as_UCT.t -> 'a1 tree -> 'a1 triple

        val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

        val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

        val elements : 'a1 tree -> (key * 'a1) list

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

        type 'elt enumeration = 'elt R.Defs.SigFM.Raw.enumeration =
        | End
        | More of key * 'elt * 'elt tree * 'elt enumeration

        val enumeration_rect :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val enumeration_rec :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

        val equal_more :
          ('a1 -> 'a1 -> bool) -> T_as_UCT.t -> 'a1 -> ('a1 enumeration ->
          bool) -> 'a1 enumeration -> bool

        val equal_cont :
          ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
          'a1 enumeration -> bool

        val equal_end : 'a1 enumeration -> bool

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

        val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

        val map2_opt :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
          'a3 tree

        module Proofs :
         sig
          module MX :
           sig
            module TO :
             sig
              type t = T_as_UCT.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

            val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

            val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
           end

          module PX :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = T_as_UCT.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
             end
           end

          module L :
           sig
            module MX :
             sig
              module TO :
               sig
                type t = T_as_UCT.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
             end

            module PX :
             sig
              module MO :
               sig
                module TO :
                 sig
                  type t = T_as_UCT.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

                val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

                val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
               end
             end

            type key = T_as_UCT.t

            type 'elt t = (T_as_UCT.t * 'elt) list

            val empty : 'a1 t

            val is_empty : 'a1 t -> bool

            val mem : key -> 'a1 t -> bool

            type 'elt coq_R_mem = 'elt R.Defs.SigFM.Raw.Proofs.L.coq_R_mem =
            | R_mem_0 of 'elt t
            | R_mem_1 of 'elt t * T_as_UCT.t * 'elt * (T_as_UCT.t * 'elt) list
            | R_mem_2 of 'elt t * T_as_UCT.t * 'elt * (T_as_UCT.t * 'elt) list
            | R_mem_3 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * bool * 'elt coq_R_mem

            val coq_R_mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
              -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

            val coq_R_mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
              -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

            val mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

            val find : key -> 'a1 t -> 'a1 option

            type 'elt coq_R_find = 'elt R.Defs.SigFM.Raw.Proofs.L.coq_R_find =
            | R_find_0 of 'elt t
            | R_find_1 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list
            | R_find_2 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list
            | R_find_3 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * 'elt option * 'elt coq_R_find

            val coq_R_find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2
              -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

            val coq_R_find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2
              -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

            val find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val coq_R_find_correct :
              key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

            val add : key -> 'a1 -> 'a1 t -> 'a1 t

            type 'elt coq_R_add = 'elt R.Defs.SigFM.Raw.Proofs.L.coq_R_add =
            | R_add_0 of 'elt t
            | R_add_1 of 'elt t * T_as_UCT.t * 'elt * (T_as_UCT.t * 'elt) list
            | R_add_2 of 'elt t * T_as_UCT.t * 'elt * (T_as_UCT.t * 'elt) list
            | R_add_3 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * 'elt t * 'elt coq_R_add

            val coq_R_add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t ->
              'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
              coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add ->
              'a2

            val coq_R_add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t ->
              'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
              coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add ->
              'a2

            val add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t ->
              'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
              t -> 'a2

            val add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t ->
              'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1
              t -> 'a2

            val coq_R_add_correct :
              key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

            val remove : key -> 'a1 t -> 'a1 t

            type 'elt coq_R_remove = 'elt R.Defs.SigFM.Raw.Proofs.L.coq_R_remove =
            | R_remove_0 of 'elt t
            | R_remove_1 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list
            | R_remove_2 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list
            | R_remove_3 of 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * 'elt t * 'elt coq_R_remove

            val coq_R_remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 ->
              'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

            val coq_R_remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 ->
              'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

            val remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __
              -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
              list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

            val coq_R_remove_correct :
              key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

            val elements : 'a1 t -> 'a1 t

            val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

            type ('elt, 'a) coq_R_fold = ('elt, 'a) R.Defs.SigFM.Raw.Proofs.L.coq_R_fold =
            | R_fold_0 of 'elt t * 'a
            | R_fold_1 of 'elt t * 'a * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * 'a * ('elt, 'a) coq_R_fold

            val coq_R_fold_rect :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t
              -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

            val coq_R_fold_rec :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t
              -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

            val fold_rect :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

            val fold_rec :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

            val coq_R_fold_correct :
              (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
              coq_R_fold

            val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

            type 'elt coq_R_equal = 'elt R.Defs.SigFM.Raw.Proofs.L.coq_R_equal =
            | R_equal_0 of 'elt t * 'elt t
            | R_equal_1 of 'elt t * 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * bool * 'elt coq_R_equal
            | R_equal_2 of 'elt t * 'elt t * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * T_as_UCT.t * 'elt
               * (T_as_UCT.t * 'elt) list * T_as_UCT.t compare0
            | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

            val coq_R_equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t ->
              'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              T_as_UCT.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
              'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t ->
              bool -> 'a1 coq_R_equal -> 'a2

            val coq_R_equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t ->
              'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              T_as_UCT.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
              'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t ->
              bool -> 'a1 coq_R_equal -> 'a2

            val equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1
              -> (T_as_UCT.t * 'a1) list -> __ -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> T_as_UCT.t compare0 -> __ ->
              __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ ->
              __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

            val equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
              -> __ -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
              __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1
              -> (T_as_UCT.t * 'a1) list -> __ -> T_as_UCT.t -> 'a1 ->
              (T_as_UCT.t * 'a1) list -> __ -> T_as_UCT.t compare0 -> __ ->
              __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ ->
              __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

            val coq_R_equal_correct :
              ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
              coq_R_equal

            val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

            val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

            val option_cons :
              key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

            val map2_l :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

            val map2_r :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

            val map2 :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              'a3 t

            val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

            val fold_right_pair :
              ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

            val map2_alt :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              (key * 'a3) list

            val at_least_one :
              'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

            val at_least_one_then_f :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
              option -> 'a3 option
           end

          type 'elt coq_R_mem = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_mem =
          | R_mem_0 of 'elt tree
          | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem
          | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem

          val coq_R_mem_rect :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool ->
            'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree ->
            bool -> 'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool ->
            'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree ->
            bool -> 'a1 coq_R_mem -> 'a2

          type 'elt coq_R_find = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_find =
          | R_find_0 of 'elt tree
          | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find
          | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find

          val coq_R_find_rect :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2)
            -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
            -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2)
            -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

          val coq_R_find_rec :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2)
            -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
            -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2)
            -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

          type 'elt coq_R_bal = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_bal =
          | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

          val coq_R_bal_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          val coq_R_bal_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          type 'elt coq_R_add = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_add =
          | R_add_0 of 'elt tree
          | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add
          | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          type 'elt coq_R_remove_min = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_remove_min =
          | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
          | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
             * key * 'elt * 'elt tree * Z_as_Int.t
             * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min * 'elt tree
             * (key * 'elt)

          val coq_R_remove_min_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          val coq_R_remove_min_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          type 'elt coq_R_merge = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_merge =
          | R_merge_0 of 'elt tree * 'elt tree
          | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

          val coq_R_merge_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2

          val coq_R_merge_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2

          type 'elt coq_R_remove = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_remove =
          | R_remove_0 of 'elt tree
          | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
          | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

          val coq_R_remove_rect :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2)
            -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
            -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2)
            -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

          val coq_R_remove_rec :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree
            -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2)
            -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
            -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2)
            -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

          type 'elt coq_R_concat = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_concat =
          | R_concat_0 of 'elt tree * 'elt tree
          | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt)

          val coq_R_concat_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

          val coq_R_concat_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

          type 'elt coq_R_split = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_split =
          | R_split_0 of 'elt tree
          | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree
          | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree

          val coq_R_split_rect :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
            tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option ->
            'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
            coq_R_split -> 'a2

          val coq_R_split_rec :
            T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
            tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option ->
            'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
            coq_R_split -> 'a2

          type ('elt, 'x) coq_R_map_option = ('elt, 'x) R.Defs.SigFM.Raw.Proofs.coq_R_map_option =
          | R_map_option_0 of 'elt tree
          | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
             * 'x tree * ('elt, 'x) coq_R_map_option
          | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
             * ('elt, 'x) coq_R_map_option

          val coq_R_map_option_rect :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          val coq_R_map_option_rec :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          type ('elt, 'x0, 'x) coq_R_map2_opt = ('elt, 'x0, 'x) R.Defs.SigFM.Raw.Proofs.coq_R_map2_opt =
          | R_map2_opt_0 of 'elt tree * 'x0 tree
          | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t
          | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
             * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt
          | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
             * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt

          val coq_R_map2_opt_rect :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val coq_R_map2_opt_rec :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

          val flatten_e : 'a1 enumeration -> (key * 'a1) list
         end
       end

      type 'elt bst =
        'elt Raw.tree
        (* singleton inductive, whose constructor was Bst *)

      val this : 'a1 bst -> 'a1 Raw.tree

      type 'elt t = 'elt bst

      type key = T_as_UCT.t

      val empty : 'a1 t

      val is_empty : 'a1 t -> bool

      val add : key -> 'a1 -> 'a1 t -> 'a1 t

      val remove : key -> 'a1 t -> 'a1 t

      val mem : key -> 'a1 t -> bool

      val find : key -> 'a1 t -> 'a1 option

      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

      val elements : 'a1 t -> (key * 'a1) list

      val cardinal : 'a1 t -> nat

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
     end

    module SigFMF :
     sig
      val eqb : T_as_UCT.t -> T_as_UCT.t -> bool

      val coq_In_dec : 'a1 SigFM.t -> SigFM.key -> bool
     end

    module Strings :
     sig
      type coq_String = R.Ty.coq_Sigma list

      val coq_String_dec : coq_String -> coq_String -> bool

      val rm_empty : coq_String list -> R.Ty.coq_Sigma list list
     end

    module Regexes :
     sig
      type regex = R.Defs.Regexes.regex =
      | EmptySet
      | EmptyStr
      | Char of R.Ty.coq_Sigma
      | App of regex * regex
      | Union of regex * regex
      | Star of regex

      val regex_rect :
        'a1 -> 'a1 -> (R.Ty.coq_Sigma -> 'a1) -> (regex -> 'a1 -> regex ->
        'a1 -> 'a1) -> (regex -> 'a1 -> regex -> 'a1 -> 'a1) -> (regex -> 'a1
        -> 'a1) -> regex -> 'a1

      val regex_rec :
        'a1 -> 'a1 -> (R.Ty.coq_Sigma -> 'a1) -> (regex -> 'a1 -> regex ->
        'a1 -> 'a1) -> (regex -> 'a1 -> regex -> 'a1 -> 'a1) -> (regex -> 'a1
        -> 'a1) -> regex -> 'a1

      val regex_dec : regex -> regex -> bool

      val regex_eq : regex -> regex -> bool

      val nullable' : regex -> bool

      val nullable : regex -> bool

      val derivative : R.Ty.coq_Sigma -> regex -> regex

      val derivative_list : R.Ty.coq_Sigma list -> regex -> regex

      val re_compare : regex -> regex -> comparison
     end

    module Coq_regex_as_UCT :
     sig
      type t = Regexes.regex

      val compare : Regexes.regex -> Regexes.regex -> comparison
     end

    module Coq_regex_as_UOT :
     sig
      type t = Coq_regex_as_UCT.t

      val compare : t -> t -> t compare0

      val eq_dec : t -> t -> bool
     end

    module Coq_reFS :
     sig
      module X' :
       sig
        type t = Coq_regex_as_UCT.t

        val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

        val compare : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison
       end

      module MSet :
       sig
        module Raw :
         sig
          type elt = Coq_regex_as_UCT.t

          type tree = R.Defs.Coq_reFS.MSet.Raw.tree =
          | Leaf
          | Node of Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree

          val empty : tree

          val is_empty : tree -> bool

          val mem : Coq_regex_as_UCT.t -> tree -> bool

          val min_elt : tree -> elt option

          val max_elt : tree -> elt option

          val choose : tree -> elt option

          val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

          val elements_aux :
            Coq_regex_as_UCT.t list -> tree -> Coq_regex_as_UCT.t list

          val elements : tree -> Coq_regex_as_UCT.t list

          val rev_elements_aux :
            Coq_regex_as_UCT.t list -> tree -> Coq_regex_as_UCT.t list

          val rev_elements : tree -> Coq_regex_as_UCT.t list

          val cardinal : tree -> nat

          val maxdepth : tree -> nat

          val mindepth : tree -> nat

          val for_all : (elt -> bool) -> tree -> bool

          val exists_ : (elt -> bool) -> tree -> bool

          type enumeration = R.Defs.Coq_reFS.MSet.Raw.enumeration =
          | End
          | More of elt * tree * enumeration

          val cons : tree -> enumeration -> enumeration

          val compare_more :
            Coq_regex_as_UCT.t -> (enumeration -> comparison) -> enumeration
            -> comparison

          val compare_cont :
            tree -> (enumeration -> comparison) -> enumeration -> comparison

          val compare_end : enumeration -> comparison

          val compare : tree -> tree -> comparison

          val equal : tree -> tree -> bool

          val subsetl : (tree -> bool) -> Coq_regex_as_UCT.t -> tree -> bool

          val subsetr : (tree -> bool) -> Coq_regex_as_UCT.t -> tree -> bool

          val subset : tree -> tree -> bool

          type t = tree

          val height : t -> Z_as_Int.t

          val singleton : Coq_regex_as_UCT.t -> tree

          val create : t -> Coq_regex_as_UCT.t -> t -> tree

          val assert_false : t -> Coq_regex_as_UCT.t -> t -> tree

          val bal : t -> Coq_regex_as_UCT.t -> t -> tree

          val add : Coq_regex_as_UCT.t -> tree -> tree

          val join : tree -> elt -> t -> t

          val remove_min : tree -> elt -> t -> t * elt

          val merge : tree -> tree -> tree

          val remove : Coq_regex_as_UCT.t -> tree -> tree

          val concat : tree -> tree -> tree

          type triple = R.Defs.Coq_reFS.MSet.Raw.triple = { t_left :
                                                            t; t_in :
                                                            bool; t_right :
                                                            t }

          val t_left : triple -> t

          val t_in : triple -> bool

          val t_right : triple -> t

          val split : Coq_regex_as_UCT.t -> tree -> triple

          val inter : tree -> tree -> tree

          val diff : tree -> tree -> tree

          val union : tree -> tree -> tree

          val filter : (elt -> bool) -> tree -> tree

          val partition : (elt -> bool) -> t -> t * t

          val ltb_tree : Coq_regex_as_UCT.t -> tree -> bool

          val gtb_tree : Coq_regex_as_UCT.t -> tree -> bool

          val isok : tree -> bool

          module MX :
           sig
            module OrderTac :
             sig
              module OTF :
               sig
                type t = Coq_regex_as_UCT.t

                val compare :
                  Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

                val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
               end

              module TO :
               sig
                type t = Coq_regex_as_UCT.t

                val compare :
                  Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

                val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
               end
             end

            val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

            val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

            val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
           end

          type coq_R_min_elt = R.Defs.Coq_reFS.MSet.Raw.coq_R_min_elt =
          | R_min_elt_0 of tree
          | R_min_elt_1 of tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree
          | R_min_elt_2 of tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree
             * elt option * coq_R_min_elt

          type coq_R_max_elt = R.Defs.Coq_reFS.MSet.Raw.coq_R_max_elt =
          | R_max_elt_0 of tree
          | R_max_elt_1 of tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree
          | R_max_elt_2 of tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree
             * elt option * coq_R_max_elt

          module L :
           sig
            module MO :
             sig
              module OrderTac :
               sig
                module OTF :
                 sig
                  type t = Coq_regex_as_UCT.t

                  val compare :
                    Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

                  val eq_dec :
                    Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
                 end

                module TO :
                 sig
                  type t = Coq_regex_as_UCT.t

                  val compare :
                    Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

                  val eq_dec :
                    Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
                 end
               end

              val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
             end
           end

          val flatten_e : enumeration -> elt list

          type coq_R_bal = R.Defs.Coq_reFS.MSet.Raw.coq_R_bal =
          | R_bal_0 of t * Coq_regex_as_UCT.t * t
          | R_bal_1 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree
          | R_bal_2 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree
          | R_bal_3 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree
          | R_bal_4 of t * Coq_regex_as_UCT.t * t
          | R_bal_5 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree
          | R_bal_6 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree
          | R_bal_7 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree
          | R_bal_8 of t * Coq_regex_as_UCT.t * t

          type coq_R_remove_min = R.Defs.Coq_reFS.MSet.Raw.coq_R_remove_min =
          | R_remove_min_0 of tree * elt * t
          | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree * (t * elt) * coq_R_remove_min *
             t * elt

          type coq_R_merge = R.Defs.Coq_reFS.MSet.Raw.coq_R_merge =
          | R_merge_0 of tree * tree
          | R_merge_1 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree
          | R_merge_2 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree *
             t * elt

          type coq_R_concat = R.Defs.Coq_reFS.MSet.Raw.coq_R_concat =
          | R_concat_0 of tree * tree
          | R_concat_1 of tree * tree * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree
          | R_concat_2 of tree * tree * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * Coq_regex_as_UCT.t * tree * t * elt

          type coq_R_inter = R.Defs.Coq_reFS.MSet.Raw.coq_R_inter =
          | R_inter_0 of tree * tree
          | R_inter_1 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree
          | R_inter_2 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree *
             t * bool * t * tree * coq_R_inter * tree * coq_R_inter
          | R_inter_3 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree *
             t * bool * t * tree * coq_R_inter * tree * coq_R_inter

          type coq_R_diff = R.Defs.Coq_reFS.MSet.Raw.coq_R_diff =
          | R_diff_0 of tree * tree
          | R_diff_1 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree
          | R_diff_2 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree *
             t * bool * t * tree * coq_R_diff * tree * coq_R_diff
          | R_diff_3 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree *
             t * bool * t * tree * coq_R_diff * tree * coq_R_diff

          type coq_R_union = R.Defs.Coq_reFS.MSet.Raw.coq_R_union =
          | R_union_0 of tree * tree
          | R_union_1 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree
          | R_union_2 of tree * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree *
             t * bool * t * tree * coq_R_union * tree * coq_R_union
         end

        module E :
         sig
          type t = Coq_regex_as_UCT.t

          val compare : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

          val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
         end

        type elt = Coq_regex_as_UCT.t

        type t_ = Raw.t
          (* singleton inductive, whose constructor was Mkt *)

        val this : t_ -> Raw.t

        type t = t_

        val mem : elt -> t -> bool

        val add : elt -> t -> t

        val remove : elt -> t -> t

        val singleton : elt -> t

        val union : t -> t -> t

        val inter : t -> t -> t

        val diff : t -> t -> t

        val equal : t -> t -> bool

        val subset : t -> t -> bool

        val empty : t

        val is_empty : t -> bool

        val elements : t -> elt list

        val choose : t -> elt option

        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

        val cardinal : t -> nat

        val filter : (elt -> bool) -> t -> t

        val for_all : (elt -> bool) -> t -> bool

        val exists_ : (elt -> bool) -> t -> bool

        val partition : (elt -> bool) -> t -> t * t

        val eq_dec : t -> t -> bool

        val compare : t -> t -> comparison

        val min_elt : t -> elt option

        val max_elt : t -> elt option
       end

      type elt = Coq_regex_as_UCT.t

      type t = MSet.t

      val empty : t

      val is_empty : t -> bool

      val mem : elt -> t -> bool

      val add : elt -> t -> t

      val singleton : elt -> t

      val remove : elt -> t -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val eq_dec : t -> t -> bool

      val equal : t -> t -> bool

      val subset : t -> t -> bool

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val filter : (elt -> bool) -> t -> t

      val partition : (elt -> bool) -> t -> t * t

      val cardinal : t -> nat

      val elements : t -> elt list

      val choose : t -> elt option

      module MF :
       sig
        val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
       end

      val min_elt : t -> elt option

      val max_elt : t -> elt option

      val compare : t -> t -> t compare0

      module E :
       sig
        type t = Coq_regex_as_UCT.t

        val compare :
          Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t
          compare0

        val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
       end
     end

    module Coq_reFSF :
     sig
      val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
     end

    module Coq_reFM :
     sig
      module E :
       sig
        type t = Coq_regex_as_UCT.t

        val compare :
          Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t
          compare0

        val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
       end

      module Raw :
       sig
        type key = Coq_regex_as_UCT.t

        type 'elt tree = 'elt R.Defs.Coq_reFM.Raw.tree =
        | Leaf
        | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

        val tree_rect :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val tree_rec :
          'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
          Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

        val height : 'a1 tree -> Z_as_Int.t

        val cardinal : 'a1 tree -> nat

        val empty : 'a1 tree

        val is_empty : 'a1 tree -> bool

        val mem : Coq_regex_as_UCT.t -> 'a1 tree -> bool

        val find : Coq_regex_as_UCT.t -> 'a1 tree -> 'a1 option

        val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

        val remove_min :
          'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

        val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

        val remove : Coq_regex_as_UCT.t -> 'a1 tree -> 'a1 tree

        val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

        type 'elt triple = 'elt R.Defs.Coq_reFM.Raw.triple = { t_left :
                                                               'elt tree;
                                                               t_opt :
                                                               'elt option;
                                                               t_right :
                                                               'elt tree }

        val t_left : 'a1 triple -> 'a1 tree

        val t_opt : 'a1 triple -> 'a1 option

        val t_right : 'a1 triple -> 'a1 tree

        val split : Coq_regex_as_UCT.t -> 'a1 tree -> 'a1 triple

        val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

        val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

        val elements : 'a1 tree -> (key * 'a1) list

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

        type 'elt enumeration = 'elt R.Defs.Coq_reFM.Raw.enumeration =
        | End
        | More of key * 'elt * 'elt tree * 'elt enumeration

        val enumeration_rect :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val enumeration_rec :
          'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) ->
          'a1 enumeration -> 'a2

        val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

        val equal_more :
          ('a1 -> 'a1 -> bool) -> Coq_regex_as_UCT.t -> 'a1 -> ('a1
          enumeration -> bool) -> 'a1 enumeration -> bool

        val equal_cont :
          ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
          'a1 enumeration -> bool

        val equal_end : 'a1 enumeration -> bool

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

        val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

        val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

        val map2_opt :
          (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree)
          -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree ->
          'a3 tree

        module Proofs :
         sig
          module MX :
           sig
            module TO :
             sig
              type t = Coq_regex_as_UCT.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

            val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

            val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
           end

          module PX :
           sig
            module MO :
             sig
              module TO :
               sig
                type t = Coq_regex_as_UCT.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
             end
           end

          module L :
           sig
            module MX :
             sig
              module TO :
               sig
                type t = Coq_regex_as_UCT.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
             end

            module PX :
             sig
              module MO :
               sig
                module TO :
                 sig
                  type t = Coq_regex_as_UCT.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

                val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

                val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
               end
             end

            type key = Coq_regex_as_UCT.t

            type 'elt t = (Coq_regex_as_UCT.t * 'elt) list

            val empty : 'a1 t

            val is_empty : 'a1 t -> bool

            val mem : key -> 'a1 t -> bool

            type 'elt coq_R_mem = 'elt R.Defs.Coq_reFM.Raw.Proofs.L.coq_R_mem =
            | R_mem_0 of 'elt t
            | R_mem_1 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_mem_2 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_mem_3 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list * bool * 'elt coq_R_mem

            val coq_R_mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> bool ->
              'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem
              -> 'a2

            val coq_R_mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> bool ->
              'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem
              -> 'a2

            val mem_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val mem_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

            val find : key -> 'a1 t -> 'a1 option

            type 'elt coq_R_find = 'elt R.Defs.Coq_reFM.Raw.Proofs.L.coq_R_find =
            | R_find_0 of 'elt t
            | R_find_1 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_find_2 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_find_3 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list * 'elt option
               * 'elt coq_R_find

            val coq_R_find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 option
              -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
              coq_R_find -> 'a2

            val coq_R_find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 option
              -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
              coq_R_find -> 'a2

            val find_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val find_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val coq_R_find_correct :
              key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

            val add : key -> 'a1 -> 'a1 t -> 'a1 t

            type 'elt coq_R_add = 'elt R.Defs.Coq_reFM.Raw.Proofs.L.coq_R_add =
            | R_add_0 of 'elt t
            | R_add_1 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_add_2 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_add_3 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list * 'elt t * 'elt coq_R_add

            val coq_R_add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list ->
              __ -> __ -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1
              -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
              'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
              -> 'a2

            val coq_R_add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list ->
              __ -> __ -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1
              -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
              'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
              -> 'a2

            val add_rect :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list ->
              __ -> __ -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1
              -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val add_rec :
              key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
              Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list ->
              __ -> __ -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1
              -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val coq_R_add_correct :
              key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

            val remove : key -> 'a1 t -> 'a1 t

            type 'elt coq_R_remove = 'elt R.Defs.Coq_reFM.Raw.Proofs.L.coq_R_remove =
            | R_remove_0 of 'elt t
            | R_remove_1 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_remove_2 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list
            | R_remove_3 of 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list * 'elt t * 'elt coq_R_remove

            val coq_R_remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
              'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
              coq_R_remove -> 'a2

            val coq_R_remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
              'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
              coq_R_remove -> 'a2

            val remove_rect :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val remove_rec :
              key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
              ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
              'a2) -> 'a1 t -> 'a2

            val coq_R_remove_correct :
              key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

            val elements : 'a1 t -> 'a1 t

            val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

            type ('elt, 'a) coq_R_fold = ('elt, 'a) R.Defs.Coq_reFM.Raw.Proofs.L.coq_R_fold =
            | R_fold_0 of 'elt t * 'a
            | R_fold_1 of 'elt t * 'a * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list * 'a * ('elt, 'a) coq_R_fold

            val coq_R_fold_rect :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
              coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
              coq_R_fold -> 'a3

            val coq_R_fold_rec :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
              coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
              coq_R_fold -> 'a3

            val fold_rect :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t
              -> 'a2 -> 'a3

            val fold_rec :
              (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
              ('a1 t -> 'a2 -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t
              -> 'a2 -> 'a3

            val coq_R_fold_correct :
              (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
              coq_R_fold

            val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

            type 'elt coq_R_equal = 'elt R.Defs.Coq_reFM.Raw.Proofs.L.coq_R_equal =
            | R_equal_0 of 'elt t * 'elt t
            | R_equal_1 of 'elt t * 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list * Coq_regex_as_UCT.t *
               'elt * (Coq_regex_as_UCT.t * 'elt) list * bool
               * 'elt coq_R_equal
            | R_equal_2 of 'elt t * 'elt t * Coq_regex_as_UCT.t * 'elt
               * (Coq_regex_as_UCT.t * 'elt) list * Coq_regex_as_UCT.t *
               'elt * (Coq_regex_as_UCT.t * 'elt) list
               * Coq_regex_as_UCT.t compare0
            | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

            val coq_R_equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
              Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list ->
              __ -> Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1)
              list -> __ -> Coq_regex_as_UCT.t compare0 -> __ -> __ -> 'a2)
              -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
              -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

            val coq_R_equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
              Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list ->
              __ -> Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1)
              list -> __ -> Coq_regex_as_UCT.t compare0 -> __ -> __ -> 'a2)
              -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
              -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

            val equal_rect :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2
              -> 'a2) -> ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ ->
              Coq_regex_as_UCT.t compare0 -> __ -> __ -> 'a2) -> ('a1 t ->
              'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
              'a1 t -> 'a2

            val equal_rec :
              ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) ->
              ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2
              -> 'a2) -> ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
              (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t ->
              'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ ->
              Coq_regex_as_UCT.t compare0 -> __ -> __ -> 'a2) -> ('a1 t ->
              'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
              'a1 t -> 'a2

            val coq_R_equal_correct :
              ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
              coq_R_equal

            val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

            val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

            val option_cons :
              key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

            val map2_l :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

            val map2_r :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

            val map2 :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              'a3 t

            val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

            val fold_right_pair :
              ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

            val map2_alt :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
              (key * 'a3) list

            val at_least_one :
              'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

            val at_least_one_then_f :
              ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
              option -> 'a3 option
           end

          type 'elt coq_R_mem = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_mem =
          | R_mem_0 of 'elt tree
          | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem
          | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * bool * 'elt coq_R_mem

          val coq_R_mem_rect :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
            tree -> bool -> 'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
            tree -> bool -> 'a1 coq_R_mem -> 'a2

          type 'elt coq_R_find = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_find =
          | R_find_0 of 'elt tree
          | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find
          | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt option * 'elt coq_R_find

          val coq_R_find_rect :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
            'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

          val coq_R_find_rec :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
            'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

          type 'elt coq_R_bal = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_bal =
          | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
          | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t
          | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
             key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t
          | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

          val coq_R_bal_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          val coq_R_bal_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) ->
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __
            -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
            -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
            -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
            -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
            'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1
            -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
            'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
            -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

          type 'elt coq_R_add = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_add =
          | R_add_0 of 'elt tree
          | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add
          | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
            tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
            key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
            ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
            __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

          type 'elt coq_R_remove_min = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_remove_min =
          | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
          | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
             * key * 'elt * 'elt tree * Z_as_Int.t
             * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min * 'elt tree
             * (key * 'elt)

          val coq_R_remove_min_rect :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          val coq_R_remove_min_rec :
            ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree ->
            key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
            coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2)
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1))
            -> 'a1 coq_R_remove_min -> 'a2

          type 'elt coq_R_merge = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_merge =
          | R_merge_0 of 'elt tree * 'elt tree
          | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

          val coq_R_merge_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2

          val coq_R_merge_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1
            -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
            coq_R_merge -> 'a2

          type 'elt coq_R_remove = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_remove =
          | R_remove_0 of 'elt tree
          | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
          | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

          val coq_R_remove_rect :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
            'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

          val coq_R_remove_rec :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
            'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

          type 'elt coq_R_concat = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_concat =
          | R_concat_0 of 'elt tree * 'elt tree
          | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t
          | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
             * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt tree * (key * 'elt)

          val coq_R_concat_rect :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

          val coq_R_concat_rec :
            ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
            Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1
            tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

          type 'elt coq_R_split = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_split =
          | R_split_0 of 'elt tree
          | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree
          | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t
          | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
             * 'elt option * 'elt tree

          val coq_R_split_rect :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option ->
            'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
            'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
            option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
            coq_R_split -> 'a2

          val coq_R_split_rec :
            Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
            'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option ->
            'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
            'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
            'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
            __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
            option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
            coq_R_split -> 'a2

          type ('elt, 'x) coq_R_map_option = ('elt, 'x) R.Defs.Coq_reFM.Raw.Proofs.coq_R_map_option =
          | R_map_option_0 of 'elt tree
          | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
             * 'x tree * ('elt, 'x) coq_R_map_option
          | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
             * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
             * ('elt, 'x) coq_R_map_option

          val coq_R_map_option_rect :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          val coq_R_map_option_rec :
            (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 ->
            'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1
            tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
            __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree
            -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2
            tree -> ('a1, 'a2) coq_R_map_option -> 'a3

          type ('elt, 'x0, 'x) coq_R_map2_opt = ('elt, 'x0, 'x) R.Defs.Coq_reFM.Raw.Proofs.coq_R_map2_opt =
          | R_map2_opt_0 of 'elt tree * 'x0 tree
          | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t
          | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
             * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt
          | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key *
             'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
             * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
             * ('elt, 'x0, 'x) coq_R_map2_opt

          val coq_R_map2_opt_rect :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val coq_R_map2_opt_rec :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ ->
            'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
            tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree
            -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2
            tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1,
            'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
            tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree ->
            key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2
            option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
            coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree
            -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

          val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

          val flatten_e : 'a1 enumeration -> (key * 'a1) list
         end
       end

      type 'elt bst =
        'elt Raw.tree
        (* singleton inductive, whose constructor was Bst *)

      val this : 'a1 bst -> 'a1 Raw.tree

      type 'elt t = 'elt bst

      type key = Coq_regex_as_UCT.t

      val empty : 'a1 t

      val is_empty : 'a1 t -> bool

      val add : key -> 'a1 -> 'a1 t -> 'a1 t

      val remove : key -> 'a1 t -> 'a1 t

      val mem : key -> 'a1 t -> bool

      val find : key -> 'a1 t -> 'a1 option

      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

      val elements : 'a1 t -> (key * 'a1) list

      val cardinal : 'a1 t -> nat

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
     end

    module Coq_reFMF :
     sig
      val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

      val coq_In_dec : 'a1 Coq_reFM.t -> Coq_reFM.key -> bool
     end

    module MatchSpec :
     sig
     end

    module MatchSpecLemmas :
     sig
     end

    module Notations :
     sig
     end

    module Helpers :
     sig
      val coq_Plus : Regexes.regex -> Regexes.regex

      val coq_IterUnion : Regexes.regex list -> Regexes.regex

      val coq_IterApp : Regexes.regex list -> Regexes.regex

      val coq_Optional : Regexes.regex -> Regexes.regex

      val coq_REString : Strings.coq_String -> Regexes.regex
     end
   end

  module Coq_reFS :
   sig
    module X' :
     sig
      type t = DS.Coq_regex_as_UCT.t

      val eq_dec : DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool

      val compare :
        DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> comparison
     end

    module MSet :
     sig
      module Raw :
       sig
        type elt = DS.Coq_regex_as_UCT.t

        type tree = R.Defs.Coq_reFS.MSet.Raw.tree =
        | Leaf
        | Node of Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t * tree

        val empty : tree

        val is_empty : tree -> bool

        val mem : DS.Coq_regex_as_UCT.t -> tree -> bool

        val min_elt : tree -> elt option

        val max_elt : tree -> elt option

        val choose : tree -> elt option

        val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

        val elements_aux :
          DS.Coq_regex_as_UCT.t list -> tree -> DS.Coq_regex_as_UCT.t list

        val elements : tree -> DS.Coq_regex_as_UCT.t list

        val rev_elements_aux :
          DS.Coq_regex_as_UCT.t list -> tree -> DS.Coq_regex_as_UCT.t list

        val rev_elements : tree -> DS.Coq_regex_as_UCT.t list

        val cardinal : tree -> nat

        val maxdepth : tree -> nat

        val mindepth : tree -> nat

        val for_all : (elt -> bool) -> tree -> bool

        val exists_ : (elt -> bool) -> tree -> bool

        type enumeration = R.Defs.Coq_reFS.MSet.Raw.enumeration =
        | End
        | More of elt * tree * enumeration

        val cons : tree -> enumeration -> enumeration

        val compare_more :
          DS.Coq_regex_as_UCT.t -> (enumeration -> comparison) -> enumeration
          -> comparison

        val compare_cont :
          tree -> (enumeration -> comparison) -> enumeration -> comparison

        val compare_end : enumeration -> comparison

        val compare : tree -> tree -> comparison

        val equal : tree -> tree -> bool

        val subsetl : (tree -> bool) -> DS.Coq_regex_as_UCT.t -> tree -> bool

        val subsetr : (tree -> bool) -> DS.Coq_regex_as_UCT.t -> tree -> bool

        val subset : tree -> tree -> bool

        type t = tree

        val height : t -> Z_as_Int.t

        val singleton : DS.Coq_regex_as_UCT.t -> tree

        val create : t -> DS.Coq_regex_as_UCT.t -> t -> tree

        val assert_false : t -> DS.Coq_regex_as_UCT.t -> t -> tree

        val bal : t -> DS.Coq_regex_as_UCT.t -> t -> tree

        val add : DS.Coq_regex_as_UCT.t -> tree -> tree

        val join : tree -> elt -> t -> t

        val remove_min : tree -> elt -> t -> t * elt

        val merge : tree -> tree -> tree

        val remove : DS.Coq_regex_as_UCT.t -> tree -> tree

        val concat : tree -> tree -> tree

        type triple = R.Defs.Coq_reFS.MSet.Raw.triple = { t_left : t;
                                                          t_in : bool;
                                                          t_right : t }

        val t_left : triple -> t

        val t_in : triple -> bool

        val t_right : triple -> t

        val split : DS.Coq_regex_as_UCT.t -> tree -> triple

        val inter : tree -> tree -> tree

        val diff : tree -> tree -> tree

        val union : tree -> tree -> tree

        val filter : (elt -> bool) -> tree -> tree

        val partition : (elt -> bool) -> t -> t * t

        val ltb_tree : DS.Coq_regex_as_UCT.t -> tree -> bool

        val gtb_tree : DS.Coq_regex_as_UCT.t -> tree -> bool

        val isok : tree -> bool

        module MX :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = DS.Coq_regex_as_UCT.t

              val compare :
                DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> comparison

              val eq_dec :
                DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
             end

            module TO :
             sig
              type t = DS.Coq_regex_as_UCT.t

              val compare :
                DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> comparison

              val eq_dec :
                DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
             end
           end

          val eq_dec : DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool

          val lt_dec : DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool

          val eqb : DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
         end

        type coq_R_min_elt = R.Defs.Coq_reFS.MSet.Raw.coq_R_min_elt =
        | R_min_elt_0 of tree
        | R_min_elt_1 of tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t
           * tree
        | R_min_elt_2 of tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t
           * tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t * tree
           * elt option * coq_R_min_elt

        type coq_R_max_elt = R.Defs.Coq_reFS.MSet.Raw.coq_R_max_elt =
        | R_max_elt_0 of tree
        | R_max_elt_1 of tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t
           * tree
        | R_max_elt_2 of tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t
           * tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t * tree
           * elt option * coq_R_max_elt

        module L :
         sig
          module MO :
           sig
            module OrderTac :
             sig
              module OTF :
               sig
                type t = DS.Coq_regex_as_UCT.t

                val compare :
                  DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> comparison

                val eq_dec :
                  DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
               end

              module TO :
               sig
                type t = DS.Coq_regex_as_UCT.t

                val compare :
                  DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> comparison

                val eq_dec :
                  DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
               end
             end

            val eq_dec :
              DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool

            val lt_dec :
              DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool

            val eqb : DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
           end
         end

        val flatten_e : enumeration -> elt list

        type coq_R_bal = R.Defs.Coq_reFS.MSet.Raw.coq_R_bal =
        | R_bal_0 of t * DS.Coq_regex_as_UCT.t * t
        | R_bal_1 of t * DS.Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree
        | R_bal_2 of t * DS.Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree
        | R_bal_3 of t * DS.Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree
        | R_bal_4 of t * DS.Coq_regex_as_UCT.t * t
        | R_bal_5 of t * DS.Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree
        | R_bal_6 of t * DS.Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree
        | R_bal_7 of t * DS.Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree
        | R_bal_8 of t * DS.Coq_regex_as_UCT.t * t

        type coq_R_remove_min = R.Defs.Coq_reFS.MSet.Raw.coq_R_remove_min =
        | R_remove_min_0 of tree * elt * t
        | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree * (t * elt) * coq_R_remove_min *
           t * elt

        type coq_R_merge = R.Defs.Coq_reFS.MSet.Raw.coq_R_merge =
        | R_merge_0 of tree * tree
        | R_merge_1 of tree * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree
        | R_merge_2 of tree * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree * t * elt

        type coq_R_concat = R.Defs.Coq_reFS.MSet.Raw.coq_R_concat =
        | R_concat_0 of tree * tree
        | R_concat_1 of tree * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree
        | R_concat_2 of tree * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree * t * elt

        type coq_R_inter = R.Defs.Coq_reFS.MSet.Raw.coq_R_inter =
        | R_inter_0 of tree * tree
        | R_inter_1 of tree * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree
        | R_inter_2 of tree * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree * t * bool * t * tree * coq_R_inter
           * tree * coq_R_inter
        | R_inter_3 of tree * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree * t * bool * t * tree * coq_R_inter
           * tree * coq_R_inter

        type coq_R_diff = R.Defs.Coq_reFS.MSet.Raw.coq_R_diff =
        | R_diff_0 of tree * tree
        | R_diff_1 of tree * tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t
           * tree
        | R_diff_2 of tree * tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t
           * tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t * tree *
           t * bool * t * tree * coq_R_diff * tree * coq_R_diff
        | R_diff_3 of tree * tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t
           * tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t * tree *
           t * bool * t * tree * coq_R_diff * tree * coq_R_diff

        type coq_R_union = R.Defs.Coq_reFS.MSet.Raw.coq_R_union =
        | R_union_0 of tree * tree
        | R_union_1 of tree * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree
        | R_union_2 of tree * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
           * DS.Coq_regex_as_UCT.t * tree * t * bool * t * tree * coq_R_union
           * tree * coq_R_union
       end

      module E :
       sig
        type t = DS.Coq_regex_as_UCT.t

        val compare :
          DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> comparison

        val eq_dec : DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
       end

      type elt = DS.Coq_regex_as_UCT.t

      type t_ = Raw.t
        (* singleton inductive, whose constructor was Mkt *)

      val this : t_ -> Raw.t

      type t = t_

      val mem : elt -> t -> bool

      val add : elt -> t -> t

      val remove : elt -> t -> t

      val singleton : elt -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val equal : t -> t -> bool

      val subset : t -> t -> bool

      val empty : t

      val is_empty : t -> bool

      val elements : t -> elt list

      val choose : t -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val cardinal : t -> nat

      val filter : (elt -> bool) -> t -> t

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val partition : (elt -> bool) -> t -> t * t

      val eq_dec : t -> t -> bool

      val compare : t -> t -> comparison

      val min_elt : t -> elt option

      val max_elt : t -> elt option
     end

    type elt = DS.Coq_regex_as_UCT.t

    type t = MSet.t

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val eq_dec : t -> t -> bool

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val partition : (elt -> bool) -> t -> t * t

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    module MF :
     sig
      val eqb : DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
     end

    val min_elt : t -> elt option

    val max_elt : t -> elt option

    val compare : t -> t -> t compare0

    module E :
     sig
      type t = DS.Coq_regex_as_UCT.t

      val compare :
        DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t ->
        DS.Coq_regex_as_UCT.t compare0

      val eq_dec : DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
     end
   end

  type coq_Table

  val emptyTable : coq_Table

  val set_Table :
    coq_Table -> DS.Regexes.regex -> R.Ty.coq_Sigma -> DS.Regexes.regex ->
    coq_Table

  val get_Table :
    coq_Table -> DS.Regexes.regex -> R.Ty.coq_Sigma -> DS.Regexes.regex option

  val add_state : coq_Table -> DS.Regexes.regex -> coq_Table

  val get_states : coq_Table -> Coq_reFS.t

  val get_eq : coq_Table -> DS.Regexes.regex -> DS.Regexes.regex option
 end) ->
 struct
  module FillTable =
   struct
    (** val mkIterUnion' :
        R.Defs.Regexes.regex -> R.Defs.Regexes.regex list **)

    let rec mkIterUnion' e = match e with
    | R.Defs.Regexes.Union (e1, e2) -> e1 :: (mkIterUnion' e2)
    | _ -> e :: []

    (** val merge' :
        R.Defs.Regexes.regex list -> R.Defs.Regexes.regex list ->
        R.Defs.Regexes.regex list **)

    let rec merge' es1 es2 =
      match es1 with
      | [] -> es2
      | h1 :: t1 ->
        (match es2 with
         | [] -> es1
         | h2 :: t2 ->
           (match R.Defs.Regexes.re_compare h1 h2 with
            | Eq -> merge' (h1 :: t1) t2
            | Lt -> h1 :: (merge' t1 (h2 :: t2))
            | Gt -> h2 :: (merge' (h1 :: t1) t2)))

    (** val merge'' :
        R.Defs.Regexes.regex list -> R.Defs.Regexes.regex list ->
        R.Defs.Regexes.regex list **)

    let merge'' =
      merge'

    (** val merge :
        R.Defs.Regexes.regex list -> R.Defs.Regexes.regex list ->
        R.Defs.Regexes.regex list **)

    let merge =
      merge''

    (** val mkIterApp' : R.Defs.Regexes.regex -> R.Defs.Regexes.regex list **)

    let rec mkIterApp' e = match e with
    | R.Defs.Regexes.App (e1, e2) -> e1 :: (mkIterApp' e2)
    | _ -> e :: []

    (** val canon : R.Defs.Regexes.regex -> R.Defs.Regexes.regex **)

    let rec canon e = match e with
    | R.Defs.Regexes.App (e1, e2) ->
      (match canon e1 with
       | R.Defs.Regexes.EmptySet -> R.Defs.Regexes.EmptySet
       | R.Defs.Regexes.EmptyStr -> canon e2
       | x ->
         (match canon e2 with
          | R.Defs.Regexes.EmptySet -> R.Defs.Regexes.EmptySet
          | R.Defs.Regexes.EmptyStr -> x
          | x0 ->
            R.Defs.Helpers.coq_IterApp (app (mkIterApp' x) (mkIterApp' x0))))
    | R.Defs.Regexes.Union (e1, e2) ->
      (match canon e1 with
       | R.Defs.Regexes.EmptySet -> canon e2
       | x ->
         (match canon e2 with
          | R.Defs.Regexes.EmptySet -> x
          | x0 ->
            R.Defs.Helpers.coq_IterUnion
              (merge (mkIterUnion' x) (mkIterUnion' x0))))
    | R.Defs.Regexes.Star r ->
      (match r with
       | R.Defs.Regexes.EmptySet -> R.Defs.Regexes.EmptyStr
       | R.Defs.Regexes.EmptyStr -> R.Defs.Regexes.EmptyStr
       | _ -> e)
    | _ -> e

    (** val fill_Table_all' :
        TabTy.coq_Table -> R.Defs.Regexes.regex -> R.Ty.coq_Sigma list -> nat
        -> TabTy.coq_Table **)

    let rec fill_Table_all' t0 e bs = function
    | O -> t0
    | S n0 ->
      let rec fill_Table_ds = function
      | [] -> t0
      | c :: cs ->
        let t1 = fill_Table_ds cs in
        let d = canon (R.Defs.Regexes.derivative c e) in
        (match TabTy.get_eq t0 d with
         | Some e' -> TabTy.set_Table t1 e c e'
         | None ->
           let t2 = TabTy.add_state t1 d in
           let t3 = TabTy.set_Table t2 e c d in fill_Table_all' t3 d bs n0)
      in fill_Table_ds bs

    (** val fill_Table_all :
        TabTy.coq_Table -> R.Defs.Regexes.regex -> R.Ty.coq_Sigma list -> nat
        -> TabTy.coq_Table **)

    let fill_Table_all t0 e bs fuel =
      fill_Table_all' t0 (canon e) bs fuel
   end

  module Spec =
   struct
   end

  module Correct =
   struct
   end
 end

module type Coq0_T =
 sig
  module R :
   T

  module TabTy :
   sig
    module DS :
     sig
      module T_as_UCT :
       sig
        type t = R.Ty.coq_Sigma

        val compare : R.Ty.coq_Sigma -> R.Ty.coq_Sigma -> comparison
       end

      module T_as_UOT :
       sig
        type t = T_as_UCT.t

        val compare : t -> t -> t compare0

        val eq_dec : t -> t -> bool
       end

      module SigFS :
       sig
        module X' :
         sig
          type t = T_as_UCT.t

          val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

          val compare : T_as_UCT.t -> T_as_UCT.t -> comparison
         end

        module MSet :
         sig
          module Raw :
           sig
            type elt = T_as_UCT.t

            type tree = R.Defs.SigFS.MSet.Raw.tree =
            | Leaf
            | Node of Z_as_Int.t * tree * T_as_UCT.t * tree

            val empty : tree

            val is_empty : tree -> bool

            val mem : T_as_UCT.t -> tree -> bool

            val min_elt : tree -> elt option

            val max_elt : tree -> elt option

            val choose : tree -> elt option

            val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

            val elements_aux : T_as_UCT.t list -> tree -> T_as_UCT.t list

            val elements : tree -> T_as_UCT.t list

            val rev_elements_aux : T_as_UCT.t list -> tree -> T_as_UCT.t list

            val rev_elements : tree -> T_as_UCT.t list

            val cardinal : tree -> nat

            val maxdepth : tree -> nat

            val mindepth : tree -> nat

            val for_all : (elt -> bool) -> tree -> bool

            val exists_ : (elt -> bool) -> tree -> bool

            type enumeration = R.Defs.SigFS.MSet.Raw.enumeration =
            | End
            | More of elt * tree * enumeration

            val cons : tree -> enumeration -> enumeration

            val compare_more :
              T_as_UCT.t -> (enumeration -> comparison) -> enumeration ->
              comparison

            val compare_cont :
              tree -> (enumeration -> comparison) -> enumeration -> comparison

            val compare_end : enumeration -> comparison

            val compare : tree -> tree -> comparison

            val equal : tree -> tree -> bool

            val subsetl : (tree -> bool) -> T_as_UCT.t -> tree -> bool

            val subsetr : (tree -> bool) -> T_as_UCT.t -> tree -> bool

            val subset : tree -> tree -> bool

            type t = tree

            val height : t -> Z_as_Int.t

            val singleton : T_as_UCT.t -> tree

            val create : t -> T_as_UCT.t -> t -> tree

            val assert_false : t -> T_as_UCT.t -> t -> tree

            val bal : t -> T_as_UCT.t -> t -> tree

            val add : T_as_UCT.t -> tree -> tree

            val join : tree -> elt -> t -> t

            val remove_min : tree -> elt -> t -> t * elt

            val merge : tree -> tree -> tree

            val remove : T_as_UCT.t -> tree -> tree

            val concat : tree -> tree -> tree

            type triple = R.Defs.SigFS.MSet.Raw.triple = { t_left : t;
                                                           t_in : bool;
                                                           t_right :
                                                           t }

            val t_left : triple -> t

            val t_in : triple -> bool

            val t_right : triple -> t

            val split : T_as_UCT.t -> tree -> triple

            val inter : tree -> tree -> tree

            val diff : tree -> tree -> tree

            val union : tree -> tree -> tree

            val filter : (elt -> bool) -> tree -> tree

            val partition : (elt -> bool) -> t -> t * t

            val ltb_tree : T_as_UCT.t -> tree -> bool

            val gtb_tree : T_as_UCT.t -> tree -> bool

            val isok : tree -> bool

            module MX :
             sig
              module OrderTac :
               sig
                module OTF :
                 sig
                  type t = T_as_UCT.t

                  val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

                  val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
                 end

                module TO :
                 sig
                  type t = T_as_UCT.t

                  val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

                  val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
                 end
               end

              val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
             end

            type coq_R_min_elt = R.Defs.SigFS.MSet.Raw.coq_R_min_elt =
            | R_min_elt_0 of tree
            | R_min_elt_1 of tree * Z_as_Int.t * tree * T_as_UCT.t * tree
            | R_min_elt_2 of tree * Z_as_Int.t * tree * T_as_UCT.t *
               tree * Z_as_Int.t * tree * T_as_UCT.t * tree * elt option
               * coq_R_min_elt

            type coq_R_max_elt = R.Defs.SigFS.MSet.Raw.coq_R_max_elt =
            | R_max_elt_0 of tree
            | R_max_elt_1 of tree * Z_as_Int.t * tree * T_as_UCT.t * tree
            | R_max_elt_2 of tree * Z_as_Int.t * tree * T_as_UCT.t *
               tree * Z_as_Int.t * tree * T_as_UCT.t * tree * elt option
               * coq_R_max_elt

            module L :
             sig
              module MO :
               sig
                module OrderTac :
                 sig
                  module OTF :
                   sig
                    type t = T_as_UCT.t

                    val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

                    val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
                   end

                  module TO :
                   sig
                    type t = T_as_UCT.t

                    val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

                    val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
                   end
                 end

                val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

                val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

                val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
               end
             end

            val flatten_e : enumeration -> elt list

            type coq_R_bal = R.Defs.SigFS.MSet.Raw.coq_R_bal =
            | R_bal_0 of t * T_as_UCT.t * t
            | R_bal_1 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
               * tree
            | R_bal_2 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
               * tree
            | R_bal_3 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
               * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
            | R_bal_4 of t * T_as_UCT.t * t
            | R_bal_5 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
               * tree
            | R_bal_6 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
               * tree
            | R_bal_7 of t * T_as_UCT.t * t * Z_as_Int.t * tree * T_as_UCT.t
               * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
            | R_bal_8 of t * T_as_UCT.t * t

            type coq_R_remove_min = R.Defs.SigFS.MSet.Raw.coq_R_remove_min =
            | R_remove_min_0 of tree * elt * t
            | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
               * T_as_UCT.t * tree * (t * elt) * coq_R_remove_min * t *
               elt

            type coq_R_merge = R.Defs.SigFS.MSet.Raw.coq_R_merge =
            | R_merge_0 of tree * tree
            | R_merge_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
            | R_merge_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t
               * tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * elt

            type coq_R_concat = R.Defs.SigFS.MSet.Raw.coq_R_concat =
            | R_concat_0 of tree * tree
            | R_concat_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t
               * tree
            | R_concat_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t
               * tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * elt

            type coq_R_inter = R.Defs.SigFS.MSet.Raw.coq_R_inter =
            | R_inter_0 of tree * tree
            | R_inter_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
            | R_inter_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t
               * tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
               t * tree * coq_R_inter * tree * coq_R_inter
            | R_inter_3 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t
               * tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
               t * tree * coq_R_inter * tree * coq_R_inter

            type coq_R_diff = R.Defs.SigFS.MSet.Raw.coq_R_diff =
            | R_diff_0 of tree * tree
            | R_diff_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
            | R_diff_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
               tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
               t * tree * coq_R_diff * tree * coq_R_diff
            | R_diff_3 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t *
               tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
               t * tree * coq_R_diff * tree * coq_R_diff

            type coq_R_union = R.Defs.SigFS.MSet.Raw.coq_R_union =
            | R_union_0 of tree * tree
            | R_union_1 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t * tree
            | R_union_2 of tree * tree * Z_as_Int.t * tree * T_as_UCT.t
               * tree * Z_as_Int.t * tree * T_as_UCT.t * tree * t * bool *
               t * tree * coq_R_union * tree * coq_R_union
           end

          module E :
           sig
            type t = T_as_UCT.t

            val compare : T_as_UCT.t -> T_as_UCT.t -> comparison

            val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
           end

          type elt = T_as_UCT.t

          type t_ = Raw.t
            (* singleton inductive, whose constructor was Mkt *)

          val this : t_ -> Raw.t

          type t = t_

          val mem : elt -> t -> bool

          val add : elt -> t -> t

          val remove : elt -> t -> t

          val singleton : elt -> t

          val union : t -> t -> t

          val inter : t -> t -> t

          val diff : t -> t -> t

          val equal : t -> t -> bool

          val subset : t -> t -> bool

          val empty : t

          val is_empty : t -> bool

          val elements : t -> elt list

          val choose : t -> elt option

          val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

          val cardinal : t -> nat

          val filter : (elt -> bool) -> t -> t

          val for_all : (elt -> bool) -> t -> bool

          val exists_ : (elt -> bool) -> t -> bool

          val partition : (elt -> bool) -> t -> t * t

          val eq_dec : t -> t -> bool

          val compare : t -> t -> comparison

          val min_elt : t -> elt option

          val max_elt : t -> elt option
         end

        type elt = T_as_UCT.t

        type t = MSet.t

        val empty : t

        val is_empty : t -> bool

        val mem : elt -> t -> bool

        val add : elt -> t -> t

        val singleton : elt -> t

        val remove : elt -> t -> t

        val union : t -> t -> t

        val inter : t -> t -> t

        val diff : t -> t -> t

        val eq_dec : t -> t -> bool

        val equal : t -> t -> bool

        val subset : t -> t -> bool

        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

        val for_all : (elt -> bool) -> t -> bool

        val exists_ : (elt -> bool) -> t -> bool

        val filter : (elt -> bool) -> t -> t

        val partition : (elt -> bool) -> t -> t * t

        val cardinal : t -> nat

        val elements : t -> elt list

        val choose : t -> elt option

        module MF :
         sig
          val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
         end

        val min_elt : t -> elt option

        val max_elt : t -> elt option

        val compare : t -> t -> t compare0

        module E :
         sig
          type t = T_as_UCT.t

          val compare : T_as_UCT.t -> T_as_UCT.t -> T_as_UCT.t compare0

          val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
         end
       end

      module SigFSF :
       sig
        val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
       end

      module SigFM :
       sig
        module E :
         sig
          type t = T_as_UCT.t

          val compare : T_as_UCT.t -> T_as_UCT.t -> T_as_UCT.t compare0

          val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool
         end

        module Raw :
         sig
          type key = T_as_UCT.t

          type 'elt tree = 'elt R.Defs.SigFM.Raw.tree =
          | Leaf
          | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

          val tree_rect :
            'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
            Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

          val tree_rec :
            'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
            Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

          val height : 'a1 tree -> Z_as_Int.t

          val cardinal : 'a1 tree -> nat

          val empty : 'a1 tree

          val is_empty : 'a1 tree -> bool

          val mem : T_as_UCT.t -> 'a1 tree -> bool

          val find : T_as_UCT.t -> 'a1 tree -> 'a1 option

          val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

          val remove_min :
            'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

          val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

          val remove : T_as_UCT.t -> 'a1 tree -> 'a1 tree

          val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          type 'elt triple = 'elt R.Defs.SigFM.Raw.triple = { t_left :
                                                              'elt tree;
                                                              t_opt :
                                                              'elt option;
                                                              t_right :
                                                              'elt tree }

          val t_left : 'a1 triple -> 'a1 tree

          val t_opt : 'a1 triple -> 'a1 option

          val t_right : 'a1 triple -> 'a1 tree

          val split : T_as_UCT.t -> 'a1 tree -> 'a1 triple

          val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

          val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

          val elements : 'a1 tree -> (key * 'a1) list

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

          type 'elt enumeration = 'elt R.Defs.SigFM.Raw.enumeration =
          | End
          | More of key * 'elt * 'elt tree * 'elt enumeration

          val enumeration_rect :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2

          val enumeration_rec :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2

          val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

          val equal_more :
            ('a1 -> 'a1 -> bool) -> T_as_UCT.t -> 'a1 -> ('a1 enumeration ->
            bool) -> 'a1 enumeration -> bool

          val equal_cont :
            ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
            'a1 enumeration -> bool

          val equal_end : 'a1 enumeration -> bool

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

          val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

          val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

          val map2_opt :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3
            tree

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree
            -> 'a3 tree

          module Proofs :
           sig
            module MX :
             sig
              module TO :
               sig
                type t = T_as_UCT.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

              val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
             end

            module PX :
             sig
              module MO :
               sig
                module TO :
                 sig
                  type t = T_as_UCT.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

                val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

                val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
               end
             end

            module L :
             sig
              module MX :
               sig
                module TO :
                 sig
                  type t = T_as_UCT.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

                val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

                val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
               end

              module PX :
               sig
                module MO :
                 sig
                  module TO :
                   sig
                    type t = T_as_UCT.t
                   end

                  module IsTO :
                   sig
                   end

                  module OrderTac :
                   sig
                   end

                  val eq_dec : T_as_UCT.t -> T_as_UCT.t -> bool

                  val lt_dec : T_as_UCT.t -> T_as_UCT.t -> bool

                  val eqb : T_as_UCT.t -> T_as_UCT.t -> bool
                 end
               end

              type key = T_as_UCT.t

              type 'elt t = (T_as_UCT.t * 'elt) list

              val empty : 'a1 t

              val is_empty : 'a1 t -> bool

              val mem : key -> 'a1 t -> bool

              type 'elt coq_R_mem = 'elt R.Defs.SigFM.Raw.Proofs.L.coq_R_mem =
              | R_mem_0 of 'elt t
              | R_mem_1 of 'elt t * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list
              | R_mem_2 of 'elt t * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list
              | R_mem_3 of 'elt t * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list * bool * 'elt coq_R_mem

              val coq_R_mem_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
                -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
                coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem ->
                'a2

              val coq_R_mem_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
                -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1
                coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem ->
                'a2

              val mem_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
                -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
                'a1 t -> 'a2

              val mem_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
                -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
                'a1 t -> 'a2

              val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

              val find : key -> 'a1 t -> 'a1 option

              type 'elt coq_R_find = 'elt R.Defs.SigFM.Raw.Proofs.L.coq_R_find =
              | R_find_0 of 'elt t
              | R_find_1 of 'elt t * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list
              | R_find_2 of 'elt t * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list
              | R_find_3 of 'elt t * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list * 'elt option * 'elt coq_R_find

              val coq_R_find_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
                -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 option ->
                'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
                coq_R_find -> 'a2

              val coq_R_find_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
                -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 option ->
                'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
                coq_R_find -> 'a2

              val find_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
                -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
                'a1 t -> 'a2

              val find_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
                -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
                'a1 t -> 'a2

              val coq_R_find_correct :
                key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

              val add : key -> 'a1 -> 'a1 t -> 'a1 t

              type 'elt coq_R_add = 'elt R.Defs.SigFM.Raw.Proofs.L.coq_R_add =
              | R_add_0 of 'elt t
              | R_add_1 of 'elt t * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list
              | R_add_2 of 'elt t * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list
              | R_add_3 of 'elt t * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list * 'elt t * 'elt coq_R_add

              val coq_R_add_rect :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t ->
                'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __
                -> __ -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
                coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
                -> 'a2

              val coq_R_add_rec :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t ->
                'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __
                -> __ -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
                coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
                -> 'a2

              val add_rect :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t ->
                'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __
                -> __ -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
                'a1 t -> 'a2

              val add_rec :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t ->
                'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __
                -> __ -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
                'a1 t -> 'a2

              val coq_R_add_correct :
                key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

              val remove : key -> 'a1 t -> 'a1 t

              type 'elt coq_R_remove = 'elt R.Defs.SigFM.Raw.Proofs.L.coq_R_remove =
              | R_remove_0 of 'elt t
              | R_remove_1 of 'elt t * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list
              | R_remove_2 of 'elt t * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list
              | R_remove_3 of 'elt t * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list * 'elt t * 'elt coq_R_remove

              val coq_R_remove_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
                -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
                coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
                coq_R_remove -> 'a2

              val coq_R_remove_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
                -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
                coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
                coq_R_remove -> 'a2

              val remove_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
                -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
                'a1 t -> 'a2

              val remove_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
                -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ -> __
                -> __ -> 'a2) -> ('a1 t -> T_as_UCT.t -> 'a1 ->
                (T_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) ->
                'a1 t -> 'a2

              val coq_R_remove_correct :
                key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

              val elements : 'a1 t -> 'a1 t

              val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

              type ('elt, 'a) coq_R_fold = ('elt, 'a) R.Defs.SigFM.Raw.Proofs.L.coq_R_fold =
              | R_fold_0 of 'elt t * 'a
              | R_fold_1 of 'elt t * 'a * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list * 'a * ('elt, 'a) coq_R_fold

              val coq_R_fold_rect :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
                -> __ -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t
                -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

              val coq_R_fold_rec :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
                -> __ -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t
                -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

              val fold_rect :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
                -> __ -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

              val fold_rec :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list
                -> __ -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

              val coq_R_fold_correct :
                (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
                'a2) coq_R_fold

              val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

              type 'elt coq_R_equal = 'elt R.Defs.SigFM.Raw.Proofs.L.coq_R_equal =
              | R_equal_0 of 'elt t * 'elt t
              | R_equal_1 of 'elt t * 'elt t * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list * bool * 'elt coq_R_equal
              | R_equal_2 of 'elt t * 'elt t * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list * T_as_UCT.t * 'elt
                 * (T_as_UCT.t * 'elt) list * T_as_UCT.t compare0
              | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

              val coq_R_equal_rect :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
                list -> __ -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list ->
                __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) ->
                ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
                list -> __ -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list ->
                __ -> T_as_UCT.t compare0 -> __ -> __ -> 'a2) -> ('a1 t ->
                'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
                'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

              val coq_R_equal_rec :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
                list -> __ -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list ->
                __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) ->
                ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
                list -> __ -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list ->
                __ -> T_as_UCT.t compare0 -> __ -> __ -> 'a2) -> ('a1 t ->
                'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
                'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

              val equal_rect :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
                list -> __ -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list ->
                __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
                T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
                T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
                T_as_UCT.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
                'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t ->
                'a2

              val equal_rec :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1)
                list -> __ -> T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list ->
                __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
                T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
                T_as_UCT.t -> 'a1 -> (T_as_UCT.t * 'a1) list -> __ ->
                T_as_UCT.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
                'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t ->
                'a2

              val coq_R_equal_correct :
                ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
                coq_R_equal

              val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

              val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

              val option_cons :
                key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

              val map2_l :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

              val map2_r :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

              val map2 :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                'a3 t

              val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

              val fold_right_pair :
                ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

              val map2_alt :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                (key * 'a3) list

              val at_least_one :
                'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

              val at_least_one_then_f :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
                option -> 'a3 option
             end

            type 'elt coq_R_mem = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_mem =
            | R_mem_0 of 'elt tree
            | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * bool * 'elt coq_R_mem
            | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * bool * 'elt coq_R_mem

            val coq_R_mem_rect :
              T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
              'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

            val coq_R_mem_rec :
              T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
              'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

            type 'elt coq_R_find = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_find =
            | R_find_0 of 'elt tree
            | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt option * 'elt coq_R_find
            | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt option * 'elt coq_R_find

            val coq_R_find_rect :
              T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
              'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

            val coq_R_find_rec :
              T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
              'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

            type 'elt coq_R_bal = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_bal =
            | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
            | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
               key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t
            | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
            | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
               key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t
            | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

            val coq_R_bal_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
              __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
              tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
              key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
              -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              'a1 tree -> 'a1 coq_R_bal -> 'a2

            val coq_R_bal_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
              __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
              tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
              key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
              -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              'a1 tree -> 'a1 coq_R_bal -> 'a2

            type 'elt coq_R_add = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_add =
            | R_add_0 of 'elt tree
            | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_add
            | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_add

            val coq_R_add_rect :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
              'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

            val coq_R_add_rec :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
              'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

            type 'elt coq_R_remove_min = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_remove_min =
            | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
            | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree
               * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
               * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min
               * 'elt tree * (key * 'elt)

            val coq_R_remove_min_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ ->
              'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
              tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

            val coq_R_remove_min_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ ->
              'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
              tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

            type 'elt coq_R_merge = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_merge =
            | R_merge_0 of 'elt tree * 'elt tree
            | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t
            | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'elt tree * (key * 'elt) *
               key * 'elt

            val coq_R_merge_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key ->
              'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_merge -> 'a2

            val coq_R_merge_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key ->
              'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_merge -> 'a2

            type 'elt coq_R_remove = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_remove =
            | R_remove_0 of 'elt tree
            | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
            | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

            val coq_R_remove_rect :
              T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
              'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

            val coq_R_remove_rec :
              T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
              'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

            type 'elt coq_R_concat = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_concat =
            | R_concat_0 of 'elt tree * 'elt tree
            | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t
            | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'elt tree * (key * 'elt)

            val coq_R_concat_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
              'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

            val coq_R_concat_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
              'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

            type 'elt coq_R_split = 'elt R.Defs.SigFM.Raw.Proofs.coq_R_split =
            | R_split_0 of 'elt tree
            | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
               * 'elt option * 'elt tree
            | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
               * 'elt option * 'elt tree

            val coq_R_split_rect :
              T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option
              -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree
              -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1
              triple -> 'a1 coq_R_split -> 'a2

            val coq_R_split_rec :
              T_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option
              -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree
              -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1
              triple -> 'a1 coq_R_split -> 'a2

            type ('elt, 'x) coq_R_map_option = ('elt, 'x) R.Defs.SigFM.Raw.Proofs.coq_R_map_option =
            | R_map_option_0 of 'elt tree
            | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'x * 'x tree
               * ('elt, 'x) coq_R_map_option * 'x tree
               * ('elt, 'x) coq_R_map_option
            | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'x tree
               * ('elt, 'x) coq_R_map_option * 'x tree
               * ('elt, 'x) coq_R_map_option

            val coq_R_map_option_rect :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3

            val coq_R_map_option_rec :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3

            type ('elt, 'x0, 'x) coq_R_map2_opt = ('elt, 'x0, 'x) R.Defs.SigFM.Raw.Proofs.coq_R_map2_opt =
            | R_map2_opt_0 of 'elt tree * 'x0 tree
            | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t
            | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0
               * 'x0 tree * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree
               * 'x * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
               * ('elt, 'x0, 'x) coq_R_map2_opt
            | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0
               * 'x0 tree * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree
               * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
               * ('elt, 'x0, 'x) coq_R_map2_opt

            val coq_R_map2_opt_rect :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
              tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2,
              'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

            val coq_R_map2_opt_rec :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
              tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2,
              'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

            val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

            val flatten_e : 'a1 enumeration -> (key * 'a1) list
           end
         end

        type 'elt bst =
          'elt Raw.tree
          (* singleton inductive, whose constructor was Bst *)

        val this : 'a1 bst -> 'a1 Raw.tree

        type 'elt t = 'elt bst

        type key = T_as_UCT.t

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        val remove : key -> 'a1 t -> 'a1 t

        val mem : key -> 'a1 t -> bool

        val find : key -> 'a1 t -> 'a1 option

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val elements : 'a1 t -> (key * 'a1) list

        val cardinal : 'a1 t -> nat

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
       end

      module SigFMF :
       sig
        val eqb : T_as_UCT.t -> T_as_UCT.t -> bool

        val coq_In_dec : 'a1 SigFM.t -> SigFM.key -> bool
       end

      module Strings :
       sig
        type coq_String = R.Ty.coq_Sigma list

        val coq_String_dec : coq_String -> coq_String -> bool

        val rm_empty : coq_String list -> R.Ty.coq_Sigma list list
       end

      module Regexes :
       sig
        type regex = R.Defs.Regexes.regex =
        | EmptySet
        | EmptyStr
        | Char of R.Ty.coq_Sigma
        | App of regex * regex
        | Union of regex * regex
        | Star of regex

        val regex_rect :
          'a1 -> 'a1 -> (R.Ty.coq_Sigma -> 'a1) -> (regex -> 'a1 -> regex ->
          'a1 -> 'a1) -> (regex -> 'a1 -> regex -> 'a1 -> 'a1) -> (regex ->
          'a1 -> 'a1) -> regex -> 'a1

        val regex_rec :
          'a1 -> 'a1 -> (R.Ty.coq_Sigma -> 'a1) -> (regex -> 'a1 -> regex ->
          'a1 -> 'a1) -> (regex -> 'a1 -> regex -> 'a1 -> 'a1) -> (regex ->
          'a1 -> 'a1) -> regex -> 'a1

        val regex_dec : regex -> regex -> bool

        val regex_eq : regex -> regex -> bool

        val nullable' : regex -> bool

        val nullable : regex -> bool

        val derivative : R.Ty.coq_Sigma -> regex -> regex

        val derivative_list : R.Ty.coq_Sigma list -> regex -> regex

        val re_compare : regex -> regex -> comparison
       end

      module Coq_regex_as_UCT :
       sig
        type t = Regexes.regex

        val compare : Regexes.regex -> Regexes.regex -> comparison
       end

      module Coq_regex_as_UOT :
       sig
        type t = Coq_regex_as_UCT.t

        val compare : t -> t -> t compare0

        val eq_dec : t -> t -> bool
       end

      module Coq_reFS :
       sig
        module X' :
         sig
          type t = Coq_regex_as_UCT.t

          val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

          val compare : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison
         end

        module MSet :
         sig
          module Raw :
           sig
            type elt = Coq_regex_as_UCT.t

            type tree = R.Defs.Coq_reFS.MSet.Raw.tree =
            | Leaf
            | Node of Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree

            val empty : tree

            val is_empty : tree -> bool

            val mem : Coq_regex_as_UCT.t -> tree -> bool

            val min_elt : tree -> elt option

            val max_elt : tree -> elt option

            val choose : tree -> elt option

            val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

            val elements_aux :
              Coq_regex_as_UCT.t list -> tree -> Coq_regex_as_UCT.t list

            val elements : tree -> Coq_regex_as_UCT.t list

            val rev_elements_aux :
              Coq_regex_as_UCT.t list -> tree -> Coq_regex_as_UCT.t list

            val rev_elements : tree -> Coq_regex_as_UCT.t list

            val cardinal : tree -> nat

            val maxdepth : tree -> nat

            val mindepth : tree -> nat

            val for_all : (elt -> bool) -> tree -> bool

            val exists_ : (elt -> bool) -> tree -> bool

            type enumeration = R.Defs.Coq_reFS.MSet.Raw.enumeration =
            | End
            | More of elt * tree * enumeration

            val cons : tree -> enumeration -> enumeration

            val compare_more :
              Coq_regex_as_UCT.t -> (enumeration -> comparison) ->
              enumeration -> comparison

            val compare_cont :
              tree -> (enumeration -> comparison) -> enumeration -> comparison

            val compare_end : enumeration -> comparison

            val compare : tree -> tree -> comparison

            val equal : tree -> tree -> bool

            val subsetl : (tree -> bool) -> Coq_regex_as_UCT.t -> tree -> bool

            val subsetr : (tree -> bool) -> Coq_regex_as_UCT.t -> tree -> bool

            val subset : tree -> tree -> bool

            type t = tree

            val height : t -> Z_as_Int.t

            val singleton : Coq_regex_as_UCT.t -> tree

            val create : t -> Coq_regex_as_UCT.t -> t -> tree

            val assert_false : t -> Coq_regex_as_UCT.t -> t -> tree

            val bal : t -> Coq_regex_as_UCT.t -> t -> tree

            val add : Coq_regex_as_UCT.t -> tree -> tree

            val join : tree -> elt -> t -> t

            val remove_min : tree -> elt -> t -> t * elt

            val merge : tree -> tree -> tree

            val remove : Coq_regex_as_UCT.t -> tree -> tree

            val concat : tree -> tree -> tree

            type triple = R.Defs.Coq_reFS.MSet.Raw.triple = { t_left :
                                                              t; t_in :
                                                              bool;
                                                              t_right :
                                                              t }

            val t_left : triple -> t

            val t_in : triple -> bool

            val t_right : triple -> t

            val split : Coq_regex_as_UCT.t -> tree -> triple

            val inter : tree -> tree -> tree

            val diff : tree -> tree -> tree

            val union : tree -> tree -> tree

            val filter : (elt -> bool) -> tree -> tree

            val partition : (elt -> bool) -> t -> t * t

            val ltb_tree : Coq_regex_as_UCT.t -> tree -> bool

            val gtb_tree : Coq_regex_as_UCT.t -> tree -> bool

            val isok : tree -> bool

            module MX :
             sig
              module OrderTac :
               sig
                module OTF :
                 sig
                  type t = Coq_regex_as_UCT.t

                  val compare :
                    Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

                  val eq_dec :
                    Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
                 end

                module TO :
                 sig
                  type t = Coq_regex_as_UCT.t

                  val compare :
                    Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

                  val eq_dec :
                    Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
                 end
               end

              val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
             end

            type coq_R_min_elt = R.Defs.Coq_reFS.MSet.Raw.coq_R_min_elt =
            | R_min_elt_0 of tree
            | R_min_elt_1 of tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
               * tree
            | R_min_elt_2 of tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
               * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree
               * elt option * coq_R_min_elt

            type coq_R_max_elt = R.Defs.Coq_reFS.MSet.Raw.coq_R_max_elt =
            | R_max_elt_0 of tree
            | R_max_elt_1 of tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
               * tree
            | R_max_elt_2 of tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t
               * tree * Z_as_Int.t * tree * Coq_regex_as_UCT.t * tree
               * elt option * coq_R_max_elt

            module L :
             sig
              module MO :
               sig
                module OrderTac :
                 sig
                  module OTF :
                   sig
                    type t = Coq_regex_as_UCT.t

                    val compare :
                      Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

                    val eq_dec :
                      Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
                   end

                  module TO :
                   sig
                    type t = Coq_regex_as_UCT.t

                    val compare :
                      Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

                    val eq_dec :
                      Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
                   end
                 end

                val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

                val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

                val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
               end
             end

            val flatten_e : enumeration -> elt list

            type coq_R_bal = R.Defs.Coq_reFS.MSet.Raw.coq_R_bal =
            | R_bal_0 of t * Coq_regex_as_UCT.t * t
            | R_bal_1 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree
            | R_bal_2 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree
            | R_bal_3 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree
            | R_bal_4 of t * Coq_regex_as_UCT.t * t
            | R_bal_5 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree
            | R_bal_6 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree
            | R_bal_7 of t * Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree
            | R_bal_8 of t * Coq_regex_as_UCT.t * t

            type coq_R_remove_min = R.Defs.Coq_reFS.MSet.Raw.coq_R_remove_min =
            | R_remove_min_0 of tree * elt * t
            | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * (t * elt) * coq_R_remove_min *
               t * elt

            type coq_R_merge = R.Defs.Coq_reFS.MSet.Raw.coq_R_merge =
            | R_merge_0 of tree * tree
            | R_merge_1 of tree * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree
            | R_merge_2 of tree * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * t * elt

            type coq_R_concat = R.Defs.Coq_reFS.MSet.Raw.coq_R_concat =
            | R_concat_0 of tree * tree
            | R_concat_1 of tree * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree
            | R_concat_2 of tree * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * t * elt

            type coq_R_inter = R.Defs.Coq_reFS.MSet.Raw.coq_R_inter =
            | R_inter_0 of tree * tree
            | R_inter_1 of tree * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree
            | R_inter_2 of tree * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * t * bool * t * tree
               * coq_R_inter * tree * coq_R_inter
            | R_inter_3 of tree * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * t * bool * t * tree
               * coq_R_inter * tree * coq_R_inter

            type coq_R_diff = R.Defs.Coq_reFS.MSet.Raw.coq_R_diff =
            | R_diff_0 of tree * tree
            | R_diff_1 of tree * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree
            | R_diff_2 of tree * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * t * bool * t * tree * coq_R_diff
               * tree * coq_R_diff
            | R_diff_3 of tree * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * t * bool * t * tree * coq_R_diff
               * tree * coq_R_diff

            type coq_R_union = R.Defs.Coq_reFS.MSet.Raw.coq_R_union =
            | R_union_0 of tree * tree
            | R_union_1 of tree * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree
            | R_union_2 of tree * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
               * Coq_regex_as_UCT.t * tree * t * bool * t * tree
               * coq_R_union * tree * coq_R_union
           end

          module E :
           sig
            type t = Coq_regex_as_UCT.t

            val compare :
              Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> comparison

            val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
           end

          type elt = Coq_regex_as_UCT.t

          type t_ = Raw.t
            (* singleton inductive, whose constructor was Mkt *)

          val this : t_ -> Raw.t

          type t = t_

          val mem : elt -> t -> bool

          val add : elt -> t -> t

          val remove : elt -> t -> t

          val singleton : elt -> t

          val union : t -> t -> t

          val inter : t -> t -> t

          val diff : t -> t -> t

          val equal : t -> t -> bool

          val subset : t -> t -> bool

          val empty : t

          val is_empty : t -> bool

          val elements : t -> elt list

          val choose : t -> elt option

          val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

          val cardinal : t -> nat

          val filter : (elt -> bool) -> t -> t

          val for_all : (elt -> bool) -> t -> bool

          val exists_ : (elt -> bool) -> t -> bool

          val partition : (elt -> bool) -> t -> t * t

          val eq_dec : t -> t -> bool

          val compare : t -> t -> comparison

          val min_elt : t -> elt option

          val max_elt : t -> elt option
         end

        type elt = Coq_regex_as_UCT.t

        type t = MSet.t

        val empty : t

        val is_empty : t -> bool

        val mem : elt -> t -> bool

        val add : elt -> t -> t

        val singleton : elt -> t

        val remove : elt -> t -> t

        val union : t -> t -> t

        val inter : t -> t -> t

        val diff : t -> t -> t

        val eq_dec : t -> t -> bool

        val equal : t -> t -> bool

        val subset : t -> t -> bool

        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

        val for_all : (elt -> bool) -> t -> bool

        val exists_ : (elt -> bool) -> t -> bool

        val filter : (elt -> bool) -> t -> t

        val partition : (elt -> bool) -> t -> t * t

        val cardinal : t -> nat

        val elements : t -> elt list

        val choose : t -> elt option

        module MF :
         sig
          val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
         end

        val min_elt : t -> elt option

        val max_elt : t -> elt option

        val compare : t -> t -> t compare0

        module E :
         sig
          type t = Coq_regex_as_UCT.t

          val compare :
            Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t
            compare0

          val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
         end
       end

      module Coq_reFSF :
       sig
        val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
       end

      module Coq_reFM :
       sig
        module E :
         sig
          type t = Coq_regex_as_UCT.t

          val compare :
            Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t
            compare0

          val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
         end

        module Raw :
         sig
          type key = Coq_regex_as_UCT.t

          type 'elt tree = 'elt R.Defs.Coq_reFM.Raw.tree =
          | Leaf
          | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

          val tree_rect :
            'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
            Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

          val tree_rec :
            'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
            Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

          val height : 'a1 tree -> Z_as_Int.t

          val cardinal : 'a1 tree -> nat

          val empty : 'a1 tree

          val is_empty : 'a1 tree -> bool

          val mem : Coq_regex_as_UCT.t -> 'a1 tree -> bool

          val find : Coq_regex_as_UCT.t -> 'a1 tree -> 'a1 option

          val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

          val remove_min :
            'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

          val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

          val remove : Coq_regex_as_UCT.t -> 'a1 tree -> 'a1 tree

          val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

          type 'elt triple = 'elt R.Defs.Coq_reFM.Raw.triple = { t_left :
                                                                 'elt tree;
                                                                 t_opt :
                                                                 'elt option;
                                                                 t_right :
                                                                 'elt tree }

          val t_left : 'a1 triple -> 'a1 tree

          val t_opt : 'a1 triple -> 'a1 option

          val t_right : 'a1 triple -> 'a1 tree

          val split : Coq_regex_as_UCT.t -> 'a1 tree -> 'a1 triple

          val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

          val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

          val elements : 'a1 tree -> (key * 'a1) list

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

          type 'elt enumeration = 'elt R.Defs.Coq_reFM.Raw.enumeration =
          | End
          | More of key * 'elt * 'elt tree * 'elt enumeration

          val enumeration_rect :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2

          val enumeration_rec :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2

          val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

          val equal_more :
            ('a1 -> 'a1 -> bool) -> Coq_regex_as_UCT.t -> 'a1 -> ('a1
            enumeration -> bool) -> 'a1 enumeration -> bool

          val equal_cont :
            ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
            'a1 enumeration -> bool

          val equal_end : 'a1 enumeration -> bool

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

          val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

          val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

          val map2_opt :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3
            tree

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree
            -> 'a3 tree

          module Proofs :
           sig
            module MX :
             sig
              module TO :
               sig
                type t = Coq_regex_as_UCT.t
               end

              module IsTO :
               sig
               end

              module OrderTac :
               sig
               end

              val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

              val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
             end

            module PX :
             sig
              module MO :
               sig
                module TO :
                 sig
                  type t = Coq_regex_as_UCT.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

                val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

                val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
               end
             end

            module L :
             sig
              module MX :
               sig
                module TO :
                 sig
                  type t = Coq_regex_as_UCT.t
                 end

                module IsTO :
                 sig
                 end

                module OrderTac :
                 sig
                 end

                val eq_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

                val lt_dec : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

                val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
               end

              module PX :
               sig
                module MO :
                 sig
                  module TO :
                   sig
                    type t = Coq_regex_as_UCT.t
                   end

                  module IsTO :
                   sig
                   end

                  module OrderTac :
                   sig
                   end

                  val eq_dec :
                    Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

                  val lt_dec :
                    Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

                  val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool
                 end
               end

              type key = Coq_regex_as_UCT.t

              type 'elt t = (Coq_regex_as_UCT.t * 'elt) list

              val empty : 'a1 t

              val is_empty : 'a1 t -> bool

              val mem : key -> 'a1 t -> bool

              type 'elt coq_R_mem = 'elt R.Defs.Coq_reFM.Raw.Proofs.L.coq_R_mem =
              | R_mem_0 of 'elt t
              | R_mem_1 of 'elt t * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list
              | R_mem_2 of 'elt t * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list
              | R_mem_3 of 'elt t * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list * bool * 'elt coq_R_mem

              val coq_R_mem_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> bool ->
                'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
                coq_R_mem -> 'a2

              val coq_R_mem_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> bool ->
                'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
                coq_R_mem -> 'a2

              val mem_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
                'a2) -> 'a1 t -> 'a2

              val mem_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
                'a2) -> 'a1 t -> 'a2

              val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

              val find : key -> 'a1 t -> 'a1 option

              type 'elt coq_R_find = 'elt R.Defs.Coq_reFM.Raw.Proofs.L.coq_R_find =
              | R_find_0 of 'elt t
              | R_find_1 of 'elt t * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list
              | R_find_2 of 'elt t * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list
              | R_find_3 of 'elt t * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list * 'elt option
                 * 'elt coq_R_find

              val coq_R_find_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1
                option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
                option -> 'a1 coq_R_find -> 'a2

              val coq_R_find_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1
                option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
                option -> 'a1 coq_R_find -> 'a2

              val find_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
                'a2) -> 'a1 t -> 'a2

              val find_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
                'a2) -> 'a1 t -> 'a2

              val coq_R_find_correct :
                key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

              val add : key -> 'a1 -> 'a1 t -> 'a1 t

              type 'elt coq_R_add = 'elt R.Defs.Coq_reFM.Raw.Proofs.L.coq_R_add =
              | R_add_0 of 'elt t
              | R_add_1 of 'elt t * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list
              | R_add_2 of 'elt t * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list
              | R_add_3 of 'elt t * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list * 'elt t * 'elt coq_R_add

              val coq_R_add_rect :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list
                -> __ -> __ -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
                'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
                'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
                'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
                coq_R_add -> 'a2

              val coq_R_add_rec :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list
                -> __ -> __ -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
                'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
                'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
                'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
                coq_R_add -> 'a2

              val add_rect :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list
                -> __ -> __ -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
                'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
                'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
                'a2) -> 'a1 t -> 'a2

              val add_rec :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list
                -> __ -> __ -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t ->
                'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ ->
                'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
                'a2) -> 'a1 t -> 'a2

              val coq_R_add_correct :
                key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

              val remove : key -> 'a1 t -> 'a1 t

              type 'elt coq_R_remove = 'elt R.Defs.Coq_reFM.Raw.Proofs.L.coq_R_remove =
              | R_remove_0 of 'elt t
              | R_remove_1 of 'elt t * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list
              | R_remove_2 of 'elt t * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list
              | R_remove_3 of 'elt t * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list * 'elt t
                 * 'elt coq_R_remove

              val coq_R_remove_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
                'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
                coq_R_remove -> 'a2

              val coq_R_remove_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
                'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
                coq_R_remove -> 'a2

              val remove_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
                'a2) -> 'a1 t -> 'a2

              val remove_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> 'a2) -> ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
                ('a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __ -> 'a2 ->
                'a2) -> 'a1 t -> 'a2

              val coq_R_remove_correct :
                key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

              val elements : 'a1 t -> 'a1 t

              val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

              type ('elt, 'a) coq_R_fold = ('elt, 'a) R.Defs.Coq_reFM.Raw.Proofs.L.coq_R_fold =
              | R_fold_0 of 'elt t * 'a
              | R_fold_1 of 'elt t * 'a * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list * 'a
                 * ('elt, 'a) coq_R_fold

              val coq_R_fold_rect :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
                coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
                'a2) coq_R_fold -> 'a3

              val coq_R_fold_rec :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
                coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
                'a2) coq_R_fold -> 'a3

              val fold_rect :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t
                -> 'a2 -> 'a3

              val fold_rec :
                (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) ->
                ('a1 t -> 'a2 -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t
                -> 'a2 -> 'a3

              val coq_R_fold_correct :
                (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
                'a2) coq_R_fold

              val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

              type 'elt coq_R_equal = 'elt R.Defs.Coq_reFM.Raw.Proofs.L.coq_R_equal =
              | R_equal_0 of 'elt t * 'elt t
              | R_equal_1 of 'elt t * 'elt t * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list * Coq_regex_as_UCT.t
                 * 'elt * (Coq_regex_as_UCT.t * 'elt) list * bool
                 * 'elt coq_R_equal
              | R_equal_2 of 'elt t * 'elt t * Coq_regex_as_UCT.t * 'elt
                 * (Coq_regex_as_UCT.t * 'elt) list * Coq_regex_as_UCT.t
                 * 'elt * (Coq_regex_as_UCT.t * 'elt) list
                 * Coq_regex_as_UCT.t compare0
              | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

              val coq_R_equal_rect :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
                -> Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1)
                list -> __ -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t
                compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t ->
                __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool ->
                'a1 coq_R_equal -> 'a2

              val coq_R_equal_rec :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
                -> Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1)
                list -> __ -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t
                compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t ->
                __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool ->
                'a1 coq_R_equal -> 'a2

              val equal_rect :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t ->
                'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ ->
                Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list
                -> __ -> Coq_regex_as_UCT.t compare0 -> __ -> __ -> 'a2) ->
                ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
                -> 'a1 t -> 'a1 t -> 'a2

              val equal_rec :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t -> 'a1 ->
                (Coq_regex_as_UCT.t * 'a1) list -> __ -> Coq_regex_as_UCT.t
                -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ -> __ -> __
                -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> Coq_regex_as_UCT.t ->
                'a1 -> (Coq_regex_as_UCT.t * 'a1) list -> __ ->
                Coq_regex_as_UCT.t -> 'a1 -> (Coq_regex_as_UCT.t * 'a1) list
                -> __ -> Coq_regex_as_UCT.t compare0 -> __ -> __ -> 'a2) ->
                ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
                -> 'a1 t -> 'a1 t -> 'a2

              val coq_R_equal_correct :
                ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
                coq_R_equal

              val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

              val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

              val option_cons :
                key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

              val map2_l :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

              val map2_r :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

              val map2 :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                'a3 t

              val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

              val fold_right_pair :
                ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

              val map2_alt :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                (key * 'a3) list

              val at_least_one :
                'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

              val at_least_one_then_f :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
                option -> 'a3 option
             end

            type 'elt coq_R_mem = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_mem =
            | R_mem_0 of 'elt tree
            | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * bool * 'elt coq_R_mem
            | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * bool * 'elt coq_R_mem

            val coq_R_mem_rect :
              Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
              'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

            val coq_R_mem_rec :
              Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
              'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

            type 'elt coq_R_find = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_find =
            | R_find_0 of 'elt tree
            | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt option * 'elt coq_R_find
            | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt option * 'elt coq_R_find

            val coq_R_find_rect :
              Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree
              -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
              coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
              coq_R_find -> 'a2

            val coq_R_find_rec :
              Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree
              -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
              coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1
              coq_R_find -> 'a2

            type 'elt coq_R_bal = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_bal =
            | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
            | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
               key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t
            | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
            | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
               key * 'elt * 'elt tree * Z_as_Int.t
            | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree *
               key * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t
            | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

            val coq_R_bal_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
              __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
              tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
              key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
              -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              'a1 tree -> 'a1 coq_R_bal -> 'a2

            val coq_R_bal_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ ->
              __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
              tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
              key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
              -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ ->
              __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              'a1 tree -> 'a1 coq_R_bal -> 'a2

            type 'elt coq_R_add = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_add =
            | R_add_0 of 'elt tree
            | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_add
            | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_add

            val coq_R_add_rect :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
              'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

            val coq_R_add_rec :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add ->
              'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

            type 'elt coq_R_remove_min = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_remove_min =
            | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
            | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree
               * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
               * ('elt tree * (key * 'elt)) * 'elt coq_R_remove_min
               * 'elt tree * (key * 'elt)

            val coq_R_remove_min_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ ->
              'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
              tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

            val coq_R_remove_min_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ ->
              'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1
              tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

            type 'elt coq_R_merge = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_merge =
            | R_merge_0 of 'elt tree * 'elt tree
            | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t
            | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'elt tree * (key * 'elt) *
               key * 'elt

            val coq_R_merge_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key ->
              'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_merge -> 'a2

            val coq_R_merge_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key ->
              'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_merge -> 'a2

            type 'elt coq_R_remove = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_remove =
            | R_remove_0 of 'elt tree
            | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
            | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

            val coq_R_remove_rect :
              Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree
              -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
              coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_remove -> 'a2

            val coq_R_remove_rec :
              Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree
              -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __
              -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
              coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
              coq_R_remove -> 'a2

            type 'elt coq_R_concat = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_concat =
            | R_concat_0 of 'elt tree * 'elt tree
            | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t
            | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'elt tree * (key * 'elt)

            val coq_R_concat_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
              'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

            val coq_R_concat_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.t -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) ->
              'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

            type 'elt coq_R_split = 'elt R.Defs.Coq_reFM.Raw.Proofs.coq_R_split =
            | R_split_0 of 'elt tree
            | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
               * 'elt option * 'elt tree
            | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t
            | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
               * 'elt option * 'elt tree

            val coq_R_split_rect :
              Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
              option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
              -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) ->
              'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

            val coq_R_split_rec :
              Coq_regex_as_UCT.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ ->
              __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
              option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
              -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) ->
              'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

            type ('elt, 'x) coq_R_map_option = ('elt, 'x) R.Defs.Coq_reFM.Raw.Proofs.coq_R_map_option =
            | R_map_option_0 of 'elt tree
            | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'x * 'x tree
               * ('elt, 'x) coq_R_map_option * 'x tree
               * ('elt, 'x) coq_R_map_option
            | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.t * 'x tree
               * ('elt, 'x) coq_R_map_option * 'x tree
               * ('elt, 'x) coq_R_map_option

            val coq_R_map_option_rect :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3

            val coq_R_map_option_rec :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
              -> __ -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3
              -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) ->
              'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3

            type ('elt, 'x0, 'x) coq_R_map2_opt = ('elt, 'x0, 'x) R.Defs.Coq_reFM.Raw.Proofs.coq_R_map2_opt =
            | R_map2_opt_0 of 'elt tree * 'x0 tree
            | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t
            | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0
               * 'x0 tree * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree
               * 'x * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
               * ('elt, 'x0, 'x) coq_R_map2_opt
            | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key *
               'elt * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0
               * 'x0 tree * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree
               * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
               * ('elt, 'x0, 'x) coq_R_map2_opt

            val coq_R_map2_opt_rect :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
              tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2,
              'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

            val coq_R_map2_opt_rec :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __
              -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
              tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t ->
              __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
              'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree ->
              ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2,
              'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

            val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

            val flatten_e : 'a1 enumeration -> (key * 'a1) list
           end
         end

        type 'elt bst =
          'elt Raw.tree
          (* singleton inductive, whose constructor was Bst *)

        val this : 'a1 bst -> 'a1 Raw.tree

        type 'elt t = 'elt bst

        type key = Coq_regex_as_UCT.t

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        val remove : key -> 'a1 t -> 'a1 t

        val mem : key -> 'a1 t -> bool

        val find : key -> 'a1 t -> 'a1 option

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val elements : 'a1 t -> (key * 'a1) list

        val cardinal : 'a1 t -> nat

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
       end

      module Coq_reFMF :
       sig
        val eqb : Coq_regex_as_UCT.t -> Coq_regex_as_UCT.t -> bool

        val coq_In_dec : 'a1 Coq_reFM.t -> Coq_reFM.key -> bool
       end

      module MatchSpec :
       sig
       end

      module MatchSpecLemmas :
       sig
       end

      module Notations :
       sig
       end

      module Helpers :
       sig
        val coq_Plus : Regexes.regex -> Regexes.regex

        val coq_IterUnion : Regexes.regex list -> Regexes.regex

        val coq_IterApp : Regexes.regex list -> Regexes.regex

        val coq_Optional : Regexes.regex -> Regexes.regex

        val coq_REString : Strings.coq_String -> Regexes.regex
       end
     end

    module Coq_reFS :
     sig
      module X' :
       sig
        type t = DS.Coq_regex_as_UCT.t

        val eq_dec : DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool

        val compare :
          DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> comparison
       end

      module MSet :
       sig
        module Raw :
         sig
          type elt = DS.Coq_regex_as_UCT.t

          type tree = R.Defs.Coq_reFS.MSet.Raw.tree =
          | Leaf
          | Node of Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t * tree

          val empty : tree

          val is_empty : tree -> bool

          val mem : DS.Coq_regex_as_UCT.t -> tree -> bool

          val min_elt : tree -> elt option

          val max_elt : tree -> elt option

          val choose : tree -> elt option

          val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

          val elements_aux :
            DS.Coq_regex_as_UCT.t list -> tree -> DS.Coq_regex_as_UCT.t list

          val elements : tree -> DS.Coq_regex_as_UCT.t list

          val rev_elements_aux :
            DS.Coq_regex_as_UCT.t list -> tree -> DS.Coq_regex_as_UCT.t list

          val rev_elements : tree -> DS.Coq_regex_as_UCT.t list

          val cardinal : tree -> nat

          val maxdepth : tree -> nat

          val mindepth : tree -> nat

          val for_all : (elt -> bool) -> tree -> bool

          val exists_ : (elt -> bool) -> tree -> bool

          type enumeration = R.Defs.Coq_reFS.MSet.Raw.enumeration =
          | End
          | More of elt * tree * enumeration

          val cons : tree -> enumeration -> enumeration

          val compare_more :
            DS.Coq_regex_as_UCT.t -> (enumeration -> comparison) ->
            enumeration -> comparison

          val compare_cont :
            tree -> (enumeration -> comparison) -> enumeration -> comparison

          val compare_end : enumeration -> comparison

          val compare : tree -> tree -> comparison

          val equal : tree -> tree -> bool

          val subsetl :
            (tree -> bool) -> DS.Coq_regex_as_UCT.t -> tree -> bool

          val subsetr :
            (tree -> bool) -> DS.Coq_regex_as_UCT.t -> tree -> bool

          val subset : tree -> tree -> bool

          type t = tree

          val height : t -> Z_as_Int.t

          val singleton : DS.Coq_regex_as_UCT.t -> tree

          val create : t -> DS.Coq_regex_as_UCT.t -> t -> tree

          val assert_false : t -> DS.Coq_regex_as_UCT.t -> t -> tree

          val bal : t -> DS.Coq_regex_as_UCT.t -> t -> tree

          val add : DS.Coq_regex_as_UCT.t -> tree -> tree

          val join : tree -> elt -> t -> t

          val remove_min : tree -> elt -> t -> t * elt

          val merge : tree -> tree -> tree

          val remove : DS.Coq_regex_as_UCT.t -> tree -> tree

          val concat : tree -> tree -> tree

          type triple = R.Defs.Coq_reFS.MSet.Raw.triple = { t_left :
                                                            t; t_in :
                                                            bool; t_right :
                                                            t }

          val t_left : triple -> t

          val t_in : triple -> bool

          val t_right : triple -> t

          val split : DS.Coq_regex_as_UCT.t -> tree -> triple

          val inter : tree -> tree -> tree

          val diff : tree -> tree -> tree

          val union : tree -> tree -> tree

          val filter : (elt -> bool) -> tree -> tree

          val partition : (elt -> bool) -> t -> t * t

          val ltb_tree : DS.Coq_regex_as_UCT.t -> tree -> bool

          val gtb_tree : DS.Coq_regex_as_UCT.t -> tree -> bool

          val isok : tree -> bool

          module MX :
           sig
            module OrderTac :
             sig
              module OTF :
               sig
                type t = DS.Coq_regex_as_UCT.t

                val compare :
                  DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> comparison

                val eq_dec :
                  DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
               end

              module TO :
               sig
                type t = DS.Coq_regex_as_UCT.t

                val compare :
                  DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> comparison

                val eq_dec :
                  DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
               end
             end

            val eq_dec :
              DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool

            val lt_dec :
              DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool

            val eqb : DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
           end

          type coq_R_min_elt = R.Defs.Coq_reFS.MSet.Raw.coq_R_min_elt =
          | R_min_elt_0 of tree
          | R_min_elt_1 of tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t
             * tree
          | R_min_elt_2 of tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t * tree
             * elt option * coq_R_min_elt

          type coq_R_max_elt = R.Defs.Coq_reFS.MSet.Raw.coq_R_max_elt =
          | R_max_elt_0 of tree
          | R_max_elt_1 of tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t
             * tree
          | R_max_elt_2 of tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t
             * tree * Z_as_Int.t * tree * DS.Coq_regex_as_UCT.t * tree
             * elt option * coq_R_max_elt

          module L :
           sig
            module MO :
             sig
              module OrderTac :
               sig
                module OTF :
                 sig
                  type t = DS.Coq_regex_as_UCT.t

                  val compare :
                    DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t ->
                    comparison

                  val eq_dec :
                    DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
                 end

                module TO :
                 sig
                  type t = DS.Coq_regex_as_UCT.t

                  val compare :
                    DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t ->
                    comparison

                  val eq_dec :
                    DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
                 end
               end

              val eq_dec :
                DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool

              val lt_dec :
                DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool

              val eqb : DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
             end
           end

          val flatten_e : enumeration -> elt list

          type coq_R_bal = R.Defs.Coq_reFS.MSet.Raw.coq_R_bal =
          | R_bal_0 of t * DS.Coq_regex_as_UCT.t * t
          | R_bal_1 of t * DS.Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree
          | R_bal_2 of t * DS.Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree
          | R_bal_3 of t * DS.Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree
          | R_bal_4 of t * DS.Coq_regex_as_UCT.t * t
          | R_bal_5 of t * DS.Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree
          | R_bal_6 of t * DS.Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree
          | R_bal_7 of t * DS.Coq_regex_as_UCT.t * t * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree
          | R_bal_8 of t * DS.Coq_regex_as_UCT.t * t

          type coq_R_remove_min = R.Defs.Coq_reFS.MSet.Raw.coq_R_remove_min =
          | R_remove_min_0 of tree * elt * t
          | R_remove_min_1 of tree * elt * t * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * (t * elt) * coq_R_remove_min
             * t * elt

          type coq_R_merge = R.Defs.Coq_reFS.MSet.Raw.coq_R_merge =
          | R_merge_0 of tree * tree
          | R_merge_1 of tree * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree
          | R_merge_2 of tree * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * t * elt

          type coq_R_concat = R.Defs.Coq_reFS.MSet.Raw.coq_R_concat =
          | R_concat_0 of tree * tree
          | R_concat_1 of tree * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree
          | R_concat_2 of tree * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * t * elt

          type coq_R_inter = R.Defs.Coq_reFS.MSet.Raw.coq_R_inter =
          | R_inter_0 of tree * tree
          | R_inter_1 of tree * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree
          | R_inter_2 of tree * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * t * bool * t * tree
             * coq_R_inter * tree * coq_R_inter
          | R_inter_3 of tree * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * t * bool * t * tree
             * coq_R_inter * tree * coq_R_inter

          type coq_R_diff = R.Defs.Coq_reFS.MSet.Raw.coq_R_diff =
          | R_diff_0 of tree * tree
          | R_diff_1 of tree * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree
          | R_diff_2 of tree * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * t * bool * t * tree
             * coq_R_diff * tree * coq_R_diff
          | R_diff_3 of tree * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * t * bool * t * tree
             * coq_R_diff * tree * coq_R_diff

          type coq_R_union = R.Defs.Coq_reFS.MSet.Raw.coq_R_union =
          | R_union_0 of tree * tree
          | R_union_1 of tree * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree
          | R_union_2 of tree * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * Z_as_Int.t * tree
             * DS.Coq_regex_as_UCT.t * tree * t * bool * t * tree
             * coq_R_union * tree * coq_R_union
         end

        module E :
         sig
          type t = DS.Coq_regex_as_UCT.t

          val compare :
            DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> comparison

          val eq_dec : DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
         end

        type elt = DS.Coq_regex_as_UCT.t

        type t_ = Raw.t
          (* singleton inductive, whose constructor was Mkt *)

        val this : t_ -> Raw.t

        type t = t_

        val mem : elt -> t -> bool

        val add : elt -> t -> t

        val remove : elt -> t -> t

        val singleton : elt -> t

        val union : t -> t -> t

        val inter : t -> t -> t

        val diff : t -> t -> t

        val equal : t -> t -> bool

        val subset : t -> t -> bool

        val empty : t

        val is_empty : t -> bool

        val elements : t -> elt list

        val choose : t -> elt option

        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

        val cardinal : t -> nat

        val filter : (elt -> bool) -> t -> t

        val for_all : (elt -> bool) -> t -> bool

        val exists_ : (elt -> bool) -> t -> bool

        val partition : (elt -> bool) -> t -> t * t

        val eq_dec : t -> t -> bool

        val compare : t -> t -> comparison

        val min_elt : t -> elt option

        val max_elt : t -> elt option
       end

      type elt = DS.Coq_regex_as_UCT.t

      type t = MSet.t

      val empty : t

      val is_empty : t -> bool

      val mem : elt -> t -> bool

      val add : elt -> t -> t

      val singleton : elt -> t

      val remove : elt -> t -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val eq_dec : t -> t -> bool

      val equal : t -> t -> bool

      val subset : t -> t -> bool

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val filter : (elt -> bool) -> t -> t

      val partition : (elt -> bool) -> t -> t * t

      val cardinal : t -> nat

      val elements : t -> elt list

      val choose : t -> elt option

      module MF :
       sig
        val eqb : DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
       end

      val min_elt : t -> elt option

      val max_elt : t -> elt option

      val compare : t -> t -> t compare0

      module E :
       sig
        type t = DS.Coq_regex_as_UCT.t

        val compare :
          DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t ->
          DS.Coq_regex_as_UCT.t compare0

        val eq_dec : DS.Coq_regex_as_UCT.t -> DS.Coq_regex_as_UCT.t -> bool
       end
     end

    type coq_Table

    val emptyTable : coq_Table

    val set_Table :
      coq_Table -> DS.Regexes.regex -> R.Ty.coq_Sigma -> DS.Regexes.regex ->
      coq_Table

    val get_Table :
      coq_Table -> DS.Regexes.regex -> R.Ty.coq_Sigma -> DS.Regexes.regex
      option

    val add_state : coq_Table -> DS.Regexes.regex -> coq_Table

    val get_states : coq_Table -> Coq_reFS.t

    val get_eq : coq_Table -> DS.Regexes.regex -> DS.Regexes.regex option
   end

  module Defs :
   sig
    module FillTable :
     sig
      val mkIterUnion' : R.Defs.Regexes.regex -> R.Defs.Regexes.regex list

      val merge' :
        R.Defs.Regexes.regex list -> R.Defs.Regexes.regex list ->
        R.Defs.Regexes.regex list

      val merge'' :
        R.Defs.Regexes.regex list -> R.Defs.Regexes.regex list ->
        R.Defs.Regexes.regex list

      val merge :
        R.Defs.Regexes.regex list -> R.Defs.Regexes.regex list ->
        R.Defs.Regexes.regex list

      val mkIterApp' : R.Defs.Regexes.regex -> R.Defs.Regexes.regex list

      val canon : R.Defs.Regexes.regex -> R.Defs.Regexes.regex

      val fill_Table_all' :
        TabTy.coq_Table -> R.Defs.Regexes.regex -> R.Ty.coq_Sigma list -> nat
        -> TabTy.coq_Table

      val fill_Table_all :
        TabTy.coq_Table -> R.Defs.Regexes.regex -> R.Ty.coq_Sigma list -> nat
        -> TabTy.coq_Table
     end

    module Spec :
     sig
     end

    module Correct :
     sig
     end
   end
 end

module MatcherFn =
 functor (R:T) ->
 struct
  (** val exp_matchb :
      R.Defs.Strings.coq_String -> R.Defs.Regexes.regex -> bool **)

  let rec exp_matchb s r =
    match s with
    | [] -> R.Defs.Regexes.nullable r
    | x :: xs -> exp_matchb xs (R.Defs.Regexes.derivative x r)
 end

module DFAFn =
 functor (TabT:Coq0_T) ->
 struct
  module CoreDefs =
   struct
    (** val char_set :
        TabT.R.Defs.Regexes.regex -> TabT.R.Ty.coq_Sigma list **)

    let rec char_set _ =
      TabT.R.Ty.coq_SigmaEnum

    (** val regex_depth : TabT.R.Defs.Regexes.regex -> nat **)

    let rec regex_depth = function
    | TabT.R.Defs.Regexes.App (e1, e2) ->
      let d1 = regex_depth e1 in
      let d2 = regex_depth e2 in
      if Nat.leb d2 d1 then add d1 (S O) else add d2 (S O)
    | TabT.R.Defs.Regexes.Union (e1, e2) ->
      let d1 = regex_depth e1 in
      let d2 = regex_depth e2 in
      if Nat.leb d2 d1 then add d1 (S O) else add d2 (S O)
    | TabT.R.Defs.Regexes.Star e0 -> add (regex_depth e0) (S O)
    | _ -> O

    (** val fin_states : TabT.R.Defs.Coq_reFS.t -> TabT.R.Defs.Coq_reFS.t **)

    let fin_states es =
      TabT.R.Defs.Coq_reFS.filter TabT.R.Defs.Regexes.nullable es

    type coq_DFA =
      (TabT.R.Defs.Regexes.regex * TabT.TabTy.coq_Table) * TabT.R.Defs.Coq_reFS.t

    (** val defDFA : coq_DFA **)

    let defDFA =
      ((TabT.R.Defs.Regexes.EmptySet, TabT.TabTy.emptyTable),
        TabT.R.Defs.Coq_reFS.empty)

    (** val coq_DFAtransition : TabT.R.Ty.coq_Sigma -> coq_DFA -> coq_DFA **)

    let coq_DFAtransition a = function
    | (p, fins) ->
      let (e, t0) = p in
      (match TabT.TabTy.get_Table t0 e a with
       | Some e' -> ((e', t0), fins)
       | None -> (((TabT.R.Defs.Regexes.derivative a e), t0), fins))

    (** val coq_DFAtransition_list :
        TabT.R.Ty.coq_Sigma list -> coq_DFA -> coq_DFA **)

    let rec coq_DFAtransition_list bs dfa =
      match bs with
      | [] -> dfa
      | c :: cs -> coq_DFAtransition_list cs (coq_DFAtransition c dfa)

    (** val coq_DFAaccepting : coq_DFA -> bool **)

    let coq_DFAaccepting = function
    | (p, fins) ->
      let (e, t0) = p in
      if TabT.R.Defs.Coq_reFS.mem e (TabT.TabTy.get_states t0)
      then TabT.R.Defs.Coq_reFS.mem e fins
      else TabT.R.Defs.Regexes.nullable e

    (** val coq_DFAaccepts :
        TabT.R.Defs.Strings.coq_String -> coq_DFA -> bool **)

    let rec coq_DFAaccepts z0 dfa =
      match z0 with
      | [] -> coq_DFAaccepting dfa
      | x :: xs -> coq_DFAaccepts xs (coq_DFAtransition x dfa)

    (** val regex2dfa : TabT.R.Defs.Regexes.regex -> coq_DFA **)

    let regex2dfa e =
      let t0 =
        TabT.Defs.FillTable.fill_Table_all TabT.TabTy.emptyTable
          (TabT.Defs.FillTable.canon e) (char_set e)
          (of_uint (D2 (D0 (D0 (D0 (D0 Nil))))))
      in
      let es = TabT.TabTy.get_states t0 in
      (((TabT.Defs.FillTable.canon e), t0), (fin_states es))

    (** val dfa2regex : coq_DFA -> TabT.R.Defs.Regexes.regex **)

    let dfa2regex = function
    | (p, _) -> let (e, _) = p in e
   end

  module Correct =
   struct
    module Mat = MatcherFn(TabT.R)
   end
 end

module ImplFn =
 functor (ST:Coq_T) ->
 struct
  module MPref =
   struct
    (** val max_pref_fn :
        ST.R.Defs.Strings.coq_String -> ST.Ty.coq_State ->
        (ST.Defs.Coredefs.coq_Prefix * ST.Defs.Coredefs.coq_Suffix) option **)

    let rec max_pref_fn s state =
      match s with
      | [] -> if ST.Ty.accepting state then Some ([], []) else None
      | a :: s' ->
        let state' = ST.Ty.transition a state in
        let mpxs = max_pref_fn s' state' in
        (match mpxs with
         | Some p0 -> let (p, q) = p0 in Some ((a :: p), q)
         | None ->
           if ST.Ty.accepting state'
           then Some ((a :: []), s')
           else if ST.Ty.accepting state then Some ([], s) else None)

    (** val extract_fsm_for_max :
        ST.R.Defs.Strings.coq_String ->
        (ST.Defs.Coredefs.coq_Label * ST.Ty.coq_State) ->
        ST.Defs.Coredefs.coq_Label * (ST.Defs.Coredefs.coq_Prefix * ST.Defs.Coredefs.coq_Suffix)
        option **)

    let extract_fsm_for_max code = function
    | (a, fsm) -> (a, (max_pref_fn code fsm))

    (** val max_prefs :
        ST.R.Defs.Strings.coq_String ->
        (ST.Defs.Coredefs.coq_Label * ST.Ty.coq_State) list ->
        (ST.Defs.Coredefs.coq_Label * (ST.Defs.Coredefs.coq_Prefix * ST.Defs.Coredefs.coq_Suffix)
        option) list **)

    let max_prefs code erules =
      map (extract_fsm_for_max code) erules

    (** val longer_pref :
        (ST.Defs.Coredefs.coq_Label * (ST.Defs.Coredefs.coq_Prefix * ST.Defs.Coredefs.coq_Suffix)
        option) ->
        (ST.Defs.Coredefs.coq_Label * (ST.Defs.Coredefs.coq_Prefix * ST.Defs.Coredefs.coq_Suffix)
        option) ->
        ST.Defs.Coredefs.coq_Label * (ST.Defs.Coredefs.coq_Prefix * ST.Defs.Coredefs.coq_Suffix)
        option **)

    let longer_pref oc apref1 apref2 =
      Printf.fprintf oc "longer_pref\n";
      let (_, o) = apref1 in
      (match o with
       | Some p ->
         let (x, _) = p in
         let (_, o0) = apref2 in
         (match o0 with
          | Some p0 ->
            let (y, _) = p0 in
            if Nat.eqb (length x) (length y)
            then apref1
            else if Nat.ltb (length x) (length y) then apref2 else apref1
          | None -> apref1)
       | None -> apref2)

    (** val max_of_prefs :
        (ST.Defs.Coredefs.coq_Label * (ST.Defs.Coredefs.coq_Prefix * ST.Defs.Coredefs.coq_Suffix)
        option) list ->
        ST.Defs.Coredefs.coq_Label * (ST.Defs.Coredefs.coq_Prefix * ST.Defs.Coredefs.coq_Suffix)
        option **)

    let rec max_of_prefs oc =
      Printf.fprintf oc "max_of_prefs\n";
      function
    | [] -> ([], None)
    | p :: ps -> longer_pref oc p (max_of_prefs oc ps)
   end

  module TypeCheckLemmas =
   struct
   end

  module Lex =
   struct
    (** val lex' :
        ST.Defs.Coredefs.sRule list -> ST.R.Defs.Strings.coq_String ->
        ST.Defs.Coredefs.coq_Token list * ST.R.Defs.Strings.coq_String **)

    let rec lex' oc rules code =
      let (label, o) = MPref.max_of_prefs oc (MPref.max_prefs code rules) in
      (match o with
       | Some p ->
         let (p0, suffix) = p in
         (match p0 with
          | [] -> ([], code)
          | ph :: pt ->
            let (lexemes, rest) = lex' oc rules suffix in
            (((label, (ph :: pt)) :: lexemes), rest))
       | None -> ([], code))

    (** val init_srule :
        ST.Defs.Coredefs.coq_Rule -> ST.Defs.Coredefs.sRule **)

    let init_srule = function
    | (label, re) -> (label, (ST.Ty.init_state re))

    (** val lex :
        ST.Defs.Coredefs.coq_Rule list -> ST.R.Defs.Strings.coq_String ->
        ST.Defs.Coredefs.coq_Token list * ST.R.Defs.Strings.coq_String **)

    let lex oc rules code =
      let srules = map init_srule rules in lex' oc srules code
   end
 end

(** val asciiEnumFn : nat -> char list **)

let rec asciiEnumFn = function
| O -> []
| S m -> (ascii_of_nat m) :: (asciiEnumFn m)

(** val asciiEnum : char list **)

let asciiEnum =
  asciiEnumFn (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val ascii2list : char -> bool list **)

let ascii2list a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b b0 b1 b2 b3 b4 b5 b6 ->
    b :: (b0 :: (b1 :: (b2 :: (b3 :: (b4 :: (b5 :: (b6 :: []))))))))
    a

(** val bool_order : bool -> bool -> comparison **)

let bool_order b1 b2 =
  if b1 then if b2 then Eq else Gt else if b2 then Lt else Eq

(** val bool_list_order : bool list -> bool list -> comparison **)

let rec bool_list_order bs bs' =
  match bs with
  | [] -> (match bs' with
           | [] -> Eq
           | _ :: _ -> Lt)
  | h :: t0 ->
    (match bs' with
     | [] -> Gt
     | h' :: t' ->
       (match bool_order h h' with
        | Eq -> bool_list_order t0 t'
        | x -> x))

(** val ascii_order : char -> char -> comparison **)

let ascii_order a1 a2 =
  bool_list_order (ascii2list a1) (ascii2list a2)

module FTable =
 functor (R:T) ->
 struct
  module DS = R.Defs

  module Sigma_as_UOT = R.Defs.T_as_UOT

  module Coq_regex_as_UOT = R.Defs.Coq_regex_as_UOT

  module Coq_pair_as_UOT = Pair_as_UOT(Coq_regex_as_UOT)(Sigma_as_UOT)

  module FM = Coq_Make(Coq_pair_as_UOT)

  module FMF = Coq_Facts(FM)

  module Coq_reFS = R.Defs.Coq_reFS

  type coq_Table = (R.Defs.Regexes.regex * R.Ty.coq_Sigma, R.Defs.Regexes.regex) Hashtbl.t
  * Coq_reFS.t

  exception NoSigma of string

  let emptyMap =
      match R.Ty.coq_SigmaEnum with
      | [] -> raise (NoSigma "SigmaEnum is empty")
      | x :: xs ->
          let m = Hashtbl.create 100 in
              Hashtbl.add m (R.Defs.Regexes.EmptySet, x) R.Defs.Regexes.EmptySet;
              Hashtbl.remove m (R.Defs.Regexes.EmptySet, x);
              m

  (** val emptyTable : coq_Table **)

  let emptyTable =
    (emptyMap, Coq_reFS.empty)

  (** val set_Table :
      coq_Table -> R.Defs.Regexes.regex -> R.Ty.coq_Sigma ->
      R.Defs.Regexes.regex -> coq_Table **)

  let set_Table t0 e a r =
    let (fm, fs) = t0 in ((Hashtbl.add fm (e, a) r); fm, fs)

  (** val get_Table :
      coq_Table -> R.Defs.Regexes.regex -> R.Ty.coq_Sigma ->
      R.Defs.Regexes.regex option **)

  let get_Table t0 e a =
    if Hashtbl.mem (fst t0) (e,a)
    then Some (Hashtbl.find (fst t0) (e, a))
    else None

  (** val add_state : coq_Table -> R.Defs.Regexes.regex -> coq_Table **)

  let add_state t0 e =
    let (fm, fs) = t0 in (fm, (Coq_reFS.add e fs))

  (** val get_states : coq_Table -> Coq_reFS.t **)

  let get_states =
    snd

  (** val get_eq :
      coq_Table -> R.Defs.Regexes.regex -> R.Defs.Regexes.regex option **)

  let get_eq t0 e =
    if Coq_reFS.mem e (snd t0) then Some e else None
 end

module LemmasFn =
 functor (ST:Coq_T) ->
 struct
  module IMPL = ImplFn(ST)
 end

module CorrectFn =
 functor (ST:Coq_T) ->
 struct
  module LEM = LemmasFn(ST)
 end

module MemoDefsFn =
 functor (STT:Coq_T) ->
 functor (MEM:sig
  type coq_Memo

  val emptyMemo : coq_Memo

  val set_Memo :
    out_channel -> coq_Memo -> STT.Ty.coq_Pointer -> STT.R.Defs.Strings.coq_String ->
    (STT.R.Defs.Strings.coq_String * STT.R.Defs.Strings.coq_String) option ->
    coq_Memo

  val get_Memo :
    out_channel -> coq_Memo -> STT.Ty.coq_Pointer -> STT.R.Defs.Strings.coq_String ->
    (STT.R.Defs.Strings.coq_String * STT.R.Defs.Strings.coq_String) option
    option
 end) ->
 struct
  module NaiveLexer = ImplFn(STT)

  module NaiveLexerF = CorrectFn(STT)
 end

module type Coq1_T =
 sig
  module STT :
   Coq_T

  module MemTy :
   sig
    type coq_Memo

    val emptyMemo : coq_Memo

    val set_Memo :
      out_channel -> coq_Memo -> STT.Ty.coq_Pointer -> STT.R.Defs.Strings.coq_String ->
      (STT.R.Defs.Strings.coq_String * STT.R.Defs.Strings.coq_String) option
      -> coq_Memo

    val get_Memo :
      out_channel -> coq_Memo -> STT.Ty.coq_Pointer -> STT.R.Defs.Strings.coq_String ->
      (STT.R.Defs.Strings.coq_String * STT.R.Defs.Strings.coq_String) option
      option
   end

  module Defs :
   sig
    module NaiveLexer :
     sig
      module MPref :
       sig
        val max_pref_fn :
          STT.R.Defs.Strings.coq_String -> STT.Ty.coq_State ->
          (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix) option

        val extract_fsm_for_max :
          STT.R.Defs.Strings.coq_String ->
          (STT.Defs.Coredefs.coq_Label * STT.Ty.coq_State) ->
          STT.Defs.Coredefs.coq_Label * (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
          option

        val max_prefs :
          STT.R.Defs.Strings.coq_String ->
          (STT.Defs.Coredefs.coq_Label * STT.Ty.coq_State) list ->
          (STT.Defs.Coredefs.coq_Label * (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
          option) list

        val longer_pref :
          out_channel -> (STT.Defs.Coredefs.coq_Label * (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
          option) ->
          (STT.Defs.Coredefs.coq_Label * (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
          option) ->
          STT.Defs.Coredefs.coq_Label * (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
          option

        val max_of_prefs :
          out_channel -> (STT.Defs.Coredefs.coq_Label * (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
          option) list ->
          STT.Defs.Coredefs.coq_Label * (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
          option
       end

      module TypeCheckLemmas :
       sig
       end

      module Lex :
       sig
        val lex' :
          out_channel -> STT.Defs.Coredefs.sRule list -> STT.R.Defs.Strings.coq_String ->
          STT.Defs.Coredefs.coq_Token list * STT.R.Defs.Strings.coq_String

        val init_srule : STT.Defs.Coredefs.coq_Rule -> STT.Defs.Coredefs.sRule

        val lex :
          out_channel -> STT.Defs.Coredefs.coq_Rule list -> STT.R.Defs.Strings.coq_String ->
          STT.Defs.Coredefs.coq_Token list * STT.R.Defs.Strings.coq_String
       end
     end

    module NaiveLexerF :
     sig
      module LEM :
       sig
        module IMPL :
         sig
          module MPref :
           sig
            val max_pref_fn :
              STT.R.Defs.Strings.coq_String -> STT.Ty.coq_State ->
              (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
              option

            val extract_fsm_for_max :
              STT.R.Defs.Strings.coq_String ->
              (STT.Defs.Coredefs.coq_Label * STT.Ty.coq_State) ->
              STT.Defs.Coredefs.coq_Label * (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
              option

            val max_prefs :
              STT.R.Defs.Strings.coq_String ->
              (STT.Defs.Coredefs.coq_Label * STT.Ty.coq_State) list ->
              (STT.Defs.Coredefs.coq_Label * (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
              option) list

            val longer_pref :
              out_channel -> (STT.Defs.Coredefs.coq_Label * (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
              option) ->
              (STT.Defs.Coredefs.coq_Label * (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
              option) ->
              STT.Defs.Coredefs.coq_Label * (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
              option

            val max_of_prefs :
              out_channel -> (STT.Defs.Coredefs.coq_Label * (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
              option) list ->
              STT.Defs.Coredefs.coq_Label * (STT.Defs.Coredefs.coq_Prefix * STT.Defs.Coredefs.coq_Suffix)
              option
           end

          module TypeCheckLemmas :
           sig
           end

          module Lex :
           sig
            val lex' :
              out_channel -> STT.Defs.Coredefs.sRule list -> STT.R.Defs.Strings.coq_String
              -> STT.Defs.Coredefs.coq_Token
              list * STT.R.Defs.Strings.coq_String

            val init_srule :
              STT.Defs.Coredefs.coq_Rule -> STT.Defs.Coredefs.sRule

            val lex :
              out_channel -> STT.Defs.Coredefs.coq_Rule list ->
              STT.R.Defs.Strings.coq_String -> STT.Defs.Coredefs.coq_Token
              list * STT.R.Defs.Strings.coq_String
           end
         end
       end
     end
   end
 end

module Coq_ImplFn =
 functor (MEM:Coq1_T) ->
 struct
  module MEMO = MEM.MemTy

  module Defs = MEM.Defs

  module Utils =
   struct
    (** val zip : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

    let rec zip a b =
      match a with
      | [] -> []
      | ha :: ta ->
        (match b with
         | [] -> []
         | hb :: tb -> (ha, hb) :: (zip ta tb))

    (** val unzip : ('a1 * 'a2) list -> 'a1 list * 'a2 list **)

    let rec unzip = function
    | [] -> ([], [])
    | p :: t0 ->
      let (ha, hb) = p in let (ta, tb) = unzip t0 in ((ha :: ta), (hb :: tb))

    (** val ssnd : ('a1 * ('a2 * 'a3)) -> 'a3 **)

    let ssnd x =
      snd (snd x)
   end

  module MPref =
   struct
    (** val max_pref_fn__M :
        MEMO.coq_Memo -> MEM.STT.R.Defs.Strings.coq_String ->
        MEM.STT.Ty.coq_State ->
        MEMO.coq_Memo * (MEM.STT.R.Defs.Strings.coq_String * MEM.STT.R.Defs.Strings.coq_String)
        option **)

    let rec max_pref_fn__M oc m s state =
      Printf.fprintf oc "max_pref_fn__M\n";
      match s with
      | [] ->
        if MEM.STT.Ty.accepting state then (m, (Some ([], []))) else (m, None)
      | a :: s' ->
        let state' = MEM.STT.Ty.transition a state in
        let lookup = MEMO.get_Memo oc m (fst state') s' in
        let mpxs =
          match lookup with
          | Some o -> (m, o)
          | None -> max_pref_fn__M oc m s' state'
        in
        let (m', o) = mpxs in
        (match o with
         | Some p0 ->
           let (p, q) = p0 in
           ((MEMO.set_Memo oc m' (fst state) s (Some ((a :: p), q))), (Some
           ((a :: p), q)))
         | None ->
           if MEM.STT.Ty.accepting state'
           then ((MEMO.set_Memo oc m' (fst state) s (Some ((a :: []), s'))),
                  (Some ((a :: []), s')))
           else if MEM.STT.Ty.accepting state
                then ((MEMO.set_Memo oc m' (fst state) s (Some ([], s))), (Some
                       ([], s)))
                else ((MEMO.set_Memo oc m' (fst state) s None), None))

    (** val extract_fsm_for_max__M :
        MEM.STT.R.Defs.Strings.coq_String ->
        (MEMO.coq_Memo * (MEM.STT.Defs.Coredefs.coq_Label * MEM.STT.Ty.coq_State))
        ->
        MEMO.coq_Memo * (MEM.STT.Defs.Coredefs.coq_Label * (MEM.STT.Defs.Coredefs.coq_Prefix * MEM.STT.Defs.Coredefs.coq_Suffix)
        option) **)

    let extract_fsm_for_max__M oc code =
      Printf.fprintf oc "extract__M\n";
      function
        | (m, p) ->
          let (a, fsm) = p in
          (match MEMO.get_Memo oc m (fst fsm) code with
           | Some o -> (m, (a, o))
           | None -> let (m', o) = max_pref_fn__M oc m code fsm in (m', (a, o)))

    (** val max_prefs__M :
        MEMO.coq_Memo list -> MEM.STT.R.Defs.Strings.coq_String ->
        (MEM.STT.Defs.Coredefs.coq_Label * MEM.STT.Ty.coq_State) list ->
        MEMO.coq_Memo
        list * (MEM.STT.Defs.Coredefs.coq_Label * (MEM.STT.Defs.Coredefs.coq_Prefix * MEM.STT.Defs.Coredefs.coq_Suffix)
        option) list **)

    let max_prefs__M oc ms code erules =
      Printf.fprintf oc "max_prefs__M\n";
      let zipped = Utils.zip ms erules in
      let mapped = map (extract_fsm_for_max__M oc code) zipped in
      Utils.unzip mapped

    (** val max_of_prefs__M :
        (MEMO.coq_Memo
        list * (MEM.STT.Defs.Coredefs.coq_Label * (MEM.STT.Defs.Coredefs.coq_Prefix * MEM.STT.Defs.Coredefs.coq_Suffix)
        option) list) -> (MEMO.coq_Memo
        list * MEM.STT.Defs.Coredefs.coq_Label) * (MEM.STT.Defs.Coredefs.coq_Prefix * MEM.STT.Defs.Coredefs.coq_Suffix)
        option **)

    let rec max_of_prefs__M oc =
      Printf.fprintf oc "max_of_prefs__M\n";
      function
    | (ms, prefs) ->
      let (l, o) = Defs.NaiveLexer.MPref.max_of_prefs oc prefs in ((ms, l), o)
   end

  module TypeCheckLemmas =
   struct
    module MemoEq =
     struct
     end

    module Accessible =
     struct
     end

    module Lengths =
     struct
     end

    module LexyClosure =
     struct
     end
   end

  module Lex =
   struct
    (** val lex'__M :
        MEMO.coq_Memo list -> MEM.STT.Defs.Coredefs.sRule list ->
        MEM.STT.R.Defs.Strings.coq_String -> (MEMO.coq_Memo
        list * MEM.STT.Defs.Coredefs.coq_Token
        list) * MEM.STT.R.Defs.Strings.coq_String **)

    let rec lex'__M oc ms rules code =
      Printf.fprintf oc "lex'__M\n";
      let (p, o) = MPref.max_of_prefs__M oc (MPref.max_prefs__M oc ms code rules) in
      let (ms', label) = p in
      (match o with
       | Some p0 ->
         let (p1, suffix) = p0 in
         (match p1 with
          | [] -> ((ms', []), code)
          | ph :: pt ->
            let (p2, rest) = lex'__M oc ms' rules suffix in
            let (ms'', lexemes) = p2 in
            ((ms'', ((label, (ph :: pt)) :: lexemes)), rest))
       | None -> ((ms', []), code))

    (** val init_srule :
        MEM.STT.Defs.Coredefs.coq_Rule -> MEM.STT.Defs.Coredefs.sRule **)

    let init_srule = function
    | (label, re) -> (label, (MEM.STT.Ty.init_state re))

    (** val init_Memos :
        MEM.STT.Defs.Coredefs.sRule list -> MEMO.coq_Memo list **)

    let init_Memos srules =
      map (fun _ -> MEMO.emptyMemo) srules

    (** val lex__Ms' :
        MEM.STT.Defs.Coredefs.coq_Rule list ->
        MEM.STT.R.Defs.Strings.coq_String -> (MEMO.coq_Memo
        list * MEM.STT.Defs.Coredefs.coq_Token
        list) * MEM.STT.R.Defs.Strings.coq_String **)

    let lex__Ms' oc rules code =
      Printf.fprintf oc "lex__Ms'\n";
      let srules = map init_srule rules in
      lex'__M oc (init_Memos srules) srules code

    (** val lex__Ms :
        MEMO.coq_Memo list -> MEM.STT.Defs.Coredefs.coq_Rule list ->
        MEM.STT.R.Defs.Strings.coq_String -> (MEMO.coq_Memo
        list * MEM.STT.Defs.Coredefs.coq_Token
        list) * MEM.STT.R.Defs.Strings.coq_String **)

    let lex__Ms oc ms rules code =
      Printf.fprintf oc "lex__Ms\n";
      let srules = map init_srule rules in lex'__M oc ms srules code

    (** val lex__M :
        MEM.STT.Defs.Coredefs.coq_Rule list ->
        MEM.STT.R.Defs.Strings.coq_String -> MEM.STT.Defs.Coredefs.coq_Token
        list * MEM.STT.R.Defs.Strings.coq_String **)

    let lex__M oc rules code =
      Printf.fprintf oc "lex__M\n";
      let srules = map init_srule rules in
      let (p, rest) = lex'__M oc (init_Memos srules) srules code in
      let (_, ts) = p in (ts, rest)
   end
 end

module FMemo =
 functor (STT:Coq_T) ->
 struct
  module Pointer_as_UOT = UOT_from_UCT(STT.Defs.Pointer_as_UCT)

  module Suffix_as_UOT = List_as_UOT(STT.R.Defs.T_as_UOT)

  module Coq_pair_as_UOT = Pair_as_UOT(Pointer_as_UOT)(Suffix_as_UOT)

  module FM = Coq_Make(Coq_pair_as_UOT)

  module FMF = Coq_Facts(FM)

  let to_string chars =
    let buf = Buffer.create 16 in
    List.iter (Buffer.add_char buf) chars;
    Buffer.contents buf

  type coq_Memo =
    ((STT.Ty.coq_Pointer * STT.R.Defs.Strings.coq_String), (STT.R.Defs.Strings.coq_String * STT.R.Defs.Strings.coq_String) option) Hashtbl.t

  (** val emptyMemo : coq_Memo **)

  let emptyMemo =
    let m = Hashtbl.create 100 in
        Hashtbl.add m (STT.Ty.defPointer, []) (Some ([], []));
        Hashtbl.remove m (STT.Ty.defPointer, []);
        m


  (** val set_Memo :
      coq_Memo -> STT.Ty.coq_Pointer -> STT.R.Defs.Strings.coq_String ->
      (STT.R.Defs.Strings.coq_String * STT.R.Defs.Strings.coq_String) option
      -> (STT.R.Defs.Strings.coq_String * STT.R.Defs.Strings.coq_String)
      option FM.t **)

  let set_Memo oc m pnt sx o =
    Printf.fprintf oc "set_Memo%s\n" (to_string sx);
    Hashtbl.add m (pnt, sx) o; m

  (** val get_Memo :
      coq_Memo -> STT.Ty.coq_Pointer -> STT.R.Defs.Strings.coq_String ->
      (STT.R.Defs.Strings.coq_String * STT.R.Defs.Strings.coq_String) option
      option **)

  let get_Memo oc m pnt sx =
    Printf.fprintf oc "get_Memo... ";
    if Hashtbl.mem m (pnt, sx)
    then
      (Printf.fprintf oc "Hit\n";
      Some (Hashtbl.find m (pnt, sx)))
    else
      (Printf.fprintf oc "Miss -- %s\n" (to_string sx);
      None)
 end

module MEM =
 struct
  module STT =
   struct
    module TabT =
     struct
      module R =
       struct
        module Ty =
         struct
          type coq_Sigma = char

          (** val coq_SigmaEnum : coq_Sigma list **)

          let coq_SigmaEnum =
            asciiEnum

          (** val compareT : char -> char -> comparison **)

          let compareT =
            ascii_order

          (** val coq_Sigma_dec : coq_Sigma -> coq_Sigma -> bool **)

          let coq_Sigma_dec =
            (=)
         end

        module Defs = DefsFn(Ty)
       end

      module TabTy = FTable(R)

      module Defs = Coq0_DefsFn(R)(TabTy)
     end

    module R = TabT.R

    module Ty =
     struct
      module D = DFAFn(TabT)

      type coq_Pointer = R.Defs.Regexes.regex

      (** val defPointer : coq_Pointer **)

      let defPointer =
        R.Defs.Regexes.EmptySet

      type coq_Delta = TabT.TabTy.coq_Table * TabT.R.Defs.Coq_reFS.t

      (** val defDelta : TabT.TabTy.coq_Table * TabT.TabTy.Coq_reFS.t **)

      let defDelta =
        (TabT.TabTy.emptyTable, TabT.TabTy.Coq_reFS.empty)

      type coq_State = coq_Pointer * coq_Delta

      (** val defState :
          coq_Pointer * (TabT.TabTy.coq_Table * TabT.TabTy.Coq_reFS.t) **)

      let defState =
        (defPointer, defDelta)

      (** val transition : R.Ty.coq_Sigma -> coq_State -> coq_State **)

      let transition a = function
      | (x, d) ->
        let (y, z0) = d in
        let (p, z') = D.CoreDefs.coq_DFAtransition a ((x, y), z0) in
        let (x', y') = p in (x', (y', z'))

      (** val transition_list :
          R.Ty.coq_Sigma list -> coq_State -> coq_State **)

      let transition_list bs = function
      | (x, d) ->
        let (y, z0) = d in
        let (p, z') = D.CoreDefs.coq_DFAtransition_list bs ((x, y), z0) in
        let (x', y') = p in (x', (y', z'))

      (** val accepts : R.Defs.Strings.coq_String -> coq_State -> bool **)

      let accepts s = function
      | (x, d) -> let (y, z0) = d in D.CoreDefs.coq_DFAaccepts s ((x, y), z0)

      (** val accepting : coq_State -> bool **)

      let accepting = function
      | (x, d) -> let (y, z0) = d in D.CoreDefs.coq_DFAaccepting ((x, y), z0)

      (** val init_state : R.Defs.Regexes.regex -> coq_State **)

      let init_state r =
        let (p, z0) = D.CoreDefs.regex2dfa r in let (x, y) = p in (x, (y, z0))

      (** val init_state_inv : coq_State -> R.Defs.Regexes.regex **)

      let init_state_inv = function
      | (x, d) -> let (y, z0) = d in D.CoreDefs.dfa2regex ((x, y), z0)

      (** val pointer_compare : coq_Pointer -> coq_Pointer -> comparison **)

      let pointer_compare =
        R.Defs.Regexes.re_compare
     end

    module Defs = Coq_DefsFn(R)(Ty)
   end

  module MemTy = FMemo(STT)

  module Defs = MemoDefsFn(STT)(MemTy)
 end

module L = Coq_ImplFn(MEM)

(** val toS : char list -> MEM.STT.R.Defs.Strings.coq_String **)

let toS =
  list_ascii_of_string

(** val range' : nat -> nat list **)

let rec range' = function
| O -> []
| S n' -> app (range' n') (n' :: [])

(** val range : nat -> nat -> nat list **)

let rec range n1 n2 =
  map (add n1) (range' (add (sub n2 n1) (S O)))

(** val chars_ws : MEM.STT.R.Defs.Regexes.regex list **)

let chars_ws =
  map (fun x -> MEM.STT.R.Defs.Regexes.Char x)
    (map ascii_of_nat ((S (S (S (S (S (S (S (S (S O))))))))) :: ((S (S (S (S
      (S (S (S (S (S (S O)))))))))) :: ((S (S (S (S (S (S (S (S (S (S (S (S
      (S O))))))))))))) :: ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))) :: [])))))

(** val ru_ws : MEM.STT.Defs.Coredefs.coq_Rule **)

let ru_ws =
  ((toS ('W'::('S'::[]))),
    (MEM.STT.R.Defs.Helpers.coq_Plus
      (MEM.STT.R.Defs.Helpers.coq_IterUnion chars_ws)))

(** val ascii_digit : nat list **)

let ascii_digit =
  range (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S O)))))))))))))))))))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val chars_digit : MEM.STT.R.Defs.Regexes.regex list **)

let chars_digit =
  map (fun x -> MEM.STT.R.Defs.Regexes.Char x) (map ascii_of_nat ascii_digit)

(** val regex_digit : MEM.STT.R.Defs.Regexes.regex **)

let regex_digit =
  MEM.STT.R.Defs.Helpers.coq_IterUnion chars_digit

(** val ascii_nz_digit : nat list **)

let ascii_nz_digit =
  range (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S O))))))))))))))))))))))))))))))))))))))))))))))))) (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val chars_nz_digit : MEM.STT.R.Defs.Regexes.regex list **)

let chars_nz_digit =
  map (fun x -> MEM.STT.R.Defs.Regexes.Char x)
    (map ascii_of_nat ascii_nz_digit)

(** val regex_nz_digit : MEM.STT.R.Defs.Regexes.regex **)

let regex_nz_digit =
  MEM.STT.R.Defs.Helpers.coq_IterUnion chars_nz_digit

(** val regex_zero : MEM.STT.R.Defs.Regexes.regex **)

let regex_zero =
  MEM.STT.R.Defs.Regexes.Char
    (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))

(** val regex_nzero : MEM.STT.R.Defs.Regexes.regex **)

let regex_nzero =
  MEM.STT.R.Defs.Regexes.App (regex_nz_digit, (MEM.STT.R.Defs.Regexes.Star
    regex_digit))

(** val regex_int : MEM.STT.R.Defs.Regexes.regex **)

let regex_int =
  MEM.STT.R.Defs.Regexes.Union (regex_zero, regex_nzero)

(** val regex_sign : MEM.STT.R.Defs.Regexes.regex **)

let regex_sign =
  MEM.STT.R.Defs.Regexes.Char
    (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S O))))))))))))))))))))))))))))))))))))))))))))))

(** val regex_sign_option : MEM.STT.R.Defs.Regexes.regex **)

let regex_sign_option =
  MEM.STT.R.Defs.Helpers.coq_Optional regex_sign

(** val regex_dec_point : MEM.STT.R.Defs.Regexes.regex **)

let regex_dec_point =
  MEM.STT.R.Defs.Regexes.Char
    (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S O)))))))))))))))))))))))))))))))))))))))))))))))

(** val regex_dec0 : MEM.STT.R.Defs.Regexes.regex **)

let regex_dec0 =
  MEM.STT.R.Defs.Regexes.App (regex_dec_point,
    (MEM.STT.R.Defs.Helpers.coq_Plus regex_digit))

(** val regex_dec_option : MEM.STT.R.Defs.Regexes.regex **)

let regex_dec_option =
  MEM.STT.R.Defs.Helpers.coq_Optional regex_dec0

(** val regex_Ee : MEM.STT.R.Defs.Regexes.regex **)

let regex_Ee =
  MEM.STT.R.Defs.Regexes.Union ((MEM.STT.R.Defs.Regexes.Char
    (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (MEM.STT.R.Defs.Regexes.Char
    (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val regex_pm : MEM.STT.R.Defs.Regexes.regex **)

let regex_pm =
  MEM.STT.R.Defs.Regexes.Union ((MEM.STT.R.Defs.Regexes.Char
    (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))),
    (MEM.STT.R.Defs.Regexes.Char
    (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S O))))))))))))))))))))))))))))))))))))))))))))))))

(** val regex_pm_option : MEM.STT.R.Defs.Regexes.regex **)

let regex_pm_option =
  MEM.STT.R.Defs.Helpers.coq_Optional regex_pm

(** val regex_exp : MEM.STT.R.Defs.Regexes.regex **)

let regex_exp =
  MEM.STT.R.Defs.Helpers.coq_IterApp
    (regex_Ee :: (regex_pm_option :: (regex_int :: [])))

(** val regex_exp_option : MEM.STT.R.Defs.Regexes.regex **)

let regex_exp_option =
  MEM.STT.R.Defs.Helpers.coq_Optional regex_exp

(** val regex_number : MEM.STT.R.Defs.Regexes.regex **)

let regex_number =
  MEM.STT.R.Defs.Helpers.coq_IterApp
    (regex_sign_option :: (regex_int :: (regex_dec_option :: (regex_exp_option :: []))))

(** val ru_number :
    MEM.STT.R.Defs.Strings.coq_String * MEM.STT.R.Defs.Regexes.regex **)

let ru_number =
  ((toS ('N'::('U'::('M'::('B'::('E'::('R'::[]))))))), regex_number)

(** val ascii_lower : nat list **)

let ascii_lower =
  range (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val chars_lower : MEM.STT.R.Defs.Regexes.regex list **)

let chars_lower =
  map (fun x -> MEM.STT.R.Defs.Regexes.Char x) (map ascii_of_nat ascii_lower)

(** val regex_lower : MEM.STT.R.Defs.Regexes.regex **)

let regex_lower =
  MEM.STT.R.Defs.Helpers.coq_IterUnion chars_lower

(** val ascii_upper : nat list **)

let ascii_upper =
  range (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val chars_upper : MEM.STT.R.Defs.Regexes.regex list **)

let chars_upper =
  map (fun x -> MEM.STT.R.Defs.Regexes.Char x) (map ascii_of_nat ascii_upper)

(** val regex_upper : MEM.STT.R.Defs.Regexes.regex **)

let regex_upper =
  MEM.STT.R.Defs.Helpers.coq_IterUnion chars_upper

(** val ascii_punc : nat list **)

let ascii_punc =
  app ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) :: ((S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O))))))))))))))))))))))))))))))))) :: []))
    (app
      (range (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))
      (app
        (range (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        (app
          (range (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (range (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val chars_punc : MEM.STT.R.Defs.Regexes.regex list **)

let chars_punc =
  map (fun x -> MEM.STT.R.Defs.Regexes.Char x) (map ascii_of_nat ascii_punc)

(** val regex_punc : MEM.STT.R.Defs.Regexes.regex **)

let regex_punc =
  MEM.STT.R.Defs.Helpers.coq_IterUnion chars_punc

(** val regex_char : MEM.STT.R.Defs.Regexes.regex **)

let regex_char =
  MEM.STT.R.Defs.Helpers.coq_IterUnion
    (regex_lower :: (regex_upper :: (regex_digit :: (regex_punc :: []))))

(** val regex_par : MEM.STT.R.Defs.Regexes.regex **)

let regex_par =
  MEM.STT.R.Defs.Regexes.Char
    (ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))

(** val regex_string : MEM.STT.R.Defs.Regexes.regex **)

let regex_string =
  MEM.STT.R.Defs.Helpers.coq_IterApp
    (regex_par :: ((MEM.STT.R.Defs.Regexes.Star
    regex_char) :: (regex_par :: [])))

(** val ru_string :
    MEM.STT.R.Defs.Strings.coq_String * MEM.STT.R.Defs.Regexes.regex **)

let ru_string =
  ((toS ('S'::('T'::('R'::('I'::('N'::('G'::[]))))))), regex_string)

(** val regex_true : MEM.STT.R.Defs.Regexes.regex **)

let regex_true =
  MEM.STT.R.Defs.Helpers.coq_IterApp
    (map (fun x -> MEM.STT.R.Defs.Regexes.Char x)
      (toS ('t'::('r'::('u'::('e'::[]))))))

(** val ru_true :
    MEM.STT.R.Defs.Strings.coq_String * MEM.STT.R.Defs.Regexes.regex **)

let ru_true =
  ((toS ('T'::('R'::('U'::('E'::[]))))), regex_true)

(** val regex_false : MEM.STT.R.Defs.Regexes.regex **)

let regex_false =
  MEM.STT.R.Defs.Helpers.coq_IterApp
    (map (fun x -> MEM.STT.R.Defs.Regexes.Char x)
      (toS ('f'::('a'::('l'::('s'::('e'::[])))))))

(** val ru_false :
    MEM.STT.R.Defs.Strings.coq_String * MEM.STT.R.Defs.Regexes.regex **)

let ru_false =
  ((toS ('F'::('A'::('L'::('S'::('E'::[])))))), regex_false)

(** val regex_null : MEM.STT.R.Defs.Regexes.regex **)

let regex_null =
  MEM.STT.R.Defs.Helpers.coq_IterApp
    (map (fun x -> MEM.STT.R.Defs.Regexes.Char x)
      (toS ('n'::('u'::('l'::('l'::[]))))))

(** val ru_null :
    MEM.STT.R.Defs.Strings.coq_String * MEM.STT.R.Defs.Regexes.regex **)

let ru_null =
  ((toS ('N'::('U'::('L'::('L'::[]))))), regex_null)

(** val regex_colon : MEM.STT.R.Defs.Regexes.regex **)

let regex_colon =
  MEM.STT.R.Defs.Helpers.coq_IterApp
    (map (fun x -> MEM.STT.R.Defs.Regexes.Char x) (toS (':'::[])))

(** val ru_colon :
    MEM.STT.R.Defs.Strings.coq_String * MEM.STT.R.Defs.Regexes.regex **)

let ru_colon =
  ((toS ('C'::('O'::('L'::('O'::('N'::[])))))), regex_colon)

(** val regex_comma : MEM.STT.R.Defs.Regexes.regex **)

let regex_comma =
  MEM.STT.R.Defs.Helpers.coq_IterApp
    (map (fun x -> MEM.STT.R.Defs.Regexes.Char x) (toS (','::[])))

(** val ru_comma :
    MEM.STT.R.Defs.Strings.coq_String * MEM.STT.R.Defs.Regexes.regex **)

let ru_comma =
  ((toS ('C'::('O'::('M'::('M'::('A'::[])))))), regex_comma)

(** val regex_lbrack : MEM.STT.R.Defs.Regexes.regex **)

let regex_lbrack =
  MEM.STT.R.Defs.Helpers.coq_IterApp
    (map (fun x -> MEM.STT.R.Defs.Regexes.Char x) (toS ('['::[])))

(** val ru_lbrack :
    MEM.STT.R.Defs.Strings.coq_String * MEM.STT.R.Defs.Regexes.regex **)

let ru_lbrack =
  ((toS
     ('L'::('E'::('F'::('T'::('_'::('B'::('R'::('A'::('C'::('K'::('E'::('T'::[]))))))))))))),
    regex_lbrack)

(** val regex_rbrack : MEM.STT.R.Defs.Regexes.regex **)

let regex_rbrack =
  MEM.STT.R.Defs.Helpers.coq_IterApp
    (map (fun x -> MEM.STT.R.Defs.Regexes.Char x) (toS (']'::[])))

(** val ru_rbrack :
    MEM.STT.R.Defs.Strings.coq_String * MEM.STT.R.Defs.Regexes.regex **)

let ru_rbrack =
  ((toS
     ('R'::('I'::('G'::('H'::('T'::('_'::('B'::('R'::('A'::('C'::('K'::('E'::('T'::[])))))))))))))),
    regex_rbrack)

(** val regex_lbrace : MEM.STT.R.Defs.Regexes.regex **)

let regex_lbrace =
  MEM.STT.R.Defs.Helpers.coq_IterApp
    (map (fun x -> MEM.STT.R.Defs.Regexes.Char x) (toS ('{'::[])))

(** val ru_lbrace :
    MEM.STT.R.Defs.Strings.coq_String * MEM.STT.R.Defs.Regexes.regex **)

let ru_lbrace =
  ((toS
     ('L'::('E'::('F'::('T'::('_'::('B'::('R'::('A'::('C'::('E'::[]))))))))))),
    regex_lbrace)

(** val regex_rbrace : MEM.STT.R.Defs.Regexes.regex **)

let regex_rbrace =
  MEM.STT.R.Defs.Helpers.coq_IterApp
    (map (fun x -> MEM.STT.R.Defs.Regexes.Char x) (toS ('}'::[])))

(** val ru_rbrace :
    MEM.STT.R.Defs.Strings.coq_String * MEM.STT.R.Defs.Regexes.regex **)

let ru_rbrace =
  ((toS
     ('R'::('I'::('G'::('H'::('T'::('_'::('B'::('R'::('A'::('C'::('E'::[])))))))))))),
    regex_rbrace)

(** val rus : MEM.STT.Defs.Coredefs.coq_Rule list **)

let rus =
  ru_ws :: (ru_number :: (ru_string :: (ru_true :: (ru_false :: (ru_null :: (ru_colon :: (ru_comma :: (ru_lbrack :: (ru_rbrack :: (ru_lbrace :: (ru_rbrace :: [])))))))))))

(** val lex0 :
    MEM.STT.Defs.Coredefs.coq_Rule list -> MEM.STT.R.Defs.Strings.coq_String
    -> MEM.STT.Defs.Coredefs.coq_Token
    list * MEM.STT.R.Defs.Strings.coq_String **)

let lex0 =
  L.Lex.lex__M
