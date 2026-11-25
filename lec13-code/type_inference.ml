(* Implementation of pl-book.pdf, pp. 242--244, and Lectures 11--12.
   The slides include the marked sections directly from this file. *)

(* aststart *)
type exp =
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | ISZERO of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string
(* astend *)

(* typesstart *)
type typ =
  | TyInt
  | TyBool
  | TyFun of typ * typ
  | TyVar of tyvar
and tyvar = string
(* typesend *)

exception Type_error of string

(* freshstart *)
let tyvar_num = ref 0

let fresh_tyvar : unit -> typ
= fun () ->
  tyvar_num := !tyvar_num + 1;
  TyVar ("t" ^ string_of_int !tyvar_num)
(* freshend *)

(* tenvstart *)
module TypeEnv = struct
  type t = (var * typ) list
  let empty = []
  let extend : var * typ -> t -> t
  = fun binding tenv -> binding :: tenv

  let find : var -> t -> typ
  = fun x tenv ->
    try List.assoc x tenv
    with Not_found -> raise (Type_error ("unbound variable: " ^ x))
end
(* tenvend *)

(* substapplystart *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty : t = []
  let find : tyvar -> t -> typ
  = fun x subst ->
    List.assoc x subst

  let rec apply : typ -> t -> typ
  = fun ty subst ->
    match ty with
    | TyInt -> TyInt
    | TyBool -> TyBool
    | TyFun (t1, t2) ->
        TyFun (apply t1 subst, apply t2 subst)
    | TyVar x ->
        try find x subst with Not_found -> ty
(* substapplyend *)

  (* The solver supplies ty after applying the current substitution.
     Propagating each new binding keeps the substitution normalized:
     applying it a second time does not change the result. *)
  (* substextendstart *)
  let extend : tyvar -> typ -> t -> t
  = fun tv ty subst ->
    (tv, ty) ::
    List.map
      (fun (x, t) -> (x, apply t [(tv, ty)]))
      subst
(* substextendend *)
end
(* substmoduleend *)

(* eqntypestart *)
type typ_eqn = (typ * typ) list
(* eqntypeend *)

(* genstart *)
let rec gen_eqs : TypeEnv.t -> exp -> typ -> typ_eqn
= fun tenv e ty ->
  match e with
  | CONST _ -> [(ty, TyInt)]
  | VAR x -> [(ty, TypeEnv.find x tenv)]
  | ADD (e1, e2) | SUB (e1, e2) ->
    let eqs1 = gen_eqs tenv e1 TyInt in
    let eqs2 = gen_eqs tenv e2 TyInt in
    (ty, TyInt) :: (eqs1 @ eqs2)
  | ISZERO e -> (ty, TyBool) :: gen_eqs tenv e TyInt
(* genend *)
(* gencontrolstart *)
  | IF (e1, e2, e3) ->
    let eqs1 = gen_eqs tenv e1 TyBool in
    let eqs2 = gen_eqs tenv e2 ty in
    let eqs3 = gen_eqs tenv e3 ty in
    eqs1 @ eqs2 @ eqs3
  | LET (x, e1, e2) ->
    let a = fresh_tyvar () in
    let eqs1 = gen_eqs tenv e1 a in
    let eqs2 =
      gen_eqs (TypeEnv.extend (x, a) tenv) e2 ty in
    eqs1 @ eqs2
(* gencontrolend *)
(* genprocstart *)
  | PROC (x, e) ->
    let a = fresh_tyvar () in
    let b = fresh_tyvar () in
    (ty, TyFun (a, b)) ::
      gen_eqs (TypeEnv.extend (x, a) tenv) e b
  | CALL (e1, e2) ->
    let a = fresh_tyvar () in
    let eqs1 = gen_eqs tenv e1 (TyFun (a, ty)) in
    let eqs2 = gen_eqs tenv e2 a in
    eqs1 @ eqs2
(* genprocend *)

(* occursstart *)
let rec occurs : tyvar -> typ -> bool
= fun a ty ->
  match ty with
  | TyInt | TyBool -> false
  | TyVar b -> a = b
  | TyFun (t1, t2) -> occurs a t1 || occurs a t2
(* occursend *)

(* As in Lecture 12, unify receives types to which subst has already
   been applied. solve and the function-type case maintain this condition. *)
(* unifystart *)
let rec unify : typ -> typ -> Subst.t -> Subst.t
= fun t1 t2 subst ->
  match t1, t2 with
  | TyInt, TyInt | TyBool, TyBool -> subst
  | TyVar a, TyVar b when a = b -> subst
  | TyVar a, t ->
    if occurs a t then
      raise (Type_error "occurs check failed")
    else Subst.extend a t subst
  | t, TyVar a -> unify (TyVar a) t subst
  | TyFun (a1, b1), TyFun (a2, b2) ->
    let subst' = unify a1 a2 subst in
    unify (Subst.apply b1 subst')
          (Subst.apply b2 subst') subst'
  | _ -> raise (Type_error "type mismatch")
(* unifyend *)

(* unifyallstart *)
let rec unifyall : typ_eqn -> Subst.t -> Subst.t
= fun eqs subst ->
  match eqs with
  | [] -> subst
  | (t1, t2) :: rest ->
    let subst' =
      unify (Subst.apply t1 subst)
            (Subst.apply t2 subst) subst in
    unifyall rest subst'
(* unifyallend *)

(* solvestart *)
let solve : typ_eqn -> Subst.t
= fun eqs -> unifyall eqs Subst.empty
(* solveend *)

(* inferstart *)
let typeof : exp -> typ
= fun exp ->
  let new_tv = fresh_tyvar () in
  let eqs = gen_eqs TypeEnv.empty exp new_tv in
  let subst = solve eqs in
  Subst.apply new_tv subst
(* inferend *)

(* Formatting is only for the examples and test output. *)
let rec string_of_typ : typ -> string
= fun ty ->
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyVar a -> a
  | TyFun (t1, t2) ->
    let argument =
      match t1 with
      | TyFun _ -> "(" ^ string_of_typ t1 ^ ")"
      | _ -> string_of_typ t1
    in
    argument ^ " -> " ^ string_of_typ t2
