open Positions
open Name

type kind =
  | KStar
  | KArrow of kind * kind

type t =
  | TyVar   of position * tname
  | TyApp   of position * tname * t list

type scheme = TyScheme of tname list * class_predicates * t

and class_predicate = ClassPredicate of tname * tname

and class_predicates = class_predicate list

let tyarrow pos ity oty =
  TyApp (pos, TName "->", [ity; oty])

let ntyarrow pos itys oty =
  List.fold_left (fun oty ity -> tyarrow pos ity oty) oty (List.rev itys)

let destruct_tyarrow = function
  | (TyApp (_, TName "->", [ity; oty])) ->
    Some (ity, oty)
  | ty -> None

let rec destruct_ntyarrow ty =
  match destruct_tyarrow ty with
    | None -> ([], ty)
    | Some (i, o) -> let (is, o) = destruct_ntyarrow o in (i :: is, o)

type instantiation_kind =
  | TypeApplication of t list
  | LeftImplicit

module type TypingSyntax = sig
  type binding

  val binding
    : Lexing.position -> name -> t option -> binding

  val destruct_binding
    : binding -> name * t option

  type instantiation

  val instantiation
    : Lexing.position -> instantiation_kind -> instantiation

  val destruct_instantiation_as_type_applications
    : instantiation -> t list option

  val implicit : bool

end

module ImplicitTyping =
struct
  type binding = Name.name * t option

  let binding _ x ty : binding = (x, ty)

  let destruct_binding b = b

  type instantiation = t option

  let instantiation pos = function
    | TypeApplication _ ->
      Errors.fatal [pos] "No type application while being implicit."
    | LeftImplicit ->
      None

  let destruct_instantiation_as_type_applications _ = None

  let implicit = true

end

module ExplicitTyping =
struct
  type binding = Name.name * t

  let binding pos x = function
    | None -> Errors.fatal [pos] "An explicit type annotation is required."
    | Some ty -> (x, ty)

  let destruct_binding (x, ty) = (x, Some ty)

  type instantiation = t list

  let instantiation pos = function
    | LeftImplicit ->
      Errors.fatal [pos] "An explicit type application is required."
    | TypeApplication i -> i

  let destruct_instantiation_as_type_applications i = Some i

  let implicit = false
end

let rec kind_of_arity = function
  | 0 -> KStar
  | n -> KArrow (KStar, kind_of_arity (pred n))

let my_print_type t =
  let rec loop = function
    | TyVar (_, TName name) ->
      Format.printf "TyVar %s, " name
    | TyApp (_, TName name, tys) ->
      Format.printf "TyApp (%s, " name;
      List.iter loop tys; Format.printf "),"
  in
  loop t; Format.printf "\n"

let rec my_clean_type = function
  | TyApp (pos, tname, []) -> TyVar (pos, tname)
  | TyApp (pos, tname, tys) ->
    TyApp (pos, tname, List.map my_clean_type tys)
  | t -> t

let rec equivalent ty1 ty2 =
  (*Format.printf "equivalent t1 t2\n";
  my_print_type ty1; my_print_type ty2;*)
  match ty1, ty2 with
    | TyVar (_, t), TyVar (_, t') ->
      t = t'
    | TyApp (_, t, tys), TyApp (_, t', tys') ->
      t = t' && List.for_all2 equivalent tys tys'
    (*| TyVar (_, t), TyApp (_, t', []) -> t = t'
    | TyApp (_, t, []), TyVar (_, t') -> t = t'*)
    | _, _ ->
      false

let rec substitute (s : (tname * t) list) = function
  | TyVar (p, v) ->
    (try List.assoc v s with Not_found -> TyVar (p, v))

  | TyApp (pos, t, tys) ->
    TyApp (pos, t, List.map (substitute s) tys)
