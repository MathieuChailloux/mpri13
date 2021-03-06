open Positions
open Name
open XAST
open Types
open ElaborationExceptions

type t = {
  values       : (tnames * binding) list;
  types        : (tname * (Types.kind * type_definition)) list;
  classes      : (tname * class_definition) list;
  labels       : (lname * (tnames * Types.t * tname)) list;
  instances    : ((tname * tname) * instance_definition) list;
}

let empty = { values = []; types = []; classes = []; labels = []; instances = []; }

let values env = env.values

let lookup pos x env =
  try
    List.find (fun (_, (x', _)) -> x = x') env.values
  with Not_found -> raise (UnboundIdentifier (pos, x))

let bind_scheme x ts ty env =
  { env with values = (ts, (x, ty)) :: env.values }

let bind_simple x ty env =
  bind_scheme x [] ty env

let bind_type t kind tdef env =
  { env with types = (t, (kind, tdef)) :: env.types }

let lookup_type pos t env =
  try
    List.assoc t env.types
  with Not_found ->
    raise (UnboundTypeVariable (pos, t))

let lookup_type_kind pos t env =
  fst (lookup_type pos t env)
    
let lookup_type_definition pos t env =
  snd (lookup_type pos t env)

let lookup_class pos k env =
  try
    List.assoc k env.classes
  with Not_found -> raise (UnboundClass (pos, k))

let bind_class k c env =
  try
    let pos = c.class_position in
    ignore (lookup_class pos k env);
    raise (AlreadyDefinedClass (pos, k))
  with UnboundClass _ ->
    { env with classes = (k, c) :: env.classes }

let lookup_instance pos (k, idx) env =
  try 
    List.assoc (k, idx) env.instances
  with 
    | Not_found -> raise (UnboundInstance (pos, (k, idx)))

let bind_instance env = 
  function { instance_position = pos
	   ; instance_index = idx
	   ; instance_class_name = name
	   ; _ } as i ->
  try
    ignore (lookup_instance pos (name, idx) env);
    raise (AlreadyDefinedInstance (pos, (name, idx)))
  with UnboundInstance _ ->
    { env with instances = ((name, idx), i) :: env.instances }

let lookup_superclasses pos k env =
  (lookup_class pos k env).superclasses

let is_superclass pos k1 k2 env =
  let rec loop k2 = 
    k1 = k2 || 
    List.exists loop (lookup_superclasses pos k2 env)
  in
  k1 <> k2 && loop k2

let bind_type_variable t env =
  bind_type t KStar (TypeDef (undefined_position, KStar, t, DAlgebraic [])) env

let labels_of rtcon env =
  let p (_, (_, _, rtcon')) = rtcon = rtcon' in
  List.(fst (split (filter p env.labels)))

let lookup_label pos l env =
  try
    List.assoc l env.labels
  with Not_found ->
    raise (UnboundLabel (pos, l))

let bind_label pos l ts ty rtcon env =
  try
    ignore (lookup_label pos l env);
    raise (LabelAlreadyTaken (pos, l))
  with UnboundLabel _ ->
    { env with labels = (l, (ts, ty, rtcon)) :: env.labels }

let initial =
  let primitive_type t k = TypeDef (undefined_position, k, t, DAlgebraic []) in
  List.fold_left (fun env (t, k) ->
    bind_type t k (primitive_type t k) env
  ) empty [
    (TName "->", KArrow (KStar, KArrow (KStar, KStar)));
    (TName "int", KStar);
    (TName "char", KStar);
    (TName "unit", KStar)
  ]

let get_classes env = List.map snd env.classes
