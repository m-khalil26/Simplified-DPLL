(** Type des formules. *)

type formule =
  | Bot
  | Top
  | Atome of string
  | Imp of (formule * formule)
  | Ou of (formule * formule)
  | Et of (formule * formule)
  | Non of formule

(** Fonction de construction d'atome. *)
let atome x = Atome x

(* ----------------- Représentation en chaîne de caractères ----------------- *)

(** Conversion d'une formule en chaîne de caractères. *)
let rec string_of_formule (fr : formule) : string =
  match fr with
  | Bot -> "⊥"
  | Top ->  "T"
  | Atome (s) -> s
  | Imp(fr',fr'') -> string_of_formule(fr')^"->"^ string_of_formule(fr'');
  | Ou(fr',fr'') -> "("^string_of_formule(fr')^ " Ou " ^ string_of_formule(fr'')^")";
  | Et(fr',fr'') -> string_of_formule(fr')^ " Et " ^ string_of_formule(fr'');
  | Non(fr) -> "Non "^string_of_formule(fr)

(* ----------------- Opérateurs de simplification ----------------- *)

(** Opérateur disjonction, associatif à gauche. *)
let ( + ) (f' : formule) (f'' : formule) : formule =
  match (f', f'') with
  | Bot, _ -> f''
  | _, Bot -> f'
  | Top, _ | _, Top -> Top
  | _ -> Ou (f', f'')

(** Opérateur de conjonction, associatif à gauche. *)
let ( * ) (f' : formule) (f'' : formule) : formule =
   match(f',f'') with
    |Top,_ -> f''
    |_,Top -> f'
    |_-> Et(f',f'');;

(** Opérateur d'implication, associatif à droite. *)
let ( ^-> ) (f' : formule) (f'' : formule) : formule =
  match f',f'' with 
  |Top,_ ->  f''
  |_,Bot -> Non f'
  |Bot,_|_,Top -> Top 
  |_ -> Imp( f',f'')

(** Opérateur de négation. *)
let ( ~~ ) (f: formule) : formule = if f = Top then Bot else if f = Bot then Top else Non f;;

(* ----------------- Lecture depuis un fichier ----------------- *)

(** Transforme une chaine +at en Atome at et -at en Non (Atome at). *)
let string_to_lit (str : string) : formule =
  let len = String.length(str) -1 in
  let subStr = (String.sub str 1 len )
  in
  match (String.get str 0) with
    |'+' -> Atome(subStr)
    |'-' -> Non(Atome(subStr))
    |_ -> failwith " erreur" ;;



(** Transforme une chaine contenant des éléments de la forme
    +at ou -at séparés par des espaces ou tabulations en une disjonction des
    formules obtenues en appliquant string_to_lit sur chaque élément. *)
let string_to_disj (str : string) : formule =
  let splitStr = (String.split_on_char ' ' str)
      in
      let rec aux splitStr =
        match splitStr with
         |[] -> Bot
         | t::q ->( + ) (aux q) (string_to_lit t )
      in aux splitStr;;

(** Transforme un fichier texte dont le nom est donné en paramètre et dont chaque ligne est une chaine
    contenant des éléments de la forme
    +at ou -at séparés par des espaces ou tabulations en la conjonction des formules obtenues
    en appliquant string_to_disj sur chaque ligne. *)
let from_file (file : string) : formule =
  let strArray = Array.to_list (Arg.read_arg file) in
  let rec aux strArray fr =
    match strArray with
    |[] -> fr
    |t::q -> aux q (( * )(string_to_disj t) fr)
   in aux  strArray Top;;

 
