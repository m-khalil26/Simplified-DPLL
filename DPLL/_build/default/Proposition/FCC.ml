open Formule


(*-----------------------------------------CONSTRUCTION MODULES --------------------------------------------*)


(** Signe d'un littéral. *)
type signe = Plus | Moins

type litteral = signe * string
(** Type d'un littéral : produit d'un signe et d'un atome (string). *)

(** Le module Clause permet de manipuler les ensembles
    de littéraux. Il est généré via le foncteur Set.Make. *)
module Clause = Set.Make (struct
  type t = litteral

  let compare = Stdlib.compare
end)

type clause = Clause.t
(** Type synonyme : une clause est un ensemble de littéraux. *)

(** Le module FormeClausale permet de manipuler les ensembles
    de clauses. Il est généré via le foncteur Set.Make. *)

(** fonction permettant de définir l'ordre d'une forme clausale *)
let forme_clausale_ordre c c' =
  let card1 = (Clause.cardinal c)
  and card2 = (Clause.cardinal c')
  in
  match card1,card2 with
    |card1,card2 when card1>card2 -> 1
    |card1,card2 when card1<card2 -> -1
    |_->
      match c,c' with
      |c,c' when c>c' -> 1
      |c,c' when c<c' -> -1
      |_ -> 0;;
;;


module FormeClausale = Set.Make (struct
  type t = clause

  let compare = forme_clausale_ordre
end)

type forme_clausale = FormeClausale.t
(** Type synonyme : une forme clausale est un ensemble de clauses. *)


(*-----------------------------------------STRING_OF_FCC --------------------------------------------*)


(** Transforme une forme clausale en string. *)

(** renvoie un string à partir d'un signe *)
let string_of_signe  (s :signe ) : string =
  match s with
  | Plus -> "Plus"
  | Moins -> "Moins";;

(** renvoie un string à partir d'un litteral *)
let string_of_literal (lit : litteral ) : string =
  match lit with
    |signe,string -> string_of_signe signe  ^" "^ string;;

(** renvoie un string à partir d'une clause *)
let string_of_clause (c : clause ) : string =
("{ "^(String.concat "," (List.map string_of_literal (Clause.elements c))))^" }"

let string_of_fcc (fcc : forme_clausale) : string =
 ("{ "^( String.concat "," (List.map string_of_clause (FormeClausale.elements fcc))))^ " }";;



(*-----------------------------------------MISE EN FCC --------------------------------------------*)



(** Mise en FCC, étape 1 : Transforme une formule en une formule équivalente avec des opérateurs
    de conjonction, de disjonction, de négation, Bot et Top uniquement. *)
let rec retrait_operateurs (fr : formule) : formule =
  match fr with
  |Top |Bot | Atome _ |Non _ -> fr
  |Et(fr',fr'') ->  Et(retrait_operateurs fr' ,retrait_operateurs fr'')
  |Ou(fr',fr'') -> Ou(retrait_operateurs fr' , retrait_operateurs fr'')
  |Imp(fr', fr'' ) -> Ou( retrait_operateurs (Non fr'), retrait_operateurs fr'')
;;

(** Mise en FCC, étape 2 : Descend les négations dans une formule au plus profond de l'arbre syntaxique,
    en préservant les évaluations. *)

let rec descente_non (fr : formule) : formule =
  match fr with
    |Top|Bot|Atome _ | Non Atome _ -> fr
    |Ou (f, g) -> Ou (descente_non f, descente_non g)
    |Et (f, g) -> Et (descente_non f, descente_non g)
    |Non Top -> Bot
    |Non Bot -> Top
    |Non (Et(fr',fr'' )) -> Ou( descente_non (Non fr') ,  descente_non (Non fr''))
    |Non (Ou(fr',fr'' )) -> Et( descente_non (Non fr') ,  descente_non (Non fr''))
    |Non fr -> (descente_non fr)
    |_ -> failwith "Pas censé arrivé ici";;

(** Mise en FCC, étape 3 : calcule la forme clausale associée à une formule. *)

let fcc_conj = FormeClausale.union

(** Calcule la disjonction de deux formes clausales. *)
let fcc_disj fcc1 fcc2 =
  FormeClausale.fold
    (fun c acc ->
      FormeClausale.fold
        (fun c' acc' -> FormeClausale.add (Clause.union c c') acc')
        fcc2 acc)
    fcc1 FormeClausale.empty

(** Mise en FCC, étape 3 : calcule la forme clausale associée à une formule. *)
let rec formule_to_fcc (fr  : formule) : forme_clausale =
  match fr with
  | Top -> FormeClausale.empty
  | Bot -> FormeClausale.singleton Clause.empty
  | Non (Atome s) -> FormeClausale.singleton (Clause.singleton (Moins, s))
  | Atome s -> FormeClausale.singleton (Clause.singleton (Plus, s))
  | Et (f', f'') -> fcc_conj (formule_to_fcc f') (formule_to_fcc f'')
  | Ou (f', f'') -> fcc_disj (formule_to_fcc f') (formule_to_fcc f'')
  | _ -> failwith ""


(** Convertit une formule en une forme clausale conjonctive équivalente.*)

let formule_to_fcc f = formule_to_fcc (descente_non (retrait_operateurs f))

(*-----------------------------------------FROM_FILE --------------------------------------------*)

(** Transforme une chaine +at en (Plus, at) et -at en (Moins, at) *)
let string_to_lit (str : string) : litteral =
  let signe = String.get str 0
  and  subStr = (String.sub str 1 ((String.length str)-1) )
      in
      match signe with
      |'+' -> (Plus, subStr)
      |'-' -> (Moins, subStr)
      |_ -> failwith "Erreur de syntax ";;


(** Transforme une chaine contenant des éléments de la forme
    +at ou -at séparés par des espaces ou tabulations en une clause contenant
    les littéraux obtenus en appliquant string_to_lit sur chaque élément *)

let string_to_disj (str : string) : clause =
   let splitStr = (String.split_on_char ' ' str)
   in
   let rec aux splitStr clause =
    match splitStr with
      |[] -> clause
      | t::q -> aux q (Clause.add (string_to_lit t) clause  )
  in aux splitStr Clause.empty ;;

(** Transforme un fichier texte dont le nom est donné en paramètre et dont chaque ligne est une chaine
contenant des éléments de la forme
+at ou -at séparés par des espaces ou tabulations en la FCC contenant les clauses obtenues
en appliquant string_to_disj sur chaque ligne *)


let from_file (file : string) : forme_clausale =
  let strArray = Array.to_list (Arg.read_arg file) in
  let rec aux strArray fcc =
    match strArray with
    |[] -> fcc
    |t::q -> aux q (FormeClausale.add (string_to_disj t) fcc)
  in aux  strArray FormeClausale.empty;;

