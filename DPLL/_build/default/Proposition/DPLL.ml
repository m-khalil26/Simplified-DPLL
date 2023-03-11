open FCC

(*-----------------------------------------OUTILS-------------------------------------------*)

(** atome_of_lit : renvoie un atome d'un litteral *)
let atome_of_lit lit = match lit with |_,at -> at;;

(**boolean_of_lit : renvoie le true si signe = Plus, false sinon *)
let boolean_of_lit lit = match lit with |Plus,_ -> true |Moins,_-> false ;;

(** Simplifie la forme clausale fcc en considérant que le littéral lit est vrai *)
let negation lit = match lit with |Plus,x -> Moins,x |Moins, x -> Plus,x;;

(** concatene deux listes sans doublons *)
let rec verify_exist list1 list2=
    match list1 with
      |[] -> list2
      |t::q when not(List.mem t list2) && not(List.mem (negation t) list2) -> verify_exist q (t::list2)
      |_::q -> verify_exist q list2;;


(**Construit une liste de tout les littéraux contenue dans une fcc *)
let build_lit_list (fcc:forme_clausale) : litteral list =
  let cl_list = FormeClausale.elements fcc in
  let rec aux cl_list acc=
  match cl_list with
    |[]-> acc
    |t::q -> aux q (verify_exist (Clause.elements t) acc)
  in aux cl_list [];;

(**Choisis un litteral dans une forme clausale *)
let choix_litteral fcc =
match FormeClausale.choose_opt fcc with
    |None -> None
    |Some s -> Clause.choose_opt s

(*--------------------------------------------Simplificiation---------------------------------------------*)

let simplif_fcc (fc : forme_clausale) (lit  : litteral) : forme_clausale =
  let list_c =  FormeClausale.elements fc
  in
  let rec aux list_c acc=
  match list_c with
  |[] -> FormeClausale.of_list acc
  |t::q when (Clause.mem lit t) -> aux q acc
  |t::q when (Clause.mem (negation lit) t)-> aux q ((Clause.remove (negation lit) t)::acc)
  |t::q -> aux q (t::acc)
  in aux list_c []


(*---------------------------------------Etudes de satisfaisablité---------------------------------------*)
(** Applique l'algorithme DPLL pour déterminer si une fcc est satisfaisable. *)
let dpll_sat (fcc : forme_clausale) : bool =
  let rec aux fcc =
    match fcc with
      |f when FormeClausale.is_empty f -> true
      |f when FormeClausale.mem (Clause.empty) f -> false
      |f ->let lit' = choix_litteral f in
        if lit' == None (*normalement pas possible *)
        then failwith""
        else
        let lit = Option.get lit'
        in
        match(aux (simplif_fcc f lit)) with
        |true -> true
        |false ->  (aux(simplif_fcc f (negation lit)))
in aux fcc;;

(** Applique l'algorithme DPLL pour déterminer si une fcc est une tautologie. *)
let dpll_tauto (fcc : forme_clausale) : bool =
    let rec aux fcc =
    match fcc with
      |f when FormeClausale.is_empty f -> true
      |f when FormeClausale.mem (Clause.empty) f -> false
      |f ->let lit' = choix_litteral f in
        if (Option.is_none lit')
        then failwith""
        else
        let lit = Option.get lit'
        in (aux (simplif_fcc f lit))&&(aux(simplif_fcc f (negation lit)))
in aux fcc;;


(** Applique l'algorithme DPLL pour déterminer si une fcc est une contradiction. *)
let dpll_contra (fcc : forme_clausale) : bool =
    let rec aux fcc =
    match fcc with
      |f when FormeClausale.is_empty f -> false
      |f when FormeClausale.mem (Clause.empty) f -> true
      |f ->let lit' = choix_litteral f in
        if lit' == None
        then failwith""
        else
        let lit = Option.get lit'
        in
        (aux (simplif_fcc f lit))&&((aux(simplif_fcc f (negation lit)))) 
in aux fcc;;

(*--------------------------------------------DPLL_EX_SAT-------------------------------------------------*)

(** Applique l'algorithme DPLL pour déterminer si une fcc est satisfaisable, renvoyant None si ce n'est pas le cas
      et Some res sinon, où res est une liste de couples (atome, Booléen)
      suffisants pour que la formule soit vraie. *)

let dpll_ex_sat (fcc : forme_clausale) : (string * bool) list option =
  if(not(dpll_sat fcc)) then None else
  let rec aux fcc list =
    match fcc with
      |f when FormeClausale.is_empty f -> Some list
      |f when FormeClausale.mem (Clause.empty) f -> None
      |f ->let lit' = choix_litteral f in
        if (Option.is_none lit')
        then failwith""
        else
        let lit = Option.get lit'
        in
        match(aux (simplif_fcc f lit)((atome_of_lit lit,boolean_of_lit lit)::list) ) with
        |Some list -> Some list
        |None -> (aux(simplif_fcc f (negation lit)) ((atome_of_lit lit,boolean_of_lit (negation lit ))::list) )
in aux fcc [];;


(*----------------------------------------DPLL_ALL_SAT---------------------------------------------------*)

(** dpll_ex_sat_with_chosen_lit : prend en entrée une fcc et un littéral,renvoie None si
     la fcc n'est pas satisfaisable et Some res sinon, où res est une liste de couples (atome, Booléen)
      suffisants pour que la formule soit vraie, en prenant en compte le litteral comme premier choix de litteral *)

let dpll_ex_sat_with_chosen_lit (fcc : forme_clausale)(lit : litteral) : (string * bool) list option =
  if(not(dpll_sat fcc)) then None else
  let rec aux fcc list lit =
    match fcc with
      |f when FormeClausale.is_empty f -> Some list
      |f when FormeClausale.mem (Clause.empty) f -> None
      |f ->let lit' = choix_litteral f in
        if (Option.is_none lit')
        then Some list
        else
        let lit'' = Option.get lit'
        in
        if not (List.mem (atome_of_lit lit,boolean_of_lit lit) list) then
        match(aux (simplif_fcc f lit)((atome_of_lit lit,boolean_of_lit lit)::list) lit'' ) with
        |Some list -> Some list
        |None when  not(List.mem (atome_of_lit lit,boolean_of_lit(negation lit)) list) -> (aux(simplif_fcc f (negation lit)) ((atome_of_lit lit,boolean_of_lit(negation lit))::list) lit'' )
        |_-> (aux(simplif_fcc f (negation lit)) list lit'' )
        else
          match(aux (simplif_fcc f lit) list lit'' ) with
          |Some list -> Some list
          |None when  not(List.mem (atome_of_lit lit,boolean_of_lit(negation lit)) list) -> (aux(simplif_fcc f (negation lit)) ((atome_of_lit lit,boolean_of_lit(negation lit))::list) lit'' )
          |_-> (aux(simplif_fcc f (negation lit)) list lit'' )
in aux fcc [] lit;; 

(** Renvoie la liste des listes de couples (atome, Booléen) suffisants pour que la formule soit vraie,
    selon l'algorithme DPLL. *)
let dpll_all_sat (fcc :forme_clausale) : (string * bool ) list list =
  if(not(dpll_sat fcc)) then [] else
    let lit_list= build_lit_list fcc
    in let rec aux lit_list acc' acc''=
     match lit_list with
      |[] ->List.append acc' acc''
      |t::q-> aux q (Option.get(dpll_ex_sat_with_chosen_lit fcc t)::acc') (Option.get(dpll_ex_sat_with_chosen_lit fcc (negation t))::acc'')
    in aux lit_list [] [];;


