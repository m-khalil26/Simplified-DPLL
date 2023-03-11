open Proposition
open Formule

(* Adapteurs de code *)
    
(**renvoie la negation de toutes les formules  d'une liste*)
let neg_list f_l =
  let rec aux f_l acc =
    match f_l with
      |[] -> acc
      |t::q -> aux q ((( ~~ )t)::acc)
  in aux f_l [];;

(** renvoie la disjonction d'une formule avec toutes les formules d'une liste *)
let disj_to_all first all =
  let rec aux all acc =
      match all with
      |[] -> acc
      |t::q -> aux q (( + ) first t)
in aux all Bot;;

(** renvoie la disjonction de toutes les formules d'une liste *)
let  disj_all all =
  let rec aux all acc=
    match all with
    |[]-> acc
    |t::q -> aux q (( + ) acc t)
  in aux all Bot

(** Création d'une formule équivalente à la formule UnSeul xs, depuis une liste de formule xs.  *)
    
let unSeul (f_l : formule list) : formule =
  let rec aux f_l acc=
    match f_l with
      |[]-> acc
      |t::q -> aux q (( * ) acc (disj_to_all (((~~) t)) (neg_list(q))))
  in aux f_l (disj_all f_l)


(** Création d'une formule équivalente à la formule Tous xs, depuis une liste de formule xs.  *)

let tous (f_l : formule list) : formule =
  let rec aux f_l acc=
    match f_l with
    |[] -> acc
    |t::q ->aux q (( * ) t acc)
in aux f_l Top;;

