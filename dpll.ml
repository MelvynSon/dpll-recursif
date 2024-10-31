(* 2024/2025 - dpll.ml *)

open List

(* ----------------------------------------------------------- *)

(* fonctions utilitaires *)

(* print_modele : int list option -> unit
   afficher le résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [
  [1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];
  [19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];
  [-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];
  [-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];
  [-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];
  [-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];
  [-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];
  [-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];
  [-14;-17];[-15;-18]]

(* ----------------------------------------------------------- *)

(** simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai

  [simplifie l clauses] simplifie la liste de clauses donnée en appliquant le littéral [l].
  Si [l] est 0, elle lève une exception avec le message "littéral nul".
  Sinon, elle filtre et mappe les clauses comme suit :
  - Si une clause contient le littéral [l], la clause est supprimée.
  - Si une clause ne contient pas le littéral [l], le littéral [-l] est supprimé de la clause.
  Elle retourne une nouvelle liste de clauses après application de la simplification.

  @param l Le littéral à appliquer pour la simplification.
  @param clauses La liste de clauses à simplifier.
  @return Une nouvelle liste de clauses après application de la simplification.
  @raise Failure si [l] est 0.
 
    *)
    let simplifie l clauses =
      if l = 0 then raise (Failure "littéral nul")
      else
        (* voir le fichier de rendu (1. et 5.), sur pourquoi on utilise List.filter_map plutôt que filter_map fournie ici*)
        List.filter_map (fun clause ->
          let rec aux acc = function
            | [] -> Some acc
            | x::xs when x = l -> None
            | x::xs when x = -l -> aux acc xs
            | x::xs -> aux (x::acc) xs
          in
          aux [] clause
        ) clauses

(* ----------------------------------------------------------- *)


(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* Tests *)
 (*
 let () = print_modele (solveur_split systeme []) 
 let () = print_modele (solveur_split coloriage []) 
 *)

(* ----------------------------------------------------------- *)


  (** delete_litteral -> int -> int list -> int list
    La fonction parcourt la liste de clauses, pour supprimer toutes les occurences d'un littéral donné.
    Si le littéral est trouvé, il est supprimé de la liste, sinon la liste est inchangée.
    C'est une fonction récursive qui se rappelle pour parcourir le restant de la liste après ce qu'elle a déja traité.
    
    @param lit Le littéral à supprimer.
    @param list La liste de littéraux.
    @return La liste de littéraux après suppression du littéral.
  
  *)
  let rec delete_litteral lit list = 
    match list with
    | [] -> []
    | a::t -> 
        if (a = lit || a = (-lit)) then
          delete_litteral lit t
        else
          a::delete_litteral lit t
       
  
  (** pur_aux : int list -> int
      La fonction pur_aux prend en paramètre une liste de littéraux et retourne le premier littéral pur trouvé.
      Pour cela, elle parcourt récursivement la liste de littéraux et vérifie si l'inverse du premier littéral 
      de la liste (non(lit)), est présent dans la liste :
      - Si oui, elle rappelle pur_aux avec comme paramètre la liste modifiée par la fonction delete_litteral qui 
        supprime toutes les occurences de lit ou non(lit) de la liste avant de la renvoyer.
      - Si non, elle retourne le littéral.
      Si la liste est vide, elle lève une exception `Failure "pas de littéral pur"'.
      @see delete_litteral, la fonction qui permet de supprimer toutes les occurences d'un littéral donné dans une liste de littéraux.

      @param l Une liste de littéraux.
      @return Le premier littéral pur trouvé.
      @raise Failure si aucun littéral pur n'est trouvé.
  *)
  let rec pur_aux l =
    match l with
    | [] -> raise (Failure "pas de littéral pur")
    | a::t -> 
        if (mem (-a) t) then
          pur_aux (delete_litteral a l)
        else
          a
  
  
  (** pur : int list list -> int
      - si `clauses' contient au moins un littéral pur, retourne
        ce littéral ;
      - sinon, lève une exception `Failure "pas de littéral pur"' 
      Pour faire cela on applique la fonction flatten à la liste de clauses pour avoir une unique liste 
      comportant tous les littéraux de clauses. Si un littéral pur est trouvé, on le retourne.
      @see pur_aux, la fonction auxiliaire de pur qui permet de trouver un littéral pur dans une liste de littéraux.
      @see delete_litteral, la fonction qui permet de supprimer toutes les occurences d'un littéral donné dans une liste de littéraux.

      @param clauses Une liste de clauses, où chaque clause est une liste de littéraux.
      @return Un littéral pur s'il en existe un.
     
  *)
  let rec pur clauses =
    let ensemble_lit = flatten clauses in
      pur_aux ensemble_lit

  
  (* Tests *)
  (*
  let test = pur [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]];;
  let test = pur [[1;2;3];[-1;2;3];[3];[1;2;-3];[-1;2;-3];[-3]];;
  let test2 = simplifie (-3) test;;
  *)

(* ----------------------------------------------------------- *)


(**
  unitaire -> int list list -> int
  
  La fonction unitaire prend en paramètre une liste de clauses et retourne un littéral unitaire s'il en existe un.
  Pour cela, elle parcourt récursivement la liste de clauses et vérifie si une clause contient un seul littéral :
  - Si oui, elle retourne ce littéral.
  - Si non, elle lève une exception `Not_found'.


  @param clauses Une liste de clauses, où chaque clause est une liste de littéraux.
  @return Un littéral unitaire s'il en existe un.
  @raise Not_found si aucun littéral unitaire n'est trouvé.

  Un littéral unitaire est une clause qui contient un seul littéral.
*)

let unitaire clauses =
  match List.filter_map (function
    | [l] -> Some l
    | _ -> None) clauses with
  | [] -> raise Not_found
  | l::_ -> l

(* ----------------------------------------------------------- *)


(** 
solveur_dpll_rec : int list list -> int list -> int list option 

La fonction solveur_dpll_rec est une fonction récursive qui prend en paramètre une liste de clauses
et une interprétation partielle et retourne une interprétation complète si elle existe.
Pour cela, on fait une disjonction de cas sur les clauses, à l'aide de la fonction unitaire et pur.qui lèvent des exceptions 
si elles ne trouvent pas de littéraux unitaires ou purs.:

- Si l'ensemble de clauses est vide, l'interprétation partielle est satisfiable, on retourne cette interprétation.

- Si l'ensemble de clauses contient une clause vide, l'interprétation partielle n'est pas satisfiable, on retourne None.

- Si un littéral unitaire est trouvé, on simplifie l'ensemble de clauses en appliquant ce littéral et on rappelle solveur_dpll_rec 
  avec l'interprétation partielle mise à jour.
@see unitaire, la fonction qui permet de trouver un littéral unitaire dans une liste de clauses.

- Si un littéral pur est trouvé, on simplifie l'ensemble de clauses en appliquant ce littéral et on rappelle solveur_dpll_rec
  avec l'interprétation partielle mise à jour.
@see pur, la fonction qui permet de trouver un littéral pur dans une liste de clauses.

- Sinon, on prend le premier littéral de la première clause et on fait un branchement :
  - On rappelle solveur_dpll_rec avec l'ensemble de clauses simplifié en appliquant ce littéral et l'interprétation partielle mise à jour.
  - Si le résultat est None, on rappelle solveur_dpll_rec avec l'ensemble de clauses simplifié en appliquant le littéral opposé et 
    l'interprétation partielle mise à jour.
  - Sinon, on retourne le résultat.

  @param clauses Une liste de clauses, où chaque clause est une liste de littéraux.
  @param interpretation Une liste de littéraux, qui représente l'interprétation partielle.
  @return Une interprétation complète si elle existe, None sinon.

  @see simplifie, la fonction qui simplifie l'ensemble de clauses en appliquant un littéral.
*)
let rec solveur_dpll_rec clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* littéral unitaire *)
  try
    let l = unitaire clauses in
    solveur_dpll_rec (simplifie l clauses) (l::interpretation)
  with _ ->
  (* littéral pur *)
  try
    let l = pur clauses in
    solveur_dpll_rec (simplifie l clauses) (l::interpretation)
  with _ ->
  (* branchement *)
  let l = hd (hd clauses) in
  let branche =  solveur_dpll_rec (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

  (* Tests *)
  (*
  let () = print_modele (solveur_dpll_rec systeme []) 
  let () = print_modele (solveur_dpll_rec coloriage []) 
  *)

(* ----------------------------------------------------------- *)
let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
