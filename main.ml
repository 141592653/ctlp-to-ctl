(* Ce fichier permet d'implémenter une fonction renvoyant la nème permutation 
 * dans l'ordre lexicographique*)


(** Factorielle*)
let rec fact n = match n with
  |0 -> 1
  |_ -> n * fact (n-1)

(** Permet d'ajouter 1 à tous les éléments de la liste supérieurs à k*)
let rec succ_sup l k = match l with
  |[] -> []
  |x::q -> if x >= k then
	     (x+1)::(succ_sup q k)
	   else
	     x::(succ_sup q k)


(** Renvoie la nème permutation de {1,...,m} si elle existe
 *  et None sinon *)
let perm n m =
  let rec perm_tmp n m fact =
    match m with
    |0 -> []
    |_ -> let q = n/fact and r = n mod fact in
	  
	  q :: (succ_sup (perm_tmp
			    r
			    (m-1)
			    (fact/(if m>1 then m-1 else 1))
			 )
			 q
	       )
  in
  perm_tmp n m (fact (m-1))
  

(*ce fichier contient un module permettant de gérer les ensembles finis
 * de manière efficace. Il a été codé par Alice RIXTE dans le cadre du
 * DM du cours de programmation avancée. Le complémentaire et le générateurs
 * ont été ajoutés pour le DM de vérification. *)


(** Signature représentant les types finis.
 *
 * Le type [t] est équipé de fonctions [to_int] et [of_int],
 * qu'on supposera inverses l'une de l'autre.
 *
 * De plus le type est supposé fini, c'est à dire qu'on ne
 * rencontrera que des valeurs [x] telles que
 * [0 <= to_int x < max].
 *
 * La fonction [of_int] ne devra être appelée que sur des
 * valeurs [i] tel que [0 <= i < max]. *)
module type FIN = sig
    type t
    val max : int
    val to_int : t -> int
    val of_int : int -> t
  end

(** Signature décrivant un type d'ensembles [t] dont les éléments
 * sont dans [elt].
 *
 * Les opérations ne modifient jamais en place un ensemble,
 * mais ceux-ci sont manipulés dans un style persistant.
 *
 * L'égalité structurelle d'OCaml sur [t] doit correspondre à
 * l'égalité ensembliste. *)
module type SET = sig
    type t
    type elt

    (** Cardinal d'un ensemble, en temps constant *)
    val cardinal : t -> int

    (** Ensemble vide *)
    val empty : t

    (** Création d'un ensemble contenant tous les éléments
     * pour lesquels une fonction est vraie. *)
    val init : (elt -> bool) -> t

    (** Ajout d'un élément *)
    val add : t -> elt -> t

    (** Suppression d'un élément *)
    val remove : t -> elt -> t

    (** Test d'appartenance *)
    val member : t -> elt -> bool

    (** Détermine si le premier ensemble est sous-ensemble du second *)
    val subset : t -> t -> bool

    (** Itération d'une fonction sur les éléments d'un ensemble *)
    val iter : t -> (elt -> unit) -> unit
				       
    (** Générateur de l'ensemble des parties de l'univers*)
    val sub_generator : unit -> unit -> t option

    (**Renvoie le complémentaire de l'ensemble passé en argument*)
    val complementary : t -> t

    (**Permet d'extraire les éléments de la liste correspondant 
     * aux numéros des éléments de s*)
    val extract : 'a list -> t -> 'a list
  end

		    
module Make (F : FIN) : SET with type elt = F.t = struct
  
  type t = Int64.t array
  type elt = F.t

  let t_size = (F.max / 64) + 2
  (*Permet de connaître la position de l'élément dans l'ensemble*)
  let get_pos int_el = int_el / 64 + 1
  (*Permet de connaître le numéro du bit une fois l'entier 64 bits identifié*)
  let get_bit int_el = int_el mod 64
  (*Permet d'obtenir un masque ne comportant que des 0 hormis un 1 sur l'élément qui nous intéresse *)
  let mask int_el = Int64.shift_left Int64.one (get_bit int_el)

				     
  (* Le premier entier du tableau est le cardinal*)
  let cardinal e =  Int64.to_int e.(0)
				     
  let empty = Array.make t_size Int64.zero

  (*Ici, on n'utilise pas la fonction add car ce serait plus lent*)
  let init f =
    let new_e = Array.make t_size Int64.zero in
    for i = 0 to F.max do
      if f (F.of_int i) then
	(
	  new_e.(0) <- Int64.succ new_e.(0);
	  let pos_i = get_pos i in 
      	  new_e.(pos_i) <- Int64.logor new_e.(pos_i) (mask i) 
	)
    done;
    new_e

      
      
  let add e el =
    let int_el = F.to_int el in 
    let new_e = Array.copy e in 
    let pos_el = get_pos int_el in 
    new_e.(pos_el) <- Int64.logor (mask int_el) e.(pos_el);
    (*Si les entiers sont différents, c'est que l'élément ne se trouvait pas dans l'ensemble *)
    if Int64.compare new_e.(pos_el) e.(pos_el) <> 0 then
      new_e.(0) <- Int64.succ new_e.(0);
    new_e

      

  (*La même mais en inversant tout*)
  let remove e el =
    let int_el = F.to_int el in 
    let new_e = Array.copy e in 
    let pos_el = get_pos int_el in 
    new_e.(pos_el) <- Int64.logand (Int64.lognot (mask int_el)) e.(pos_el);
    (*Si les entiers sont différents, c'est que l'élément ne se trouvait pas dans l'ensemble *)
    if Int64.compare new_e.(pos_el) e.(pos_el) <> 0 then
      new_e.(0) <- Int64.pred new_e.(0);
    new_e


  let member e el =
    let int_el = F.to_int el in 
    Int64.compare (Int64.logand (mask int_el) e.(get_pos int_el)) Int64.zero <> 0

  (*pour que e1 soit un sous-ensemble de e2, si un élément appartient à e1, alors il appartient à e2. On peut donc utiliser l'implication logique et on ne doit alors obtenir que des 1. On veut donc que la négation de e1 => e2 soit 0. Par conséquent, on peut utiliser la formule e1/\~e2 et vérifier que le résultat est nul*)
  let subset e1 e2 =
    let sub = ref true and i = ref 1 in
    while !sub && !i < t_size do
      sub := Int64.compare (Int64.logand e1.(!i) (Int64.lognot e2.(!i))) Int64.zero = 0;
      i := !i + 1
    done;
    !sub


     
  let iter e f =
    for i = 0 to F.max do
      let el = F.of_int i in
      if member e el then
	f el
    done


  (*Ce mask permet de mettre à zéro toutes les valeurs au dessus de F.max*)
  let cut_sup_max =
    let mask_sup = ref Int64.zero in
    for i = 0 to F.max mod 64 do
      mask_sup := Int64.logor (Int64.shift_left Int64.one i) !mask_sup
    done;
    !mask_sup

     
  let complementary e =
    let c = Array.copy e in
    for i = 1 to t_size - 1 do
      c.(i) <- Int64.lognot c.(i)
    done;
    c.(t_size - 1) <- Int64.logand c.(t_size - 1) cut_sup_max;
    c

  let sub_generator () =
    let e = Array.copy empty  in
    let num_e = ref 0 and nb_sub = int_of_float (2. ** (float_of_int F.max)) in 
    let next () =
      if !num_e < nb_sub then
	begin
	  let ret = Array.copy e in
	  num_e := !num_e + 1;
	  let j = ref 1 and continue = ref true in
	  while !j < t_size && !continue do
	    e.(!j) <- Int64.succ e.(!j);
	    continue :=  Int64.compare e.(!j) Int64.zero = 0;
	    j := !j + 1;					     
	  done;
	  Some ret
	end
      else
	None

    in

    next

      
  let extract l s =
    let rec extract_tmp l n = match l with
      |[]-> []
      |x::q -> if member s (F.of_int n) then
		 x::(extract_tmp q (n+1))
	       else
		 extract_tmp q (n+1)
    in
    extract_tmp l 0
      
      


end


(*tests*)
						      
module I:FIN = struct
  type t = int
  let max = 1000
  let to_int n = n 
  let of_int n = n mod 1000
end

module S = Make(I)

let s = ref (S.empty)
let pairs = S.init (fun i -> let n = I.to_int i in n mod 2 = 0)
let impairs = S.init (fun i -> let n = I.to_int i in n mod 2 = 1)
let pairs2 = S.init (fun i -> let n = I.to_int i in n mod 2 = 0)
let p = (S.init (fun i -> let n = I.to_int i in n = 10 || n = 0 || n = 33))

module J:FIN = struct
  type t = int
  let max = 3
  let to_int n = n
  let of_int n = n mod 3
end
module T = Make(J)



(*Ceci est un convertisseur des formules CTL+ vers les formules CTL
écrit dans le cadre du cours d'introduction à la vérification par Alice RIXTE*)

(* Ce fichier ce découpe en plusieurs parties : 
I - Déclarations utiles
II - Conversion vers la forme (2) de la question 4
III - Conversion de la forme (2) vers CTL
IV -  Fonctions principales *)





(* ********************  I - Déclarations de types et globally, finally******** *)
(**formules de CTL*)
type ctl_path =
  | Next of ctl_state
  | Until of ctl_state * ctl_state
  | Globally of ctl_state

and ctl_state =
  | True
  | AP of int
  | Not of ctl_state
  | And of ctl_state * ctl_state
  | Or of ctl_state * ctl_state
  | Exists of ctl_path


(**Formules de CTL+*)
type ctl_plus_path =
  | NextP of ctl_plus_state
  | UntilP of ctl_plus_state * ctl_plus_state
  | GloballyP of ctl_plus_state
  | NotPP of ctl_plus_path
  | AndPP of ctl_plus_path * ctl_plus_path
  | OrPP of ctl_plus_path * ctl_plus_path

and ctl_plus_state =
  | TrueP
  | APP of int
  | NotPS of ctl_plus_state
  | AndPS of ctl_plus_state * ctl_plus_state
  | ExistsP of ctl_plus_path



let formula =
  OrPP(
      AndPP(
	  AndPP(
	      NotPP (NotPP (NotPP (NextP (APP 0)))),
	      NextP (APP 0)
	    ),
	  NotPP(UntilP(APP 0, APP 1))),
      NotPP (AndPP(
		 OrPP(
		     NextP (TrueP), NextP(TrueP)
		   ),
		 NextP TrueP
	       )
	    )
    )
			      


(**Renvoie la formule Ff*)
let finallyP (f :ctl_plus_state) : ctl_plus_path =
  UntilP(TrueP,f)



(* II - La première étape est celle de la question 4 du TD. Pour transformer une 
formule CTL+ quelconque en disjonction de la forme (2), nous allons procéder 
en plusieurs étapes en travaillant sur les formules de chemin de CTL+ 
1) On se débarasse des négations en les envoyant dans les sous-formules d'état.
2) On fait remonter les Or pour avoir une disjonction de conjonction de 
formules de chemin ne commençant pas par une négation
3) On rassemble les nexts et les globally 
*)

(*BEGIN Quelques fonction de conversions*)

(*Fonction pour CTL*)
	
(**Transforme une conjonction de CTL formula  en liste de CTL formula*)
let rec formula_to_and_list f  =
  match f with
  |And(g1,g2) -> (formula_to_and_list g1)@(formula_to_and_list g2)
  |_ -> [f]

(**Transforme une liste de path_formula en une conjonction de path_formula *)
let rec and_list_to_formula al =
  match al with
  |[] -> failwith "une and_list ne doit jamais être vide"
  |[f] -> f
  |f::q -> And (f, and_list_to_formula q)

	  
(**Transforme une disjonction de CTL formula en liste de and_list*)
let rec formula_to_or_list f   =
  match f with
  |Or(g1,g2) -> (formula_to_or_list g1)@(formula_to_or_list g2)
  |_ -> [formula_to_and_list f]

(**Transforme une liste de and_list  en une disjonction de CTL formula *)
let rec or_list_to_formula ol =
  match ol with
  |[] -> failwith "une or_list ne doit jamais être vide"
  |[l] -> and_list_to_formula l
  |l::q -> Or (and_list_to_formula l, or_list_to_formula q)

(*Fonction pour CTL+*)
	
(**Transforme une conjonction de path_formula  en liste de path_formula*)
let rec formula_to_and_list_p (f : ctl_plus_path)  =
  match f with
  |AndPP(g1,g2) -> (formula_to_and_list_p g1)@(formula_to_and_list_p g2)
  |_ -> [f]

(**Transforme une liste de path_formula en une conjonction de path_formula *)
let rec and_list_to_formula_p al =
  match al with
  |[] -> failwith "une and_list ne doit jamais être vide"
  |[f] -> f
  |f::q -> AndPP (f, and_list_to_formula_p q)

	  
(**Transforme une disjonction de path_formula en liste de path_formula*)
let rec formula_to_or_list_p (f : ctl_plus_path)  =
  match f with
  |OrPP(g1,g2) -> (formula_to_or_list_p g1)@(formula_to_or_list_p g2)
  |_ -> [formula_to_and_list_p f]

(**Transforme une liste de and_list  en une disjonction de path_formula *)
let rec or_list_to_formula_p ol =
  match ol with
  |[] -> failwith "une or_list ne doit jamais être vide"
  |[l] -> and_list_to_formula_p l
  |l::q -> OrPP (and_list_to_formula_p l, or_list_to_formula_p q)

(*END Quelques fonctions de conversions*)


(*BEGIN Étape II.1)*)

(**Permet de faire descendre la négation d'un niveau tout en 
conservant une conjonction*)
let rec elim_not (f : ctl_plus_path) : ctl_plus_path =
  match f with
  |NotPP g ->
    begin
      match g with
      |NotPP h -> elim_not h
      |NextP h -> NextP (NotPS h)
      |UntilP(h1,h2) -> OrPP(
			    GloballyP h1,
			    UntilP(
				AndPS(h1, NotPS h2),
				AndPS(NotPS h1, NotPS h2)
			      )
			  )
      |OrPP(h1,h2) -> AndPP(elim_not (NotPP h1), elim_not (NotPP h2))
      |AndPP(h1,h2) -> OrPP(elim_not (NotPP h1), elim_not (NotPP h2))
      |GloballyP h -> finallyP (NotPS h)	
    end  
  |_ -> f

let elim_not_and_list l = List.map elim_not l
let elim_not_or_list l = List.map elim_not_and_list l




(*END Étape II.1) *)


      
(*BEGIN Étape II.2*)

(**Fait descendre les and et remonter les or. *)
let rec drown_ands f = match f with
  | AndPP(g1,g2) ->
     begin match (drown_ands g1, drown_ands g2) with
	   |(OrPP(h1,h2),h) | (h,OrPP(h1,h2)) ->
	     drown_ands
	       (OrPP(
		    AndPP(h1,h),
		    AndPP(h2,h)
		  ))
	   |(h1,h2) -> AndPP(h1,h2)
	     
     end
		    
  | OrPP(g1,g2) -> OrPP(drown_ands g1, drown_ands g2)
  | _ -> f

(**Donne la formule sous la forme que l'on souhaite avoir à l'étape 2*)
let or_list_without_negs f =
  formula_to_or_list_p (drown_ands ( or_list_to_formula_p(
				       elim_not_or_list (formula_to_or_list_p f)
				     )))

(*END Étape II.2*)

(*BEGIN Étape II.3*)

(**Agrège les formules next et les formules globally dans une and_list*)
let aggregate_next_globally al =
  let nexts = ref TrueP and globallies = ref TrueP in
  let rec aggregate_rec l = match l with
    |[] -> []
    |f::q ->
      begin
	match f with
	|NextP g ->
	  nexts := AndPS(g,!nexts);
	  aggregate_rec q
	|GloballyP g ->
	  globallies := AndPS(g,!globallies);
	  aggregate_rec q
	|_ -> f :: aggregate_rec q
      end
  in

  (NextP !nexts)::(GloballyP !globallies)::aggregate_rec al

(**Transforme une formule CTL+ en disjonctions de formules de forme (2))
let ctlP_to_form2*)


(*END Étape II.3*)




							 
(*III - Conversion de la forme (2) en CTL *)

(*BEGIN Étape III.1 : forme 1 vers CTL : 
* 
* Commençons par appliquer le résultat de la question 2 en transformant les 
* formules de la forme 1 en formules CTL
*)

let get_psi = function
  | Until(psi,psi') -> psi
  | _ -> failwith "untils ne contient pas que des U dans get_psi"

let get_psi' = function
  | Until(psi,psi') -> psi'
  | _ -> failwith "untils ne contient pas que des U dans get_psi'"
			   
(**Permet de récupérer les psi'_i  *)
let get_psi_list untils =
  List.map get_psi untils

(**Permet de récupérer les psi_i  *)
let get_psi'_list untils =
  List.map get_psi' untils

(**Renvoie la liste des n permiers éléments de l*)
let rec begin_list l n =
  match n with
  |0 -> []
  |_ ->
    begin
      match l with
      |[] -> []
      |x::q -> x::(begin_list q (n-1))
    end
	       

(**Enlève les éléments de la liste l dont la position appartient aux
 * j premiers éléments de la liste p représentant une permutation*)
let list_minus_perm l p j =
  let p' = begin_list p j in

  let rec list_minus_perm_tmp l n =
    match l with
    | [] -> []
    | x::q ->
      try
        ignore (List.find (fun y -> y = n) p');
	list_minus_perm_tmp q (n+1)
      with
	Not_found -> x:: (list_minus_perm_tmp q (n+1))
  in
  list_minus_perm_tmp l 0

(** Renvoie la conjonction des psi dont l'indice ne se trouve pas
 * dans les j premiers éléments de p*)
let and_psi_minus_perm al p j =
  and_list_to_formula (get_psi_list (list_minus_perm al p j))

(**Renvoie le psi' à la position p j, o* p est une permutation*)
let psi'_perm al p j =
  get_psi' (List.nth al (List.nth p j))


let form1_to_CTL_perm untils phi p =
  let n = List.length p in 
  let rec form1_to_CTL_perm_tmp k =
    if k = n then
      Exists (Globally phi)
    else
      Exists (
	  Until(
	      And(and_psi_minus_perm untils p k , phi),
	      And(psi'_perm untils p k, form1_to_CTL_perm_tmp (k+1))
	    )
	)
  in

  form1_to_CTL_perm_tmp 0
  
	      

(**ici, on représente une formule de forme 2 par une and_list qui
 * commence par le globally et qui est suivi d'une liste d'untils *)
let form1_to_CTL phi untils = 
  let m = List.length untils in
  let n = fact m in
  let ctl_f = ref (Not True) in
  for i = 0 to n - 1 do
    let p = perm i m in
    ctl_f := Or(form1_to_CTL_perm untils phi p, !ctl_f)
  done;
  !ctl_f
 
				


(*BEGIN Étape III.2 : élimination du next*)
							 
(*On va faire une disjonction sur toutes les parties de [|1,n|], 
où n est l'entier qui correspond à celui de la question 4. On veut
donc extraire à partir d'un sous-ensemble de [|1,n|] la conjonction 
des psi' de cet ensemble et la conjonction des psi U Psi' du complémentaire
de cet ensemble *)

							 


(**ici, on représente une formule de forme 2 par une and_list *)
let form2_to_CTL al = match al with
  |(Next phi)::(Globally phi')::untils ->
    let lu = List.length untils in
    let module Fin : FIN = struct
      type t = int
      let max = lu
      let to_int n = n mod lu
      let of_int n = n
    end in
    let module Ens = Make(Fin) in

    (* Pour un ensemble donné, on applique la trnasformation de la question 4*)
    let form2_to_CTL_set phi phi' untils s =
      let f1 = form1_to_CTL phi' (Ens.extract untils (Ens.complementary s)) in 
      And(and_list_to_formula (get_psi'_list (Ens.extract untils s)),
	  And(phi',
	      Exists(Next(
			 And(phi,f1)
		       ))
	     ))
    in

	
    let gen = Ens.sub_generator () in
    let set = ref (gen ()) in
    let ctl_f = ref (Not True) in 
    while !set <> None do
      let Some s = !set in
       ctl_f := Or(form2_to_CTL_set phi phi' untils s, !ctl_f)
    done;
    !ctl_f
    
  |_ -> failwith "la fonction form2_to_CTL a n'a pas reçu une and_list 
		  correcte en argument"
							 


(*END Étape III.2*)

		     

let main () = ()


let () = main()
