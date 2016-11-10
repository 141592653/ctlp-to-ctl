

(*Ceci est un convertisseur des formules CTL+ vers les formules CTL
écrit dans le cadre du cours d'introduction à la vérification par Alice RIXTE*)

(* Ce fichier ce découpe en plusieurs parties : 
I - Déclarations utiles
II - Conversion vers la forme (2) de la question 4
III - Conversion de la forme (2) vers CTL
IV -  Fonctions principales *)

open Permute
open Bitset





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
  |[] -> True
  |[f] -> f
  |f::q -> And (f, and_list_to_formula q)

(**Transforme une liste de path_formula en une conjonction de path_formula *)
let rec or_list_to_formula al =
  match al with
  |[] -> failwith "une or_list ne doit jamais être vide"
  |[f] -> f
  |f::q -> Or (f, or_list_to_formula q)

(*
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
  |l::q -> Or (and_list_to_formula l, or_list_to_formula q)*)

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
let rec formula_to_or_and_list_p (f : ctl_plus_path)  =
  match f with
  |OrPP(g1,g2) -> (formula_to_or_and_list_p g1)@(formula_to_or_and_list_p g2)
  |_ -> [formula_to_and_list_p f]

(**Transforme une liste de and_list  en une disjonction de path_formula *)
let rec or_and_list_to_formula_p ol =
  match ol with
  |[] -> failwith "une or_list ne doit jamais être vide"
  |[l] -> and_list_to_formula_p l
  |l::q -> OrPP (and_list_to_formula_p l, or_and_list_to_formula_p q)

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
  formula_to_or_and_list_p (drown_ands ( or_and_list_to_formula_p(
				       elim_not_or_list (formula_to_or_and_list_p f)
				     )))

(*END Étape II.2*)

(*BEGIN Étape II.3*)

(**Agrège les formules next et les formules globally dans une and_list*)
let aggregate_next_globally al =
  let found_next = ref false and nexts = ref TrueP in 
  let found_globally = ref false and globallies = ref TrueP in
  let rec aggregate_rec l = match l with
    |[] -> []
    |f::q ->
      begin
	match f with
	
	|NextP g ->
	  
	  if !found_next then 
	    nexts := AndPS(g,!nexts)
	  else
	    (nexts := g ; found_next := true;);
	  aggregate_rec q
	|GloballyP g ->
	  if !found_globally then 
	    globallies := AndPS(g,!globallies)
	  else
	    (globallies := g ; found_globally := true);
	  aggregate_rec q
	|_ -> f :: aggregate_rec q
      end
  in

  let aggr = aggregate_rec al in 
  match (!found_next,!found_globally) with
  |(false,false) -> aggr
  |(false,true) -> (GloballyP !globallies)::aggr
  |(true,false) -> (NextP !nexts)::aggr
  |(true,true) -> (NextP !nexts)::(GloballyP !globallies)::aggr

(**Transforme une formule CTL+ en disjonctions de formules de forme (2))
let ctlP_to_form2*)

let path_formula_to_form2 f = 
  List.map aggregate_next_globally (or_list_without_negs f)


(*END Étape II.3*)




							 
(*III - Conversion de la forme (2) en CTL *)

(*BEGIN Étape III.1 : forme 1 vers CTL : 
* 
* Commençons par appliquer le résultat de la question 2 en transformant les 
* formules de la forme 1 en formules CTL
*)

let get_psi = function
  | Until(psi,_) -> psi
  | _ -> failwith "untils ne contient pas que des U dans get_psi"

let get_psi' = function
  | Until(_,psi') -> psi'
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


let form1_to_ctl_perm untils phi p =
  let n = List.length p in 
  let rec form1_to_ctl_perm_tmp k =
    if k = n then
      Exists (Globally phi)
    else
      Exists (
	  Until(
	      And(and_psi_minus_perm untils p k , phi),
	      And(psi'_perm untils p k, form1_to_ctl_perm_tmp (k+1))
	    )
	)
  in

  form1_to_ctl_perm_tmp 0
  
	      

(**ici, on représente une formule de forme 2 par une and_list qui
 * commence par le globally et qui est suivi d'une liste d'untils *)
let form1_to_ctl phi untils = 
  let m = List.length untils in
  if m = 0 then 
    True
  else
    begin
      let n = fact m in
      let ctl_f = ref (Not True) in
      for i = 0 to n - 1 do
	let p = perm i m in
	ctl_f := Or(form1_to_ctl_perm untils phi p, !ctl_f)
      done;
      !ctl_f
    end
 
				


(*BEGIN Étape III.2 : élimination du next*)
							 
(*On va faire une disjonction sur toutes les parties de [|1,n|], 
où n est l'entier qui correspond à celui de la question 4. On veut
donc extraire à partir d'un sous-ensemble de [|1,n|] la conjonction 
des psi' de cet ensemble et la conjonction des psi U Psi' du complémentaire
de cet ensemble *)

							 


(**ici, on représente une formule de forme 2 par une and_list *)
let form2_to_ctl al =  

  let (phi,phi',untils) = match al with 
    |(Next f)::(Globally f')::u -> (f,f',u) 
    |(Next f)::u -> (f,True,u)
    |(Globally f')::u -> (True,f',u)
    |u -> (True,True,u) in 

  let lu = List.length untils in

  if lu = 0 then 
    And(phi',Exists(Next(And(phi,Exists(Globally(phi'))))))
  else
    begin
      let module Fin : FIN = struct
	type t = int
	let max = lu
	let to_int n = n mod lu
	let of_int n = n
      end in
      let module Ens = Make(Fin) in

  (* Pour un ensemble donné, on applique la transformation de la question 4*)
      let form2_to_ctl_set phi phi' untils s =
	let f1 = form1_to_ctl phi' (Ens.extract untils (Ens.complementary s)) in 
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
      while 
	match !set with 
	|None -> false
	|Some s ->
	  ctl_f := Or(form2_to_ctl_set phi phi' untils s, !ctl_f);
	  set := gen();
	  true

	  do
	    ()
	  done;
      !ctl_f
    end
      
      


(*END Étape III.2*)


(*BEGIN IV :  Fonctions principales*)

let rec exists_or_to_or_exists l = match l with 
  |[] -> failwith "une or liste ne doit pas être vide (exist_or_to_or_exist)"
  |[x] -> Exists x
  |x::q -> Or (Exists x, exists_or_to_or_exists q)

let rec ctlp_to_ctl fs = match fs with 
  |TrueP -> True
  |APP n -> AP n
  |NotPS fs' -> Not (ctlp_to_ctl fs')
  |AndPS(fs', fs'') ->  And(ctlp_to_ctl fs', ctlp_to_ctl fs'')
  |ExistsP fp -> 
    let f2 = path_formula_to_form2 fp in 
    let apply_ctlp_to_ctl fp = match fp with 
      |NextP fs' -> Next (ctlp_to_ctl  fs')
      |GloballyP fs' ->  Globally (ctlp_to_ctl  fs')
      |UntilP(fs',fs'') -> Until(ctlp_to_ctl fs', ctlp_to_ctl fs'')
      |_ -> failwith "On ne devrait pas trouver de 'ou', de 'et' ou de 'non' après l'application de path_formula to form2"
    in
    let f2_ctl = List.map (List.map apply_ctlp_to_ctl) f2 in
    or_list_to_formula (List.map form2_to_ctl f2_ctl) 
    


let formula =
  ExistsP (OrPP(
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
    ))

let another_formula = ExistsP (AndPP (UntilP(APP 0,APP 1) , AndPP(UntilP(APP 1,APP 2),  AndPP(NextP(APP 1),GloballyP (ExistsP (UntilP(APP 1,APP 0)))))))
	

		     

let main () = 
  ignore (ctlp_to_ctl formula)


let () = main()

(* 

Je n'ai pas écrit de fonctions d'affichage pour les tests : j'ai utilisé le top-level avec #load.
J'ai fait principalement mes tests sur formula et sur ses sous-formules 
En utilisant le top-level, j'obtiens pour formula le résultat suivant : 
Or
 (And (AP 0,
   Exists (Next (And (And (Not (AP 0), AP 0), Exists (Globally (AP 0)))))),
 Or
  (Or
    (And (And (Not (AP 0), Not (AP 1)),
      And (True, Exists (Next (And (And (Not (AP 0), AP 0), True))))),
    Or
     (And (True,
       And (True,
        Exists
         (Next
           (And (And (Not (AP 0), AP 0),
             Or
              (Exists
                (Until (And (And (AP 0, Not (AP 1)), True),
                  And (And (Not (AP 0), Not (AP 1)), Exists (Globally True)))),
              Not True)))))),
     Not True)),
  Or
   (And (True,
     Exists (Next (And (And (Not True, Not True), Exists (Globally True))))),
   And (True, Exists (Next (And (Not True, Exists (Globally True))))))))





Sur another_formula, j'obtiens une très grosse formule qui montre l'explosion combinatoire très rapide. Les points de suspensions sont ajoutés par le top-level:
 Or
 (And (And (AP 1, AP 2),
   And
    (Or (And (AP 0, And (True, Exists (Next (And (True, True))))),
      Or
       (And (True,
         And (True,
          Exists
           (Next
             (And (True,
               Or
                (Exists
                  (Until (And (AP 1, True),
                    And (AP 0, Exists (Globally True)))),
                Not True)))))),
       Not True)),
    Exists (Next (And (AP 1, True))))),
 Or
  (And (AP 2,
    And
     (Or (And (AP 0, And (True, Exists (Next (And (True, True))))),
       Or
        (And (True,
          And (True,
           Exists
            (Next
              (And (True,
                Or
                 (Exists
                   (Until (And (AP 1, True),
                     And (AP 0, Exists (Globally True)))),
                 Not True)))))),
        Not True)),
     Exists
      (Next
        (And (AP 1,
          Or
           (Exists
             (Until
               (And (AP 0,
                 Or
                  (And (AP 0, And (True, Exists (Next (And (True, True))))),
                  Or
                   (And (True,
                     And (True,
                      Exists
                       (Next
                         (And (True,
                           Or
                            (Exists
                              (Until (And (AP 1, True),
                                And (AP 0, Exists (Globally True)))),
                            Not True)))))),
                   Not True))),
               And (AP 1,
                Exists
                 (Globally
                   (Or
                     (And (AP 0,
                       And (True, Exists (Next (And (True, True))))),
                     Or
                      (And (True,
                        And (True,
                         Exists
                          (Next
                            (And (True,
                              Or
                               (Exists
                                 (Until (And (AP 1, True),
                                   And (AP 0, Exists (Globally True)))),
                               Not True)))))),
                      Not True))))))),
           Not True)))))),
  Or
   (And (AP 1,
     And
      (Or (And (AP 0, And (True, Exists (Next (And (True, True))))),
        Or
         (And (True,
           And (True,
            Exists
             (Next
               (And (True,
                 Or
                  (Exists
                    (Until (And (AP 1, True),
                      And (AP 0, Exists (Globally True)))),
                  Not True)))))),
         Not True)),
      Exists
       (Next
         (And (AP 1,
           Or
            (Exists
              (Until
                (And (AP 1,
                  Or
                   (And (AP 0, And (True, Exists (Next (And (True, True))))),
                   Or
                    (And (True,
                      And (True,
                       Exists
                        (Next
                          (And (True,
                            Or
                             (Exists
                               (Until (And (AP 1, True),
                                 And (AP 0, Exists (Globally True)))),
                             Not True)))))),
                    Not True))),
                And (AP 2,
                 Exists
                  (Globally
                    (Or
                      (And (AP 0,
                        And (True, Exists (Next (And (True, True))))),
                      Or
                       (And (True,
                         And (True, Exists (Next (And (True, ...))))),
                       ...))))))),
            ...)))))),
   ...)))
*)
