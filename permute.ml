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
  
		 
		 
