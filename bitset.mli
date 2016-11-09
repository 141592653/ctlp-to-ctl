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
end

(** Implémentation de [SET] étant donné un [F:FIN]. *)
module Make (F : FIN) : SET with type elt = F.t
