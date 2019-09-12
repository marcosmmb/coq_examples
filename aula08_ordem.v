(** * Indu\u00e7\u00e3o em Coq *)

Set Warnings "-notation-overridden,-parsing".
Add LoadPath "/Users/marcosmonteiro/desktop/coq".
Require Export aula07_poli.

(* ############################################### *)
(** * Fun\u00e7\u00f5es de alta ordem *)

(** Assim como outras linguagens funcionais,
    \u00e9 poss\u00edvel passar fun\u00e7\u00f5es como argumentos,
    retornar fun\u00e7\u00f5es e armazenar fun\u00e7\u00f5es em
    estruturas de dados. *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.
(* ===> doit3times :
        forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times:
  doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times':
  doit3times negb true = false.
Proof. reflexivity.  Qed.

(** Uma fun\u00e7\u00e3o mais \u00fatil \u00e9 [filter]. *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

Example test_filter1:
  filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X)
                       : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** \u00c9 poss\u00edvel definir fun\u00e7\u00f5es "on the fly"
    (an\u00f4nimas); ou seja, sem dar um nome a elas.

    O exemplo a seguir n\u00e3o precisa da defini\u00e7\u00e3o
    de [length_is]. *)

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(** **** Exercise: (partition)  *)
(** Use [filter] para escrever a fun\u00e7\u00e3o [partition]:

      partition : forall X : Type,
                  (X -> bool) -> list X
                  -> list X * list X

    Dado um conjunto [X], uma fun\u00e7\u00e3o teste [X -> bool],
    e uma [list X], a fun\u00e7\u00e3o [partition] retorna um
    par de listas: o primeiro \u00e9 uma sublista com
    os elementos que satisfazem o teste; o segundo,
    com aqueles que n\u00e3o satisfazem o teste. *)

Definition partition {X : Type} (test : X -> bool)
                     (l : list X) : list X * list X
(* SUBSTITUA COM ":= _sua_defini\u00e7\u00e3o_ ." *). Admitted.

Example test_partition1:
  partition oddb [1;2;3;4;5]
  = ([1;3;5], [2;4]).
Proof.
 (* COMPLETE AQUI *) Admitted.

Example test_partition2:
  partition (fun x => false) [5;9;0]
  = ([], [5;9;0]).
Proof.
 (* COMPLETE AQUI *) Admitted.

(** Outra fun\u00e7\u00e3o \u00fatil \u00e9 [map]. *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X)
             : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1:
  map (fun x => plus 3 x) [2;0;2]
  = [5;3;5].
Proof. reflexivity.  Qed.

(** Observe que as listas de entrada e sa\u00edda
    podem ter tipos diferentes. *)

Example test_map2:
  map oddb [2;1;2;5]
  = [false;true;false;true].
Proof. reflexivity.  Qed.

Example test_map3:
  map length [ [2;3] ; [] ; [3] ]
  = [2;0;1].
Proof. reflexivity. Qed. 

(** **** Exercise: (map_rev)  *)
(** Prove que [map] e [rev] comutam. Talvez
    voc\u00ea precise definir um lemma auxiliar. *)

Theorem map_rev : forall (X Y : Type)
  (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
 (* COMPLETE AQUI *) Admitted.

(** Outra fun\u00e7\u00e3o \u00fatil \u00e9 [fold]. Esta fun\u00e7\u00e3o insere
    um operador bin\u00e1rio [f] entre cada par de elementos
    de uma certa lista. \u00c9 preciso definir um elemento
    base / inicial. Por exemplo, fold plus [1;2;3;4] 0
    retorna 1 + (2 + (3 + (4 + 0))). *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X)
              (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true
  = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] []
  = [1;2;3;4].
Proof. reflexivity. Qed.

(** \u00c9 poss\u00edvel definir fun\u00e7\u00f5es que retornam fun\u00e7\u00f5es. *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 :
  ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 :
  (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** A fun\u00e7\u00e3o [plus] \u00e9 um exemplo disto. *)

Check plus.
(* ==> nat -> nat -> nat *)

(** O operador [->] \u00e9 bin\u00e1rio. Logo, [nat -> nat -> nat]
    significa [nat -> (nat -> nat)]. Isto permite
    aplica\u00e7\u00e3o parcial de [plus]. Al\u00e9m disto, processar
    uma lista de argumentos com fun\u00e7\u00f5es que retornam
    fun\u00e7\u00f5es \u00e9 conhecido como "currying". *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :
  plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :
  doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :
  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

Module Exercises.

(** **** Exercise: (fold_length)  *)
(** Muitas fun\u00e7\u00f5es podem ser implementadas em termos
    de [fold]. Por exemplo, a seguir uma defini\u00e7\u00e3o
    alternativa para [length]. *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(** Prove a corretude de [fold_length]. *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
   (* COMPLETE AQUI *) Admitted.

(** **** Exercise: (fold_map)  *)
(** Tamb\u00e9m podemos definir [map] em termos de [fold].
    Complete a defini\u00e7\u00e3o [fold_map] e prove sua corretude. *)

Definition fold_map {X Y:Type} (f : X -> Y)
                    (l : list X) : list Y
(* SUBSTITUA COM ":= _sua_defini\u00e7\u00e3o_ ." *). Admitted.

Theorem fold_map_correct :
  forall (X Y : Type) (f : X -> Y) (l : list X),
    fold_map f l = map f l.
Proof.
   (* COMPLETE AQUI *) Admitted.

End Exercises.

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - Functions as Data
  https://softwarefoundations.cis.upenn.edu/lf-current/Poly.html
*)
