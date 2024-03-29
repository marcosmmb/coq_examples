(** * Indu\u00e7\u00e3o em Coq *)

Add LoadPath "/Users/marcosmonteiro/desktop/coq".
Require Export aula05_inducao.
Module NatList.

(* ############################################### *)
(** * Pares de n\u00fameros *)

(** A seguinte declara\u00e7\u00e3o pode ser lida como
    "s\u00f3 existe uma maneira de construir um
    par de n\u00fameros, que \u00e9 aplicando o construtor
    [pair] a dois argumentos do tipo [nat]" *)

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Check (pair 3 5).

(** Definindo fun\u00e7\u00f5es para pares.
    Observe o casamento de padr\u00e3o. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(* Definindo uma nota\u00e7\u00e3o mais conveniente. *)

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

(* Observe que \u00e9 poss\u00edvel, inclusive,
   usar esta sintaxe no casamento de padr\u00f5es. *)

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(** Algumas provas associadas a pares. *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  intros. simpl. reflexivity.
Qed.

(** Observe que o pr\u00f3ximo teorema representa
    o mesmo fato, mas [reflexivity] n\u00e3o
    \u00e9 suficiente para concluir esta prova. *)

Theorem surjective_pairing_stuck :
  forall (p : natprod),
    p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

(** \u00c9 preciso expor a estrutura de [p], tal
    que [simpl] possa realizar casamento de
    padr\u00e3o. [destruct] permite fazer isto. *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity.
Qed.

(** **** Exercise: (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity.
Qed.

(* ############################################### *)
(** * Lista de n\u00fameros *)

(** Defini\u00e7\u00e3o de uma lista de n\u00fameros. *)

Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

(** Exemplo de uma lista com 3 elementos. *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** Definindo uma nota\u00e7\u00e3o mais conveniente. *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** As defini\u00e7\u00f5es a seguir s\u00e3o equivalentes. *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** Definindo fun\u00e7\u00f5es para listas. *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Example test_repeat1 :
  repeat 5 3
  = [5;5;5].
Proof. simpl. reflexivity. Qed.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:
[1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. simpl. reflexivity. Qed.
Example test_app2:
nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3:
[1;2;3] ++ nil = [1;2;3].
Proof. simpl. reflexivity. Qed.

(** Na defini\u00e7\u00e3o a seguir, observe o
    valor [default]. *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:
hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2:
hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl:
tl [1;2;3] = [2;3].
Proof. simpl. reflexivity. Qed.

(** **** Exercise: (list_funs)  *)
(** Complete as defini\u00e7\u00f5es de [nonzeros],
    [oddmembers] e [countoddmembers]. Os testes
    mostram o comportamento esperado. *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t =>
     match h with
     | O => nonzeros t
     | _ => h :: (nonzeros t)
     end
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => 
    match oddb h with
    | true => h :: oddmembers t
    | false => oddmembers t
    end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat
(* SUBSTITUA COM ":= _sua_defini\u00e7\u00e3o_ ." *). Admitted.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
(* COMPLETE AQUI *) Admitted.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
(* COMPLETE AQUI *) Admitted.

Example test_countoddmembers3:
  countoddmembers nil = 0.
(* COMPLETE AQUI *) Admitted.

(* ############################################### *)
(** * Representando multiconjuntos como listas *)

Definition bag := natlist.

(** **** Exercise: (bag_functions)  *)
(** Complete as defini\u00e7\u00f5es de: [count], [sum],
    [add], e [member] para multiconjuntos (bags).
    Os testes mostram o comportamento esperado. *)

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => O
  | h :: t =>
    match beq_nat h v with
    | true => S (count v t)
    | false => (count v t)
    end
  end.

Example test_count1:
  count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2:
  count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

(** A opera\u00e7\u00e3o [sum] em multiconjuntos \u00e9 similar
    ao conceito de [union] de conjuntos: [sum a b]
    cont\u00e9m todos os elementos de [a] e [b].

    Observe que a pr\u00f3xima defini\u00e7\u00e3o n\u00e3o possui
    nome para os par\u00e2metros, mas somente seus tipos.
    Al\u00e9m disto, a defini\u00e7\u00e3o n\u00e3o \u00e9 recursiva. Portanto,
    [sum] precisa ser definida em fun\u00e7\u00e3o de defini\u00e7\u00f5es
    passadas. *)

Definition sum : bag -> bag -> bag := app.

Example test_sum1:
  count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := v :: s.

Example test_add1:
  count 1 (add 1 [1;4;1]) = 3. 
Proof. simpl. reflexivity. Qed.

Example test_add2:
  count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

(** Observe que a pr\u00f3xima defini\u00e7\u00e3o
    tamb\u00e9m n\u00e3o \u00e9 recursiva. *)

Definition member (v:nat) (s:bag) : bool :=
  match count v s with
  | O => false
  | _ => true
  end.

Example test_member1:
  member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_member2:
  member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

(** **** Exercise: (bag_theorem)  *)
(** Prove o seguinte teorema. Talvez voc\u00ea
    precise provar um teorema auxiliar. *)



Theorem bag_theorem :
  forall (v : nat) (b : bag),
    (count v (add v b)) = (1 + (count v b)).
Proof.
  intros. simpl. Admitted.


(* ############################################### *)
(** * Raciocinando sobre listas *)

(** Algumas propriedades podem ser provadas
    somente com [reflexivity]. *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof.
  Print app. simpl. reflexivity.
Qed.

(** \u00c0s vezes, ser\u00e1 preciso fazer an\u00e1lise de casos. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  (* Observe a quantidade de elementos
     da segunda lista do destruct. *)
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    simpl. reflexivity.
  - (* l = cons n l' *)
    Print length. simpl. reflexivity.
Qed.

(** \u00c0s vezes, ser\u00e1 preciso fazer indu\u00e7\u00e3o. *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    simpl. reflexivity.
  - (* l1 = cons n l1' *)
    Print app. simpl.
    rewrite -> IHl1'. reflexivity.
Qed.

(** Considere a seguinte defini\u00e7\u00e3o de [rev]. *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:
  rev [1;2;3] = [3;2;1].
Proof. simpl. reflexivity.  Qed.
Example test_rev2:
  rev nil = nil.
Proof. reflexivity.  Qed.

(** Vamos tentar provar a seguinte afirma\u00e7\u00e3o.
    Observe que ficamos "travados" no segundo caso. *) 

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    simpl. reflexivity.
  - (* l = n :: l' *)
    Print rev. simpl. rewrite <- IHl'.
    (* Como continuar a partir daqui? *)
Abort.

(** Vamos definir um teorema auxiliar a partir
    do ponto em que ficamos "travados" no
    teorema anterior. Contudo, vamos tornar
    o teorema auxiliar o mais geral poss\u00edvel:
    [l1] e [l2] no lugar de [rev l'] e [n]. *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - simpl. (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

(** Agora concluimos a prova de [rev_length]. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - simpl. (* l = nil *)
    reflexivity.
  - (* l = cons *)
    (* Observe o rewrite  com duas t\u00e1ticas *)
    simpl. rewrite -> app_length, plus_comm.
    simpl. rewrite -> IHl'. reflexivity.
Qed.

(** **** Exercise: (list_exercises)  *)
(** Prove os seguintes teoremas. *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
(* COMPLETE AQUI *) Admitted.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
(* COMPLETE AQUI *) Admitted.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros. induction l1.
  - simpl. reflexivity.
  - destruct n.
    + simpl. rewrite IHl1. reflexivity.
    + simpl. rewrite IHl1. reflexivity.
Qed.

(** **** Exercise: (beq_natlist)  *)
(** Complete a defini\u00e7\u00e3o de [beq_natlist], que
    compara listas de n\u00fameros. Veja os exemplos.
    Em seguida, prove o teorema [beq_natlist_refl]. *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l1 with
  | [], [] => true
  | _, [] => false
  | [], _ => false
  | h1 :: t1, h2 :: t2 => 
    match beq_nat h1 h2 with
    | true => beq_natlist t1 t2
    | false => false
    end
  end.


Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
(* COMPLETE AQUI *) Admitted.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
(* COMPLETE AQUI *) Admitted.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
(* COMPLETE AQUI *) Admitted.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros. induction l.
  - simpl. reflexivity.
Abort.

(* ############################################### *)
(** * Options *)

(** Considere a seguinte implementa\u00e7\u00e3o de uma
    fun\u00e7\u00e3o que retorna o i-\u00e9simo elemento
    de uma lista. *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42  (* um valor arbitr\u00e1rio! *)
  | a :: l' => match beq_nat n O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

(** Outra alternativa seria considerar um
    elemento padr\u00e3o -- ver defini\u00e7\u00e3o de [hd].

    Uma melhor solu\u00e7\u00e3o \u00e9 definir um "option".
    Similar ao conceito de "maybe" em Haskell. *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

(** Veja agora a fun\u00e7\u00e3o [nth_error]. *)

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 :
  nth_error [4;5;6;7] 0 = Some 4.
Proof. simpl. reflexivity. Qed.
Example test_nth_error2 :
  nth_error [4;5;6;7] 3 = Some 7.
Proof. simpl. reflexivity. Qed.
Example test_nth_error3 :
  nth_error [4;5;6;7] 9 = None.
Proof. simpl. reflexivity. Qed.

(** A seguir, uma outra possibilidade de
    implementa\u00e7\u00e3o de [nth_error] usando "if". *)

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a
               else nth_error' l' (pred n)
  end. 

(** No entanto, cuidado com o "if". *)

Inductive tipo : Type :=
  | cons1 : tipo
  | cons2 : tipo.

Definition beq_tipo (n m : nat) : tipo :=
  if beq_nat n m then cons2 else cons1.

Definition teste_if (n m : nat) : bool :=
  if beq_tipo n m then true
  else false.

Compute (teste_if 2 2).

(** O "if" s\u00f3 pode ser aplicado a tipos
    indutivos com dois construtores. *)

(** A fun\u00e7\u00e3o a seguir retira o [nat] encapsulado
    no [natoption]. Observe aqui o uso do default. *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** Exercise: (hd_error)  *)
(** Use a ideia do "option" e atualize
    a defini\u00e7\u00e3o da fun\u00e7\u00e3o [hd]. *)

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.


Example test_hd_error1 : hd_error [] = None.
Proof. simpl. reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof. simpl. reflexivity. Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. simpl. reflexivity. Qed.

(** **** Exercise: (option_elim_hd)  *)
(** Prove o seguinte teorema relacionando
    [hd_error] com [hd]. *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  Print hd. Print option_elim.
  intros. destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

End NatList.

(* ############################################### *)
(** * Mapeamentos parciais *)

(** Veja a seguinte defini\u00e7\u00e3o de mapeamentos parciais,
    similar aos tipos map ou dictionary das
    principais linguagens de programa\u00e7\u00e3o.

    Inicialmente, definimos a "chave": o [id]. *)

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

(** **** Exercise: (beq_id_refl)  *)
Theorem beq_id_refl :
  forall x, true = beq_id x x.
Proof.
  intros. destruct x. simpl. induction n.
  - simpl. reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

(** Agora, o tipo de mapeamentos parciais *)

Module PartialMap.
Export NatList.
  
Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id -> nat -> partial_map -> partial_map.

(** Logo, existem duas maneiras de construir
    [partial_map]: usando o construtor [empty],
    representando o mapeamento vazio; usando
    o construtor [record], passando uma chave,
    um n\u00famero e um mapeamento existente.

    A fun\u00e7\u00e3o [update] atualiza um mapeamento.
    Observe que, conceitualmente, o valor antigo,
    caso exista, \u00e9 mantido no mapeamento. O
    primeiro valor ser\u00e1 o mais recente. *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Example test_partial_map1 :
  (update empty (Id 0) 3)
  = (record (Id 0) 3 empty).
Proof.
    simpl. reflexivity.
Qed.

Example test_partial_map2 :
  (update (record (Id 0) 2 empty) (Id 0) 3)
  = (record (Id 0) 3 (record (Id 0) 2 empty)).
Proof.
    simpl. reflexivity.
Qed.

(** A fun\u00e7\u00e3o [find] procura por um valor em
    um mapeamento. Se houver m\u00faltiplos mapeamentos,
    retorna o primeiro. *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.

(** **** Exercise: (update_eq)  *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
(* COMPLETE AQUI *) Admitted.

(** **** Exercise: (update_neq)  *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false ->
    find x (update d y o) = find x d.
Proof.
(* COMPLETE AQUI *) Admitted.

End PartialMap.

(** Veja a diferen\u00e7a entre os dois pr\u00f3ximos
    comandos. O segundo garante que a
    express\u00e3o \u00e0 direita da igualdade
    seja igual (sintaticamente) ao
    segundo operando da soma. *)

Search (_ + _ = _).
Search (_ + ?x = ?x).

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - Lists
  https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html
*)
