(** * Programa\u00e7\u00e3o funcional em Coq *)

(* ############################################### *)
(** * Instala\u00e7\u00e3o *)

(** Passo-a-passo:
  1. Instalar OPAM: gerenciador de pacotes OCaml
  [passo j\u00e1 realizado pelo helpdesk no G3]
  Link: http://opam.ocaml.org/doc/Install.html
  a) wget https://raw.github.com/ocaml/opam/master/shell/opam_installer.sh -O - | sh -s /usr/local/bin

  2. Instalar Coq 8.8.1
  Link: https://coq.inria.fr/opam/www/using.html
  a) abrir o terminal (ctrl + alt + t)
  b) export OPAMROOT=~/opam-coq.8.8.1
     # diret\u00f3rio de instala\u00e7\u00e3o no home do usu\u00e1rio
  c) opam init -n --comp=4.02.3 -j 4
     # 4 \u00e9 o n\u00famero de n\u00facleos de processamento
  d) opam repo add coq-released http://coq.inria.fr/opam/released
  e) opam install coq.8.8.1 && opam pin add coq 8.8.1

  3. Instalar CoqIDE
  Link: https://coq.inria.fr/opam/www/using.html
  a) opam install coqide
  
  4. Para rodar a IDE, \u00e9 preciso reexecutar os
  seguintes comandos sempre que abrir um novo
  terminal:
  a) abrir o terminal (ctrl + alt + t)
  b) export OPAMROOT=~/opam-coq.8.8.1
     # diret\u00f3rio em que instalou Coq
  c) eval `opam config env`
     # configurar ambiente
  d) coqide &

  5. Para testar a instala\u00e7\u00e3o, abrir o arquivo
  01-introducao-exemplo.v e process\u00e1-lo at\u00e9 o final
  (ctrl + end). O texto deve ficar todo verde.

  Outra op\u00e7\u00e3o de IDE: Emacs + ProofGeneral
  Link: https://proofgeneral.github.io/

  Links \u00fateis:
  - https://github.com/coq/coq
  - https://github.com/coq/coq/wiki
  - https://github.com/coq/coq/wiki/The-Coq-FAQ
*)

(* ############################################### *)
(** * Pref\u00e1cio *)

(** Material baseado na s\u00e9rie Software Foundations
    https://softwarefoundations.cis.upenn.edu/. *)

(** Aspectos centrais deste material:
    - uso de l\u00f3gica para definir e provar
      afirma\u00e7\u00f5es precisas sobre programas
    - uso de um assistente de prova (Coq)
      para construir argumentos l\u00f3gicos rigorosos
    - programa\u00e7\u00e3o funcional como liga\u00e7\u00e3o
      entre programa\u00e7\u00e3o e l\u00f3gica *)

(** Coq: aspectos hist\u00f3ricos
    - Em desenvolvimento deste 1984
    - Poss\u00edveis origens do nome:
      - Tradi\u00e7\u00e3o francesa: Caml, Elan, PhoX, etc.
      - Calculus of Constructions
      - S\u00edmbolo nacional da Fran\u00e7a
      - Primeiras tr\u00eas letras de Thierry Coquand *)

(** Coq: aplica\u00e7\u00f5es em CS e matem\u00e1tica:
    - Plataforma para modelar PLs
      [instru\u00e7\u00f5es x86, C, etc.]
    - Ambiente para desenvolver HW/SW certificado
      [CompCert, CertiKos, RISC-V, etc.]
    - Ambiente para programa\u00e7\u00e3o funcional
      [Gallina]
    - Assistente de prova para l\u00f3gica de alta ordem
      [Primeira prova verificada formalmente
       do Teorema das 4 cores] *)

(* ############################################### *)
(** * Gallina: introdu\u00e7\u00e3o *)

(** Definindo novo tipo: conjunto de valores poss\u00edveis.
    - [day] \u00e9 o nome do tipo
    - a defini\u00e7\u00e3o [day] \u00e9 um elemento de [Type]
    - [:=] usado para preceder a defini\u00e7\u00e3o
    - [|] \u00e9 usado para separar elementos de [day]
*)

Inductive day : Type :=
  | monday    : day
  | tuesday   : day
  | wednesday : day
  | thursday  : day
  | friday    : day
  | saturday  : day
  | sunday    : day.

(** Definindo uma fun\u00e7\u00e3o que opera sobre dias.
    - [Definition] fun\u00e7\u00f5es n\u00e3o-recursivas
    - Tipos n\u00e3o precisam ser expl\u00edcitos
    - [:=] precede a defini\u00e7\u00e3o da fun\u00e7\u00e3o
    - A defini\u00e7\u00e3o pode ser feita por casamento
      de padr\u00e3o, como tamb\u00e9m chamada a outras fun\u00e7\u00f5es
    - [=>] representa o retorno quando [d]
      casa com uma das op\u00e7\u00f5es
 *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(** Validando a fun\u00e7\u00e3o definida:
    - [Compute]: avalia express\u00e3o
    - [Example]: define afirma\u00e7\u00e3o a ser verificada
      a) d\u00e1 um nome \u00e0 afirma\u00e7\u00e3o
      b) permite usar o modo de prova de Coq
         para verificar que a afirma\u00e7\u00e3o
         \u00e9 verdadeira (como um teste unit\u00e1rio)
    - Extrair programa funcional em OCaml ou Haskell
*)

Compute (next_weekday friday).
(* ==> monday : day *)

Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)
 
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

(** **** Exercise: (sinal) *)
(** Defina o tipo [sinal] que pode ser verde,
    amarelo ou vermelho. *)

(** **** Exercise: (next_sinal) *)
(** Defina a fun\u00e7\u00e3o [next_sinal] que muda a cor
    de um sinal para a pr\u00f3xima cor esperada *)

(** **** Exercise: (compute_sinal) *)
(** Use [Compute] para testar a defini\u00e7\u00e3o
    de [next_sinal]. *)

(** **** Exercise: (test_sinal) *)
(** Use [Example] para testar a defini\u00e7\u00e3o
    de [next_sinal]. Prove que sua
    afirma\u00e7\u00e3o \u00e9 verdadeira usando simpl.
    e reflexivity. *)

Inductive sinal : Type :=
  | verde : sinal
  | amarelo : sinal
  | vermelho : sinal.

Definition next_sinal (s:sinal) : sinal :=
  match s with
  | vermelho => amarelo
  | amarelo => verde
  | verde => vermelho
  end.

Compute (next_sinal vermelho).

Example test_sinal:
  (next_sinal (next_sinal vermelho)) = verde.
Proof. simpl. reflexivity. Qed.

(* =============================================== *)
(** ** Booleans *)

(** De forma similar, podemos definir o tipo booleano.
    - N\u00e3o confundir: booleano vs. True e False da l\u00f3gica *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

(** Definindo fun\u00e7\u00f5es sobre booleanos
    - Observe a sintaxe para v\u00e1rios par\u00e2metros *)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(** Teste unit\u00e1rios *)

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.

Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.

Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.

Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

(** \u00c9 poss\u00edvel definir uma sintaxe mais familiar
    usando [Notation] *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

(** **** Exercise: (nandb) *)
(** Defina nandb (usando casamento de padr\u00e3o e,
    em seguida, complete os testes unit\u00e1rios. *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1, b2 with
  | true, true => false
  | _, _ => true
  end.


Example test_nandb1:
(nandb true false) = true.
Proof. simpl. reflexivity.  Qed.

Example test_nandb2:
(nandb false false) = true.
Proof. simpl. reflexivity.  Qed.

Example test_nandb3:
(nandb false true) = true.
Proof. simpl. reflexivity.  Qed.

Example test_nandb4:
(nandb true true) = false.
Proof. simpl. reflexivity.  Qed.

(** **** Exercise: (nandb') *)
(** Defina nandb' usando as defini\u00e7\u00f5es [andb] e [negb] *)

Definition nandb' (b1:bool) (b2:bool) : bool
  (* SUBSTITUA COM ":= _sua_defini\u00e7\u00e3o_ ." *). Admitted.

(** Nas pr\u00f3ximas provas, observe o resultado do
    simpl. Tente antes desta t\u00e1tica, usar
    unfold nandb' (que obriga a expans\u00e3o da defini\u00e7\u00e3o
    de nandb'). *)

Example test_nandb'1:
(nandb' true false) = true.
(* COMPLETE AQUI *) Admitted.
Example test_nandb'2:
(nandb' false false) = true.
(* COMPLETE AQUI *) Admitted.
Example test_nandb'3:
(nandb' false true) = true.
(* COMPLETE AQUI *) Admitted.
Example test_nandb'4:
(nandb' true true) = false.
(* COMPLETE AQUI *) Admitted.

(** **** Exercise: (andb3)  *)
(** Defina a fun\u00e7\u00e3o [andb3]. Esta fun\u00e7\u00e3o deve
    retornar [true] quando todas suas entradas
    s\u00e3o [true], e [false] caso contr\u00e1rio *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
  (* SUBSTITUA COM ":= _sua_defini\u00e7\u00e3o_ ." *). Admitted.

Example test_andb31:
(andb3 true true true) = true.
(* COMPLETE AQUI *) Admitted.
Example test_andb32:
(andb3 false true true) = false.
(* COMPLETE AQUI *) Admitted.
Example test_andb33:
(andb3 true false true) = false.
(* COMPLETE AQUI *) Admitted.
Example test_andb34:
(andb3 true true false) = false.
(* COMPLETE AQUI *) Admitted.

(* =============================================== *)
(** ** Function Types *)

(** Toda express\u00e3o em Coq tem um tipo. O comando
    [Check] imprime o tipo de uma express\u00e3o. *)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(** A fun\u00e7\u00e3o [negb] \u00e9 tamb\u00e9m o valor de um dado, assim
    como [true] e [false]. Seu tipo \u00e9 chamado
    _function types_, e escrito usando setas *)

Check negb.
(* ===> negb : bool -> bool *)

(** [negb] \u00e9 uma fun\u00e7\u00e3o que dado um [bool],
    produz um [bool]. *)

Check andb.
(* ===> andb : bool -> bool -> bool *)

(** [andb] \u00e9 uma fun\u00e7\u00e3o que a partir de dois [bool],
    produz um [bool]. *)

(* =============================================== *)
(** ** Tipos compostos *)

(** Tipos definidos at\u00e9 ent\u00e3o: enumera\u00e7\u00f5es. Cada op\u00e7\u00e3o
    criada a partir de um certo _construtor_. *)

Inductive rgb : Type :=
  | red   : rgb
  | green : rgb
  | blue  : rgb.

(** A defini\u00e7\u00e3o a seguir possui o construtor [primary]
    que recebe um [rgb] e produz um [color]. *)

Inductive color : Type :=
  | black     : color
  | white     : color
  | primary   : rgb -> color.

Check black.

Check primary.

(** Definindo fun\u00e7\u00f5es sobre tipos compostos *)


Definition monochrome (c : color) : bool :=
  match c with
  | black     => true
  | white     => true
  | primary p => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black       => false
  | white       => false
  | primary red => true
  | primary _   => false
  end.

(** No exemplo acima, [primary _] tem o mesmo
    efeito de [primary p]. *)

(* =============================================== *)
(** ** M\u00f3dulos *)

(** Uma das maneiras de estruturar uma especifica\u00e7\u00e3o
    em Coq \u00e9 usar m\u00f3dulos. *)

Module NatPlayground.

(* =============================================== *)
(** ** N\u00fameros *)

(** Definindo um tipo usando construtores que recebem
    argumentos do tipo sendo definido. *)

(** N\u00fameros naturais
    - O: uma representa\u00e7\u00e3o do n\u00famero zero
    - S _: o sucessor de um n\u00famero natural *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(** Por isso que tipos s\u00e3o (potencialmente) indutivos:
    - [O] \u00e9 um n\u00famero natural
    - [S O] \u00e9 um n\u00famero natural
    - [S (S O)] \u00e9 um n\u00famero natural
    - [S (S false)] n\u00e3o \u00e9 um n\u00famero natural *)

(** Esta defini\u00e7\u00e3o \u00e9 uma representa\u00e7\u00e3o estrutural
    sem significado. O significado vem do seu uso *)

Inductive nat' : Type :=
  | stop : nat'
  | tick : nat' -> nat'.

(** Exemplo: fun\u00e7\u00e3o [pred] *)

Definition pred (n : nat) : nat :=
  match n with
  | O     => O
  | S n'  => n'
  end.

End NatPlayground.

(** Coq possui defini\u00e7\u00f5es para representar
    n\u00fameros de forma decimal *)

Check (S (S (S (S O)))).
(* ===> 4 : nat *)

(** Definindo a fun\u00e7\u00e3o [minustwo]. Observe
    os dois primeiros casos *)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).
(* ===> 2 : nat *)

Compute (minustwo 1).
(* ===> 0 : nat *)

(** Tipos dos construtores e das fun\u00e7\u00f5es
    para [nat] *)

Check S.
Check pred.
Check minustwo.

(** Apesar de todos serem valores, as duas
    \u00faltimas defini\u00e7\u00f5es possuem uma no\u00e7\u00e3o
    de computabilidade associada *)

(** Definindo fun\u00e7\u00f5es recursivas: [Fixpoint]. *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(** Definindo [oddb] em fun\u00e7\u00e3o de [evenb] e [negb]. *)

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1:    oddb 1 = true.
Proof. unfold oddb. simpl. reflexivity.  Qed.
Example test_oddb2:    oddb 4 = false.
Proof. simpl. reflexivity.  Qed.

(** Definindo fun\u00e7\u00f5es recursivas com
    v\u00e1rios par\u00e2metros *)

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

(** Testando a defini\u00e7\u00e3o *)
Compute (plus 3 2).
(* ===> 5 : nat *)

(** O passo-a-passo da computa\u00e7\u00e3o seria: *)

(*  [plus (S (S (S O))) (S (S O))]
==> [S (plus (S (S O)) (S (S O)))]
      pela segunda cl\u00e1sula do [match]
==> [S (S (plus (S O) (S (S O))))]
      pela segunda cl\u00e1sula do [match]
==> [S (S (S (plus O (S (S O)))))]
      pela segunda cl\u00e1sula do [match]
==> [S (S (S (S (S O))))]
      pela primeira cl\u00e1sula do [match]
*)

(** Outra nota\u00e7\u00e3o para v\u00e1rios par\u00e2metros
    do mesmo tipo *)

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity.  Qed.

(** Casamento de padr\u00e3o m\u00faltiplo *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

(** Definindo exponencia\u00e7\u00e3o: [exp] *)

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O   => S O
  | S p => mult base (exp base p)
  end.

(** **** Exercise: 1(factorial)  *)
(** Defina a fun\u00e7\u00e3o fatorial em Coq
       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)
                        (if n>0) *)

Fixpoint factorial (n:nat) : nat
  (* SUBSTITUA COM ":= _sua_defini\u00e7\u00e3o_ ." *). Admitted.

Example test_factorial1:
(factorial 3) = 6.
(* COMPLETE AQUI *) Admitted.

Example test_factorial2:
(factorial 5) = (mult 10 12).
(* COMPLETE AQUI *) Admitted.

(** As pr\u00f3ximas defini\u00e7\u00f5es definem uma sintaxe
    para adi\u00e7\u00e3o, subtra\u00e7\u00e3o e multiplica\u00e7\u00e3o
    - preced\u00eancia: [at level n], onde n 0..100
      menor valor indica maior preced\u00eancia      
    - associatividade: [left], [right] ou
                       [no] [associativity]
 *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.

Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.

Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).

(** Definindo se dois n\u00fameros s\u00e3o iguais: [beq_nat] *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(** Definindo menor ou igual: [leb] *)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity.  Qed.

Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity.  Qed.

Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

(** **** Exercise: (blt_nat)  *)
(** A fun\u00e7\u00e3o [blt_nat] testa se um n\u00famero \u00e9
    menor do que outro. Observe que a pr\u00f3xima
    defini\u00e7\u00e3o n\u00e3o \u00e9 recursiva. \u00c9 preciso definir
    [blt_nat] a partir de defini\u00e7\u00f5es passadas *)

Definition blt_nat (n m : nat) : bool
  (* SUBSTITUA COM ":= _sua_defini\u00e7\u00e3o_ ." *). Admitted.

Example test_blt_nat1:
(blt_nat 2 2) = false.
(* COMPLETE AQUI *) Admitted.

Example test_blt_nat2:
(blt_nat 2 4) = true.
(* COMPLETE AQUI *) Admitted.

Example test_blt_nat3:
(blt_nat 4 2) = false.
(* COMPLETE AQUI *) Admitted.

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - Pref\u00e1cio
  https://softwarefoundations.cis.upenn.edu/lf-current/Preface.html
  - Aspectos b\u00e1sicos (at\u00e9 o final de "Data and Functions")
  https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html
*)
