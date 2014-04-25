(** * Teorija tipov in λ-račun. *)

(** Tipi so posplošitev množic, topološki prostorov in podatkovnih tipov. Naivno si jih
    lahko predstavljamo kot množice. Dejstvo, da ima izraz [e] tip [A] pišemo [e : A].

    Razne konstrukcije tipov se vedno uvede po istem vzorcu:

    - _formacija_: kako se naredi nov tip

    - _vpeljava_: kako se naredi ali sestavi elemente tipa (konstruktorji)

    - _upraba_: kako se elemente uporabi ali razstavi na sestavne dele (eliminatorji)

    - _enačbe_: kakšne enačbe povezujejo konstruktorje in eliminatorje
*)

(** ** Funkcije

  Za vsaka dva tipa [A] in [B] lahko tvorimo tip funkcij:

  - _formacija_: če sta [A] in [B] tipa, je tudi [A -> B] tip

  - _vpeljava_: če je [x : A] spremenljivka tipa [A] in [t : B] izraz tipa [B],
    odvisen od [x], potem je [fun (x : A) => t] tipa [A -> B]. Izrazu [fun ...]
    pravimo _λ-abstrakcija_, ker se v logiki piše $\lambda x : A . t$.

  - _uporaba_: če je [f : A -> B] in [e : A] potem je [f e : B]. Pravimo, da smo
    funkcijo [f] aplicirali na argumentu [e].

  - _enačbe_:

    - _pravilo $\beta$_: [(fun (x : A) => t) e = t{e/x}] kjer zapis "[t{e/x}]" pomeni,
      da v izrazu [t] vstavimo [e] namesto [x].

    - _pravilo $\eta$_: [(fun (x : A) => f x) = f]
*)
   
(** ** Kartezični produkt

    Da bomo lahko počeli kaj zanimivega, vpeljemo še kartezični produkt tipov:

    - _formacija_: če sta [A] in [B] tipa, je [A * B] tip (matematični zapis $A \times B$)

    - _vpeljava_: če je [a : A] in [b : B], potem je [(a,b) : A * B], _urejeni par_

    - _uporaba_: če je [p : A * B], potem imamo

      - _prva projekcija_: [fst p : A]
      - _druga projekcija_: [snd p : B]

    - enačbe, pri čemer je [a : A], [b : B] in [p : A * B]:
      - [fst (a, b) = a]
      - [snd (a, b) = b]
      - [p = (fst p, snd p)]

    Poznamo še enotski tip:

    - _formacija_: [unit] je tip
    - _vpeljava_: [tt : unit]
    - _uporaba_: pravil za uporabo ni
    - _enačbe_: če je [u : unit], je [u = tt].
*)

(** V Coqu lahko datoteko razdelimo na posamične razdelke z [Section X.] in [End X.] *)
Section RazneFunkcije.

  (* Predpostavimo, da imamo tipe [A], [B] in [C]. *)
  Context {A B C : Type}.

  Definition vaja1_1 : A * B -> B * A :=
    fun (u : A * B) => (snd u, fst u).
                                  
  Definition vaja1_2 : (A * B) * C -> A * (B * C) :=
    fun (p : (A*B)*C) => (fst (fst p), (snd (fst p), snd p)).

  Definition vaja1_3 : A -> (B -> A):=
    fun (a:A) => (fun(b:B) => a).
  
  Definition vaja1_4 : (A -> B -> C) -> (A -> B) -> (A -> C):=
    fun (f: A -> B -> C) => (fun (g : A -> B) => (fun (a:A) => (f a) (g a))).

  Definition vaja1_5 : (A * B -> C) -> (A -> (B -> C)) :=
    fun (f:A * B -> C) => fun (a:A) => fun(b:B) => f (a,b).
  
  
  Definition vaja1_6 : (A -> (B -> C)) -> (A * B -> C) :=
    fun (f : A -> (B -> C)) => (fun (p:A*B) => f (fst p) (snd p)).

  Definition vaja1_7 : unit * A -> A :=
    fun (p : unit*A) => snd p.

  Definition vaja1_8 : A -> unit * A :=
    fun (a:A) => (tt,a).

Print vaja1_1.

End RazneFunkcije.

(** Ko zapremo razdelek [RazneFunkcije] nimamo več predpostavke, da so [A], [B], [C] tipi,
    vse definicije iz razdelka pa postanejo funkcije z dodatnimi parametri [A], [B], [C]. *)
Print vaja1_1.

(** Coq pravi: "Arguments [A], [B] are implicit and maximally inserted". To pomeni,
    da jih ni treba podati, ko uporabimo funkcijo [vaja1_1]. *)
Eval compute in vaja1_1 (42, false).

(* Če želimo eksplicitno nastaviti tudi [A] in [B], pišemo [@vaja1_1] namesto [vaja1_1]: *)
Eval compute in @vaja1_1 nat bool (42, false).

(** ** Izomorfni tipi

   Pravimo, da sta tipa [X] in [Y] izomorfna, če obstajata [f : X -> Y] in
   [g : Y -> X], da velja [g (f x) = x] za vse [x : X] in [f (g y) = y] za vse [y : Y].
*)
Definition iso (X : Type) (Y : Type) :=
  exists (f : X -> Y) (g : Y -> X),
    (forall x : X, g (f x) = x) /\ (forall y : Y, f (g y) = y).

(** V Coqu lahko uvedemo prikladno notacijo za izomorfizem. *)
Notation "X <~> Y" := (iso X Y) (at level 100).

Section Izomorfizmi1.
  (** Predpostavimo, da imamo tipe [A], [B] in [C]. *)
  Context {A B C : Type}.

  (** Dokaži, da so naslednji tipi izomorfni. *)

  Lemma vaja2_1 : A * B <~> B * A.
  Proof.
    unfold iso.
    exists vaja1_1, vaja1_1.
    unfold vaja1_1.
    simpl.
    tauto.
  Qed.

  Lemma vaja2_2 : (A * B) * C <~> A * (B * C).
  Proof.
    unfold iso.
    exists vaja1_2.
    exists (fun (p : A*(B*C)) => ((fst p, fst (snd p)),snd (snd p))).
    simpl.
    tauto.
  Qed.

  Lemma vaja2_3 : unit * A <~> A.
  Proof.
    unfold iso.
    exists vaja1_7, vaja1_8.
    split.
    - intro.
      destruct x.
      simpl.
      destruct u.
      tauto.
    - intro.
      tauto.
  Qed.

  (** Pravimo, da sta funkciji [f g : X -> Y] _enaki po točkah_, če velja [forall x : X, f
      x = g x]. Aksiom _funkcijske ekstenzionalnosti_ pravi, da sta funkciji enaki,
      če sta enaki po točkah. Coq ne verjame v ta aksiom, zato ga po potrebi predpostavimo. 
      Najprej ga definirajmo. *)
  Definition funext :=
    forall (X Y : Type) (f g : X -> Y), (forall x, f x = g x) -> f = g.

  (** S pomočjo ekstenzionalnosti lahko dokažemo nekatere izomorfizme. *)
  Lemma vaja2_4 (F : funext) : (A * B -> C) <~> (A -> (B -> C)).
  Proof.
    unfold iso.
    exists vaja1_5,vaja1_6.
    split.
    -  intro f.
       apply F.
       tauto.
    - intro f.
      apply F.
      tauto.
  Qed.

  Lemma vaja2_5 (F : funext) : (unit -> A) <~> A.
  Proof.
    unfold iso.
    exists (fun (h : unit -> A) => h tt), ( fun (a:A)(_ : unit) => a ).
    split.
    - intro h.
      apply F.
      intros [].
      reflexivity.
    - tauto.
  Qed.

  Lemma vaja2_6 (F : funext) : (A -> unit) <~> unit.
  Proof.
    unfold iso.
    exists (fun (_: A-> unit) => tt), (fun (_:unit) => fun (_:A) => tt).
    split.
    - intro f.
      apply F.
      intro x.
      destruct f.
      reflexivity.
    - intros [].
      reflexivity.
  Qed.
End Izomorfizmi1.

(** ** Vsota tipov

   Vsota tipov je kot disjunktna unija v teorijo množic ali koprodukt v kategorijah:

   - _formacija_: če sta [A] in [B] tipa, je [A + B] tip

   - _vpeljava_:

      - če je [a : A], potem je [inl a : A + B]
      - če je [b : B], potem je [inr b : A + B]

   - _uporaba_: če pri predpostavki [x : A] velja [u(x) : C] in
     če pri predpostavki [y : B] velja [v(y) : C] in če je [t : A + B], potem
     ima
     [(match t with
       | inl x => u(x)
       | inr y => v(y)
      end)]
     tip [C].

   - _enačbe_:

      - [match (inl a) with
         | x => u(x)
         | y => v(y)
         end] je enako [u(a)].

      - [match (inr b) with
         | x => u(x)
         | y => v(y)
         end] je enako [v(b)].

      - [match t with
         | inl x => inl x
         | inr y => inr y
         end] je enako [t].

*) 

(** ** Prazen tip

    Nekoliko bolj nenavaden je prazen tip:

    - _formacija_: [Empty_set] je tip
   
    - _vpeljava_: ni pravil za uporabo

    - _uporaba_: če [t : Empty_set], potem ima [match t with end] tip [A]

    - _enačbe_: [match t with end] je enako [a] za vse [a : A]
*)

Section FunkcijeVsote.
  (** Predpostavimo, da imamo tipe [A], [B] in [C]. *)
  Context {A B C : Type}.

  Definition vaja3_1 : (A + B -> C) -> (A -> C) * (B -> C):=
    fun (f : A+B -> C) => 
       (fun (a:A) => f (inl a),
        fun (b:B) => f (inr b)).

  (* S stavkom match obravnavmo element, ki je vsota tipov. *)

  Definition vaja3_2 : A + B -> B + A :=
    fun u : A+B => 
       match u with
         | inl x => inr x
         | inr y => inl y
       end.

  Definition vaja3_3 : (A + B) * C -> A * C + B * C :=
    fun p : (A+B)*C => match p with
       | (inl a,c) => inl (a,c)
       | (inr b,c) => inr (b,c)
    end.
  
  Definition vaja3_4 : A * C + B * C -> (A + B) * C:=
    fun (u : A*C + B*C) => match u with
      | inl (a,c) => (inl a,c)
      | inr (b,c) => (inr b,c)
    end.
  

  Definition vaja3_5 : (A -> C) * (B -> C) -> (A + B -> C):=
    fun (p : (A-> C) * (B-> C)) => 
        fun (u : A+B) => match u with
          | inl a => (fst p) a
          | inr b => (snd p) b
        end.

  Definition vaja3_6 : Empty_set -> A :=
    fun (t : Empty_set) => match t with end.

  Definition vaja3_7 : Empty_set + A -> A:=
    fun (u : Empty_set +A) => match u with
      | inl t => match t with end
      | inr a => a
    end.

  Definition vaja3_8 : A -> ((A -> Empty_set) -> Empty_set) := 
    fun (a :A ) => fun ( f: A -> Empty_set) => f a.

  Definition vaja3_9 : A + (A -> Empty_set) -> (((A -> Empty_set) -> Empty_set) -> A) := 
    fun (u : A + (A -> Empty_set)) => 
        fun (v : (A -> Empty_set) -> Empty_set ) => match u with
          | inl a => a
          | inr f => match (v f) with end
        end.

End FunkcijeVsote.

Section Izomorfizmi2.
  (** Sam ugotovi, kje potrebuješ funkcijsko ekstenzionalnost. *)

  Context {A B C : Type}.

  Definition vaja4_1 : A + B <~> B + A.
  Proof.
    unfold iso.
    exists vaja3_2,vaja3_2.
    split.
    - intro x.
      tauto.
    - intro y.
      tauto.
  Qed.

  Definition vaja4_2 : (A + B) * C <~> A * C + B * C.
  Proof.
    unfold iso.
    exists vaja3_3,vaja3_4.
    split.
    - intro x.
      tauto.
    - intro y.
      tauto.
  Qed.

  Definition vaja4_3 (F:funext) : (A + B -> C) <~> (A -> C) * (B -> C).
  Proof.
    unfold iso.
    exists vaja3_1,vaja3_5.
    split.
    - intro x.
      apply F.
      intro y.
      tauto.
    - intro x.
      tauto.
      
  Qed.

  Definition vaja4_4 : Empty_set + A <~> A.
  Proof.
    unfold iso.
    exists vaja3_7, (fun (a:A) => inr a ).
    tauto.
  Qed.

  Definition vaja4_5 (F:funext) (a:A): (A -> Empty_set) <~> Empty_set.
  Proof.
    unfold iso.
    exists  (fun (f:A -> Empty_set) => f a ).
    exists  (fun (t:Empty_set) => match t with end).
    split.
    - intro x.
      apply F.
      intro y.
      destruct x.
    -  intro y.
      tauto.
    
  Qed.

  Definition vaja5_5 (F:funext): (Empty_set -> A) <~> unit.
  Proof.
    unfold iso.
    exists (fun (f: Empty_set -> A) => tt).
    exists (fun (x:unit) => fun(t:Empty_set) => match t with end).
    split.
    - intro x.
      apply F.
      tauto.
    - intros [].
      reflexivity.
  Qed.

End Izomorfizmi2.

Section Zabava.
  (** Pa še neka vaj za zabavo. *)
  Context {A B : Type}.

  (* Koliko funkcij A * B -> A + B lahko definiraš? dve *)  
  Definition vaja5_1_XX : A * B -> A + B.
  Admitted.

  (* Koliko funkcij tipa (A * A) * A -> A * A lahko definiraš? šest*)
  Definition vaja5_2_XX : (A * A) * A -> A * A.
  Admitted.

  (* Koliko funkcij tipa (A -> A) -> (A -> A) lahko definiraš? neskončno*)
  Definition vaja5_3_XX : (A -> A) -> (A -> A).
  Admitted.

End Zabava.
