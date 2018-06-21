Module terms Import basics;

(* terms *)
[XX|Prop];
[XXeq|XX->XX->BB];
[XXeq_iff_Q:{p,q:XX}iff (is_tt (XXeq p q)) (Q p q)];

Goal {p,q|XX}(is_tt (XXeq p q))->Q p q;
intros; Refine fst (XXeq_iff_Q ??); Immed;
Save XXdecide;

Goal {p:XX}is_tt (XXeq p p);
intros; Refine snd (XXeq_iff_Q ??); Refine Q_refl;
Save XXrefl;

Goal {x,y:XX}Q (XXeq x y) (XXeq y x);
intros; Refine tt_or_ff (XXeq x y);
intros h; Qrepl (XXdecide h); Refine Q_refl;
intros h; Refine tt_or_ff (XXeq y x);
intros g; Qrepl (XXdecide g); Refine Q_refl;
intros g; Qrepl g; Qrepl h; Refine Q_refl;
Save XXsym;

Goal {x,y|XX}(is_tt (XXeq x y))->{z:XX}Q (XXeq x z) (XXeq y z);
intros;Qrepl XXdecide H;Refine Q_refl;
Save XXtrans;

Goal {x,y:XX}Q (if (XXeq x y) x y) y;
intros; Refine tt_or_ff (XXeq x y);
intros eqxy; Qrepl eqxy; Qrepl XXdecide eqxy; Refine Q_refl;
intros neqxy; Qrepl neqxy; Refine Q_refl;
Save if_XXeq_xy_lem;


Discharge XX;

[PP:Prop];                                                    (* Parameters *)
[PPeq:PP->PP->BB];
[PPeq_iff_Q:{p,q:PP}iff (is_tt (PPeq p q)) (Q p q)];
[PPs = LL|PP];                                       (* lists of parameters *)
[PPinf:{l:PPs}ex[p:PP] is_ff (member PPeq p l)];
[PPdecide : {p,q|PP}(is_tt (PPeq p q))->Q p q = XXdecide PPeq_iff_Q];
[PPrefl   : {p:PP}is_tt (PPeq p p) = XXrefl PPeq_iff_Q];
[PPsym    : {p,q:PP}Q (PPeq p q) (PPeq q p) = XXsym PPeq_iff_Q];
[PPtrans  : {x,y|PP}(is_tt (PPeq x y))->{z:PP}Q (PPeq x z) (PPeq y z)
                                = XXtrans PPeq_iff_Q];
[if_PPeq_pq_lem : {p,q:PP}Q (if (PPeq p q) p q) q
          = if_XXeq_xy_lem PPeq_iff_Q];

(* Variables *)
[VV:Prop];
[VVeq:VV->VV->BB];
[VVeq_iff_Q:{p,q:VV}iff (is_tt (VVeq p q)) (Q p q)];
[VVs = LL|VV];
[VVinf : {l:VVs}ex[v:VV] is_ff (member VVeq v l)];
[VVdecide : {p,q|VV}(is_tt (VVeq p q))->Q p q = XXdecide VVeq_iff_Q];
[VVrefl   : {p:VV}is_tt (VVeq p p) = XXrefl VVeq_iff_Q];
[VVsym    : {p,q:VV}Q (VVeq p q) (VVeq q p) = XXsym VVeq_iff_Q];
[VVtrans  : {x,y|VV}(is_tt (VVeq x y))->{z:VV}Q (VVeq x z) (VVeq y z)
                                = XXtrans VVeq_iff_Q];
[if_VVeq_xy_lem : {x,y:VV}Q (if (VVeq x y) x y) y
          = if_XXeq_xy_lem VVeq_iff_Q];

(* Sorts *)
[SS|Prop];
[SSeq:SS->SS->BB];
[SSs = LL|SS];
[SSeq_iff_Q:{p,q:SS}iff (is_tt (SSeq p q)) (Q p q)];
[SSdecide : {p,q|SS}(is_tt (SSeq p q))->Q p q = XXdecide SSeq_iff_Q];
[SSrefl   : {p:SS}is_tt (SSeq p p) = XXrefl SSeq_iff_Q];
[SSsym    : {p,q:SS}Q (SSeq p q) (SSeq q p) = XXsym SSeq_iff_Q];
[SStrans  : {x,y|SS}(is_tt (SSeq x y))->{z:SS}Q (SSeq x z) (SSeq y z)
                                = XXtrans SSeq_iff_Q];

(* A particular parameter *)
Goal p0: PP;
Refine PPinf (NIL|PP);
intros; Assumption;
Save;

(* raw terms *)
%\VerbFileOpen Trm_verb
Inductive [Trm:Prop] Inversion 
Constructors [sort:SS->Trm]
             [var:VV->Trm]
             [par:PP->Trm]
             [pi:VV->Trm->Trm->Trm]
             [lda:VV->Trm->Trm->Trm]
             [app:Trm->Trm->Trm];
%\VerbFileClos Trm_verb

%\VerbFileOpen Trec_verb
[Trec = Trm_elim
  : {C:Trm->Prop}
    ({s:SS}C (sort s))->
    ({n:VV}C (var n))->
    ({n:PP}C (par n))->
    ({n:VV}{A,B:Trm}{ihA:C A}{ihB:C B}C (pi n A B))->
    ({n:VV}{A,B:Trm}{ihA:C A}{ihB:C B}C (lda n A B))->
    ({A,B:Trm}{ihA:C A}{ihB:C B}C (app A B))->
      {t:Trm}C t];
%\VerbFileClos Trec_verb


[Trms = LL|Trm];

[Trm_eq : Trm->Trm->BB =
  Trec ([_:Trm]Trm->BB)
       ([s:SS]Trec ([_:Trm]BB)
                   ([t:SS]SSeq s t)
                   ([_:VV]ff)
                   ([_:PP]ff)
                   ([_:VV][_,_:Trm][_,_:BB]ff)
                   ([_:VV][_,_:Trm][_,_:BB]ff)
                   ([_,_:Trm][_,_:BB]ff))
       ([v:VV]Trec ([_:Trm]BB)
                   ([_:SS]ff)
                   ([w:VV]VVeq v w)
                   ([_:PP]ff)
                   ([_:VV][_,_:Trm][_,_:BB]ff)
                   ([_:VV][_,_:Trm][_,_:BB]ff)
                   ([_,_:Trm][_,_:BB]ff))
       ([p:PP]Trec ([_:Trm]BB)
                   ([_:SS]ff)
                   ([_:VV]ff)
                   ([q:PP]PPeq p q)
                   ([_:VV][_,_:Trm][_,_:BB]ff)
                   ([_:VV][_,_:Trm][_,_:BB]ff)
                   ([_,_:Trm][_,_:BB]ff))
       ([v:VV][_,_:Trm][l,r:Trm->BB]
              Trec ([_:Trm]BB)
                   ([_:SS]ff)
                   ([_:VV]ff)
                   ([_:PP]ff)
                   ([w:VV][l',r':Trm][_,_:BB]
                         andd (VVeq v w) (andd (l l') (r r')))
                   ([_:VV][_,_:Trm][_,_:BB]ff)
                   ([_,_:Trm][_,_:BB]ff))
       ([v:VV][_,_:Trm][l,r:Trm->BB]
              Trec ([_:Trm]BB)
                   ([_:SS]ff)
                   ([_:VV]ff)
                   ([_:PP]ff)
                   ([_:VV][_,_:Trm][_,_:BB]ff)
                   ([w:VV][l',r':Trm][_,_:BB]
                         andd (VVeq v w) (andd (l l') (r r')))
                   ([_,_:Trm][_,_:BB]ff))
       ([_,_:Trm][l,r:Trm->BB]
              Trec ([_:Trm]BB)
                   ([_:SS]ff)
                   ([_:VV]ff)
                   ([_:PP]ff)
                   ([_:VV][_,_:Trm][_,_:BB]ff)
                   ([_:VV][_,_:Trm][_,_:BB]ff)
                   ([l',r':Trm][_,_:BB]andd (l l') (r r')))];

Goal Trm_eq_refl: {A:Trm}is_tt (Trm_eq A A);
Refine Trec [A:Trm]is_tt (Trm_eq A A);
intros; Expand Trm_eq; Refine SSrefl s;
intros; Expand Trm_eq; Refine VVrefl n;
intros; Expand Trm_eq; Refine PPrefl n;
intros; Refine snd (andd_character ? ?)
                   (pair (VVrefl n)
                         (snd (andd_character ? ?) (pair ihA ihB)));
intros; Refine snd (andd_character ? ?)
                   (pair (VVrefl n)
                         (snd (andd_character ? ?) (pair ihA ihB)));
intros; Refine snd (andd_character ? ?) (pair ihA ihB);
Save Trm_eq_refl;

Goal Trm_eq_pi_lem:
     {v,v'|VV}{A,A',B,B'|Trm}(is_tt (Trm_eq (pi v A B) (pi v' A' B')))->
     and3 (is_tt (VVeq v v')) (is_tt (Trm_eq A A')) (is_tt (Trm_eq B B'));
intros;Refine fst (andd_character ? (andd (Trm_eq A A') (Trm_eq B B'))) H;
intros eqV eqAB;Refine fst (andd_character ? ?) eqAB;
intros eqA eqB;Refine pair3;Immed;
Save Trm_eq_pi_lem;

Goal {v,v'|VV}{A,A',B,B'|Trm}(is_tt (Trm_eq (lda v A B) (lda v' A' B')))->
       and3 (is_tt (VVeq v v')) (is_tt (Trm_eq A A')) (is_tt (Trm_eq B B'));
intros;Refine fst (andd_character ? (andd (Trm_eq A A') (Trm_eq B B'))) H;
intros eqV eqAB;Refine fst (andd_character ? ?) eqAB;
intros eqA eqB;Refine pair3;Immed;
Save Trm_eq_lda_lem;

Goal {A,A',B,B'|Trm}(is_tt (Trm_eq (app A B) (app A' B')))->
       and (is_tt (Trm_eq A A')) (is_tt (Trm_eq B B'));
intros; Refine fst (andd_character (Trm_eq A A') (Trm_eq B B')) H;
Save Trm_eq_app_lem;

(* double induction on Trm *)

Goal {C:Trm->Trm->Prop}
(**************************************************************)
({s1,s2:SS}C (sort s1) (sort s2))->
({s:SS}{v:VV}C (sort s) (var v))->
({s:SS}{p:PP}C (sort s) (par p))->
({s:SS}{v:VV}{A,B:Trm}(C (sort s) A)->(C (sort s) B)->C (sort s) (pi v A B))->
({s:SS}{v:VV}{A,B:Trm}(C (sort s) A)->(C (sort s) B)->C (sort s) (lda v A B))->
({s:SS}{A,B:Trm}(C (sort s) A)->(C (sort s) B)->C (sort s) (app A B))->
(**************************************************************)
({v:VV}{s:SS}C (var v) (sort s))->
({v,u:VV}C (var v) (var u))->
({v:VV}{p:PP}C (var v) (par p))->
({v,u:VV}{A,B:Trm}(C (var v) A)->(C (var v) B)->C (var v) (pi u A B))->
({v,u:VV}{A,B:Trm}(C (var v) A)->(C (var v) B)->C (var v) (lda u A B))->
({v:VV}{A,B:Trm}(C (var v) A)->(C (var v) B)->C (var v) (app A B))->
(**************************************************************)
({p:PP}{s:SS}C (par p) (sort s))->
({p:PP}{u:VV}C (par p) (var u))->
({p:PP}{q:PP}C (par p) (par q))->
({p:PP}{u:VV}{A,B:Trm}(C (par p) A)->(C (par p) B)->C (par p) (pi u A B))->
({p:PP}{u:VV}{A,B:Trm}(C (par p) A)->(C (par p) B)->C (par p) (lda u A B))->
({p:PP}{A,B:Trm}(C (par p) A)->(C (par p) B)->C (par p) (app A B))->
(**************************************************************)
({v:VV}{M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->{s:SS}C (pi v M N) (sort s))->
({v:VV}{M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->{u:VV}C (pi v M N) (var u))->
({v:VV}{M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->{q:PP}C (pi v M N) (par q))->
({v:VV}{M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->
  {u:VV}{A,B:Trm}(C (pi v M N) A)->(C (pi v M N) B)->C (pi v M N) (pi u A B))->
({v:VV}{M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->
  {u:VV}{A,B:Trm}(C (pi v M N) A)->(C (pi v M N) B)->C (pi v M N) (lda u A B))->
({v:VV}{M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->
  {A,B:Trm}(C (pi v M N) A)->(C (pi v M N) B)->C (pi v M N) (app A B))->
(**************************************************************)
({v:VV}{M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->{s:SS}C (lda v M N) (sort s))->
({v:VV}{M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->{u:VV}C (lda v M N) (var u))->
({v:VV}{M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->{q:PP}C (lda v M N) (par q))->
({v:VV}{M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->
  {u:VV}{A,B:Trm}(C (lda v M N) A)->(C (lda v M N) B)->C (lda v M N) (pi u A B))->
({v:VV}{M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->
  {u:VV}{A,B:Trm}(C (lda v M N) A)->(C (lda v M N) B)->C (lda v M N) (lda u A B))->
({v:VV}{M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->
  {A,B:Trm}(C (lda v M N) A)->(C (lda v M N) B)->C (lda v M N) (app A B))->
(**************************************************************)
({M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->{s:SS}C (app M N) (sort s))->
({M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->{u:VV}C (app M N) (var u))->
({M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->{q:PP}C (app M N) (par q))->
({M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->
  {u:VV}{A,B:Trm}(C (app M N) A)->(C (app M N) B)->C (app M N) (pi u A B))->
({M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->
  {u:VV}{A,B:Trm}(C (app M N) A)->(C (app M N) B)->C (app M N) (lda u A B))->
({M,N:Trm}({T:Trm}C M T)->({T:Trm}C N T)->
  {A,B:Trm}(C (app M N) A)->(C (app M N) B)->C (app M N) (app A B))->
(**************************************************************)
            {A,B:Trm}C A B;

intros C ss sv sp spi sl sa
         vs vv vp vpi vl va
         ps pv pp ppi pl pa
         pis piv pip pipi pil pia
         ls lv lp lpi ll la
         as av ap api al aa;

Refine Trec [A:Trm]{B:Trm}C A B;
intros s;Refine Trec (C (sort s));Immed;
intros v;Refine Trec (C (var v));Immed;
intros p;Refine Trec (C (par p));Immed;
intros v M N hypM hypN;Refine Trec (C (pi v M N));
Refine pis v M N hypM hypN;
Refine piv v M N hypM hypN;
Refine pip v M N hypM hypN;
Refine pipi v M N hypM hypN;
Refine pil v M N hypM hypN;
Refine pia v M N hypM hypN;
intros v M N hypM hypN;Refine Trec (C (lda v M N));
Refine ls v M N hypM hypN;
Refine lv v M N hypM hypN;
Refine lp v M N hypM hypN;
Refine lpi v M N hypM hypN;
Refine ll v M N hypM hypN;
Refine la v M N hypM hypN;
intros M N hypM hypN;Refine Trec (C (app M N));
Refine as M N hypM hypN;
Refine av M N hypM hypN;
Refine ap M N hypM hypN;
Refine api M N hypM hypN;
Refine al M N hypM hypN;
Refine aa M N hypM hypN;

Save Trm_double_induct;

%\VerbFileOpen Trm_eq_subst_verb
Goal Trm_eq_subst: {A,B|Trm}(is_tt (Trm_eq A B))->Q A B;
%\VerbFileClos Trm_eq_subst_verb
Refine Trm_double_induct [A,B|Trm](is_tt (Trm_eq A B))->Q A B;

intros;Qrepl SSdecide H;Refine Q_refl;
intros;Refine tt_not_ff (Q_sym H);
intros;Refine tt_not_ff (Q_sym H);
intros;Refine tt_not_ff (Q_sym H2);
intros;Refine tt_not_ff (Q_sym H2);
intros;Refine tt_not_ff (Q_sym H2);

intros;Refine tt_not_ff (Q_sym H);
intros;Qrepl VVdecide H;Refine Q_refl;
intros;Refine tt_not_ff (Q_sym H);
intros;Refine tt_not_ff (Q_sym H2);
intros;Refine tt_not_ff (Q_sym H2);
intros;Refine tt_not_ff (Q_sym H2);

intros;Refine tt_not_ff (Q_sym H);
intros;Refine tt_not_ff (Q_sym H);
intros;Qrepl PPdecide H;Refine Q_refl;
intros;Refine tt_not_ff (Q_sym H2);
intros;Refine tt_not_ff (Q_sym H2);
intros;Refine tt_not_ff (Q_sym H2);

intros;Refine tt_not_ff (Q_sym H2);
intros;Refine tt_not_ff (Q_sym H2);
intros;Refine tt_not_ff (Q_sym H2);
intros;Refine Trm_eq_pi_lem H4;
intros eqUV eqMA eqNB;
Qrepl VVdecide eqUV;Qrepl H ? eqMA;Qrepl H1 ? eqNB;Refine Q_refl;
intros;Refine tt_not_ff (Q_sym H4);
intros;Refine tt_not_ff (Q_sym H4);

intros;Refine tt_not_ff (Q_sym H2);
intros;Refine tt_not_ff (Q_sym H2);
intros;Refine tt_not_ff (Q_sym H2);
intros;Refine tt_not_ff (Q_sym H4);
intros;Refine Trm_eq_lda_lem H4;
intros eqUV eqMA eqNB;
Qrepl VVdecide eqUV;Qrepl H ? eqMA;Qrepl H1 ? eqNB;Refine Q_refl;
intros;Refine tt_not_ff (Q_sym H4);

intros;Refine tt_not_ff (Q_sym H2);
intros;Refine tt_not_ff (Q_sym H2);
intros;Refine tt_not_ff (Q_sym H2);
intros;Refine tt_not_ff (Q_sym H4);
intros;Refine tt_not_ff (Q_sym H4);
intros;Refine Trm_eq_app_lem H4;
intros eqMA eqNB;
Qrepl H ? eqMA;Qrepl H1 ? eqNB;Refine Q_refl;

Save;

Goal {A,B:Trm}iff (is_tt (Trm_eq A B)) (Q A B);
intros; Refine pair; Refine Trm_eq_subst;
intros; Qrepl H; Refine Trm_eq_refl;
Save Trm_eq_iff_Q;

[Trm_eq_sym = XXsym Trm_eq_iff_Q];

(* induction on the length of terms *)
%\VerbFileOpen lngth
[lngth : Trm->NN =
  Trec ([_:Trm]NN)
       ([_:SS]one)
       ([_:VV]one)
       ([_:PP]one)
       ([_:VV][_,_:Trm][l,r:NN]S (add l r))
       ([_:VV][_,_:Trm][l,r:NN]S (add l r))
       ([_,_:Trm][l,r:NN]S (add l r))];
%\VerbFileClos lngth

(* every term has lngth a successor *)
%\VerbFileOpen lngth_is_S
Goal lngth_is_S: {A:Trm}Ex [n:NN] Q (lngth A) (S n);
%\VerbFileClos lngth_is_S
Refine Trec [A:Trm]Ex [n:NN] Q (lngth A) (S n);
(* atomic *)
intros; Refine ExIn Z; Refine Q_refl;
intros; Refine ExIn Z; Refine Q_refl;
intros; Refine ExIn Z; Refine Q_refl;
(* compound *)
intros; Refine ExIn (add (lngth A) (lngth B)); Refine Q_refl;
intros; Refine ExIn (add (lngth A) (lngth B)); Refine Q_refl;
intros; Refine ExIn (add (lngth A) (lngth B)); Refine Q_refl;
Save;

[WF_Trm_ind = WF_induction|Trm|lngth
  :  {P:Trm->Prop}
     {ih:{A:Trm}({x:Trm}(Lt (lngth x) (lngth A))->(P x))->P A}
     {k:Trm}P k];

(* using predicates to define the shape of terms *)

[isSrt : Trm -> BB = Trec ([_:Trm]BB)
                     ([_:SS]tt) 
                     ([_:VV]ff) 
                     ([_:PP]ff) 
                     ([_:VV][_,_:Trm][_,_:BB]ff) 
                     ([_:VV][_,_:Trm][_,_:BB]ff) 
                     ([_,_:Trm][_,_:BB]ff)];
%\VerbFileOpen IsSrt
[IsSrt [A:Trm] = Ex [s:SS]is_tt (Trm_eq A (sort s))];
%\VerbFileClos IsSrt

[isVar : Trm -> BB = Trec ([_:Trm]BB)
                     ([_:SS]ff) 
                     ([_:VV]tt) 
                     ([_:PP]ff) 
                     ([_:VV][_,_:Trm][_,_:BB]ff) 
                     ([_:VV][_,_:Trm][_,_:BB]ff) 
                     ([_,_:Trm][_,_:BB]ff)];

[isPar : Trm -> BB = Trec ([_:Trm]BB)
                     ([_:SS]ff) 
                     ([_:VV]ff) 
                     ([_:PP]tt) 
                     ([_:VV][_,_:Trm][_,_:BB]ff) 
                     ([_:VV][_,_:Trm][_,_:BB]ff) 
                     ([_,_:Trm][_,_:BB]ff)];


[isPi  : Trm -> BB = Trec ([_:Trm]BB)
                     ([_:SS]ff) 
                     ([_:VV]ff) 
                     ([_:PP]ff) 
                     ([_:VV][_,_:Trm][_,_:BB]tt) 
                     ([_:VV][_,_:Trm][_,_:BB]ff) 
                     ([_,_:Trm][_,_:BB]ff)];
[IsPi [M:Trm] = Ex3 [v:VV][A,B:Trm]is_tt (Trm_eq M (pi v A B))];


[isLda : Trm -> BB = Trec ([_:Trm]BB)
                     ([_:SS]ff) 
                     ([_:VV]ff) 
                     ([_:PP]ff) 
                     ([_:VV][_,_:Trm][_,_:BB]ff) 
                     ([_:VV][_,_:Trm][_,_:BB]tt) 
                     ([_,_:Trm][_,_:BB]ff)];


[isApp : Trm -> BB = Trec ([_:Trm]BB)
                     ([_:SS]ff) 
                     ([_:VV]ff) 
                     ([_:PP]ff) 
                     ([_:VV][_,_:Trm][_,_:BB]ff) 
                     ([_:VV][_,_:Trm][_,_:BB]ff) 
                     ([_,_:Trm][_,_:BB]tt)];

Goal {M|Trm}(is_tt (isSrt M))->IsSrt M;
Refine Trec [M:Trm]{is:is_tt (isSrt M)}IsSrt M;
intros;Refine ExIn s;Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
Save isSrt_lem;

Goal {M|Trm}(is_ff (isSrt M))->{s:SS}is_ff (Trm_eq M (sort s));
Refine Trec [M:Trm]{is_not:is_ff (isSrt M)}{s:SS}is_ff (Trm_eq M (sort s));
intros;Refine tt_not_ff is_not;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save isnotSrt_lem;

Goal {M|Trm}(is_tt (isVar M))->Ex [v:VV]is_tt (Trm_eq M (var v));
Refine Trec [M:Trm]{is:is_tt (isVar M)}Ex [v:VV]is_tt (Trm_eq M (var v));
intros;Refine tt_not_ff (Q_sym is);
intros;Refine ExIn n;Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
Save isVar_lem;

Goal {M|Trm}(is_ff (isVar M))->{v:VV}is_ff (Trm_eq M (var v));
Refine Trec [M:Trm]{is_not:is_ff (isVar M)}{v:VV}is_ff (Trm_eq M (var v));
intros;Refine Q_refl;
intros;Refine tt_not_ff is_not;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save isnotVar_lem;

Goal {M|Trm}(is_tt (isPar M))->Ex [p:PP]is_tt (Trm_eq M (par p));
Refine Trec [M:Trm]{is:is_tt (isPar M)}Ex [p:PP]is_tt (Trm_eq M (par p));
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine ExIn n;Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
Save isPar_lem;

Goal {M|Trm}(is_ff (isPar M))->{p:PP}is_ff (Trm_eq M (par p));
Refine Trec [M:Trm]{is_not:is_ff (isPar M)}{p:PP}is_ff (Trm_eq M (par p));
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine tt_not_ff is_not;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save isnotPar_lem;

Goal {M|Trm}(is_tt (isPi M))->IsPi M;
Refine Trec [M:Trm]{is:is_tt (isPi M)}IsPi M;
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine Ex3In n A B;Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
Save isPi_lem;

Goal {M|Trm}(is_ff (isPi M))->{v:VV}{A,B:Trm}is_ff (Trm_eq M (pi v A B));
Refine Trec [M:Trm]{is_not:is_ff (isPi M)}
            {v:VV}{A,B:Trm}is_ff (Trm_eq M (pi v A B));
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine tt_not_ff is_not;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save isnotPi_lem;

Goal {M|Trm}(is_tt (isLda M))->Ex3 [v:VV][A,B:Trm]is_tt (Trm_eq M (lda v A B));
Refine Trec [M:Trm]{is:is_tt (isLda M)}
            Ex3 [v:VV][A,B:Trm]is_tt (Trm_eq M (lda v A B));
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine Ex3In n A B;Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym is);
Save isLda_lem;

Goal {M|Trm}(is_ff (isLda M))->{v:VV}{A,B:Trm}is_ff (Trm_eq M (lda v A B));
Refine Trec [M:Trm]{is_not:is_ff (isLda M)}
            {v:VV}{A,B:Trm}is_ff (Trm_eq M (lda v A B));
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine tt_not_ff is_not;
intros;Refine Q_refl;
Save isnotLda_lem;

Goal {M|Trm}(is_tt (isApp M))->Ex2 [A,B:Trm]is_tt (Trm_eq M (app A B));
Refine Trec [M:Trm]{is:is_tt (isApp M)}
            Ex2 [A,B:Trm]is_tt (Trm_eq M (app A B));
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine tt_not_ff (Q_sym is);
intros;Refine Ex2In A B;Refine Trm_eq_refl;
Save isApp_lem;

Goal {M|Trm}(is_ff (isApp M))->{A,B:Trm}is_ff (Trm_eq M (app A B));
Refine Trec [M:Trm]{is_not:is_ff (isApp M)}
            {A,B:Trm}is_ff (Trm_eq M (app A B));
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine tt_not_ff is_not;
Save isnotApp_lem;

(* decidability of term shape *)
%\VerbFileOpen decide_IsSrt
Goal decide_IsSrt: {A:Trm}decidable (IsSrt A);
%\VerbFileClos decide_IsSrt
Refine Trec [A:Trm]or (IsSrt A) (not (IsSrt A));
intros; Refine inl; Refine ExIn s; Refine Trm_eq_refl;
intros; Refine inr; Intros is; Refine is; intros s sh;
  Refine tt_not_ff; Refine Q_sym sh;
intros; Refine inr; Intros is; Refine is; intros s sh;
  Refine tt_not_ff; Refine Q_sym sh;
intros; Refine inr; Intros is; Refine is; intros s sh;
  Refine tt_not_ff; Refine Q_sym sh;
intros; Refine inr; Intros is; Refine is; intros s sh;
  Refine tt_not_ff; Refine Q_sym sh;
intros; Refine inr; Intros is; Refine is; intros s sh;
  Refine tt_not_ff; Refine Q_sym sh;
Save;

Goal decide_IsPi: {A:Trm}or (IsPi A) (not (IsPi A));
Refine Trec [A:Trm]or (IsPi A) (not (IsPi A));
intros; Refine inr; Intros ip; Refine ip; intros v Al Ar h;
  Refine tt_not_ff; Refine Q_sym h;
intros; Refine inr; Intros ip; Refine ip; intros v Al Ar h;
  Refine tt_not_ff; Refine Q_sym h;
intros; Refine inr; Intros ip; Refine ip; intros v Al Ar h;
  Refine tt_not_ff; Refine Q_sym h;
intros; Refine inl; Refine Ex3In n A B; Refine Trm_eq_refl;
intros; Refine inr; Intros ip; Refine ip; intros v Al Ar h;
  Refine tt_not_ff; Refine Q_sym h;
intros; Refine inr; Intros ip; Refine ip; intros v Al Ar h;
  Refine tt_not_ff; Refine Q_sym h;
Save;
