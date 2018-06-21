Init XCC; 

Module basics;

Logic;
Forget Q;
[TYPE=Prop];

(*** Inductive equality ***)
%\VerbFileOpen Qverb
Inductive [Q:A->A->Prop] Parameters [A|Prop] Constructors [Q_refl:{a:A}Q a a];

Goal Q_subst: {a,b|A}(Q a b)->{P:A->Prop}(P a)->P b;
%\VerbFileNoRecord Qverb
intros; Refine Q_elim [a,y:A][p:Q a y](P a)->P y;
Immed; intros; Immed;
Save;

%\VerbFileRecord Qverb
Goal Q_sym: {a,b|A}(Q a b)->(Q b a);
%\VerbFileNoRecord Qverb
intros; Refine Q_subst H ([x:A]Q x a) (Q_refl a);
Save Q_sym;

%\VerbFileRecord Qverb
Goal Q_trans: {a,b,c|A}(Q a b)->(Q b c)->(Q a c);
%\VerbFileClos Qverb
intros; Refine Q_subst H1 ([x:A]Q a x) H;
Save Q_trans;

Discharge A;
Configure Qrepl Q Q_subst Q_sym;

Goal {T,S|Prop}{f:T->S}{t,u|T}(Q t u)->Q (f t) (f u);
intros; Qrepl H; Refine Q_refl;
Save Q_resp;


(* some more preliminaries *)
[TT = {A:Prop}A->A];
[true = [A:Prop][a:A]a : TT];
[FF = {A:Prop}A];


%\VerbFileOpen decidable
[decidable [P:Prop] = or P (not P)];
%\VerbFileClos decidable

Goal Contrapos: {A,B|Prop}(A->B)->{X|Prop}(B->X)->A->X;
intros; Refine H1 (H H2);
Save Contrapos;

Goal and_commutes: {A,B|Prop}(and A B)->(and B A);
intros; Refine H; intros; Refine pair; Immed;
Save and_commutes;

[ExIn = [T|Type][wit:T][P:T->Prop]ExIntro P|wit];
[exIn = [A|Prop][wit:A][P:A->Prop]ex_intro P|wit];


[T,S,U,V,W,X,Y|Prop]
[Ex2 [P:T->S->Prop] : Prop =
    {B:Prop}({t|T}{s|S}(P t s)->B)->B]
[Ex2In [t:T][s:S][P:T->S->Prop][p:P t s] : Ex2 P =
    [B:Prop][gen:{t|T}{s|S}(P t s)->B]gen p]
[Ex3 [P:T->S->U->Prop] : Prop =
    {B:Prop}({t|T}{s|S}{u|U}(P t s u)->B)->B]
[Ex3In [t:T][s:S][u:U][P:T->S->U->Prop][p:P t s u] : Ex3 P =
    [B:Prop][gen:{t|T}{s|S}{u|U}(P t s u)->B]gen p]
[Ex4 [P:T->S->U->V->Prop] : Prop =
    {B:Prop}({t|T}{s|S}{u|U}{v|V}(P t s u v)->B)->B]
[Ex4In [t:T][s:S][u:U][v:V][P:T->S->U->V->Prop][p:P t s u v] : Ex4 P =
    [B:Prop][gen:{t|T}{s|S}{u|U}{v|V}(P t s u v)->B]gen p]
[Ex5 [P:T->S->U->V->W->Prop] : Prop =
    {B:Prop}({t|T}{s|S}{u|U}{v|V}{w|W}(P t s u v w)->B)->B]
[Ex5In [t:T][s:S][u:U][v:V][w:W][P:T->S->U->V->W->Prop][p:P t s u v w] : Ex5 P =
    [B:Prop][gen:{t|T}{s|S}{u|U}{v|V}{w|W}(P t s u v w)->B]gen p]
[Ex6 [P:T->S->U->V->W->X->Prop] : Prop =
    {B:Prop}({t|T}{s|S}{u|U}{v|V}{w|W}{x|X}(P t s u v w x)->B)->B]
[Ex6In [t:T][s:S][u:U][v:V][w:W][x:X][P:T->S->U->V->W->X->Prop][p:P t s u v w x]
      : Ex6 P
      = [B:Prop][gen:{t|T}{s|S}{u|U}{v|V}{w|W}{x|X}(P t s u v w x)->B]gen p]
[Ex7 [P:T->S->U->V->W->X->Y->Prop] : Prop =
    {B:Prop}({t|T}{s|S}{u|U}{v|V}{w|W}{x|X}{y|Y}(P t s u v w x y)->B)->B]
[Ex7In [t:T][s:S][u:U][v:V][w:W][x:X][y:Y][P:T->S->U->V->W->X->Y->Prop]
       [p:P t s u v w x y] : Ex7 P
 = [B:Prop][gen:{t|T}{s|S}{u|U}{v|V}{w|W}{x|X}{y|Y}(P t s u v w x y)->B]gen p]
[Q_resp2 [f:T->U->S][t,t'|T][u,u':U][Qtt':Q t t'][Quu':Q u u']
   : Q (f t u) (f t' u')
   = Q_subst Qtt' ([x:T]Q (f t u) (f x u'))
                  (Q_subst Quu' ([y:U]Q (f t u) (f t y))
                                (Q_refl (f t u)))];
Discharge T;

[A,B,C,D,E,F,G|Prop][a:A][b:B][c:C][d:D][e:E][f:F][g:G]

[and4 [A,B,C,D:Prop] = {chi|Prop}{premise:A->B->C->D->chi}chi]
[pair4 = [chi|Prop][premise:A->B->C->D->chi](premise a b c d):and4 A B C D]
[and4_out1 [conj:and4 A B C D] = conj|A [a:A][_:B][_:C][_:D]a:A]
[and4_out2 [conj:and4 A B C D] = conj|B [_:A][b:B][_:C][_:D]b:B]
[and4_out3 [conj:and4 A B C D] = conj|C [_:A][_:B][c:C][_:D]c:C]
[and4_out4 [conj:and4 A B C D] = conj|D [_:A][_:B][_:C][d:D]d:D]

[and5 [A,B,C,D,E:Prop] = {chi|Prop}{premise:A->B->C->D->E->chi}chi]
[pair5 = [chi|Prop][premise:A->B->C->D->E->chi](premise a b c d e):and5 A B C D E]
[and5_out1 [conj:and5 A B C D E] = conj|A [a:A][_:B][_:C][_:D][_:E]a:A]
[and5_out2 [conj:and5 A B C D E] = conj|B [_:A][b:B][_:C][_:D][_:E]b:B]
[and5_out3 [conj:and5 A B C D E] = conj|C [_:A][_:B][c:C][_:D][_:E]c:C]
[and5_out4 [conj:and5 A B C D E] = conj|D [_:A][_:B][_:C][d:D][_:E]d:D]
[and5_out5 [conj:and5 A B C D E] = conj|E [_:A][_:B][_:C][_:D][e:E]e:E]

[and6 [A,B,C,D,E,F:Prop] = {chi|Prop}{premise:A->B->C->D->E->F->chi}chi]
[pair6 = [chi|Prop][premise:A->B->C->D->E->F->chi](premise a b c d e f)
       : and6 A B C D E F]
[and6_out1 [conj:and6 A B C D E F] = conj|A [a:A][_:B][_:C][_:D][_:E][_:F]a:A]
[and6_out2 [conj:and6 A B C D E F] = conj|B [_:A][b:B][_:C][_:D][_:E][_:F]b:B]
[and6_out3 [conj:and6 A B C D E F] = conj|C [_:A][_:B][c:C][_:D][_:E][_:F]c:C]
[and6_out4 [conj:and6 A B C D E F] = conj|D [_:A][_:B][_:C][d:D][_:E][_:F]d:D]
[and6_out5 [conj:and6 A B C D E F] = conj|E [_:A][_:B][_:C][_:D][e:E][_:F]e:E]
[and6_out6 [conj:and6 A B C D E F] = conj|F [_:A][_:B][_:C][_:D][_:E][f:F]f:F]

[and7 [A,B,C,D,E,F,G:Prop] = {chi|Prop}{premise:A->B->C->D->E->F->G->chi}chi]
[pair7 = [chi|Prop][premise:A->B->C->D->E->F->G->chi](premise a b c d e f g)
       : and7 A B C D E F G]
[and7_out1 [conj:and7 A B C D E F G] = conj|A [a:A][_:B][_:C][_:D][_:E][_:F][_:G]a:A]
[and7_out2 [conj:and7 A B C D E F G] = conj|B [_:A][b:B][_:C][_:D][_:E][_:F][_:G]b:B]
[and7_out3 [conj:and7 A B C D E F G] = conj|C [_:A][_:B][c:C][_:D][_:E][_:F][_:G]c:C]
[and7_out4 [conj:and7 A B C D E F G] = conj|D [_:A][_:B][_:C][d:D][_:E][_:F][_:G]d:D]
[and7_out5 [conj:and7 A B C D E F G] = conj|E [_:A][_:B][_:C][_:D][e:E][_:F][_:G]e:E]
[and7_out6 [conj:and7 A B C D E F G] = conj|F [_:A][_:B][_:C][_:D][_:E][f:F][_:G]f:F]
[and7_out7 [conj:and7 A B C D E F G] = conj|G [_:A][_:B][_:C][_:D][_:E][_:F][g:G]g:G];

Discharge A;

(* contrapositive *)
%\VerbFileOpen contrapos
Goal contrapos: {A,B|Prop}(A->B)->(not B)->(not A);
%\VerbFileClos contrapos
Intros _____; Refine H1; Refine H; Refine H2;
Save contrapos;

(* Bool *)
%\VerbFileOpen BBverb
Inductive [BB:Prop] ElimOver Type(0) Constructors [tt,ff:BB];
%\VerbFileClos BBverb

%\VerbFileOpen moreBBverb
[is_tt [b:BB] = Q b tt]
[is_ff [b:BB] = Q b ff]
[if [a:BB][D|Prop][d,e:D] = BB_elim ([_:BB]D) d e a]
[andd [a,b:BB] = if a b ff]
[orr [a,b:BB] = if a a b]
[nott [a:BB] = if a ff tt]
[Brec: {C:BB->Type(0)}{d:C tt}{e:C ff}{b:BB}C b = BB_elim];
%\VerbFileClos moreBBverb

Goal {C:BB->BB->Prop}
     (C tt tt)->(C tt ff)->(C ff tt)->(C ff ff)->
     {x,y:BB}C x y;
intros _____; Refine Brec [x:BB]{y:BB}C x y;
Refine Brec [y:BB]C tt y; Immed;
Refine Brec [y:BB]C ff y; Immed;
Save BB_double_induct;    (**** Unfrozen *********)

[BBeq : BB->BB->BB = BB_double_induct ([_,_:BB]BB) tt ff ff tt];

Goal BBeq_refl: {b:BB}is_tt (BBeq b b);
Refine Brec [b:BB]is_tt (BBeq b b);
Refine Q_refl; Refine Q_refl;
Save BBeq_refl;

Goal {b,c|BB}(is_tt (BBeq b c))->Q b c;
Refine BB_double_induct [b,c:BB](is_tt (BBeq b c))->Q b c;
intros; Refine Q_refl;
intros; Refine Q_sym; Immed;
intros; Immed;
intros; Refine Q_refl;
Save BBeq_subst;

Goal BBeq_iff_Q : {p,q:BB}iff (is_tt (BBeq p q)) (Q p q);
intros; Refine pair; Refine BBeq_subst;
intros h; Qrepl h; Refine BBeq_refl;
Save;

(************
[tt_not_ff: not (Q tt ff)];
*************)

%\VerbFileOpen tt_not_ff
Goal tt_not_ff: not (Q tt ff);
%\VerbFileClos tt_not_ff
Intros h;
[isT = BB_elim ([_:BB]Prop) TT FF];
Equiv isT ff; Qrepl (Q_sym h); Refine [A:Prop][a:A]a;
Save tt_not_ff;


Goal {b:BB}or (is_tt b) (is_ff b);
Refine Brec [b:BB]or (is_tt b) (is_ff b);
Refine inl; Refine Q_refl;
Refine inr; Refine Q_refl;
Save tt_or_ff;

Goal {b:BB}iff (is_tt b) (not (is_ff b));
intros; Refine pair;
intros h; Qrepl h; Refine tt_not_ff;
intros h; Refine tt_or_ff b; intros; Immed; intros; Refine h; Immed;
Save is_tt_isnot_ff;

Goal {x:BB}{A|Prop}{a:A}Q (if x a a) a;
intros; Refine Brec [x:BB]Q (if x a a) a;
Refine Q_refl;
intros; Refine Q_refl;
Save triv_if;

Goal {A|Prop}{a,b,c|A}{x|BB}(Q (if x a b) c)->or (Q a c) (Q b c);
intros ____;
Refine Brec [x|BB](Q (if x a b) c)->or (Q a c) (Q b c);
intros; Refine inl; Immed;
intros; Refine inr; Immed;
Save if_character;

Goal {A|Prop}{a,b,a',b'|A}(Q a a')->(Q b b')->
                   {x:BB}Q (if x a b) (if x a' b');
intros; Refine tt_or_ff x;
intros ttx; Qrepl ttx; Expand if; Refine H;
intros ffx; Qrepl ffx; Expand if; Refine H1;
Save Q_if_triv;

(* moving inside if *)
Goal {A,B|Prop}{f:A->B}{a,b:A}{x:BB}Q (f (if x a b)) (if x (f a) (f b));
intros; Refine tt_or_ff x;
intros ttx; Qrepl ttx; Refine Q_refl;
intros ffx; Qrepl ffx; Refine Q_refl;
Save if_inside;

Goal {A|Prop}{a,b,c,d:A}{x,y:BB}Q (if x (if y a b) (if y c d))
                                  (if y (if x a c) (if x b d));
intros; Refine tt_or_ff x;
intros ttx; Qrepl ttx; Refine Q_refl;
intros ffx; Qrepl ffx; Refine Q_refl;
Save middle_four_if;

Goal {A|Prop}{a,b,c:A}{x:BB}Q (if x (if x a b) c) (if x a c);
intros; Refine tt_or_ff x;
intros ttx; Qrepl ttx; Refine Q_refl;
intros ffx; Qrepl ffx; Refine Q_refl;
Save reduce_if_left;

Goal {A|Prop}{a,b,c:A}{x:BB}Q (if x a (if x b c)) (if x a c);
intros; Refine tt_or_ff x;
intros ttx; Qrepl ttx; Refine Q_refl;
intros ffx; Qrepl ffx; Refine Q_refl;
Save reduce_if_right;

Goal {a,b:BB}iff (is_tt (andd a b)) (and (is_tt a) (is_tt b));
intros; Refine pair;
intros h; Refine tt_or_ff a; intros att; Refine tt_or_ff b;
intros btt; Refine pair att btt;
intros bff; Refine tt_not_ff; Qrepl Q_sym h;
    Qrepl att; Qrepl bff; Refine Q_refl;
intros aff; Refine tt_not_ff; Qrepl Q_sym h; Qrepl aff; Refine Q_refl;
intros attbtt; Qrepl fst attbtt; Qrepl snd attbtt; Refine Q_refl;
Save andd_character;

Goal {a:BB}Q (andd a a) a;
intros; Refine tt_or_ff a;
intros tta; Qrepl tta; Refine Q_refl;
intros ffa; Qrepl ffa; Refine Q_refl;
Save triv_and;

Goal {b:BB}iff (is_tt (nott b)) (not (is_tt b));
intros; Refine pair;
Intros h g; Refine tt_not_ff; Qrepl Q_sym h; Qrepl g; Refine Q_refl;
intros notbtt; Refine tt_or_ff b;
intros; Refine notbtt; Immed;
intros bff; Qrepl bff; Refine Q_refl;
Save nott_character;

Goal {b:BB}iff (is_tt (nott b)) (is_ff b);
Refine Brec [b:BB]iff (is_tt (nott b)) (is_ff b);
Refine pair; intros; Refine Q_sym H; intros; Refine Q_sym H;
Refine pair; intros; Refine Q_refl; intros; Refine Q_refl;
Save nott_negates_tt;

Goal {a,b|BB}((is_tt a)->(is_tt b))->(is_ff b)->(is_ff a);
Expand is_tt is_ff;
Refine BB_double_induct [a,b|BB]((Q a tt)->Q b tt)->(Q b ff)->Q a ff;
intros; Immed;
intros h j; Refine Q_sym (h (Q_refl tt));
intros; Refine Q_refl;
intros; Refine Q_refl;
Save B_contrapos;

Goal {a,b|BB}((is_ff a)->(is_ff b))->(is_tt b)->(is_tt a);
Expand is_tt is_ff;
Refine BB_double_induct [a,b|BB]((Q a ff)->Q b ff)->(Q b tt)->Q a tt;
intros; Immed;
intros; Refine Q_refl;
intros h j; Refine Q_sym (h (Q_refl ff));
intros; Immed;
Save contrapos_B;

Goal {P|Prop}{b|BB}((is_tt b)->P)->(not P)->is_ff b;
intros; Refine tt_or_ff b;
intros ttb; Refine H1 (H ttb);
intros; Immed;
Save cross_contrapos_tt_P;

Goal {a,b:BB}iff (is_tt (orr a b)) (or (is_tt a) (is_tt b));
intros; Refine pair;
intros orrab; Refine tt_or_ff a; intros att; Refine inl att;
intros aff; Refine inr;  Expand is_tt;
Qrepl Q_sym orrab; Qrepl aff; Refine Q_refl;
intros orab; Refine orab;
intros att; Expand is_tt; Qrepl att; Refine Q_refl;
intros btt; Expand is_tt; Qrepl btt; Refine tt_or_ff a;
intros att; Expand is_tt; Qrepl att; Refine Q_refl;
intros aff; Expand is_tt; Qrepl aff; Refine Q_refl;
Save orr_character;

Goal {a:BB}Q (orr a a) a;
intros; Refine tt_or_ff a;
intros tta; Qrepl tta; Refine Q_refl;
intros ffa; Qrepl ffa; Refine Q_refl;
Save triv_orr;

Goal {a:BB}Q (orr a ff) a;
Refine Brec [a:BB]Q (orr a ff) a; Refine Q_refl; Refine Q_refl;
Save ff_orr_unit;

Goal {a:BB}Q (orr a tt) tt;
Refine Brec [a:BB]Q (orr a tt) tt; Refine Q_refl; Refine Q_refl;
Save tt_orr_zero;

Goal {a,b,c:BB}Q (orr (orr a b) c) (orr a (orr b c));
intros;
Refine tt_or_ff a;
intros tta; Qrepl tta; Refine Q_refl;
intros ffa; Qrepl ffa; Refine Q_refl;
Save orr_associates;

Goal {a,b:BB}Q (orr a b) (orr b a);
intros;
Refine tt_or_ff a;
intros ah; Qrepl ah;
Refine tt_or_ff b;
intros bh; Qrepl bh; Refine Q_refl;
intros bh; Qrepl bh; Refine Q_refl;
intros ah; Qrepl ah;
Refine tt_or_ff b;
intros bh; Qrepl bh; Refine Q_refl;
intros bh; Qrepl bh; Refine Q_refl;
Save orr_commutes;

(* deMorgan laws *)
Goal {a,b:BB}iff (is_ff (orr a b)) (and (is_ff a) (is_ff b));
intros; Refine pair;
intros hyp; Refine pair;
Refine tt_or_ff a; intros tta; Refine tt_not_ff;
Qrepl Q_sym hyp; Qrepl tta; Refine Q_refl;
intros; Immed;
Refine tt_or_ff b; intros ttb; Refine tt_not_ff;
Qrepl Q_sym hyp; Qrepl orr_commutes a b; Qrepl ttb; Refine Q_refl;
intros; Immed;
intros g; Qrepl fst g; Qrepl snd g; Refine Q_refl;
Save deMorgan;

(* proof by contradiction *)
Goal {a|BB}(is_tt a)->(is_ff a)->{A:Prop}A;
intros; Refine tt_not_ff; Qrepl Q_sym H; Qrepl Q_sym H1; Refine Q_refl;
Save B_contradiction;

(**)
(* Naturals *)
%\VerbFileOpen NNverb
Inductive [NN:Prop] Constructors [Z:NN][S:NN->NN];

[Nrec : {C:NN->Prop}{Nbase:C Z}{Nstep:{x:NN}{Nih:C x}C (S x)}{a:NN}C a
      = NN_elim];
[add [n,m:NN] : NN = Nrec ([_:NN]NN) m ([_,x:NN]S x) n];
[pred : NN->NN = Nrec ([_:NN]NN) Z [x,_:NN]x];
[sbt [n:NN] : NN->NN = Nrec ([_:NN]NN) n ([_,x:NN]pred x)];
%\VerbFileClos NNverb


[mul [n,m:NN] = Nrec ([_:NN]NN) Z ([_,x:NN]add m x) n];
[exp [n,m:NN] = Nrec ([_:NN]NN) (S Z) ([_,x:NN]mul n x) m];

[one = S Z];
[two = S one];
[three = S two];
[four = S three];
[five = S four];
[six = S five];

%\VerbFileOpen double_induct
Goal double_induct:
     {C:NN->NN->Prop}
     (C Z Z)->
     ({y:NN}(C Z y)->(C Z (S y)))->
     ({x:NN}({y:NN}C x y)->C (S x) Z)->
     ({x:NN}({y:NN}C x y)->{y:NN}(C (S x) y)->C (S x) (S y))->
     {x,y:NN}C x y;
%\VerbFileClos double_induct
intros C bb_step bs_step sb_step ss_step;
Refine Nrec [x:NN]{y:NN}C x y; Refine Nrec (C Z); Immed;
intros x h; Refine Nrec (C (S x));
Refine sb_step x h; Refine ss_step x h;
Save double_induct;       (**** Unfrozen *********)

[Q_resp_S [x,y|NN][h:Q x y] : Q (S x) (S y) = Q_resp S h];
[Q_resp_pred [x,y|NN][h:Q x y] : Q (pred x) (pred y) = Q_resp pred h];
[S_injective [x,y|NN][h:Q (S x) (S y)] : Q x y = Q_resp_pred h];

%\VerbFileOpen nat_eq
[nat_eq : NN->NN->BB
    = Nrec ([_:NN]NN->BB)
           (Nrec ([_:NN]BB) tt ([_:NN][_:BB]ff))
           ([_:NN][eqn:NN->BB]Nrec ([_:NN]BB) ff ([x:NN][_:BB]eqn x))];
%\VerbFileClos nat_eq

Goal nat_eq_refl: {n:NN}is_tt (nat_eq n n);
Refine Nrec [n:NN] is_tt (nat_eq n n);
Refine Q_refl; intros; Immed;
Save nat_eq_refl;

%\VerbFileOpen nat_eq_character
Goal nat_eq_character: {m,n:NN}iff (is_tt (nat_eq m n)) (Q m n);
%\VerbFileClos nat_eq_character
Refine double_induct [m,n:NN]iff (is_tt (nat_eq m n)) (Q m n);
Refine pair; intros; Refine Q_refl; intros; Refine Q_refl;
intros; Refine pair;
  intros; Refine tt_not_ff (Q_sym H1);
  intros; Qrepl H1; Refine nat_eq_refl;
intros; Refine pair;
  intros; Refine tt_not_ff (Q_sym H1);
  intros; Qrepl H1; Refine nat_eq_refl;
intros; andE H y; andI;
  intros; Refine Q_resp; Refine H2 H4;
  intros; Refine H3; Refine S_injective H4;
Save;

Goal nat_eq_subst: {m,n|NN}(is_tt (nat_eq m n))->Q m n;
intros; Refine fst (nat_eq_character ? ?); Immed;
Save nat_eq_subst;

Goal Z_not_S: {n:NN}not (Q Z (S n));
Intros; Refine tt_not_ff (Q_sym (snd (nat_eq_character ??) H));
Save;

Goal S_not_Z: {n:NN}not (Q (S n) Z);
Intros; Refine Z_not_S n; Refine Q_sym; Immed;
Save S_not_Z;


Goal {n:NN}not (Q n (S n));
Refine Nrec [n:NN]not (Q n (S n));
Refine Z_not_S;
Intros x ih hyp; Refine ih; Refine S_injective; Immed;
Save n_not_Sn;

[is_S [n:NN] = Q n (S (pred n))];

Goal {n:NN}or (Q n Z) (is_S n);
Refine Nrec ([n:NN]or (Q n Z) (is_S n));
Refine inl; Refine Q_refl;
intros; Refine inr; Refine Q_refl;
Save ZorS;

(**)
(* add *)
Goal {n:NN}Q (add n Z) n;
Refine Nrec [n:NN]Q (add n Z) n;
Refine Q_refl;
intros n ih; Refine Q_resp_S ih;
Save addZ;

Goal {m,n:NN}Q (add n (S m)) (S (add n m));
intros m;
Refine Nrec ([n:NN]Q (add n (S m)) (S (add n m)));
Refine Q_refl;
intros x ih; Refine Q_resp_S ih;
Save addS;

[addSubstL [a,b,y|NN][h:Q a b] : Q (add a y) (add b y) =
      Q_resp ([x:NN](add x y)) h];
[addSubstR [a,b,y|NN][h:Q a b] : Q (add y a) (add y b) =
      Q_resp ([x:NN](add y x)) h];

Goal {m,k,n:NN}Q (add (add n m) k) (add n (add m k));
intros m k;
Refine Nrec [n:NN]Q (add (add n m) k) (add n ?);
Refine Q_refl;
intros x ih; Refine Q_resp_S ih;
Save addAssocR;

Goal {n,m:NN}Q (add m n) (add n m);
intros n;
Refine Nrec [m:NN]Q (add m n) (add n m);
Refine Q_sym (addZ n);
intros x ih;
Refine Q_trans; Refine S (add n x); Refine Q_resp_S ih;
Qrepl addS x n; Refine Q_refl;
Save addCommute;

Goal {n,m|NN}(Q (add n m) Z)->and (Q n Z) (Q m Z);
intros n;
Refine Nrec [m|NN](Q (add n m) Z)->and (Q n Z) (Q m Z);
intros; Refine pair; Refine Q_trans (Q_sym (addZ n)) H; Refine Q_refl;
intros; Refine Z_not_S (add n x); Qrepl (Q_sym (addS x n)); Refine Q_sym H;
Save add_strict;

Goal {i,j,k:NN}(Q (add i j) (add i k))->Q j k;
Refine Nrec [i:NN]{j,k:NN}(Q (add i j) (add i k))->Q j k;
intros;Immed;
intros;Refine Nih;Refine S_injective;Immed;
Save cancel_add;

(**)
(* subtract *)

Goal {x,y:NN}Q (sbt x (S y)) (sbt (pred x) y);
intros x;
Refine Nrec [y:NN]Q (sbt x (S y)) (sbt (pred x) y);
intros; Refine Q_refl;
intros x ih;
Refine Q_resp_pred; Immed;
Save sbt_S_pred;

Goal {x,y:NN}Q (sbt (S x) (S y)) (sbt x y);
intros; Qrepl sbt_S_pred (S x) y; Refine Q_refl;
Save sbt_respect_S;

Goal {x:NN}Q (sbt x x) Z;
Refine Nrec [x:NN]Q (sbt x x) Z;
Refine Q_refl;
intros x ih; Qrepl sbt_S_pred (S x) x; Immed;
Save sbt_x_x_eq_z;

Goal {x:NN}Q (sbt Z x) Z;
Refine Nrec [x:NN]Q (sbt Z x) Z;
Refine Q_refl;
intros x ih; Qrepl sbt_S_pred Z x; Immed;
Save sbt_Z_x_eq_Z;

Goal {m,n,t|NN}(Q (sbt n m) (S t))->Q (sbt (S n) m) (S (sbt n m));
Refine double_induct [m,n:NN]{t:NN}(Q (sbt n m) (S t))->
                                   Q (sbt (S n) m) (S (sbt n m));
intros; Refine Q_refl;
intros; Refine Q_refl;
intros; Refine Z_not_S t; Qrepl Q_sym H1;
   Qrepl sbt_Z_x_eq_Z (S x); Refine Q_refl;
intros; Qrepl sbt_respect_S (S y) x; Qrepl sbt_respect_S y x;
   Refine H ? t; Qrepl Q_sym (sbt_respect_S y x); Immed;
Save sbt_commutes_S_left;

Goal {m,n,t|NN}(Q (sbt n m) (S t))->Q (sbt n (S m)) t;
intros;
Equiv Q (pred (sbt n m)) t;
Qrepl H; Refine Q_refl;
Save sbt_commutes_S_right;

Goal {a:NN}{m,n,t|NN}(Q (sbt n m) (S t))->Q (sbt (add n a) m) (S (add t a));
Refine Nrec [a:NN]{m,n,t|NN}(Q (sbt n m) (S t))->
         Q (sbt (add n a) m) (S (add t a));
intros; Qrepl addZ n; Qrepl addZ t; Immed;
intros; Qrepl addS x n; Qrepl addS x t; Refine Nih|m|(S n)|(S t);
Qrepl Q_sym H; Refine sbt_commutes_S_left H;
Save sbt_monotone_left;


(**)
[lt : NN->NN->BB
    = Nrec ([_:NN]NN->BB)
           (Nrec ([_:NN]BB) ff ([_:NN][_:BB]tt))
           ([_:NN][ltn:NN->BB]Nrec ([_:NN]BB) ff ([x:NN][_:BB]ltn x))];

(* Le: an excursus from the library, modified  *)

[Le = [n,m:NN] Ex [k:NN] Q m (add k n) : NN->NN->Prop];

Goal Le_Z_n: {n:NN}Le Z n;
intros; Refine ExIn n; Qrepl addZ n; Refine Q_refl;
Save;

Goal {m,n|NN}(Le m n)->Le (S m) (S n);
intros;Refine H;
intros k eq;Refine ExIn k;Qrepl addS m k;
Refine Q_resp_S;Immed;
Save Le_resp_S;

Goal {m,n|NN}Le n (add m n);
intros;Refine ExIn;Refine +1 Q_refl;
Save Le_add_lemma1;

Goal {m,n|NN}Le m (add m n);
intros;Qrepl addCommute n m;
Refine Le_add_lemma1;
Save Le_add_lemma2;

Goal {m,n|NN}(Le m (S n))->or (Le m n) (Q m (S n));
intros;Refine H;
Refine Nrec [t:NN](Q (S n) (add t m))->or (Le m n) (Q m (S n));
intros;Refine inr;Refine Q_sym H1;
intros;Refine inl;Refine ExIn;Refine +1 S_injective;Immed;
Save Le_S_lemma;

Goal trans Le;
Intros x y z Lexy Leyz;Refine Lexy; 
intros t Qxty;Refine Leyz;
intros u Qyuz;Refine ExIn (add t u);
Qrepl Qyuz;
Qrepl addCommute u t;
Qrepl addAssocR t x u;
Refine Q_resp (add u);
Immed;
Save Le_trans;

Goal not_Le_Sn_Z: {n:NN}not (Le (S n) Z);
Intros n LeSnZ; Refine LeSnZ; intros t h;
Refine Z_not_S (add t n); Qrepl Q_sym (addS n t); Immed;
Save;

Goal Le_Z_Z: {n|NN}(Le n Z)->Q n Z;
intros; Refine ZorS n;
intros; Immed;
intros Sn; Refine not_Le_Sn_Z (pred n); Qrepl Q_sym Sn; Immed;
Save Le_Z_Z;

Goal S_resp_Le: {x,y:NN}(Le (S x) (S y))->Le x y;
intros x y LeSxSy; Refine LeSxSy; intros t h; Refine ExIn t;
Refine Q_resp_pred (?:Q (S y) (S (add t x))); Qrepl Q_sym (addS x t);
Refine h;
Save;

Goal Le_decidable: {m,n:NN}decidable (Le m n);
Refine double_induct [m,n:NN]or (Le m n) (not (Le m n));
Refine inl (Le_Z_n ?);
intros; Refine inl (Le_Z_n ?);
intros; Refine inr (not_Le_Sn_Z ?);
intros; Refine H y;
  intros lexy; Refine inl (Le_resp_S lexy);
  intros nlexy; Refine inr; Refine contrapos (S_resp_Le|x|y); Immed;
Save;

Goal {C|Prop}(NN->C)->(NN->C)->(C->C)->(NN->NN->C);
intros C fst_zero snd_zero inc;
Refine Nrec ([_:NN]NN -> C);
Refine fst_zero;
intros n f;Refine Nrec([_:NN]C);Refine snd_zero (S n);
intros;Refine inc (f x);
Save NN_double_iter;    (**** Unfrozen *********)

[max = NN_double_iter ([n:NN]n) ([n:NN]n) S];

Goal {x,y:NN}Le x (max x y);
Refine double_induct  [x,y:NN]Le x (max x y);
Refine ExIn Z;Refine Q_refl;
intros;Refine ExIn (S y);Qrepl addZ (S y);Refine Q_refl;
intros;Refine ExIn Z;Refine Q_refl;
intros;Equiv Le (S x) (S (max x y));Refine Le_resp_S;Immed;
Save max_Le_left;

Goal {x,y:NN}Le y (max x y);
Refine double_induct  [x,y:NN]Le y (max x y);
Refine ExIn Z;Refine Q_refl;
intros;Refine ExIn Z;Refine Q_refl;
intros;Refine ExIn (S x);Qrepl addZ (S x);Refine Q_refl;
intros;Equiv Le (S y) (S (max x y));Refine Le_resp_S;Immed;
Save max_Le_right;

Goal max_is_Le: {x,y,z|NN}(Le x z)->(Le y z)->Le (max x y) z;
Refine double_induct [x,y:NN]{z|NN}(Le x z)->(Le y z)->Le (max x y) z;
intros; Refine Le_Z_n;
intros; Refine H2;
intros; Refine H1;
intros; Equiv Le (S (max x y)) z;
Refine ZorS z;
intros qzZ; Refine not_Le_Sn_Z; Qrepl +1 Q_sym qzZ; Immed;
intros Sz; Qrepl Sz; Refine Le_resp_S; Refine H;
Refine S_resp_Le; Qrepl Q_sym Sz; Immed;
Refine S_resp_Le; Qrepl Q_sym Sz; Immed;
Save;

Goal Le_resp_max:
     {x1,y1,x2,y2|NN}(Le x1 y1)->(Le x2 y2)->Le (max x1 x2) (max y1 y2);
intros; Refine max_is_Le;
Refine Le_trans H (max_Le_left ??);
Refine Le_trans H1 (max_Le_right ??);
Save;


(* less: an arithmetic definition  *)
%\VerbFileOpen Ltverb
[Lt [n,m:NN] = Ex[x:NN] Q (add n (S x)) m];
%\VerbFileClos Ltverb

Goal Lt_Z_Sn: {n:NN}Lt Z (S n);
intros; Refine ExIn n; Refine Q_refl;
Save Lt_Z_Sn;

Goal Lt_incl_S: {n:NN}Lt n (S n);
Intros n; Refine ExIn Z;
Refine Q_subst (addCommute ? ?) [t:NN]Q t ?; Refine Q_refl;
Save Lt_incl_S;

Goal Lt_trans: {x,y,z|NN}(Lt x y)->(Lt y z)->(Lt x z);
Intros x y z Ltxy Ltyz;
Refine Ltxy; Intros t QxSty; Refine Ltyz; Intros u QySuz;
Refine ExIn (S (add t u));
Equiv Q (add x (add (S (S t)) u)) z;
Refine Q_subst (addAssocR ? ? ?) [t:NN]Q t z;
Refine Q_subst (Q_sym (addS ? ?)) [t:NN]Q (add t u) z;
Refine Q_subst (Q_sym QxSty) [t:NN]Q (add (S t) u) z;
Equiv Q (S (add y u)) z;
Refine Q_subst (addS u y) [t:NN]Q t z;
Immed;
Save Lt_trans;

Goal not_Lt_n_Z: {n:NN}not (Lt n Z);
Intros n LtnZ; Refine LtnZ; Intros t h;
Refine Z_not_S (add n t); Qrepl Q_sym (addS t n); Refine Q_sym h;
Save;

Goal Lt_resp_S: {x,y:NN}iff (Lt x y) (Lt (S x) (S y));
Intros x y; Refine pair;
Intros Ltxy; Refine Ltxy; Intros t h; Refine ExIn t;
Refine Q_resp_S h;
Intros LtSxSy; Refine LtSxSy; Intros t h; Refine ExIn t;
Refine Q_resp_pred h;
Save Lt_resp_S;

Goal LtnSm_character: {n,m|NN}(Lt n (S m))->or (Lt n m) (Q n m);
intros; Refine H; 
Refine Nrec [t:NN](Q (add n (S t)) (S m))->or (Lt n m) (Q n m);
intros; Refine inr; Refine S_injective;
   Qrepl Q_sym H1; Qrepl addS Z n; Qrepl addZ n; Refine Q_refl;
intros; Refine inl; Refine ExIn x; Refine S_injective;
   Qrepl Q_sym H1; Refine Q_sym; Refine addS;
Save LtnSm_character;

Goal not_Lt_n_n: {n|NN}not (Lt n n);
Refine Nrec [n:NN]not (Lt n n);
Refine not_Lt_n_Z;
Intros; Refine Nih; Refine snd (Lt_resp_S ??) H;
Save not_Lt_n_n;

Goal Lt_not_Q: {x,y|NN}(Lt x y)->not (Q y x);
Refine double_induct [x,y:NN](Lt x y)->not (Q y x);
intros; Refine not_Lt_n_Z; Immed;
Intros; Refine Z_not_S ? (Q_sym H2);
intros; Refine Z_not_S;
Intros; Refine H y; Refine snd (Lt_resp_S ??);
   Refine +1 S_injective; Immed;
Save Lt_not_Q;

(* Lt and add *)
Goal add_resp_Lt_left: {i,j|NN}(Lt i j)->{n:NN}Lt (add i n) (add j n);
intros i j Ltij;
Refine Nrec [n:NN]Lt (add i n) (add j n);
Qrepl addZ i; Qrepl addZ j; Immed;
intros x Ltixjx;
Qrepl addS x i; Qrepl addS x j;
Refine fst (Lt_resp_S (add i x) (add j x)); Immed;
Save add_resp_Lt_left;

Goal add_resp_Lt_right: {i,j|NN}(Lt i j)->{n:NN}Lt (add n i) (add n j);
intros; Qrepl addCommute i n; Qrepl addCommute j n;
Refine add_resp_Lt_left; Immed;
Save add_resp_Lt_right;

Goal Lt_add_S_left: {i,j:NN}Lt j (S (add i j));
intros;Equiv Lt (add Z j) (add (S i) j);
Refine add_resp_Lt_left;Refine Lt_Z_Sn;
Save Lt_add_S_left;

Goal Lt_add_S_right: {i,j:NN}Lt i  (S (add i j));
intros;Qrepl addCommute j i;Refine Lt_add_S_left;
Save Lt_add_S_right;

Goal Lt_S_add: {n,m,l|NN}(Lt (S (add n m)) l)->and (Lt n l) (Lt m l);
Refine double_induct [n,m:NN]{l|NN}(Lt (S (add n m)) l)->and (Lt n l) (Lt m l);
intros;Refine pair;Refine ?+1;
Refine Lt_trans;Refine +1 Lt_Z_Sn;Immed;
intros;Refine pair (fst (H ?));Refine ?+1;
Refine Lt_trans;Refine +1 Lt_incl_S;Immed;
intros;Refine pair;Refine +1 Lt_trans;Refine ?+3;
Refine Lt_Z_Sn;Refine Lt_trans;Refine +1 Lt_incl_S;
Qrepl Q_sym (addZ (S x));Immed;
intros;Refine pair (fst (H1 ?)) (snd (H (S y) ?));
Qrepl Q_sym (addS y x);Refine ?+1;
Refine Lt_trans;Refine +1 Lt_incl_S;Immed;
Save Lt_S_add;

Goal add_resp_Lt: {i,j,a,b|NN}(Lt i a)->(Lt j b)->Lt (add i j) (add a b);
intros ____ ia jb; Refine ia; intros n nh; Refine jb; intros m mh;
Refine ExIn (S (add n m)); Qrepl Q_sym nh; Qrepl Q_sym mh;
Qrepl addS (S (add n m)) (add i j); Qrepl addS (add n m) (add i j);
Qrepl addS n i; Qrepl addS m j; Qrepl addS (add j m) (S (add i n));
Refine Q_resp_S; Refine Q_resp_S; Equiv Q ? (add ??);
Qrepl addAssocR n (add j m) i; Qrepl Q_sym (addAssocR j m n);
Qrepl addCommute j n; Qrepl addAssocR n m j;
Qrepl Q_sym (addAssocR j (add n m) i); Refine Q_refl;
Save;

(* complete induction *)
%\VerbFileOpen completeInduction_verb
Goal complete_induction:
     {P:NN->Prop}{ih:{n:NN}({x:NN}(Lt x n)->(P x))->P n}{m:NN}P m;
%\VerbFileClos completeInduction_verb
intros; Refine ih;
Refine Nrec [m:NN]{x:NN}(Lt x m)->P x;
intros; Refine not_Lt_n_Z; Immed;
intros; Refine LtnSm_character; Immed;
intros; Refine ih; Qrepl H1; Immed;
Save;

(* Well-Founded induction *)
%\VerbFileOpen WFinduction_verb
Goal WF_induction:
     {T|Prop}{f|T->NN}{P:T->Prop}
     {wf_ih:{t:T}({x:T}(Lt (f x) (f t))->(P x))->P t}
     {k:T}P k;
%\VerbFileclos WFinduction_verb
intros;
Refine complete_induction [n:NN]{y:T}(Q n (f y))->P y;
intros; Refine wf_ih;
intros; Refine H; Refine f x; Qrepl H1; Refine H2; Refine Q_refl;
Refine f k; Refine Q_refl;
Save;

(* lexicograpic induction is nested complete induction *)
%\VerbFileOpen complete2Induction_verb
Goal complete2_induction:
     {P:NN->NN->Prop}
     {wf_ih:{n,m:NN}
        {ih:{x,y:NN}(or (Lt x n) (and (Q x n) (Lt y m)))->P x y}
           P n m}
     {n,m:NN}P n m;
%\VerbFileClos complete2Induction_verb
intros;
Refine complete_induction [n:NN]{m:NN}P n m;
intros;
Refine complete_induction [m1:NN](P n1 m1);
intros; Refine wf_ih;
intros; Refine H2;
intros; Refine H; Immed;
intros; Qrepl fst H3;
Refine H1; Refine snd H3;
Save;

(* really want this WF2_induction *)
%\VerbFileOpen WF2induction_verb
Goal WF2_induction:
     {A|Prop}{f,g:A->NN}{P:A->Prop}
     {wf_ih:{n:A}
        {ih:{x:A}(or (Lt (f x) (f n))
                     (and (Q (f x) (f n)) (Lt (g x) (g n))))->P x}
           P n}
     {n:A}P n;
%\VerbFileClos WF2induction_verb
intros;
Refine complete2_induction [n,m:NN]{x:A}(Q n (f x))->(Q m (g x))->P x;
intros; Refine wf_ih; intros; Refine ih;
Refine f x1; Refine g x1;
Refine H2;
intros; Qrepl H; Refine inl; Immed;
intros; Qrepl H; Qrepl H1; Refine inr; Immed;
Refine Q_refl; Refine Q_refl; 
Refine f n; Refine g n; Refine Q_refl; Refine Q_refl;
Save;


(**)
(* lists *)
%\VerbFileOpen LLverb
Inductive [LL:Prop] Parameters [A|Prop] Constructors [NIL:LL][CONS:A->LL->LL];

[unit [a:A] = CONS a NIL];
[hd [a:A][l:LL] = LL_elim ([_:LL]A) a ([x:A][_:LL][_:A]x) l];
[tl [l:LL] = LL_elim ([_:LL]LL) NIL ([_:A][k,_:LL]k) l];
[append [k,l:LL] = LL_elim ([_:LL]LL) l ([a:A][_,j:LL]CONS a j) k];
[length = LL_elim ([_:LL]NN) Z ([_:A][_:LL]S)];

[exist [P:A->BB] : LL->BB =
    LL_elim ([_:LL]BB) ff ([b:A][_:LL][rest:BB]orr (P b) rest)];
[member [eq:A->A->BB][a:A] : LL->BB = exist (eq a)];
%\VerbFileClos LLverb

[LLrec = LL_elim
       : {C:LL->Prop}
         {Lbase:C NIL}
         {Lstep:{b:A}{prem:LL}{LLih:C prem}C (CONS b prem)}
         {l:LL}C l];

[sublist [eq:A->A->BB][k,l:LL]
        = {a|A}(is_tt (member eq a k)) -> is_tt (member eq a l)];
[nth [n:NN][l:LL][a:A] : A =
     [zro [k:LL] = hd a k]
     [suc [_:NN][f:LL->A][k:LL] = f (tl k)]
       Nrec ([_:NN]LL->A) zro suc n l];
[listRemove [eq:A->BB] : LL->LL =
     LLrec ([_:LL]LL) NIL ([b:A][_:LL][k:LL]if (eq b) k (CONS b k))];
[noDups [eq:A->A->BB] : LL->BB =
   LLrec ([_:LL]BB)
         tt
         ([a:A][as:LL][rest:BB]andd (nott (member eq a as)) rest)];

[Q_resp_tl [k,l|LL][h:Q k l]
        : Q (tl k) (tl l) = Q_resp|LL|LL tl h];
[Q_resp_hd [k,l|LL][a,b|A][h:Q (CONS a k) (CONS b l)]
        : Q a b = Q_resp|LL|A (hd a) h];
[CONS_injective [k,l|LL][a,b|A][h:Q (CONS a k) (CONS b l)]
        : Q k l = Q_resp_tl h];

Goal {a,b|A}(Q a b)->{k,l|LL}(Q k l)->Q (CONS a k) (CONS b l);
intros; Qrepl H; Qrepl H1; Refine Q_refl;
Save Q_resp_CONS;

Goal {l|LL}(Q (length l) Z)->(Q l NIL);
Refine LLrec [l:LL](Q (length l) Z)->(Q l NIL);
intros; Refine Q_refl;
intros; Refine Z_not_S ? (Q_sym H);
Save length_Z_NIL;

Goal {C:LL->LL->Prop}
     (C NIL NIL)->
     ({b:A}{l:LL}(C NIL l)->C NIL (CONS b l))->
     ({b:A}{x:LL}({y:LL}C x y)->C (CONS b x) NIL)->
     ({b:A}{x:LL}({y:LL}C x y)->{c:A}{y:LL}(C (CONS b x) y)->
                    C (CONS b x) (CONS c y))->
     {x,y:LL}C x y;
intros C bb bs sb ss; Refine LLrec [x:LL]{y:LL}C x y;
Refine LLrec (C NIL); Immed;
intros b x h; Refine LLrec (C (CONS b x));
Refine sb b x h; Refine ss b x h;
Save list_double_induct;    (**** Unfrozen *********)

Goal NIL_or_CONS:
     {l:LL}or (Q l NIL) (Ex2 [a:A][j:LL] Q l (CONS a j));
intros _;
Refine LLrec [l:LL]or (Q l NIL) (Ex2 [a:A][j:LL] Q l (CONS a j));
Refine inl; Refine Q_refl;
intros; Refine inr; Refine Ex2In b prem; Refine Q_refl;
Save;

$[NIL_not_CONS:{l|LL}{a|A}not (Q NIL (CONS a l))];

Goal {l:LL}{a:A}not (Q l (CONS a l));
Refine LLrec [l:LL]{a:A}not (Q l (CONS a l));
intros; Refine NIL_not_CONS;
Intros _____; Refine LLih b;
Refine CONS_injective; Refine +2 H;
Save l_not_CONSl;

Goal {l:LL}{a:A}Ex2 [b:A][m:LL]Q (CONS a l) (append m (unit b));
Refine LLrec [l:LL]{a:A}Ex2 [b:A][m:LL]Q (CONS a l) (append m (unit b));
intros;Refine Ex2In a NIL;Refine Q_refl;
intros;Refine LLih b;
intros c m eq;Qrepl eq;Refine Ex2In c (CONS a m);Refine Q_refl;
Save non_nil_list_lem;

Goal {k,l:LL}{a:A}
        Ex2 [b:A][j:LL]Q (append k (CONS a l)) (CONS b j); 
Refine LLrec [k:LL]{l:LL}{a:A}
        Ex2 [b:A][j:LL]Q (append k (CONS a l)) (CONS b j);
intros; Refine Ex2In a l; Refine Q_refl;
intros; Refine Ex2In b (append prem (CONS a l)); Refine Q_refl;
Save append_CONS;

Goal {a:A}{k,l:LL}not (Q NIL (append k (CONS a l)));
intros; Refine append_CONS k l a; intros;
Qrepl H; Refine NIL_not_CONS;
Save NIL_not_append_CONS;

Goal {l:LL}(Q (append l (NIL)) l);
Refine LLrec [l:LL](Q (append l (NIL)) l);
Refine Q_refl;
intros;Equiv Q (CONS b (append prem (NIL))) (CONS b prem);
Refine Q_resp;Immed;
Save append_nil;

Goal {j,k,l:LL}Q (append j (append k l))
                 (append (append j k) l);
intros _;
Refine LLrec [j:LL]{k,l:LL}Q (append j (append k l))
                             (append (append j k) l);
(* case NIL *)
intros; Refine Q_refl;
(* case CONS *)
intros;
Equiv Q (CONS b (append prem (append k l)))
        (CONS b (append (append prem k) l));
Qrepl LLih k l; Refine Q_refl;
Save append_associative;

(* fold *)
%\VerbFileOpen fold
[B|Prop][g:A->B->B];
[foldright [l:LL][strt:B] = LL_elim ([_:LL]B) strt ([a:A][_:LL][b:B]g a b) l];
[foldleft = LL_elim ([_:LL]B->B) ([b:B]b) ([a:A][_:LL][f:B->B][b:B]f (g a b))];

Goal foldright_append_lem:
     {G,H:LL}{b:B}Q (foldright (append G H) b) (foldright G (foldright H b));
%\VerbFileNoRecord fold
Refine LLrec [G:LL]{H:LL}{b:B}
              Q (foldright (append G H) b) (foldright G (foldright H b));
intros; Refine Q_refl;
intros;
Equiv Q (g b (foldright (append prem H) b1))
        (g b (foldright prem (foldright H b1)));
Qrepl LLih H b1;Refine Q_refl;
Save foldright_append_lem;

%\VerbFileRecord fold
Goal foldleft_append_lem:
     {G,H:LL}{b:B}Q (foldleft (append G H) b) (foldleft H (foldleft G b));
%\VerbFileClos fold
Refine LLrec [G:LL]{H:LL}{b:B}
              Q (foldleft (append G H) b) (foldleft H (foldleft G b));
intros; Refine Q_refl;
intros;
Equiv Q (foldleft (append prem H) (g b b1))
        (foldleft H (foldleft prem (g b b1)));
Qrepl LLih H (g b b1);Refine Q_refl;
Save foldleft_append_lem;

Discharge g;

(* member *)
Goal {eq|A->A->BB}{a|A}(is_tt (eq a a))->
     {l:LL}is_tt (member eq a (CONS a l));
intros; Equiv is_tt (orr ? (member ???));
Qrepl H; Refine Q_refl;
Save member_hd;

Goal {P:A->BB}{j,k:LL}
        Q (exist P (append j k))
          (orr (exist P  j) (exist P k));
intros;
Refine LLrec [j:LL]Q (exist P (append j k))
                     (orr (exist P j) (exist P k));
Refine Q_refl;
intros;
Equiv Q (orr (P b) (exist P (append prem k)))
        (orr (orr (P b) (exist P prem)) ?);
Qrepl orr_associates (P b) (exist P prem) (exist P k);
Qrepl LLih; Refine Q_refl;
Save exist_append_lem;

Goal {eq:A->A->BB}{a:A}{j,k:LL}
        Q (member eq a (append j k))
          (orr (member eq a j) (member eq a k));
intros; Refine exist_append_lem (eq a) j k;
Save member_append_lem;

Goal {P:A->BB}{j,k|LL}
        (is_ff (exist P (append j k)))->
          is_ff (orr (exist P  j) (exist P k));
intros; Qrepl Q_sym (exist_append_lem P j k); Immed;
Save exist_append_lem';

Goal {eq:A->A->BB}{a:A}{j,k|LL}
        (is_ff (member eq a (append j k)))->
          is_ff (orr (member eq a j) (member eq a k));
intros; Refine exist_append_lem' (eq a) H;
Save member_append_lem';

(***********
Goal {eq:A->A->BB}{a:A}{j,k|LL}
        (is_ff (member eq a (append j k)))->
          and (is_ff (member eq a j)) (is_ff (member eq a k));
intros; Refine exist_append_lem' (eq a) H;
Save not_member_append2;
************)

Goal {eq:A->A->BB}{a|A}{l|LL}(is_tt (member eq a (tl l)))->
     is_tt (member eq a l);
intros __;
Refine LLrec [l:LL](is_tt (member eq a (tl l)))->is_tt (member eq a l);
intros; Immed;
intros;Refine snd (orr_character ? (member eq a prem));
Refine inr H;
Save member_tl_lem;

Goal {P:A->BB}{l:LL}is_ff (exist P (listRemove P l));
intros P;
Refine LLrec [l:LL]is_ff (exist P (listRemove P l));
Refine Q_refl;
intros;
Equiv is_ff (exist P (if (P b)
                      (listRemove P prem)
                      (CONS b (listRemove P prem))));
Refine tt_or_ff (P b);
intros Pb; Qrepl Pb; Expand if; Immed;
intros nPb; Qrepl nPb; Expand if;
Refine snd (deMorgan ? ?); Refine pair; Immed;
Save member_listRemove_lem;

Goal {eq|A->A->BB}{eq_refl:{a:A}is_tt (eq a a)}
     {l|LL}(sublist eq l (NIL))->Q l (NIL);
intros __;Refine LLrec [l|LL]{sub:sublist eq l (NIL)}Q l (NIL);
intros;Refine Q_refl;
intros;Refine tt_not_ff;Refine Q_sym;Refine sub;
Refine +1 snd (orr_character ? (member ? ? ?));
Refine +1 inl;Refine +1 eq_refl;
Save sublist_nil;

(* list structural equality *)
[list_eq [eq:A->A->BB] : LL->LL->BB =
   LLrec ([_:LL]LL->BB)
         (LLrec ([_:LL]BB) tt ([_:A][_:LL][_:BB]ff))
         ([a:A][_:LL][rest:LL->BB]
            LLrec ([_:LL]BB)
                  ff
                  ([b:A][k:LL][_:BB]andd (eq a b) (rest k)))];

Goal {eq|A->A->BB}({a:A}is_tt (eq a a))->{l:LL}is_tt (list_eq eq l l);
intros;
Refine LLrec [l:LL]is_tt (list_eq eq l l);
Refine Q_refl;
intros; Refine snd (andd_character ? (list_eq ? ? ?));
Refine pair (H b) LLih;
Save list_eq_refl;

Goal list_eq_sym:
     {eq|A->A->BB}({a,b|A}(is_tt (eq a b))->is_tt (eq b a))->
     {l,k|LL}(is_tt (list_eq eq l k))->is_tt (list_eq eq k l);
intros eq eqHyp;
Refine list_double_induct [l,k:LL](is_tt (list_eq eq l k))->
                                          is_tt (list_eq eq k l);
intros; Refine Q_refl;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros;
[lem : and (is_tt (eq b c)) (is_tt (list_eq eq x y))
     = fst (andd_character ??) H2];
Refine snd (andd_character ? (list_eq ???)); Refine pair;
Refine eqHyp (fst lem); Refine H ? (snd lem);
Save;

Goal list_eq_subst:
     {eq|A->A->BB}({a,b|A}(is_tt (eq a b))->Q a b)->
     {l,k|LL}(is_tt (list_eq eq l k))->Q l k;
intros eq eqHyp;
Refine list_double_induct [l,k:LL](is_tt (list_eq eq l k))->Q l k;
intros; Refine Q_refl;
intros; Refine tt_not_ff (Q_sym H1);
intros; Refine tt_not_ff (Q_sym H1);
intros;
[lem : and (is_tt (eq b c)) (is_tt (list_eq eq x y))
     = fst (andd_character ? ?) H2];
Refine Q_resp_CONS; Refine eqHyp (fst lem); Refine H ? (snd lem);
Save;

(* A well-founded induction on lists *)
Goal {P:LL->Prop}
     {ih:{l:LL}({x:LL}(Lt (length x) (length l))->(P x))->P l}
     {k:LL}P k;
intros; Claim {y:LL}(Lt (length y) (length k))->P y; Refine ih k ?+1;
Refine LLrec [k:LL]{y:LL}(Lt (length y) (length k))->P y;
intros; Refine not_Lt_n_Z; Immed;
intros; Refine LtnSm_character H;
intros; Refine LLih y H1;
intros; Refine ih; Qrepl H1; Refine LLih;
Save WF_list_induction;

DischargeKeep A;

(* the true map function *)
[C|Prop][g:B->C][f:A->B];

[map : (LL|A)->(LL|B) =
   LLrec ([_:LL|A]LL|B) (NIL|B) ([a:A][_:LL|A][k:LL|B]CONS (f a) k)];

Goal {l|LL|A}(Q (map l) (NIL|B))->Q l (NIL|A);
Refine LLrec [l|LL|A]{eq:Q (map l) (NIL|B)}Q l (NIL|A);
intros;Refine Q_refl;
intros;Refine NIL_not_CONS (Q_sym eq);
Save map_nil;

Goal {G,H:LL|A}Q (map (append G H)) (append (map G) (map H));
Refine LLrec [G:LL|A]{H:LL|A}
              Q (map (append G H)) (append (map G) (map H));
intros; Refine Q_refl;
intros;
Equiv Q (CONS (f b) (map (append prem H)))
        (CONS (f b) (append (map prem) (map H)));
Qrepl LLih H; Refine Q_refl;
Save map_append_lem;

DischargeKeep A;

Goal {G:LL|A}Q (map (compose g f) G) ((compose (map g) (map f)) G);
Refine LLrec [G:LL|A]Q (map (compose g f) G)
                       ((compose (map g) (map f)) G);
Refine Q_refl;
intros;Equiv Q (CONS (g (f ?)) (map ? ?))
               (CONS (g (f ?)) (compose (map ?) (map ?) ?));
Refine Q_resp;Immed;
Save map_compose_lem;

Discharge A;

(**)
(* "there are infinitely many nats" *)
[nats = LL|NN];

Goal {l:nats}ex[n:NN] {m|NN}(is_tt (member nat_eq m l))->Lt m n;
Refine LLrec [l:nats]ex[n:NN] {m|NN}(is_tt (member nat_eq m l))->Lt m n;
(* nil *)
Refine exIn Z; intros; Refine tt_not_ff (Q_sym H);
(* cons *)
intros; Refine LLih; intros m mhyp; Refine exIn (S (add m b));
intros; Refine fst (orr_character ? (member nat_eq m1 prem)) H;
intros; Qrepl nat_eq_subst H1; Refine Lt_add_S_left;
intros; Refine Lt_trans (mhyp H1); Refine Lt_add_S_right;
Save bigger_than_any_in_list;

%\VerbFileOpen NNinf
Goal NNinf: {l:nats}ex[n:NN] is_ff (member nat_eq n l);
%\VerbFileClos NNinf
Refine LLrec [l:nats]ex[n:NN] is_ff (member nat_eq n l);
(* nil *)
Refine exIn Z; Refine Q_refl;
(* cons *)
intros; 
Refine bigger_than_any_in_list (CONS b prem); intros n nhyp;
Refine exIn n; Refine snd (deMorgan ? (member nat_eq n prem));
Refine pair;
Refine cross_contrapos_tt_P (fst (nat_eq_character ??));
Refine Lt_not_Q (nhyp (member_hd (nat_eq_refl b) ?));
Refine tt_or_ff (member nat_eq n prem);
intros ttmem; Refine not_Lt_n_n|n;
Refine nhyp (member_tl_lem nat_eq|n|(CONS b prem) ttmem);
intros; Immed;
Save;

(**)
(* pairs *)
%\VerbFileOpen PRODverb
Inductive [PROD:Prop] Parameters [A,B|Prop] Constructors [Pr:A->B->PROD];

[Fst = PROD_elim ([_:PROD]A) ([a:A][b:B]a)];
[Snd = PROD_elim ([_:PROD]B) ([a:A][b:B]b)];
%\VerbFileClos PRODverb

[PRODrec = PROD_elim
         : {C:PROD->Prop}({a:A}{b:B}C (Pr a b))->{g:PROD}C g];

(* equality of pairs *)
Goal Q_resp_proj:
     {u,v|PROD}(Q u v)->(and (Q (Fst u) (Fst v)) (Q (Snd u) (Snd v)));
intros; Refine pair;
Refine Q_resp|PROD|A Fst H; Refine Q_resp|PROD|B Snd H;  (* ??? *)
Save Q_resp_proj;

(* Fst and Snd are proper destructors *)
%\VerbFileOpen PROD_surj_pair
Goal PROD_surj_pair: {b:PROD}Q b (Pr (Fst b) (Snd b));
%\VerbFileClos PROD_surj_pair
Refine PRODrec [b:PROD]Q b (Pr (Fst b) (Snd b));
intros; Refine Q_refl;
Save PROD_surj_pair;

Goal {p,q|A}(Q p q)->{A,B|B}(Q A B)->Q (Pr p A) (Pr q B);
intros; Qrepl H; Qrepl H1; Refine Q_refl;
Save Q_resp_Pr;

(**)
(* lists of pairs *)

[lefts : (LL|PROD)->(LL|A) = map Fst];
[rights : (LL|PROD)->(LL|B) = map Snd];

[eq:A->BB][dummy:B];
[assoc [abs:LL|PROD] : B
      = foldright ([x:PROD][rest:B]if (eq (Fst x)) (Snd x) rest) abs dummy];

Goal {abs|LL|PROD}(is_ff (exist eq (lefts abs))) ->
      Q (assoc abs) dummy;
Refine LLrec [abs|LL|PROD]
             {nocc:is_ff (exist eq (lefts abs))}
              Q (assoc abs) dummy;
intros;Refine Q_refl;
intros;Refine fst (deMorgan (eq (Fst b)) (exist eq (lefts prem))) nocc;
intros neqA nocc_prem;Equiv Q (if ? ? (assoc ?)) ?;
Qrepl neqA;Qrepl LLih nocc_prem;Refine Q_refl;
Save assoc_dummy_lem;

DischargeKeep dummy;

[dummy':B];

Goal {abs|LL|PROD}(is_tt (exist eq (lefts abs))) ->
      Q (assoc dummy abs) (assoc dummy' abs);
Refine LLrec [abs|LL|PROD]
             {occ:is_tt (exist eq (lefts abs))}
              Q (assoc dummy abs) (assoc dummy' abs);
intros;Refine tt_not_ff;Refine Q_sym;Immed;
intros;Equiv Q (if ? ? (assoc ? ?)) (if ? ? (assoc ? ?));
Refine fst (orr_character (eq (Fst b)) (exist eq (lefts prem))) occ;
intros eqA;Qrepl eqA;Refine Q_refl;
intros occ_prem;Qrepl LLih occ_prem;Refine Q_refl;
Save assoc_occurs_lem;

Discharge dummy';

Goal {abs1|LL|PROD}(is_tt (exist eq (lefts abs1))) ->
     {abs2:LL|PROD} Q (assoc dummy (append abs1 abs2)) (assoc dummy abs1);
intros;
Qrepl foldright_append_lem
      ([x:PROD][rest:B]if (eq (Fst x)) (Snd x) rest)
      abs1 abs2 dummy;
Qrepl assoc_occurs_lem (assoc dummy abs2) H;
Refine Q_refl;
Save assoc_append_lem_left;

Goal {abs1|LL|PROD}(is_ff (exist eq (lefts abs1))) ->
     {abs2:LL|PROD} Q (assoc dummy (append abs1 abs2)) (assoc dummy abs2);
intros;
Qrepl foldright_append_lem
      ([x:PROD][rest:B]if (eq (Fst x)) (Snd x) rest)
      abs1 abs2 dummy;
Qrepl assoc_dummy_lem (assoc dummy abs2) H;
Refine Q_refl;
Save assoc_append_lem_right;

[zip [as:LL|A][bs:LL|B] : LL|PROD
    = foldright ([a:A][_:(LL|B)->LL|PROD]map (Pr a))
                  as ([_:LL|B]NIL|PROD) bs];
                
[listSub [a:A] : (LL|A)->(LL|A) = map ([b:A]if (eq b) a b)];

DischargeKeep A;

[C|Prop][f:B->C];

Goal {abs:LL|(PROD|A|B)}
      Q (f (assoc eq dummy abs))
        (assoc eq (f dummy) (map ([ab:PROD|A|B]Pr (Fst ab) (f (Snd ab))) abs));
Refine LLrec [abs:LL|(PROD|A|B)]Q (f (assoc eq dummy abs))
        (assoc eq (f dummy) (map ([ab:PROD|A|B]Pr (Fst ab) (f (Snd ab))) abs));
Refine Q_refl;
intros;Qrepl if_inside f (Snd b) (assoc eq dummy prem) (eq (Fst b));
Qrepl LLih;Refine Q_refl;
Save assoc_map_lem;

Discharge A;


(**********  for Cutting in to define some PTSs  *********

(* lambda cube *)
[star = tt];
[box = ff];
[Cube_ax [s1,s2:BB] = and (Q s1 star) (Q s2 box)];
[PCC_rl [_,s2,s3:BB] = Q s2 s3];
[LF_rl [s1,s2,s3:BB] = and (Q s1 star) (Q s2 s3)];
********************************)
