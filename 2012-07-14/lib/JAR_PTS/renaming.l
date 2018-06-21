Module renaming 
Import terms alpha context Vclosed;

(* renamings, as a prelude to the thinning lemma *)
%\VerbFileOpen renaming_verb
[rp = PROD|PP|PP];
[Renaming = LL|rp];
%\VerbFileClos renaming_verb

%\VerbFileOpen renX_verb
[renPar [rho:Renaming][p:PP] : PP = assoc (PPeq p) p rho];

[renTrm [rho:Renaming] : Trm->Trm =
  Trec ([_:Trm]Trm)
       ([s:SS]sort s)
       ([v:VV]var v)
       ([p:PP]par (renPar rho p))
       ([v:VV][_,_,l,r:Trm]pi v l r)
       ([v:VV][_,_,l,r:Trm]lda v l r)
       ([_,_,l,r:Trm]app l r)];

[renGB [rho:Renaming] : GB->GB =
  GBrec ([_:GB]GB) ([p:PP][t:Trm](Gb (renPar rho p) (renTrm rho t)))];
        
[renCxt [rho:Renaming] : Cxt->Cxt = map (renGB rho)];
%\VerbFileClos renX_verb

[renId = NIL|rp:Renaming];

[rho:Renaming];

Goal {M:Trm}Q (isSrt (renTrm rho M)) (isSrt M);
Refine Trec [M:Trm]Q (isSrt (renTrm rho M)) (isSrt M);
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save renTrm_isSrt;

Goal {M:Trm}Q (isVar (renTrm rho M)) (isVar M);
Refine Trec [M:Trm]Q (isVar (renTrm rho M)) (isVar M);
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save renTrm_isVar;

Goal {M:Trm}Q (isPar (renTrm rho M)) (isPar M);
Refine Trec [M:Trm]Q (isPar (renTrm rho M)) (isPar M);
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save renTrm_isPar;

Goal {M:Trm}Q (isPi (renTrm rho M)) (isPi M);
Refine Trec [M:Trm]Q (isPi (renTrm rho M)) (isPi M);
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save renTrm_isPi;

Goal {M:Trm}Q (isLda (renTrm rho M)) (isLda M);
Refine Trec [M:Trm]Q (isLda (renTrm rho M)) (isLda M);
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save renTrm_isLda;

Goal {M:Trm}Q (isApp (renTrm rho M)) (isApp M);
Refine Trec [M:Trm]Q (isApp (renTrm rho M)) (isApp M);
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
Save renTrm_isApp;

Discharge rho;

Goal {M:Trm}Q M (renTrm renId M);
Refine Trec [M:Trm]Q M (renTrm renId M);
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Refine Q_refl;
intros;Equiv Q (pi n A B) (pi n (renTrm renId A) (renTrm renId B));
       Qrepl Q_sym ihA;Qrepl Q_sym ihB;Refine Q_refl;
intros;Equiv Q (lda n A B) (lda n (renTrm renId A) (renTrm renId B));
       Qrepl Q_sym ihA;Qrepl Q_sym ihB;Refine Q_refl;
intros;Equiv Q (app A B) (app (renTrm renId A) (renTrm renId B));
       Qrepl Q_sym ihA;Qrepl Q_sym ihB;Refine Q_refl;
Save renTrm_Id;

Goal {b:GB}Q b (renGB renId b);
Refine GBrec [b:GB]Q b (renGB renId b);
intros; Equiv Q ? (Gb ? ?);
Qrepl Q_sym (renTrm_Id b); Refine Q_refl;
Save renGB_Id;

Goal {G:Cxt}Q G (renCxt renId G);
Refine LLrec [G:Cxt]Q G (renCxt renId G);
Refine Q_refl;
intros;Equiv Q ? (CONS (renGB ? ?) (renCxt ? ?));
Qrepl Q_sym (renGB_Id b);Qrepl Q_sym LLih;Refine Q_refl;
Save renCxt_Id;


(*******  new ******)
Goal {r|PP}{rho|Renaming}(is_ff (member PPeq r (lefts rho)))->
     Q r (renPar rho r);
intros r;
Refine LLrec [rho:Renaming](is_ff (member PPeq r (lefts rho)))->
     Q r (renPar rho r);
intros; Refine Q_refl;
intros;
Equiv Q r (if (PPeq r (Fst b)) (Snd b) (renPar prem r));
Refine fst (deMorgan (PPeq r (Fst b)) (member PPeq r (lefts prem))) H;
intros h g; Qrepl h; Refine LLih; Immed;
Save triv_renPar_transpose_left;

(***************
Goal {r|PP}{rho|Renaming}(is_ff (member PPeq r (rights rho)))->
     {p|PP}(Q r (renPar rho p))->(Q r p);
intros r;
Refine LLrec [rho:Renaming](is_ff (member PPeq r (rights rho)))->
     {p|PP}(Q r (renPar rho p))->(Q r p);
intros; Immed;
intros;
Refine fst (deMorgan (PPeq r (Snd b)) (member PPeq r (rights prem))) H;
intros h g; Refine tt_or_ff (PPeq p (Fst b));
intros eqpb; Refine tt_not_ff; Qrepl Q_sym h; Qrepl H1;
Qrepl PROD_surj_pair b; Qrepl Q_sym (PPdecide eqpb);
Equiv Q tt (PPeq (if (PPeq p p) (Snd b) (renPar  prem p)) (Snd b));
Qrepl PPrefl p; Refine Q_sym; Refine PPrefl;

intros neqpb; Qrepl neqpb; Refine LLih; Immed;
Save triv_renPar_transpose_right;
*****************)

Goal {r|PP}{rho|Renaming}(is_ff (member PPeq r (rights rho)))->
     {p|PP}(is_ff (PPeq r p))->is_ff (PPeq r (renPar rho p));
intros r;
Refine LLrec [rho:Renaming](is_ff (member PPeq r (rights rho)))->
     {p|PP}(is_ff (PPeq r p))->is_ff (PPeq r (renPar rho p));
intros; Immed;
intros;
Equiv is_ff (PPeq r (if (PPeq p (Fst b)) (Snd b) (renPar prem p)));
Refine fst (deMorgan (PPeq r (Snd b)) (member PPeq r (rights prem))) H;
intros h g; Refine tt_or_ff (PPeq p (Fst b));
intros eqpb; Qrepl eqpb; Immed;
intros neqpb; Qrepl neqpb; Refine LLih; Immed;
Save triv_renPar_transpose_right;

%\VerbFileOpen renTrm_is_conjugated_psub_verb
Goal renTrm_is_conjugated_psub:
     {r|PP}{M|Trm}(is_ff (poccur r M))->
     {rho|Renaming}(is_ff (member PPeq r (lefts rho)))->
                   (is_ff (member PPeq r (rights rho)))->
     {p,q:PP}Q (renTrm (CONS (Pr p q) rho) M)
               (psub (par q) r (renTrm rho (psub (par r) p M)));
%\VerbFileClos renTrm_is_conjugated_psub_verb
intros r;
Refine not_pocc_Trec ([r:PP][M:Trm]
     {rho|Renaming}(is_ff (member PPeq r (lefts rho)))->
                   (is_ff (member PPeq r (rights rho)))->
     {p,q:PP}Q (renTrm (CONS (Pr p q) rho) M)
               (psub (par q) r (renTrm rho (psub (par r) p M))));
(* sort *)
intros; Refine Q_refl;
(* var *)
intros; Refine Q_refl;
(* par *)
intros;
Equiv Q (par (if (PPeq n p) q (assoc (PPeq n) n rho)))
        (psub (par q) r (renTrm rho (if (PPeq p n) (par r) (par n))));
Qrepl PPsym p n; Refine tt_or_ff (PPeq n p);
intros eqnp; Qrepl eqnp;
  Equiv Q (par q) (psub (par q) r (par (renPar rho r)));
  Qrepl Q_sym (triv_renPar_transpose_left H);
  Equiv Q (par q) (if (PPeq ??) ? ?);
  Qrepl PPrefl r; Refine Q_refl;
intros neqnp; Qrepl neqnp;
  Equiv Q (par (renPar rho n)) (psub (par q) r (par (renPar rho n)));
  Claim is_ff (poccur r (par (renPar rho n)));
  Qrepl (Trm_eq_subst (not_pocc_psub_eq_lem ?+1 (par q))); Refine Q_refl;
  Qrepl ff_orr_unit (PPeq r (renPar rho n));
  Refine triv_renPar_transpose_right; Immed;
(* pi *)
intros;
Equiv Q (pi n (renTrm ??) (renTrm ??))
        (pi n (psub ?? (renTrm ? (psub ???)))
              (psub ?? (renTrm ? (psub ???))));
Qrepl ihA H H1 p q; Qrepl ihB H H1 p q; Refine Q_refl;
(* lda *)
intros;
Equiv Q (lda n (renTrm ??) (renTrm ??))
        (lda n (psub ?? (renTrm ? (psub ???)))
               (psub ?? (renTrm ? (psub ???))));
Qrepl ihA H H1 p q; Qrepl ihB H H1 p q; Refine Q_refl;
(* app *)
intros;
Equiv Q (app (renTrm ??) (renTrm ??))
        (app (psub ?? (renTrm ? (psub ???)))
             (psub ?? (renTrm ? (psub ???))));
Qrepl ihA H H1 p q; Qrepl ihB H H1 p q; Refine Q_refl;
Save;
(**** end new ****)


(* renaming and occurrence lemmas *)
Goal soccur_rename:
     {t:SS}{rho:Renaming}{B:Trm}Q (soccur t B) (soccur t (renTrm rho B));
intros __;
Refine Trec [B:Trm]Q (soccur t B) (soccur t (renTrm rho B));
(* sort *)
intros; Refine Q_refl;
(* var *)
intros; Refine Q_refl;
(* par *)
intros; Claim is_tt (isPar (renTrm rho (par n)));
Refine isPar_lem ?+1; intros q qh; Qrepl Trm_eq_subst qh; Refine Q_refl;
Qrepl renTrm_isPar rho (par n); Refine Q_refl;
(* pi *)
intros; Refine Q_trans; Refine orr (soccur t A) (soccur t B);
Qrepl socc_split t A B; Refine Q_refl;
Qrepl ihA; Qrepl ihB;
Qrepl member_append_lem SSeq t (sorts (renTrm rho A)) (sorts (renTrm rho B));
Refine Q_refl;
(* lda *)
intros; Refine Q_trans; Refine orr (soccur t A) (soccur t B);
Qrepl socc_split t A B; Refine Q_refl;
Qrepl ihA; Qrepl ihB;
Qrepl member_append_lem SSeq t (sorts (renTrm rho A)) (sorts (renTrm rho B));
Refine Q_refl;
(* app *)
intros; Refine Q_trans; Refine orr (soccur t A) (soccur t B);
Qrepl socc_split t A B; Refine Q_refl;
Qrepl ihA; Qrepl ihB;
Qrepl member_append_lem SSeq t (sorts (renTrm rho A)) (sorts (renTrm rho B));
Refine Q_refl;
Save;

Goal {A|Trm}{q|PP}{rho:Renaming}{occ:is_tt (poccur q (renTrm rho A))}
      ex [p:PP]and (is_tt (PPeq q (renPar rho p))) (is_tt (poccur p A));

Refine Trec [A:Trm]{q|PP}{rho:Renaming}{pocc:is_tt (poccur q (renTrm rho A))}
             ex [p:PP]and (is_tt (PPeq q (renPar rho p))) (is_tt (poccur p A));
intros; Refine tt_not_ff (Q_sym pocc);
intros; Refine tt_not_ff (Q_sym pocc);
intros;Refine ExIn n;
Qrepl pocc_par_lem n n;Qrepl Q_sym (pocc_par_lem q (renPar rho n));
Refine pair pocc (PPrefl ?);
intros;Refine pocc_compound_lem
             (pocc:is_tt (poccur q (pi n (renTrm rho ?) (renTrm rho ?))));
intros poccA;Refine ihA rho poccA;
intros p pHyp;Refine ExIn p;Refine pair (fst pHyp) ?;
Refine pocc_split_lem;Refine inl;Refine snd pHyp;
intros poccB;Refine ihB rho poccB;
intros p pHyp;Refine ExIn p;Refine pair (fst pHyp) ?;
Refine pocc_split_lem;Refine inr;Refine snd pHyp;
intros;Refine pocc_compound_lem
             (pocc:is_tt (poccur q (pi n (renTrm rho ?) (renTrm rho ?))));
intros poccA;Refine ihA rho poccA;
intros p pHyp;Refine ExIn p;Refine pair (fst pHyp) ?;
Refine pocc_split_lem;Refine inl;Refine snd pHyp;
intros poccB;Refine ihB rho poccB;
intros p pHyp;Refine ExIn p;Refine pair (fst pHyp) ?;
Refine pocc_split_lem;Refine inr;Refine snd pHyp;
intros;Refine pocc_compound_lem
             (pocc:is_tt (poccur q (app (renTrm rho ?) (renTrm rho ?))));
intros poccA;Refine ihA rho poccA;
intros p pHyp;Refine ExIn p;Refine pair (fst pHyp) ?;
Refine pocc_split_lem;Refine inl;Refine snd pHyp;
intros poccB;Refine ihB rho poccB;
intros p pHyp;Refine ExIn p;Refine pair (fst pHyp) ?;
Refine pocc_split_lem;Refine inr;Refine snd pHyp;
Save renaming_poccur;

Goal {G|Cxt}{p|PP}(is_tt (Poccur p G))->
     {rho:Renaming}is_tt (Poccur (renPar rho p) (renCxt rho G));

Refine LLrec [G:Cxt]{p|PP}{poccG:is_tt (Poccur p G)}
       {rho:Renaming}is_tt (Poccur (renPar rho p) (renCxt rho G));
intros; Refine tt_not_ff (Q_sym poccG);
intros;
Refine snd (orr_character ? (Poccur (renPar ? ?) (renCxt ? ?)));
Refine fst (orr_character ? (Poccur ? ?)) poccG;
intros eq; Refine inl;
Qrepl GB_surj_pair b;Qrepl PPdecide eq;Refine PPrefl;
intros inC; Refine inr; Refine LLih inC;
Save renaming_Poccur;

Goal {G|Cxt}{p|PP}{rho|Renaming}
     (is_ff (Poccur (renPar rho p) (renCxt rho G)))->is_ff (Poccur p G);
intros ___; Refine B_contrapos;
intros; Refine renaming_Poccur; Immed;
Save renaming_not_Poccur;

Goal {G|Cxt}{p|PP}{A|Trm}(is_tt (GBoccur (Gb p A) G))->
       {rho:Renaming}is_tt (GBoccur (Gb (renPar rho p) (renTrm rho A))
                                  (renCxt rho G));
Refine LLrec [G:Cxt]{p|PP}{A|Trm}(is_tt (GBoccur (Gb p A) G))->
       {rho:Renaming}is_tt (GBoccur (Gb (renPar rho p) (renTrm rho A))
                                  (renCxt rho G));
intros; Refine tt_not_ff (Q_sym H);
intros;
Refine snd (orr_character ? (GBoccur (Gb (renPar ? ?) (renTrm ? ?))
                                   (renCxt ? ?)));
Refine fst (orr_character ? (GBoccur (Gb p A) prem)) H;
intros eq; Refine inl;
[lem : and (is_tt (PPeq p (namOf b))) (is_tt (Trm_eq A (typOf b)))
     = fst (andd_character ? ?) eq];
Qrepl GB_surj_pair b;
Qrepl PPdecide (fst lem); Qrepl Trm_eq_subst (snd lem);
Refine GBeq_refl;
intros inC; Refine inr; Refine LLih inC;
Save renaming_GBoccur;

Goal {G|Cxt}{b|GB}(is_tt (GBoccur b G))->
       {rho:Renaming}is_tt (GBoccur (renGB rho b) (renCxt rho G));
Refine LLrec [G:Cxt]{b|GB}(is_tt (GBoccur b G))->
       {rho:Renaming}is_tt (GBoccur (renGB rho b) (renCxt rho G));
intros; Refine H;
intros;
[lem : or (is_tt (GBeq b1 b)) (is_tt (GBoccur b1 prem))
     = fst (orr_character ? ?) H];
Refine snd (orr_character ? (GBoccur (renGB rho b1) (renCxt rho prem)));
Refine lem;
intros; Refine inl; Qrepl GBeq_subst H1; Refine GBeq_refl;
intros; Refine inr; Refine LLih H1;
Save renRespGBoccur;

(* inversion principles for renamed terms *)
Goal {rho|Renaming}{u|VV}{A',B',X|Trm}
     (is_tt (Trm_eq (renTrm rho X) (pi u A' B')))->
       Ex2 [A'',B''|Trm]and3 (is_tt (Trm_eq X (pi u A'' B'')))
                             (is_tt (Trm_eq A' (renTrm rho A'')))
                             (is_tt (Trm_eq B' (renTrm rho B'')));
intros ____;
Refine Trec [X:Trm]{eq:is_tt (Trm_eq (renTrm rho X) (pi u A' B'))}
       Ex2 [A'',B''|Trm]and3 (is_tt (Trm_eq X (pi u A'' B'')))
                             (is_tt (Trm_eq A' (renTrm rho A'')))
                             (is_tt (Trm_eq B' (renTrm rho B'')));
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine Trm_eq_pi_lem
       (eq:is_tt (Trm_eq (pi n (renTrm rho A) (renTrm rho B)) (pi u A' B')));
intros eqV eqA eqB;
Qrepl VVdecide eqV;Qrepl Q_sym (Trm_eq_subst eqA);
Qrepl Q_sym (Trm_eq_subst eqB);
Refine Ex2In A B;Refine pair3;
Refine Trm_eq_refl;Refine Trm_eq_refl;Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
Save renTrm_pi_character;

Goal {rho|Renaming}{u|VV}{A',B',X|Trm}
     (is_tt (Trm_eq (renTrm rho X) (lda u A' B')))->
       Ex2 [A'',B''|Trm]and3 (is_tt (Trm_eq X (lda u A'' B'')))
                             (is_tt (Trm_eq A' (renTrm rho A'')))
                             (is_tt (Trm_eq B' (renTrm rho B'')));
intros ____;
Refine Trec [X:Trm]{eq:is_tt (Trm_eq (renTrm rho X) (lda u A' B'))}
       Ex2 [A'',B''|Trm]and3 (is_tt (Trm_eq X (lda u A'' B'')))
                             (is_tt (Trm_eq A' (renTrm rho A'')))
                             (is_tt (Trm_eq B' (renTrm rho B'')));
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine Trm_eq_lda_lem 
       (eq:is_tt (Trm_eq (lda n (renTrm rho A) (renTrm rho B)) (lda u A' B')));
intros eqV eqA eqB;
Qrepl VVdecide eqV;Qrepl Q_sym (Trm_eq_subst eqA);
Qrepl Q_sym (Trm_eq_subst eqB);
Refine Ex2In A B;Refine pair3;
Refine Trm_eq_refl;Refine Trm_eq_refl;Refine Trm_eq_refl;
intros;Refine tt_not_ff (Q_sym eq);
Save renTrm_lda_character;

Goal {rho|Renaming}{A',B',X|Trm}(is_tt (Trm_eq (renTrm rho X) (app A' B')))->
       Ex2 [A'',B''|Trm]and3 (is_tt (Trm_eq X (app A'' B'')))
                             (is_tt (Trm_eq A' (renTrm rho A'')))
                             (is_tt (Trm_eq B' (renTrm rho B'')));
intros ___;
Refine Trec [X:Trm]{eq:is_tt (Trm_eq (renTrm rho X) (app A' B'))}
       Ex2 [A'',B''|Trm]and3 (is_tt (Trm_eq X (app A'' B'')))
                             (is_tt (Trm_eq A' (renTrm rho A'')))
                             (is_tt (Trm_eq B' (renTrm rho B'')));
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine tt_not_ff (Q_sym eq);
intros;Refine Trm_eq_app_lem 
       (eq:is_tt (Trm_eq (app (renTrm rho ?) (renTrm rho ?)) (app A' B')));
intros eqA eqB;
Qrepl Q_sym (Trm_eq_subst eqA);Qrepl Q_sym (Trm_eq_subst eqB);
Refine Ex2In A B;Refine pair3;
Refine Trm_eq_refl;Refine Trm_eq_refl;Refine Trm_eq_refl;
Save renTrm_app_character;

(* the key lemmas for using renamings *)

[rho:Renaming][q:PP][p|PP];

Goal {M|Trm}(is_ff (poccur p M))->
      Q (renTrm (CONS (Pr p q) rho) M) (renTrm rho M);
Refine not_pocc_Trec [p|PP][M|Trm]
      Q (renTrm (CONS (Pr p q) rho) M) (renTrm rho M);
(* sort *)
intros;Refine Q_refl;
(* var *)
intros;Refine Q_refl;
(* par *)
intros;
Equiv Q (par (if (PPeq n p) q (assoc (PPeq n) n rho))) ?;
Qrepl PPsym n p;Qrepl noccP;Refine Q_refl;
(* pi *)
intros;
Equiv Q (pi n (renTrm (CONS (Pr p q) rho) A)
              (renTrm (CONS (Pr p q) rho) B))
        (pi n (renTrm rho A) (renTrm rho B));
Qrepl ihA;Qrepl ihB;Refine Q_refl;
(* lda *)
intros;
Equiv Q (lda n (renTrm (CONS (Pr p q) rho) A)
              (renTrm (CONS (Pr p q) rho) B))
        (lda n (renTrm rho A) (renTrm rho B));
Qrepl ihA;Qrepl ihB;Refine Q_refl;
(* app *)
intros;
Equiv Q (app (renTrm (CONS (Pr p q) rho) A)
             (renTrm (CONS (Pr p q) rho) B))
        (app (renTrm rho A) (renTrm rho B));
Qrepl ihA;Qrepl ihB;Refine Q_refl;
Save triv_renTrm_lem;

Goal {G|Cxt}(is_ff (POCCUR p G))->
      Q (renCxt (CONS (Pr p q) rho) G) (renCxt rho G);
Refine LLrec [G:Cxt]{NOCC:is_ff (POCCUR p G)}
              Q (renCxt (CONS (Pr p q) rho) G) (renCxt rho G);
intros;Refine Q_refl;
intros;Refine POCCUR_CONS_lem NOCC;
intros neqP nocc NOCC_prem;
Equiv Q (CONS  ? (renCxt (CONS (Pr p q) rho) prem))
        (CONS  ? (renCxt rho prem));
Refine Q_resp_CONS; Qrepl GB_surj_pair b; Refine Q_resp_Gb;
Equiv Q (if (PPeq (namOf b) p) q (renPar rho (namOf b))) ?;
Qrepl PPsym (namOf b) p; Qrepl neqP; Refine Q_refl;
Refine triv_renTrm_lem nocc;
Refine LLih NOCC_prem;
Save triv_renCxt_lem;

[N:Trm][v:VV][M:Trm];

Goal Q (alpha (renPar rho q) v (renTrm rho M))
       (renTrm rho (alpha q v M));
Refine Trec [M:Trm]Q (alpha (renPar rho q) v (renTrm rho M))
                     (renTrm rho (alpha q v M));
(* sort *)
intros; Refine Q_refl;
(* var *)
intros; 
Equiv Q (if (VVeq v n) (par (renPar rho q)) (renTrm rho (var n)))
        (renTrm rho (if (VVeq v n) (par q) (var n)));
Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl eqV; Refine Q_refl;
intros neqV; Qrepl neqV; Refine Q_refl;
(* par *)
intros; Refine Q_refl;
(* pi *)
intros;
Equiv Q (pi n (alpha (renPar rho q) v (renTrm rho A))
             (if (VVeq v n) (renTrm rho B) (alpha (renPar rho q) v (renTrm rho B))))
        (renTrm rho (pi n (alpha q v A) (if (VVeq v n) B (alpha q v B))));
Qrepl ihA; Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl eqV; Refine Q_refl;
intros neqV; Qrepl neqV; Qrepl ihB; Refine Q_refl;       
(* lda *)
intros;
Equiv Q (lda n (alpha (renPar rho q) v (renTrm rho A))
             (if (VVeq v n) (renTrm rho B) (alpha (renPar rho q) v (renTrm rho B))))
        (renTrm rho (lda n (alpha q v A) (if (VVeq v n) B (alpha q v B))));
Qrepl ihA; Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl eqV; Refine Q_refl;
intros neqV; Qrepl neqV; Qrepl ihB; Refine Q_refl;       
(* app *)
intros;
Equiv Q (app (alpha (renPar rho q) v (renTrm rho A))
               (alpha (renPar rho q) v (renTrm rho B)))
        (renTrm rho (app (alpha q v A) (alpha q v B)));
Qrepl ihA; Qrepl ihB; Refine Q_refl;
Save alpha_renTrm_commutes;

Goal Q (vsub (renTrm rho N) v (renTrm rho M))
              (renTrm rho (vsub N v M));
Refine Trec [M:Trm]Q (vsub (renTrm rho N) v (renTrm rho M))
                     (renTrm rho (vsub N v M));
(* sort *)
intros; Refine Q_refl;
(* var *)
intros; 
Equiv Q (if (VVeq v n) (renTrm rho N) (renTrm rho (var n)))
        (renTrm rho (if (VVeq v n) N (var n)));
Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl eqV; Refine Q_refl;
intros neqV; Qrepl neqV; Refine Q_refl;
(* par *)
intros; Refine Q_refl;
(* pi *)
intros;
Equiv Q (pi n (vsub (renTrm rho N) v (renTrm rho A))
              (if (VVeq v n) (renTrm rho B) (vsub (renTrm rho N) v (renTrm rho B))))
        (renTrm rho (pi n (vsub N v A) (if (VVeq v n) B (vsub N v B))));
Qrepl ihA; Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl eqV; Refine Q_refl;
intros neqV; Qrepl neqV; Qrepl ihB; Refine Q_refl;       
(* lda *)
intros;
Equiv Q (lda n (vsub (renTrm rho N) v (renTrm rho A))
              (if (VVeq v n) (renTrm rho B) (vsub (renTrm rho N) v (renTrm rho B))))
        (renTrm rho (lda n (vsub N v A) (if (VVeq v n) B (vsub N v B))));
Qrepl ihA; Refine tt_or_ff (VVeq v n);
intros eqV; Qrepl eqV; Refine Q_refl;
intros neqV; Qrepl neqV; Qrepl ihB; Refine Q_refl;       
(* app *)
intros;
Equiv Q (app (vsub (renTrm rho N) v (renTrm rho A))
               (vsub (renTrm rho N) v (renTrm rho B)))
        (renTrm rho (app (vsub N v A) (vsub N v B)));
Qrepl ihA; Qrepl ihB; Refine Q_refl;
Save vsub_renTrm_commutes;

Discharge rho;

Goal sorts_trivial_rename:
     {B|Trm}(is_tt (isSrt B))->{rho|Renaming}Q (renTrm rho B) B;
intros B srtB;
Refine LLrec [rho:Renaming]Q (renTrm rho B) B;
Refine Q_sym (renTrm_Id B);
intros; Refine Q_subst LLih [x:Trm]Q (renTrm (CONS b prem) B) x;
  Qrepl PROD_surj_pair b; Refine triv_renTrm_lem;
  Refine isSrt_lem srtB; intros s sh; Qrepl Trm_eq_subst sh; Refine Q_refl;
Save;


(* renaming Vclosed terms *)
Goal {A|Trm}(aVclosed A)->{rho:Renaming}aVclosed (renTrm rho A);
Refine aVclosedRec [A:Trm][_:aVclosed A]{rho:Renaming}aVclosed (renTrm rho A);
intros;Refine aVclosed_sort;
intros;Refine aVclosed_par;
intros;Equiv aVclosed (pi n (renTrm rho A) (renTrm rho B));
       Refine aVclosed_pi;Immed;
       Refine fresh_params_lem1 B;
       intros p noccB q;
       Claim Ex [sigma:Renaming]and (Q (renPar sigma p) q)
                                    (Q (renTrm sigma B) (renTrm rho B));
       Refine ?+1;intros sigma sigmaSpec;
       Qrepl Q_sym (fst sigmaSpec);
       Qrepl Q_sym (snd sigmaSpec);
       Qrepl alpha_renTrm_commutes sigma p n B;Immed;
       [sigma = CONS (Pr p q) rho:Renaming];
       Refine ExIn sigma;Refine pair;
       Equiv Q (if (PPeq p p) q (renPar ? ?)) q;Qrepl PPrefl p;Refine Q_refl;
       Qrepl triv_renTrm_lem rho q noccB;Refine Q_refl;

intros;Equiv aVclosed (lda n (renTrm rho A) (renTrm rho B));
       Refine aVclosed_lda;Immed;
       Refine fresh_params_lem1 B;
       intros p noccB q;
       Claim Ex [sigma:Renaming]and (Q (renPar sigma p) q)
                                    (Q (renTrm sigma B) (renTrm rho B));
       Refine ?+1;intros sigma sigmaSpec;
       Qrepl Q_sym (fst sigmaSpec);
       Qrepl Q_sym (snd sigmaSpec);
       Qrepl alpha_renTrm_commutes sigma p n B;Immed;
       [sigma = CONS (Pr p q) rho:Renaming];
       Refine ExIn sigma;Refine pair;
       Equiv Q (if (PPeq p p) q (renPar ? ?)) q;Qrepl PPrefl p;Refine Q_refl;
       Qrepl triv_renTrm_lem rho q noccB;Refine Q_refl;
       
intros;Equiv aVclosed (app (renTrm rho A) (renTrm rho B));
       Refine aVclosed_app;Immed;
Save renTrm_resp_aVclosed;


Goal {A|Trm}(Vclosed A)->{rho:Renaming}Vclosed (renTrm rho A);
intros;
Refine aVclosed_Vclosed;
Refine renTrm_resp_aVclosed;
Refine Vclosed_aVclosed;
Immed;
Save renTrm_resp_Vclosed;

(* renTrm respects any relation that psub respects *)
Goal {P|Trm->Prop}
     {psub_resp_P:{A|Trm}(P A)->{N:Trm}{p:PP}P (psub N p A)}
     {rho:Renaming}{A|Trm}(P A)->P (renTrm rho A);
intros __;
Refine LLrec [rho:Renaming]{A|Trm}(P A)->P (renTrm rho A);
intros; Qrepl Q_sym (renTrm_Id A); Immed;
intros;
Refine PPinf (append (params A) (append (lefts prem) (rights prem)));
intros r;
Qrepl member_append_lem PPeq r (params A) (append (lefts prem) (rights prem));
Qrepl member_append_lem PPeq r (lefts prem) (rights prem);
intros rh; 
Refine fst (deMorgan ??) rh; intros Ah Arest;
Refine fst (deMorgan ??) Arest; intros lefth rghth;
Qrepl PROD_surj_pair b;
Qrepl renTrm_is_conjugated_psub Ah lefth rghth (Fst b) (Snd b);
Refine psub_resp_P; Refine LLih; Refine psub_resp_P; Immed;

(***************************
%\VerbFileOpen psub_resp_renTrm_resp_verb
Goal psub_resp_renTrm_resp:
     {P|Trm->Trm->Prop}
     {psub_resp_P:{N|Trm}(Vclosed N)->{A,B|Trm}(P A B)->
                                          {p:PP}P (psub N p A) (psub N p B)}
     {rho:Renaming}{A,B|Trm}(P A B)->P (renTrm rho A) (renTrm rho B);
%\VerbFileClos psub_resp_renTrm_resp_verb
intros __;
Refine LLrec [rho:Renaming]{A,B|Trm}(P A B)->
     P (renTrm rho A) (renTrm rho B);
intros; Qrepl Q_sym (renTrm_Id A); Qrepl Q_sym (renTrm_Id B); Immed;
intros;
Refine PPinf (append (params A)
                     (append (params B)
                             (append (lefts prem) (rights prem))));
intros r;
Qrepl member_append_lem PPeq r (params A)
         (append (params B) (append (lefts prem) (rights prem)));
Qrepl member_append_lem PPeq r (params B) (append (lefts prem) (rights prem));
Qrepl member_append_lem PPeq r (lefts prem) (rights prem);
intros rh; 
Refine fst (deMorgan ??) rh; intros Ah Arest;
Refine fst (deMorgan ??) Arest; intros Bh Brest;
Refine fst (deMorgan ??) Brest; intros lefth rghth;
Qrepl PROD_surj_pair b;
Qrepl renTrm_is_conjugated_psub Ah lefth rghth (Fst b) (Snd b);
Qrepl renTrm_is_conjugated_psub Bh lefth rghth (Fst b) (Snd b);
Refine psub_resp_P; Refine Vclosed_par; Refine LLih;
Refine psub_resp_P; Refine Vclosed_par; Immed;
Save;


(* experimental *)
Goal {P|Trm->Trm->Prop}                      (* no Vclosed *)
     {psub_resp_P:{N|Trm}{A,B|Trm}(P A B)->
                  {p:PP}P (psub N p A) (psub N p B)}
     {rho:Renaming}{A,B|Trm}(P A B)->P (renTrm rho A) (renTrm rho B);
intros __;
Refine LLrec [rho:Renaming]{A,B|Trm}(P A B)->
     P (renTrm rho A) (renTrm rho B);
intros; Qrepl Q_sym (renTrm_Id A); Qrepl Q_sym (renTrm_Id B); Immed;
intros;
Refine PPinf (append (params A)
                     (append (params B)
                             (append (lefts prem) (rights prem))));
intros r;
Qrepl member_append_lem PPeq r (params A)
         (append (params B) (append (lefts prem) (rights prem)));
Qrepl member_append_lem PPeq r (params B) (append (lefts prem) (rights prem));
Qrepl member_append_lem PPeq r (lefts prem) (rights prem);
intros rh; 
Refine fst (deMorgan ??) rh; intros Ah Arest;
Refine fst (deMorgan ??) Arest; intros Bh Brest;
Refine fst (deMorgan ??) Brest; intros lefth rghth;
Qrepl PROD_surj_pair b;
Qrepl renTrm_is_conjugated_psub Ah lefth rghth (Fst b) (Snd b);
Qrepl renTrm_is_conjugated_psub Bh lefth rghth (Fst b) (Snd b);
Refine psub_resp_P; Refine LLih;
Refine psub_resp_P; Immed;

*******************************)

Goal psub_resp_renTrm_resp:
     {P|Trm->Trm->Prop}
     {psub_resp_P:{A,B|Trm}(P A B)->
                  {q,p:PP}P (psub (par q) p A) (psub (par q) p B)}
     {rho:Renaming}{A,B|Trm}(P A B)->P (renTrm rho A) (renTrm rho B);
intros __;
Refine LLrec [rho:Renaming]{A,B|Trm}(P A B)->
     P (renTrm rho A) (renTrm rho B);
intros; Qrepl Q_sym (renTrm_Id A); Qrepl Q_sym (renTrm_Id B); Immed;
intros;
Refine PPinf (append (params A)
                     (append (params B)
                             (append (lefts prem) (rights prem))));
intros r;
Qrepl member_append_lem PPeq r (params A)
         (append (params B) (append (lefts prem) (rights prem)));
Qrepl member_append_lem PPeq r (params B) (append (lefts prem) (rights prem));
Qrepl member_append_lem PPeq r (lefts prem) (rights prem);
intros rh; 
Refine fst (deMorgan ??) rh; intros Ah Arest;
Refine fst (deMorgan ??) Arest; intros Bh Brest;
Refine fst (deMorgan ??) Brest; intros lefth rghth;
Qrepl PROD_surj_pair b;
Qrepl renTrm_is_conjugated_psub Ah lefth rghth (Fst b) (Snd b);
Qrepl renTrm_is_conjugated_psub Bh lefth rghth (Fst b) (Snd b);
Refine psub_resp_P; Refine LLih;
Refine psub_resp_P; Immed;
Save;
