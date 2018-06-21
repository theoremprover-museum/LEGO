Module cut
Import thinning;

(* cut is an admissible rule for PTSs *)
Goal substitution_lem:
     {Gamma|Cxt}{N,A|Trm}(gts Gamma N A)->
     {q:PP}[sub = psub N q][subGB = GBsub N q]
     {Delta:Cxt}{M,B|Trm}(gts (append Delta (CONS (Gb q A) Gamma)) M B)->
     gts (append (map subGB Delta) Gamma) (sub M) (sub B);

intros;
Refine gtsRec [G|Cxt][M,B|Trm][_:gts G M B]
      {Delta:Cxt}{eqG:Q G (append Delta (CONS (Gb q A) Gamma))}
      gts (append (map subGB Delta) Gamma) (sub M) (sub B);
Immed;

(* ax *) 
intros;Refine NIL_not_append_CONS ??? eqG;

(* start *) 
intros;
Refine LLrec [Delta:Cxt]
             {eqCxt:Q (CONS (Gb p A1) G) (append Delta (CONS (Gb q A) Gamma))}
              gts (append (map subGB Delta) Gamma) (if ???) (psub ???);
Immed;
(* Delta NIL *)
intros;
[eqP = fst (Q_resp_bnd_proj (Q_resp_hd eqCxt)) :Q p q];
[eqA = snd (Q_resp_bnd_proj (Q_resp_hd eqCxt)) :Q A1 A];
[noccA = fst (free_params_lem1 prem noccG): is_ff (poccur p A1)];
Qrepl Q_sym eqP;Qrepl Trm_eq_subst (not_pocc_psub_eq_lem noccA N);
Qrepl PPrefl p;Qrepl eqA;Immed;
(* Delta CONS *)
intros pA Xi __;
[p2 = namOf pA][A2 = typOf pA];
[eqP = fst (Q_resp_bnd_proj (Q_resp_hd eqCxt)) :Q p p2];
[eqA = snd (Q_resp_bnd_proj (Q_resp_hd eqCxt)) :Q A1 A2];
[eqGG = (Q_resp_tl eqCxt) :Q G (append Xi (CONS (Gb q A) Gamma))];
Refine Poccur_compound_lem (Q_subst eqGG ([G:Cxt]is_ff (Poccur p G)) noccG);
intros noccXi neqP noccGamma;  
Qrepl (PPsym q p);Qrepl neqP;
Equiv gts (CONS (Gb p2 (sub A2)) (append (map subGB Xi) Gamma))
          (par p) (sub A1);
Qrepl Q_sym eqP;Qrepl Q_sym eqA;
Refine Start ? (ih Xi eqGG);Refine Pocc_split_lem2;
Qrepl GBsub_Poccur_lem N q p Xi;Immed;

(* vWeak *) 
intros;
Refine LLrec [Delta:Cxt]
             {eqCxt:Q (CONS (Gb p A1) G) (append Delta (CONS (Gb q A) Gamma))}
              gts (append (map subGB Delta) Gamma) (if ???) (psub ???);
Immed;
(* Delta NIL *)
intros;
[eqP = fst (Q_resp_bnd_proj (Q_resp_hd eqCxt)) :Q p q];
[eqA = snd (Q_resp_bnd_proj (Q_resp_hd eqCxt)) :Q A1 A];
[eqGG = Q_resp_tl eqCxt :Q G Gamma];
[noccA = fst (free_params_lem1 r_prem noccG): is_ff (poccur p A1)];
[noccD = snd (free_params_lem1 l_prem noccG): is_ff (poccur p D)];
[neqP : is_ff (PPeq p n)
      = Q_subst (pocc_par_lem ??) is_ff (fst (free_params_lem1 l_prem noccG))];
Qrepl Q_sym eqP;Qrepl Q_sym eqGG;
Qrepl Trm_eq_subst (not_pocc_psub_eq_lem noccD N);
Qrepl neqP;Immed;
(* Delta CONS *)
intros pA Xi __;
[p2 = namOf pA][A2 = typOf pA];
[eqP = fst (Q_resp_bnd_proj (Q_resp_hd eqCxt)) :Q p p2];
[eqA = snd (Q_resp_bnd_proj (Q_resp_hd eqCxt)) :Q A1 A2];
[eqGG = (Q_resp_tl eqCxt) :Q G (append Xi (CONS (Gb q A) Gamma))];
Equiv gts (CONS (Gb p2 (sub A2)) (append (map subGB ?) ?))
          (sub (par ?)) (sub ?);
Qrepl Q_sym eqP;Qrepl Q_sym eqA;
Refine Poccur_compound_lem (Q_subst eqGG ([G:Cxt]is_ff (Poccur p G)) noccG);
intros noccXi neqP noccGamma;
(* this really needs thinning, because in case q=n atomic weakening rules
 * won't do *)
Refine weakening;
Refine l_ih Xi eqGG;
Refine Pocc_split_lem2;
Qrepl GBsub_Poccur_lem N q p Xi;Immed;
Refine r_ih Xi eqGG;

(* sWeak *)
intros;
Refine LLrec [Delta:Cxt]
             {eqCxt:Q (CONS (Gb p A1) G) (append Delta (CONS (Gb q A) Gamma))}
              gts (append (map subGB Delta) Gamma) (sort t) (psub ???);
Immed;
(* Delta NIL *)
intros;
[eqP = fst (Q_resp_bnd_proj (Q_resp_hd eqCxt)) :Q p q];
[eqGG = Q_resp_tl eqCxt :Q G Gamma];
[noccD = snd (free_params_lem1 l_prem noccG): is_ff (poccur p D)];
Qrepl Q_sym eqP;Qrepl Q_sym eqGG;
Qrepl Trm_eq_subst (not_pocc_psub_eq_lem noccD N);
Immed;
(* Delta CONS *)
intros pA Xi __;
[p2 = namOf pA][A2 = typOf pA];
[eqP = fst (Q_resp_bnd_proj (Q_resp_hd eqCxt)) :Q p p2];
[eqA = snd (Q_resp_bnd_proj (Q_resp_hd eqCxt)) :Q A1 A2];
[eqGG = (Q_resp_tl eqCxt) :Q G (append Xi (CONS (Gb q A) Gamma))];
Equiv gts (CONS (Gb p2 (sub A2)) (append (map subGB Xi) Gamma))
          (sort ?) (sub ?);
Qrepl Q_sym eqP;Qrepl Q_sym eqA;
Refine Poccur_compound_lem (Q_subst eqGG ([G:Cxt]is_ff (Poccur p G)) noccG);
intros noccXi neqP noccGamma;
Refine sWeak ? (l_ih Xi eqGG) (r_ih Xi eqGG);
Refine Pocc_split_lem2;
Qrepl GBsub_Poccur_lem N q p Xi;Immed;

(* pi *)
intros;Equiv gts ? (pi n (sub ?) (sub ?)) (sort s3);
[noccG : is_ff (Poccur p G) = CxtCorrect0 r_prem];
Refine Poccur_compound_lem (Q_subst eqG ([G:Cxt]is_ff (Poccur p G)) noccG);
intros noccDelta neqP noccGamma;  
[noccN : is_ff (poccur p N) = fst (free_params_lem1 H noccGamma)];
Refine Pi sc;Refine +1 not_pocc_psub_lem;Immed;
Refine l_ih ? eqG;
Equiv gts ? (vsub (if ff N (par p)) n (psub ???)) ?;
Qrepl Q_sym neqP;Qrepl PPsym p q;
Qrepl Q_sym (Trm_eq_subst
      (psub_vsub_commutes (fst (gts_Vclosed_lem H)) q (par p) n B1));
Refine r_ih (CONS (Gb p A1) ?);Refine Q_resp ? eqG;

(* lda *)
intros;Equiv gts ? (lda n (sub A1) (sub M1)) (pi m (sub A1) (sub B1));
[noccG : is_ff (Poccur p G) = CxtCorrect0 l_prem];
Refine Poccur_compound_lem (Q_subst eqG ([G:Cxt]is_ff (Poccur p G)) noccG);
intros noccDelta neqP noccGamma;  
[noccN : is_ff (poccur p N) = fst (free_params_lem1 H noccGamma)];
Refine Lda;
Refine +2 not_pocc_psub_lem;
Refine +4 not_pocc_psub_lem;Immed;
Refine +1 r_ih ? eqG; 
Equiv gts ? (vsub (if ff N (par p)) n (psub ???))
            (vsub (if ff N (par p)) m (psub ???));
Qrepl Q_sym neqP;Qrepl PPsym p q;
Qrepl Q_sym (Trm_eq_subst
      (psub_vsub_commutes (fst (gts_Vclosed_lem H)) q (par p) n M1));
Qrepl Q_sym (Trm_eq_subst
      (psub_vsub_commutes (fst (gts_Vclosed_lem H)) q (par p) m B1));
Refine l_ih (CONS (Gb p A1) ?);Refine Q_resp ? eqG;
(* app *)
intros;Equiv gts ? (app (sub ?) (sub ?)) (psub ???);
Qrepl Trm_eq_subst (psub_vsub_commutes (fst (gts_Vclosed_lem H)) q L n B1);
Refine App (l_ih ? eqG) (r_ih ? eqG);
(* cnv *)
intros;
Refine tCnv (psub_resp_cnv (fst (gts_Vclosed_lem H)) sc q)
             (l_ih ? eqG) (r_ih ? eqG);

Refine Q_refl;
Save;

(* only case ever used *)
%\VerbFileOpen cut_rule
Goal cut_rule: {G|Cxt}{N,A|Trm}(gts G N A)->
               {q:PP}{M,B|Trm}(gts (CONS (Gb q A) G) M B)->
               gts G (psub N q M) (psub N q B);
%\VerbFileClos cut_rule
intros;Refine substitution_lem ?? nilCxt;Immed;
Save cut_rule;

