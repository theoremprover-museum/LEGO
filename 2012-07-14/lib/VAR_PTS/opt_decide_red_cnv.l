Module opt_decide_red_cnv Import decide_red_cnv;

[M:Trm];
Inductive [opt_normalizing:Prop]  NoReductions Constructors
  [on_some:{j:normalizing M}opt_normalizing]
  [on_none:opt_normalizing];
Discharge M;

[gts_term_opt_Normalizing = {M|Trm}(gts_term M)->opt_normalizing M];

Goal gts_type_opt_normalizing:
     {gtn:gts_term_opt_Normalizing}{M|Trm}(gts_type M)->opt_normalizing M;
intros; Refine H; intros G A gtsGAM;
Refine type_correctness gtsGAM; intros s jj; Refine jj;
  intros eq; Qrepl Trm_eq_subst eq; Refine on_some; Refine ExIn (sort s);
    Refine pair (bn_sort ?) (par_redn_refl ?); Refine Vclosed_sort;
  intros gtsGMs; Refine gtn; Refine Ex2In G (sort s); Immed;
Save;

[M:Trm];
Inductive [opt_RedToSort:Prop]  NoReductions Constructors
  [oRTS_yes:{j:RedToSort M}opt_RedToSort]
  [oRTS_no:{j:not (RedToSort M)}opt_RedToSort]
  [oRTS_maybe:opt_RedToSort];
Inductive [opt_RedToPi:Prop]  NoReductions Constructors
  [oRTP_yes:{j:RedToPi M}opt_RedToPi]
  [oRTP_no:{j:not (RedToPi M)}opt_RedToPi]
  [oRTP_maybe:opt_RedToPi];
Discharge M;
Goal opt_normalizing_opt_RedToSort:
     {A|Trm}(opt_normalizing A)->(Vclosed A)->opt_RedToSort A;
intros A;
Refine opt_normalizing_elim A [_:opt_normalizing A]
     (Vclosed A)->opt_RedToSort A;
(* normalizing *)
intros; Refine normalizing_decides_RedToSort; Immed;
intros; Refine oRTS_yes; Immed;
intros; Refine oRTS_no; Immed;
(* don't know *)
intros; Refine oRTS_maybe;
Save;

Goal opt_normalizing_opt_RedToPi:
     {A|Trm}(opt_normalizing A)->(Vclosed A)->opt_RedToPi A;
intros A;
Refine opt_normalizing_elim A [_:opt_normalizing A]
     (Vclosed A)->opt_RedToPi A;
(* normalizing *)
intros; Refine normalizing_decides_RedToPi; Immed;
intros; Refine oRTP_yes; Immed;
intros; Refine oRTP_no; Immed;
(* don't know *)
intros; Refine oRTP_maybe;
Save;

Goal gts_term_opt_RedToSort:
     {gtn:gts_term_opt_Normalizing}{M|Trm}(gts_term M)->opt_RedToSort M;
intros; Refine H; intros G A gtsGMA;
Refine gts_Vclosed_lem gtsGMA; intros vclM _;
Refine opt_normalizing_opt_RedToSort ? vclM;
Refine gtn; Refine Ex2In G A; Immed;
Save;

Goal gts_type_opt_RedToSort:
     {gtn:gts_term_opt_Normalizing}{M|Trm}(gts_type M)->opt_RedToSort M;
intros; Refine H; intros G A gtsGAM;
Refine gts_Vclosed_lem gtsGAM; intros _ vclM;
Refine opt_normalizing_opt_RedToSort ? vclM;
Refine gts_type_opt_normalizing gtn; Immed;
Save;

Goal gts_term_opt_RedToPi:
     {gtn:gts_term_opt_Normalizing}{M|Trm}(gts_term M)->opt_RedToPi M;
intros; Refine H; intros G A gtsGMA;
Refine gts_Vclosed_lem gtsGMA; intros vclM _;
Refine opt_normalizing_opt_RedToPi ? vclM;
Refine gtn; Refine Ex2In G A; Immed;
Save;

Goal gts_type_opt_RedToPi:
     {gtn:gts_term_opt_Normalizing}{M|Trm}(gts_type M)->opt_RedToPi M;
intros; Refine H; intros G A gtsGAM;
Refine gts_Vclosed_lem gtsGAM; intros _ vclM;
Refine opt_normalizing_opt_RedToPi ? vclM;
Refine gts_type_opt_normalizing gtn; Immed;
Save;

(* conversion testing *)
[M,N:Trm];
Inductive [opt_conv:Prop]  NoReductions Constructors
  [oc_yes:{j:conv M N}opt_conv]
  [oc_no:{j:not (conv M N)}opt_conv]
  [oc_maybe:opt_conv];
Discharge M;

Goal opt_normalizing_opt_conv:
     {A,B|Trm}(opt_normalizing A)->(opt_normalizing B)->
              (Vclosed A)->(Vclosed B)->
     opt_conv A B;
intros A B onlzA onlzB;
(* elim opt_normalizing A *)
Refine opt_normalizing_elim A [_:opt_normalizing A]
       (Vclosed A)->(Vclosed B)->opt_conv A B;
Immed;
(* fail if no normal form for A *)
intros +1; Refine oc_maybe;
(* A has a normal form *)
intros nlzA vclA;
Refine nlzA; intros nA nAh; Refine nAh; intros bnnA redAnA;
(* elim opt_normalizing B *)
Refine opt_normalizing_elim B [_:opt_normalizing B]
       (Vclosed B)->opt_conv A B;
Immed;
(* fail if no normal form for B *)
intros +1; Refine oc_maybe;
(* B has a normal form *)
intros nlzB vclB;
Refine nlzB; intros nB nBh; Refine nBh; intros bnnB redBnB;
[vclnA : Vclosed nA = beta_norm_Vclosed bnnA];
[vclnB : Vclosed nB = beta_norm_Vclosed bnnB];
Refine decide_alpha_conv vclnA vclnB;
intros acnAnB; Refine oc_yes;
  Refine conv_trans (conv_redn redAnA)
                    (conv_trans (alpha_conv_conv acnAnB)
                                (conv_sym (conv_redn redBnB)));
intros nacnAnB; Refine oc_no; Refine contrapos ? nacnAnB; intros cnvAB;
Refine convCR (?:conv nA nB);
Refine conv_trans (conv_sym (conv_redn redAnA))
                  (conv_trans cnvAB (conv_redn redBnB));
intros D Dh; Refine Dh; intros nAD nBD;
Refine alpha_conv_trans ? (alpha_conv_sym ?);
Refine +1 par_redn_bnorm_is_alpha_conv nAD;
Refine +1 par_redn_bnorm_is_alpha_conv nBD; Immed;
Save;


Goal gts_type_term_opt_conv:
     {gtn:gts_term_opt_Normalizing}
     {A,B|Trm}(gts_type A)->(gts_term B)->opt_conv A B;
intros ___ typA trmB;
Refine typA; intros G M gtsGMA; Refine trmB; intros K N gtsKBN;
Refine gts_Vclosed_lem gtsGMA; intros;
Refine gts_Vclosed_lem gtsKBN; intros;
Refine opt_normalizing_opt_conv; Immed;
Refine gts_type_opt_normalizing gtn typA;
Refine gtn trmB;
Save;
