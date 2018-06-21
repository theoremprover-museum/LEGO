Module decide_red_cnv Import beta_normal subject_reduction;

%\VerbFileOpen gts_term_type
[gts_term [M:Trm] = Ex2 [G:Cxt][A:Trm] gts G M A];
[gts_type [A:Trm] = Ex2 [G:Cxt][M:Trm] gts G M A];
%\VerbFileClos gts_term_type

%\VerbFileOpen gts_term_normalizing
[gts_term_Normalizing = {M|Trm}(gts_term M)->normalizing M];
%\VerbFileClos gts_term_normalizing


%\VerbFileOpen gts_type_normalizing
Goal gts_type_normalizing:
     {gtn:gts_term_Normalizing}{M|Trm}(gts_type M)->normalizing M;
%\VerbFileClos gts_type_normalizing
intros; Refine H; intros G A gtsGAM;
Refine type_correctness gtsGAM; intros s jj; Refine jj;
  intros eq; Qrepl Trm_eq_subst eq; Refine ExIn (sort s);
    Refine pair (bn_sort ?) (par_redn_refl (Vclosed_sort ?));
  intros gtsGMs; Refine gtn; Refine Ex2In G (sort s); Immed;
Save;


Goal gts_term_decides_RedToSort:
     {gtn:gts_term_Normalizing}{M|Trm}(gts_term M)->decidable (RedToSort M);
intros; Refine H; intros G A gtsGMA;
Refine normalizing_decides_RedToSort;
Refine gtn; Refine Ex2In G A; Immed;
Save;

Goal gts_type_decides_RedToSort:
     {gtn:gts_term_Normalizing}{M|Trm}(gts_type M)->decidable (RedToSort M);
intros; Refine H; intros G A gtsGAM;
Refine normalizing_decides_RedToSort;
Refine gts_type_normalizing gtn; Refine Ex2In G A; Immed;
Save;

Goal gts_term_decides_RedToPi:
     {gtn:gts_term_Normalizing}{M|Trm}(gts_term M)->decidable (RedToPi M);
intros; Refine H; intros G A gtsGMA;
Refine normalizing_decides_RedToPi;
Refine gtn; Refine Ex2In G A; Immed;
Save;

Goal gts_type_decides_RedToPi:
     {gtn:gts_term_Normalizing}{M|Trm}(gts_type M)->decidable (RedToPi M);
intros; Refine H; intros G A gtsGAM;
Refine normalizing_decides_RedToPi;
Refine gts_type_normalizing gtn; Refine Ex2In G A; Immed;
Save;


%\VerbFileOpen normalizing_decides_cnv
[normalizing_decides_cnv =
     {A,B|Trm}(normalizing A)->(normalizing B)->decidable (cnv A B)];
%\VerbFileClos normalizing_decides_cnv

%\VerbFileOpen ndc_dcs
Goal ndc_dcs:
     {ndc:normalizing_decides_cnv}{s,t:SS}decidable (cnv (sort s) (sort t));
%\VerbFileClos ndc_dcs
intros; Refine ndc;
Refine ExIn (sort s); Refine pair (bn_sort ?) (par_redn_refl (Vclosed_sort ?));
Refine ExIn (sort t); Refine pair (bn_sort ?) (par_redn_refl (Vclosed_sort ?));
Save;

Goal gts_type_term_decides_cnv:
     {gtn:gts_term_Normalizing}
     {ndc:normalizing_decides_cnv}
     {A,B|Trm}(gts_type A)->(gts_term B)->decidable (cnv A B);
intros ____ typA trmB;
Refine typA; intros G M gtsGMA; Refine trmB; intros K N gtsKBN;
Refine gts_Vclosed_lem gtsGMA; intros;
Refine gts_Vclosed_lem gtsKBN; intros;
Refine ndc;
Refine gts_type_normalizing gtn typA;
Refine gtn trmB;
Save;
