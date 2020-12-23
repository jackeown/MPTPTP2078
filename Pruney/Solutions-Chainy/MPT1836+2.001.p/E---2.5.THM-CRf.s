%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:37 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :   90 (4969 expanded)
%              Number of clauses        :   71 (1449 expanded)
%              Number of leaves         :    8 (1203 expanded)
%              Depth                    :   12
%              Number of atoms          :  740 (98721 expanded)
%              Number of equality atoms :   16 (3435 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal clause size      :   88 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t152_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v1_borsuk_1(X3,X1)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_borsuk_1(X4,X1)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & v5_pre_topc(X5,X3,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(X6,X4,X2)
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                         => ( ( X1 = k1_tsep_1(X1,X3,X4)
                              & r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X5)
                              & r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X6) )
                           => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
                              & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(X1),u1_struct_0(X2))
                              & v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),X1,X2)
                              & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_tmap_1)).

fof(dt_k10_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1)
        & ~ v2_struct_0(X4)
        & m1_pre_topc(X4,X1)
        & v1_funct_1(X5)
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
        & v1_funct_1(X6)
        & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
     => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
        & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
        & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(dt_k3_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_pre_topc(X3,X1)
        & m1_pre_topc(X4,X1)
        & v1_funct_1(X5)
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
     => ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
        & v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(t126_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( r4_tsep_1(X1,X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                       => ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                            & v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                        <=> ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))
                            & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))
                            & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)
                            & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                            & v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))
                            & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)
                            & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_tmap_1)).

fof(t87_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_borsuk_1(X2,X1)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_borsuk_1(X3,X1)
                & m1_pre_topc(X3,X1) )
             => r4_tsep_1(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tsep_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & v1_borsuk_1(X3,X1)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & v1_borsuk_1(X4,X1)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                          & v5_pre_topc(X5,X3,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                              & v5_pre_topc(X6,X4,X2)
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                           => ( ( X1 = k1_tsep_1(X1,X3,X4)
                                & r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X5)
                                & r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X6) )
                             => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
                                & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(X1),u1_struct_0(X2))
                                & v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),X1,X2)
                                & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t152_tmap_1])).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( v1_funct_1(k10_tmap_1(X11,X12,X13,X14,X15,X16))
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X11)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X11)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X12))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X12))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X12))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12)))) )
      & ( v1_funct_2(k10_tmap_1(X11,X12,X13,X14,X15,X16),u1_struct_0(k1_tsep_1(X11,X13,X14)),u1_struct_0(X12))
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X11)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X11)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X12))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X12))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X12))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12)))) )
      & ( m1_subset_1(k10_tmap_1(X11,X12,X13,X14,X15,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X11,X13,X14)),u1_struct_0(X12))))
        | v2_struct_0(X11)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,X11)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X11)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X12))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X12))))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X12))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v1_borsuk_1(esk3_0,esk1_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & v1_borsuk_1(esk4_0,esk1_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & v5_pre_topc(esk5_0,esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    & v5_pre_topc(esk6_0,esk4_0,esk2_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    & esk1_0 = k1_tsep_1(esk1_0,esk3_0,esk4_0)
    & r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0)
    & r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0)
    & ( ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
      | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)
      | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_10,plain,
    ( m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_funct_2(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v1_funct_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

fof(c_0_27,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v2_struct_0(k1_tsep_1(X17,X18,X19))
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17) )
      & ( v1_pre_topc(k1_tsep_1(X17,X18,X19))
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17) )
      & ( m1_pre_topc(k1_tsep_1(X17,X18,X19),X17)
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X17)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_28,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( v1_funct_1(k3_tmap_1(X20,X21,X22,X23,X24))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X22,X20)
        | ~ m1_pre_topc(X23,X20)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21)))) )
      & ( v1_funct_2(k3_tmap_1(X20,X21,X22,X23,X24),u1_struct_0(X23),u1_struct_0(X21))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X22,X20)
        | ~ m1_pre_topc(X23,X20)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21)))) )
      & ( m1_subset_1(k3_tmap_1(X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X21))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X22,X20)
        | ~ m1_pre_topc(X23,X20)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

cnf(c_0_29,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( esk1_0 = k1_tsep_1(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_38,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_39,plain,(
    ! [X1,X5,X4,X3,X2] :
      ( epred1_5(X2,X3,X4,X5,X1)
    <=> ( ( v1_funct_1(X5)
          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    introduced(definition)).

fof(c_0_40,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ r2_funct_2(X7,X8,X9,X10)
        | X9 = X10
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( X9 != X10
        | r2_funct_2(X7,X8,X9,X10)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_41,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_30]),c_0_32]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_33])]),c_0_16]),c_0_35])).

fof(c_0_47,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( r4_tsep_1(X1,X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                       => epred1_5(X2,X3,X4,X5,X1) ) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t126_tmap_1,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_49,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_12]),c_0_13]),c_0_44]),c_0_45])]),c_0_17])).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_32]),c_0_31]),c_0_24])).

cnf(c_0_53,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_54,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X27,X25)
      | v2_struct_0(X28)
      | ~ m1_pre_topc(X28,X25)
      | ~ r4_tsep_1(X25,X27,X28)
      | ~ v1_funct_1(X29)
      | ~ v1_funct_2(X29,u1_struct_0(k1_tsep_1(X25,X27,X28)),u1_struct_0(X26))
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X27,X28)),u1_struct_0(X26))))
      | epred1_5(X26,X27,X28,X29,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_47])])])])).

fof(c_0_55,plain,(
    ! [X30,X31,X32] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ v1_borsuk_1(X31,X30)
      | ~ m1_pre_topc(X31,X30)
      | ~ v1_borsuk_1(X32,X30)
      | ~ m1_pre_topc(X32,X30)
      | r4_tsep_1(X30,X31,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t87_tsep_1])])])])).

cnf(c_0_56,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_31])).

fof(c_0_57,plain,(
    ! [X1,X5,X4,X3,X2] :
      ( epred1_5(X2,X3,X4,X5,X1)
     => ( ( v1_funct_1(X5)
          & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5))
          & v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2)
          & m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk6_0
    | ~ m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_11]),c_0_14]),c_0_15])])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk2_0,esk1_0,X2,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_43]),c_0_12]),c_0_13]),c_0_44]),c_0_45])]),c_0_17])).

cnf(c_0_61,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | epred1_5(X2,X3,X4,X5,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ r4_tsep_1(X1,X3,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | r4_tsep_1(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_borsuk_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_borsuk_1(X3,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( v1_borsuk_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_65,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk5_0
    | ~ m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_56]),c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_67,plain,(
    ! [X39,X40,X41,X42,X43] :
      ( ( v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))
        | ~ v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))))
        | ~ epred1_5(X43,X42,X41,X40,X39) )
      & ( v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),u1_struct_0(X42),u1_struct_0(X43))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))
        | ~ v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))))
        | ~ epred1_5(X43,X42,X41,X40,X39) )
      & ( v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),X42,X43)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))
        | ~ v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))))
        | ~ epred1_5(X43,X42,X41,X40,X39) )
      & ( m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X43))))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))
        | ~ v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))))
        | ~ epred1_5(X43,X42,X41,X40,X39) )
      & ( v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))
        | ~ v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))))
        | ~ epred1_5(X43,X42,X41,X40,X39) )
      & ( v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),u1_struct_0(X41),u1_struct_0(X43))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))
        | ~ v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))))
        | ~ epred1_5(X43,X42,X41,X40,X39) )
      & ( v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),X41,X43)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))
        | ~ v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))))
        | ~ epred1_5(X43,X42,X41,X40,X39) )
      & ( m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X43))))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))
        | ~ v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))))
        | ~ epred1_5(X43,X42,X41,X40,X39) )
      & ( v1_funct_1(X40)
        | ~ v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40))
        | ~ v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),u1_struct_0(X42),u1_struct_0(X43))
        | ~ v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),X42,X43)
        | ~ m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X43))))
        | ~ v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40))
        | ~ v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),u1_struct_0(X41),u1_struct_0(X43))
        | ~ v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),X41,X43)
        | ~ m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X43))))
        | ~ epred1_5(X43,X42,X41,X40,X39) )
      & ( v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))
        | ~ v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40))
        | ~ v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),u1_struct_0(X42),u1_struct_0(X43))
        | ~ v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),X42,X43)
        | ~ m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X43))))
        | ~ v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40))
        | ~ v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),u1_struct_0(X41),u1_struct_0(X43))
        | ~ v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),X41,X43)
        | ~ m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X43))))
        | ~ epred1_5(X43,X42,X41,X40,X39) )
      & ( v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)
        | ~ v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40))
        | ~ v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),u1_struct_0(X42),u1_struct_0(X43))
        | ~ v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),X42,X43)
        | ~ m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X43))))
        | ~ v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40))
        | ~ v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),u1_struct_0(X41),u1_struct_0(X43))
        | ~ v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),X41,X43)
        | ~ m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X43))))
        | ~ epred1_5(X43,X42,X41,X40,X39) )
      & ( m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))))
        | ~ v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40))
        | ~ v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),u1_struct_0(X42),u1_struct_0(X43))
        | ~ v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),X42,X43)
        | ~ m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X43))))
        | ~ v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40))
        | ~ v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),u1_struct_0(X41),u1_struct_0(X43))
        | ~ v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),X41,X43)
        | ~ m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X43))))
        | ~ epred1_5(X43,X42,X41,X40,X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).

cnf(c_0_68,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk6_0
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_30])])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_52]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_43]),c_0_12]),c_0_13]),c_0_44]),c_0_45])]),c_0_17])).

cnf(c_0_71,negated_conjecture,
    ( epred1_5(X1,esk3_0,esk4_0,X2,esk1_0)
    | v2_struct_0(X1)
    | ~ r4_tsep_1(esk1_0,esk3_0,esk4_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_31]),c_0_30]),c_0_32]),c_0_33]),c_0_34])]),c_0_16]),c_0_24]),c_0_35])).

cnf(c_0_72,negated_conjecture,
    ( r4_tsep_1(esk1_0,X1,esk4_0)
    | ~ v1_borsuk_1(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_30]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_73,negated_conjecture,
    ( v1_borsuk_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_74,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk5_0
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_59]),c_0_32])])).

cnf(c_0_75,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_45])])).

cnf(c_0_76,plain,
    ( v5_pre_topc(X1,k1_tsep_1(X2,X3,X4),X5)
    | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1))
    | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),u1_struct_0(X3),u1_struct_0(X5))
    | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),X3,X5)
    | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X5))))
    | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1))
    | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),u1_struct_0(X4),u1_struct_0(X5))
    | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),X4,X5)
    | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
    | ~ epred1_5(X5,X3,X4,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk6_0
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_30])])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_52]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_79,negated_conjecture,
    ( epred1_5(X1,esk3_0,esk4_0,X2,esk1_0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_32])])).

cnf(c_0_80,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk5_0
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_69]),c_0_32])])).

cnf(c_0_81,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_44])])).

cnf(c_0_82,negated_conjecture,
    ( v5_pre_topc(X1,esk1_0,X2)
    | ~ epred1_5(X2,esk3_0,esk4_0,X1,esk1_0)
    | ~ v5_pre_topc(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),esk4_0,X2)
    | ~ v5_pre_topc(k3_tmap_1(esk1_0,X2,esk1_0,esk3_0,X1),esk3_0,X2)
    | ~ m1_subset_1(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))
    | ~ m1_subset_1(k3_tmap_1(esk1_0,X2,esk1_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X2))))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,X2,esk1_0,esk3_0,X1),u1_struct_0(esk3_0),u1_struct_0(X2))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,X2,esk1_0,esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_31])).

cnf(c_0_83,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_30])])).

cnf(c_0_84,negated_conjecture,
    ( epred1_5(esk2_0,esk3_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_43]),c_0_12]),c_0_13]),c_0_44]),c_0_45])]),c_0_17])).

cnf(c_0_85,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_86,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_78]),c_0_32])])).

cnf(c_0_87,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_88,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_43])])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_85]),c_0_86]),c_0_87]),c_0_11]),c_0_86]),c_0_21]),c_0_14]),c_0_86]),c_0_22]),c_0_15]),c_0_86]),c_0_23])]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:20:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.34  # Version: 2.5pre002
% 0.21/0.34  # No SInE strategy applied
% 0.21/0.34  # Trying AutoSched0 for 299 seconds
% 7.68/7.88  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 7.68/7.88  # and selection function SelectComplexExceptUniqMaxHorn.
% 7.68/7.88  #
% 7.68/7.88  # Preprocessing time       : 0.030 s
% 7.68/7.88  # Presaturation interreduction done
% 7.68/7.88  
% 7.68/7.88  # Proof found!
% 7.68/7.88  # SZS status Theorem
% 7.68/7.88  # SZS output start CNFRefutation
% 7.68/7.88  fof(t152_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v1_borsuk_1(X3,X1))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_borsuk_1(X4,X1))&m1_pre_topc(X4,X1))=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(((X1=k1_tsep_1(X1,X3,X4)&r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X5))&r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X6))=>(((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),X1,X2))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_tmap_1)).
% 7.68/7.88  fof(dt_k10_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))&~(v2_struct_0(X4)))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(X6))&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 7.68/7.88  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 7.68/7.88  fof(dt_k3_tmap_1, axiom, ![X1, X2, X3, X4, X5]:(((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_pre_topc(X3,X1))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 7.68/7.88  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 7.68/7.88  fof(t126_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r4_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_tmap_1)).
% 7.68/7.88  fof(t87_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_borsuk_1(X2,X1)&m1_pre_topc(X2,X1))=>![X3]:((v1_borsuk_1(X3,X1)&m1_pre_topc(X3,X1))=>r4_tsep_1(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_tsep_1)).
% 7.68/7.88  fof(c_0_7, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v1_borsuk_1(X3,X1))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_borsuk_1(X4,X1))&m1_pre_topc(X4,X1))=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(((X1=k1_tsep_1(X1,X3,X4)&r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X5))&r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,k10_tmap_1(X1,X2,X3,X4,X5,X6)),X6))=>(((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),X1,X2))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))))))))))), inference(assume_negation,[status(cth)],[t152_tmap_1])).
% 7.68/7.88  fof(c_0_8, plain, ![X11, X12, X13, X14, X15, X16]:(((v1_funct_1(k10_tmap_1(X11,X12,X13,X14,X15,X16))|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X11)|v2_struct_0(X14)|~m1_pre_topc(X14,X11)|~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X12))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X12))))|~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X12))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12))))))&(v1_funct_2(k10_tmap_1(X11,X12,X13,X14,X15,X16),u1_struct_0(k1_tsep_1(X11,X13,X14)),u1_struct_0(X12))|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X11)|v2_struct_0(X14)|~m1_pre_topc(X14,X11)|~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X12))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X12))))|~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X12))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12)))))))&(m1_subset_1(k10_tmap_1(X11,X12,X13,X14,X15,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X11,X13,X14)),u1_struct_0(X12))))|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|v2_struct_0(X13)|~m1_pre_topc(X13,X11)|v2_struct_0(X14)|~m1_pre_topc(X14,X11)|~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X12))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X12))))|~v1_funct_1(X16)|~v1_funct_2(X16,u1_struct_0(X14),u1_struct_0(X12))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X12))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).
% 7.68/7.88  fof(c_0_9, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v1_borsuk_1(esk3_0,esk1_0))&m1_pre_topc(esk3_0,esk1_0))&(((~v2_struct_0(esk4_0)&v1_borsuk_1(esk4_0,esk1_0))&m1_pre_topc(esk4_0,esk1_0))&((((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&v5_pre_topc(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&((((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&v5_pre_topc(esk6_0,esk4_0,esk2_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&(((esk1_0=k1_tsep_1(esk1_0,esk3_0,esk4_0)&r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0))&r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0))&(~v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))|~v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 7.68/7.88  cnf(c_0_10, plain, (m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 7.68/7.88  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_12, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_13, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_14, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_15, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_18, plain, (v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 7.68/7.88  cnf(c_0_19, plain, (v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 7.68/7.88  cnf(c_0_20, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_16]), c_0_17])).
% 7.68/7.88  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_25, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v1_funct_2(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_16]), c_0_17])).
% 7.68/7.88  cnf(c_0_26, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|v1_funct_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])]), c_0_16]), c_0_17])).
% 7.68/7.88  fof(c_0_27, plain, ![X17, X18, X19]:(((~v2_struct_0(k1_tsep_1(X17,X18,X19))|(v2_struct_0(X17)|~l1_pre_topc(X17)|v2_struct_0(X18)|~m1_pre_topc(X18,X17)|v2_struct_0(X19)|~m1_pre_topc(X19,X17)))&(v1_pre_topc(k1_tsep_1(X17,X18,X19))|(v2_struct_0(X17)|~l1_pre_topc(X17)|v2_struct_0(X18)|~m1_pre_topc(X18,X17)|v2_struct_0(X19)|~m1_pre_topc(X19,X17))))&(m1_pre_topc(k1_tsep_1(X17,X18,X19),X17)|(v2_struct_0(X17)|~l1_pre_topc(X17)|v2_struct_0(X18)|~m1_pre_topc(X18,X17)|v2_struct_0(X19)|~m1_pre_topc(X19,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 7.68/7.88  fof(c_0_28, plain, ![X20, X21, X22, X23, X24]:(((v1_funct_1(k3_tmap_1(X20,X21,X22,X23,X24))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|~m1_pre_topc(X22,X20)|~m1_pre_topc(X23,X20)|~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21))))))&(v1_funct_2(k3_tmap_1(X20,X21,X22,X23,X24),u1_struct_0(X23),u1_struct_0(X21))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|~m1_pre_topc(X22,X20)|~m1_pre_topc(X23,X20)|~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21)))))))&(m1_subset_1(k3_tmap_1(X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X21))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|~m1_pre_topc(X22,X20)|~m1_pre_topc(X23,X20)|~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).
% 7.68/7.88  cnf(c_0_29, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 7.68/7.88  cnf(c_0_30, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_31, negated_conjecture, (esk1_0=k1_tsep_1(esk1_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_32, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_36, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 7.68/7.88  cnf(c_0_37, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 7.68/7.88  cnf(c_0_38, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 7.68/7.88  fof(c_0_39, plain, ![X1, X5, X4, X3, X2]:(epred1_5(X2,X3,X4,X5,X1)<=>((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))), introduced(definition)).
% 7.68/7.88  fof(c_0_40, plain, ![X7, X8, X9, X10]:((~r2_funct_2(X7,X8,X9,X10)|X9=X10|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(X9!=X10|r2_funct_2(X7,X8,X9,X10)|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 7.68/7.88  cnf(c_0_41, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_42, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 7.68/7.88  cnf(c_0_43, negated_conjecture, (m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 7.68/7.88  cnf(c_0_44, negated_conjecture, (v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 7.68/7.88  cnf(c_0_45, negated_conjecture, (v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_30]), c_0_32]), c_0_33]), c_0_34])]), c_0_35])).
% 7.68/7.88  cnf(c_0_46, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,X1,esk4_0),esk1_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_30]), c_0_33])]), c_0_16]), c_0_35])).
% 7.68/7.88  fof(c_0_47, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r4_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>epred1_5(X2,X3,X4,X5,X1))))))), inference(apply_def,[status(thm)],[t126_tmap_1, c_0_39])).
% 7.68/7.88  cnf(c_0_48, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,k1_tsep_1(esk1_0,esk3_0,esk4_0),esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_49, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 7.68/7.88  cnf(c_0_50, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk6_0)), inference(rw,[status(thm)],[c_0_41, c_0_31])).
% 7.68/7.88  cnf(c_0_51, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_12]), c_0_13]), c_0_44]), c_0_45])]), c_0_17])).
% 7.68/7.88  cnf(c_0_52, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_32]), c_0_31]), c_0_24])).
% 7.68/7.88  cnf(c_0_53, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 7.68/7.88  fof(c_0_54, plain, ![X25, X26, X27, X28, X29]:(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25)|(v2_struct_0(X28)|~m1_pre_topc(X28,X25)|(~r4_tsep_1(X25,X27,X28)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(k1_tsep_1(X25,X27,X28)),u1_struct_0(X26))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X25,X27,X28)),u1_struct_0(X26))))|epred1_5(X26,X27,X28,X29,X25))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_47])])])])).
% 7.68/7.88  fof(c_0_55, plain, ![X30, X31, X32]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(~v1_borsuk_1(X31,X30)|~m1_pre_topc(X31,X30)|(~v1_borsuk_1(X32,X30)|~m1_pre_topc(X32,X30)|r4_tsep_1(X30,X31,X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t87_tsep_1])])])])).
% 7.68/7.88  cnf(c_0_56, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),esk5_0)), inference(rw,[status(thm)],[c_0_48, c_0_31])).
% 7.68/7.88  fof(c_0_57, plain, ![X1, X5, X4, X3, X2]:(epred1_5(X2,X3,X4,X5,X1)=>((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(X5,k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X3,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5)))&v1_funct_2(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X4,X2))&m1_subset_1(k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))), inference(split_equiv,[status(thm)],[c_0_39])).
% 7.68/7.88  cnf(c_0_58, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))=esk6_0|~m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_11]), c_0_14]), c_0_15])])).
% 7.68/7.88  cnf(c_0_59, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_33]), c_0_34])]), c_0_35])).
% 7.68/7.88  cnf(c_0_60, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk2_0,esk1_0,X2,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(X2),u1_struct_0(esk2_0))|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_43]), c_0_12]), c_0_13]), c_0_44]), c_0_45])]), c_0_17])).
% 7.68/7.88  cnf(c_0_61, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 7.68/7.88  cnf(c_0_62, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|epred1_5(X2,X3,X4,X5,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~r4_tsep_1(X1,X3,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 7.68/7.88  cnf(c_0_63, plain, (v2_struct_0(X1)|r4_tsep_1(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_borsuk_1(X2,X1)|~m1_pre_topc(X2,X1)|~v1_borsuk_1(X3,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 7.68/7.88  cnf(c_0_64, negated_conjecture, (v1_borsuk_1(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_65, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))=esk5_0|~m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))|~v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_56]), c_0_21]), c_0_22]), c_0_23])])).
% 7.68/7.88  cnf(c_0_66, negated_conjecture, (~v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))|~v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  fof(c_0_67, plain, ![X39, X40, X41, X42, X43]:(((((((((v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40))|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))|~v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43)))))|~epred1_5(X43,X42,X41,X40,X39))&(v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),u1_struct_0(X42),u1_struct_0(X43))|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))|~v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43)))))|~epred1_5(X43,X42,X41,X40,X39)))&(v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),X42,X43)|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))|~v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43)))))|~epred1_5(X43,X42,X41,X40,X39)))&(m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X43))))|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))|~v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43)))))|~epred1_5(X43,X42,X41,X40,X39)))&(v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40))|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))|~v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43)))))|~epred1_5(X43,X42,X41,X40,X39)))&(v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),u1_struct_0(X41),u1_struct_0(X43))|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))|~v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43)))))|~epred1_5(X43,X42,X41,X40,X39)))&(v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),X41,X43)|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))|~v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43)))))|~epred1_5(X43,X42,X41,X40,X39)))&(m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X43))))|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))|~v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43)))))|~epred1_5(X43,X42,X41,X40,X39)))&((((v1_funct_1(X40)|(~v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40))|~v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),u1_struct_0(X42),u1_struct_0(X43))|~v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),X42,X43)|~m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X43))))|~v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40))|~v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),u1_struct_0(X41),u1_struct_0(X43))|~v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),X41,X43)|~m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X43)))))|~epred1_5(X43,X42,X41,X40,X39))&(v1_funct_2(X40,u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))|(~v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40))|~v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),u1_struct_0(X42),u1_struct_0(X43))|~v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),X42,X43)|~m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X43))))|~v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40))|~v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),u1_struct_0(X41),u1_struct_0(X43))|~v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),X41,X43)|~m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X43)))))|~epred1_5(X43,X42,X41,X40,X39)))&(v5_pre_topc(X40,k1_tsep_1(X39,X42,X41),X43)|(~v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40))|~v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),u1_struct_0(X42),u1_struct_0(X43))|~v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),X42,X43)|~m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X43))))|~v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40))|~v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),u1_struct_0(X41),u1_struct_0(X43))|~v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),X41,X43)|~m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X43)))))|~epred1_5(X43,X42,X41,X40,X39)))&(m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X39,X42,X41)),u1_struct_0(X43))))|(~v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40))|~v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),u1_struct_0(X42),u1_struct_0(X43))|~v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),X42,X43)|~m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X42,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X43))))|~v1_funct_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40))|~v1_funct_2(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),u1_struct_0(X41),u1_struct_0(X43))|~v5_pre_topc(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),X41,X43)|~m1_subset_1(k3_tmap_1(X39,X43,k1_tsep_1(X39,X42,X41),X41,X40),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X43)))))|~epred1_5(X43,X42,X41,X40,X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).
% 7.68/7.88  cnf(c_0_68, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))=esk6_0|~v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_30])])).
% 7.68/7.88  cnf(c_0_69, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_52]), c_0_33]), c_0_34])]), c_0_35])).
% 7.68/7.88  cnf(c_0_70, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_43]), c_0_12]), c_0_13]), c_0_44]), c_0_45])]), c_0_17])).
% 7.68/7.88  cnf(c_0_71, negated_conjecture, (epred1_5(X1,esk3_0,esk4_0,X2,esk1_0)|v2_struct_0(X1)|~r4_tsep_1(esk1_0,esk3_0,esk4_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_31]), c_0_30]), c_0_32]), c_0_33]), c_0_34])]), c_0_16]), c_0_24]), c_0_35])).
% 7.68/7.88  cnf(c_0_72, negated_conjecture, (r4_tsep_1(esk1_0,X1,esk4_0)|~v1_borsuk_1(X1,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_30]), c_0_33]), c_0_34])]), c_0_35])).
% 7.68/7.88  cnf(c_0_73, negated_conjecture, (v1_borsuk_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_74, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))=esk5_0|~v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_59]), c_0_32])])).
% 7.68/7.88  cnf(c_0_75, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|~v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_45])])).
% 7.68/7.88  cnf(c_0_76, plain, (v5_pre_topc(X1,k1_tsep_1(X2,X3,X4),X5)|~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1))|~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),u1_struct_0(X3),u1_struct_0(X5))|~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),X3,X5)|~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X3,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X5))))|~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1))|~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),u1_struct_0(X4),u1_struct_0(X5))|~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),X4,X5)|~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X3,X4),X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))|~epred1_5(X5,X3,X4,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 7.68/7.88  cnf(c_0_77, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))=esk6_0|~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_30])])).
% 7.68/7.88  cnf(c_0_78, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_52]), c_0_33]), c_0_34])]), c_0_35])).
% 7.68/7.88  cnf(c_0_79, negated_conjecture, (epred1_5(X1,esk3_0,esk4_0,X2,esk1_0)|v2_struct_0(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_32])])).
% 7.68/7.88  cnf(c_0_80, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))=esk5_0|~v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_69]), c_0_32])])).
% 7.68/7.88  cnf(c_0_81, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_44])])).
% 7.68/7.88  cnf(c_0_82, negated_conjecture, (v5_pre_topc(X1,esk1_0,X2)|~epred1_5(X2,esk3_0,esk4_0,X1,esk1_0)|~v5_pre_topc(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),esk4_0,X2)|~v5_pre_topc(k3_tmap_1(esk1_0,X2,esk1_0,esk3_0,X1),esk3_0,X2)|~m1_subset_1(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))|~m1_subset_1(k3_tmap_1(esk1_0,X2,esk1_0,esk3_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X2))))|~v1_funct_2(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1),u1_struct_0(esk4_0),u1_struct_0(X2))|~v1_funct_2(k3_tmap_1(esk1_0,X2,esk1_0,esk3_0,X1),u1_struct_0(esk3_0),u1_struct_0(X2))|~v1_funct_1(k3_tmap_1(esk1_0,X2,esk1_0,esk4_0,X1))|~v1_funct_1(k3_tmap_1(esk1_0,X2,esk1_0,esk3_0,X1))), inference(spm,[status(thm)],[c_0_76, c_0_31])).
% 7.68/7.88  cnf(c_0_83, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_30])])).
% 7.68/7.88  cnf(c_0_84, negated_conjecture, (epred1_5(esk2_0,esk3_0,esk4_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_43]), c_0_12]), c_0_13]), c_0_44]), c_0_45])]), c_0_17])).
% 7.68/7.88  cnf(c_0_85, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_86, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_78]), c_0_32])])).
% 7.68/7.88  cnf(c_0_87, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 7.68/7.88  cnf(c_0_88, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_43])])).
% 7.68/7.88  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_85]), c_0_86]), c_0_87]), c_0_11]), c_0_86]), c_0_21]), c_0_14]), c_0_86]), c_0_22]), c_0_15]), c_0_86]), c_0_23])]), c_0_88]), ['proof']).
% 7.68/7.88  # SZS output end CNFRefutation
% 7.68/7.88  # Proof object total steps             : 90
% 7.68/7.88  # Proof object clause steps            : 71
% 7.68/7.88  # Proof object formula steps           : 19
% 7.68/7.88  # Proof object conjectures             : 63
% 7.68/7.88  # Proof object clause conjectures      : 60
% 7.68/7.88  # Proof object formula conjectures     : 3
% 7.68/7.88  # Proof object initial clauses used    : 35
% 7.68/7.88  # Proof object initial formulas used   : 7
% 7.68/7.88  # Proof object generating inferences   : 31
% 7.68/7.88  # Proof object simplifying inferences  : 151
% 7.68/7.88  # Training examples: 0 positive, 0 negative
% 7.68/7.88  # Parsed axioms                        : 7
% 7.68/7.88  # Removed by relevancy pruning/SinE    : 0
% 7.68/7.88  # Initial clauses                      : 49
% 7.68/7.88  # Removed in clause preprocessing      : 0
% 7.68/7.88  # Initial clauses in saturation        : 49
% 7.68/7.88  # Processed clauses                    : 5297
% 7.68/7.88  # ...of these trivial                  : 0
% 7.68/7.88  # ...subsumed                          : 20
% 7.68/7.88  # ...remaining for further processing  : 5277
% 7.68/7.88  # Other redundant clauses eliminated   : 1
% 7.68/7.88  # Clauses deleted for lack of memory   : 0
% 7.68/7.88  # Backward-subsumed                    : 7
% 7.68/7.88  # Backward-rewritten                   : 7
% 7.68/7.88  # Generated clauses                    : 639913
% 7.68/7.88  # ...of the previous two non-trivial   : 639874
% 7.68/7.88  # Contextual simplify-reflections      : 136
% 7.68/7.88  # Paramodulations                      : 639912
% 7.68/7.88  # Factorizations                       : 0
% 7.68/7.88  # Equation resolutions                 : 1
% 7.68/7.88  # Propositional unsat checks           : 1
% 7.68/7.88  #    Propositional check models        : 0
% 7.68/7.88  #    Propositional check unsatisfiable : 0
% 7.68/7.88  #    Propositional clauses             : 0
% 7.68/7.88  #    Propositional clauses after purity: 0
% 7.68/7.88  #    Propositional unsat core size     : 0
% 7.68/7.88  #    Propositional preprocessing time  : 0.000
% 7.68/7.88  #    Propositional encoding time       : 0.322
% 7.68/7.88  #    Propositional solver time         : 0.100
% 7.68/7.88  #    Success case prop preproc time    : 0.000
% 7.68/7.88  #    Success case prop encoding time   : 0.000
% 7.68/7.88  #    Success case prop solver time     : 0.000
% 7.68/7.88  # Current number of processed clauses  : 5213
% 7.68/7.88  #    Positive orientable unit clauses  : 225
% 7.68/7.88  #    Positive unorientable unit clauses: 0
% 7.68/7.88  #    Negative unit clauses             : 5
% 7.68/7.88  #    Non-unit-clauses                  : 4983
% 7.68/7.88  # Current number of unprocessed clauses: 634675
% 7.68/7.88  # ...number of literals in the above   : 4189553
% 7.68/7.88  # Current number of archived formulas  : 0
% 7.68/7.88  # Current number of archived clauses   : 63
% 7.68/7.88  # Clause-clause subsumption calls (NU) : 8561229
% 7.68/7.88  # Rec. Clause-clause subsumption calls : 324372
% 7.68/7.88  # Non-unit clause-clause subsumptions  : 159
% 7.68/7.88  # Unit Clause-clause subsumption calls : 175667
% 7.68/7.88  # Rewrite failures with RHS unbound    : 0
% 7.68/7.88  # BW rewrite match attempts            : 21330
% 7.68/7.88  # BW rewrite match successes           : 5
% 7.68/7.88  # Condensation attempts                : 0
% 7.68/7.88  # Condensation successes               : 0
% 7.68/7.88  # Termbank termtop insertions          : 39786711
% 7.73/7.91  
% 7.73/7.91  # -------------------------------------------------
% 7.73/7.91  # User time                : 7.172 s
% 7.73/7.91  # System time              : 0.401 s
% 7.73/7.91  # Total time               : 7.573 s
% 7.73/7.91  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
