%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:42 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  121 (1274 expanded)
%              Number of clauses        :   86 ( 436 expanded)
%              Number of leaves         :   17 ( 296 expanded)
%              Depth                    :   17
%              Number of atoms          :  616 (19184 expanded)
%              Number of equality atoms :   32 ( 860 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t80_tmap_1,conjecture,(
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
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                         => ! [X7] :
                              ( ( v1_funct_1(X7)
                                & v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))
                                & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                             => ( ( X4 = X1
                                  & r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7) )
                               => ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)
                                <=> r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t78_tmap_1,axiom,(
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
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tmap_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(d4_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(redefinition_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( r1_funct_2(X1,X2,X3,X4,X5,X6)
      <=> X5 = X6 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_17,negated_conjecture,(
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
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                           => ! [X7] :
                                ( ( v1_funct_1(X7)
                                  & v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                               => ( ( X4 = X1
                                    & r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7) )
                                 => ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)
                                  <=> r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t80_tmap_1])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    & esk4_0 = esk1_0
    & r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0)
    & ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)
      | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) )
    & ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)
      | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_19,plain,(
    ! [X15,X16,X17] :
      ( ( v4_relat_1(X17,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( v5_relat_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( esk4_0 = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | v1_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_23,plain,(
    ! [X53,X54,X55,X56,X57] :
      ( v2_struct_0(X53)
      | ~ v2_pre_topc(X53)
      | ~ l1_pre_topc(X53)
      | v2_struct_0(X54)
      | ~ v2_pre_topc(X54)
      | ~ l1_pre_topc(X54)
      | v2_struct_0(X55)
      | ~ m1_pre_topc(X55,X53)
      | v2_struct_0(X56)
      | ~ m1_pre_topc(X56,X53)
      | ~ v1_funct_1(X57)
      | ~ v1_funct_2(X57,u1_struct_0(X53),u1_struct_0(X54))
      | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54))))
      | ~ m1_pre_topc(X55,X56)
      | r2_funct_2(u1_struct_0(X55),u1_struct_0(X54),k3_tmap_1(X53,X54,X56,X55,k2_tmap_1(X53,X54,X57,X56)),k2_tmap_1(X53,X54,X57,X55)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_tmap_1])])])])).

fof(c_0_24,plain,(
    ! [X58,X59,X60] :
      ( ~ v2_pre_topc(X58)
      | ~ l1_pre_topc(X58)
      | ~ m1_pre_topc(X59,X58)
      | ~ m1_pre_topc(X60,X59)
      | m1_pre_topc(X60,X58) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_25,plain,(
    ! [X8,X9] :
      ( ( ~ v4_relat_1(X9,X8)
        | r1_tarski(k1_relat_1(X9),X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r1_tarski(k1_relat_1(X9),X8)
        | v4_relat_1(X9,X8)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_26,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X40,X41,X42,X43] :
      ( v2_struct_0(X40)
      | ~ v2_pre_topc(X40)
      | ~ l1_pre_topc(X40)
      | v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | ~ v1_funct_1(X42)
      | ~ v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X41))
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X41))))
      | ~ m1_pre_topc(X43,X40)
      | k2_tmap_1(X40,X41,X42,X43) = k2_partfun1(u1_struct_0(X40),u1_struct_0(X41),X42,u1_struct_0(X43)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ r1_tarski(k1_relat_1(X11),X10)
      | k7_relat_1(X11,X10) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( v4_relat_1(esk7_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

fof(c_0_37,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ v1_funct_1(X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k2_partfun1(X22,X23,X24,X25) = k7_relat_1(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_44,plain,(
    ! [X48,X49,X50,X51,X52] :
      ( ( v1_funct_1(k3_tmap_1(X48,X49,X50,X51,X52))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | ~ m1_pre_topc(X50,X48)
        | ~ m1_pre_topc(X51,X48)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X49))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49)))) )
      & ( v1_funct_2(k3_tmap_1(X48,X49,X50,X51,X52),u1_struct_0(X51),u1_struct_0(X49))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | ~ m1_pre_topc(X50,X48)
        | ~ m1_pre_topc(X51,X48)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X49))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49)))) )
      & ( m1_subset_1(k3_tmap_1(X48,X49,X50,X51,X52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X49))))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | ~ m1_pre_topc(X50,X48)
        | ~ m1_pre_topc(X51,X48)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X49))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_46,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_48,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(X1),X2,u1_struct_0(esk1_0)) = k2_tmap_1(esk1_0,X1,X2,esk1_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_53,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_55,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_57,plain,(
    ! [X18,X19,X20,X21] :
      ( ( v1_funct_1(k2_partfun1(X18,X19,X20,X21))
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( m1_subset_1(k2_partfun1(X18,X19,X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

cnf(c_0_58,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_60,plain,(
    ! [X44,X45,X46,X47] :
      ( ( v1_funct_1(k2_tmap_1(X44,X45,X46,X47))
        | ~ l1_struct_0(X44)
        | ~ l1_struct_0(X45)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
        | ~ l1_struct_0(X47) )
      & ( v1_funct_2(k2_tmap_1(X44,X45,X46,X47),u1_struct_0(X47),u1_struct_0(X45))
        | ~ l1_struct_0(X44)
        | ~ l1_struct_0(X45)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
        | ~ l1_struct_0(X47) )
      & ( m1_subset_1(k2_tmap_1(X44,X45,X46,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45))))
        | ~ l1_struct_0(X44)
        | ~ l1_struct_0(X45)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
        | ~ l1_struct_0(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_61,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(esk1_0,X1,esk1_0,X2,k2_tmap_1(esk1_0,X1,X3,esk1_0)),k2_tmap_1(esk1_0,X1,X3,X2))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_39]),c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_62,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_63,negated_conjecture,
    ( k7_relat_1(esk7_0,u1_struct_0(esk1_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_36])])).

cnf(c_0_64,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_27]),c_0_49])])).

cnf(c_0_65,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,u1_struct_0(esk1_0)) = k2_tmap_1(esk1_0,esk2_0,esk7_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_49]),c_0_27])]),c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(esk1_0,X1,X2,esk3_0,X3),u1_struct_0(esk3_0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_67,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(X1),X2,u1_struct_0(esk3_0)) = k2_tmap_1(esk1_0,X1,X2,esk3_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_56]),c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(esk1_0,X1,X2,esk3_0,X3))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_56]),c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(esk1_0,X1,X2,esk3_0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_56]),c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_71,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_72,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | l1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_73,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_74,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ r2_funct_2(X26,X27,X28,X29)
        | X28 = X29
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X26,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X28 != X29
        | r2_funct_2(X26,X27,X28,X29)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X26,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_75,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(X1),k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,k2_tmap_1(esk1_0,X1,X2,esk1_0)),k2_tmap_1(esk1_0,X1,X2,esk3_0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_56]),c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk7_0,esk1_0) = esk7_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_77,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2),u1_struct_0(esk3_0),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_39])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_27]),c_0_49])])).

cnf(c_0_79,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,u1_struct_0(esk3_0)) = k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_51]),c_0_52]),c_0_53]),c_0_49]),c_0_27])]),c_0_54])).

cnf(c_0_80,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_39])).

cnf(c_0_81,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_39])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_51]),c_0_49]),c_0_27])])).

cnf(c_0_83,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_51]),c_0_49]),c_0_27])])).

cnf(c_0_85,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_86,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_51]),c_0_76]),c_0_52]),c_0_53]),c_0_49]),c_0_27])]),c_0_54])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_51]),c_0_52]),c_0_53]),c_0_49]),c_0_27])]),c_0_54])).

cnf(c_0_88,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_51]),c_0_52]),c_0_53]),c_0_49]),c_0_27])]),c_0_54])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_51]),c_0_52]),c_0_53]),c_0_49]),c_0_27])]),c_0_54])).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_53])])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_83]),c_0_53])])).

fof(c_0_93,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_pre_topc(X32,X31)
      | l1_pre_topc(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_94,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0) = k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_88]),c_0_89]),c_0_90])])).

cnf(c_0_95,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_83]),c_0_41])])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_83]),c_0_41])])).

cnf(c_0_97,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_99,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0) = k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_56]),c_0_41])])).

fof(c_0_101,plain,(
    ! [X34,X35,X36,X37,X38,X39] :
      ( ( ~ r1_funct_2(X34,X35,X36,X37,X38,X39)
        | X38 = X39
        | v1_xboole_0(X35)
        | v1_xboole_0(X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X34,X35)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X36,X37)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( X38 != X39
        | r1_funct_2(X34,X35,X36,X37,X38,X39)
        | v1_xboole_0(X35)
        | v1_xboole_0(X37)
        | ~ v1_funct_1(X38)
        | ~ v1_funct_2(X38,X34,X35)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X36,X37)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_102,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_103,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_104,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),esk6_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_98,c_0_21])).

cnf(c_0_105,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0) = k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_83]),c_0_100])])).

cnf(c_0_106,plain,
    ( X5 = X6
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ r1_funct_2(X1,X2,X3,X4,X5,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_102,c_0_21])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_109,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_111,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),esk6_0)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_103,c_0_21])).

cnf(c_0_112,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),esk6_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_113,negated_conjecture,
    ( esk7_0 = esk5_0
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_51]),c_0_108]),c_0_49]),c_0_109]),c_0_27]),c_0_110])])).

fof(c_0_114,plain,(
    ! [X33] :
      ( v2_struct_0(X33)
      | ~ l1_struct_0(X33)
      | ~ v1_xboole_0(u1_struct_0(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_115,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_111,c_0_105])).

cnf(c_0_116,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_117,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_113]),c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_54])).

cnf(c_0_120,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_83]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.39/0.56  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.39/0.56  # and selection function SelectCQIPrecWNTNp.
% 0.39/0.56  #
% 0.39/0.56  # Preprocessing time       : 0.029 s
% 0.39/0.56  # Presaturation interreduction done
% 0.39/0.56  
% 0.39/0.56  # Proof found!
% 0.39/0.56  # SZS status Theorem
% 0.39/0.56  # SZS output start CNFRefutation
% 0.39/0.56  fof(t80_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_tmap_1)).
% 0.39/0.56  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.39/0.56  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.39/0.56  fof(t78_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tmap_1)).
% 0.39/0.56  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.39/0.56  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.39/0.56  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.39/0.56  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.39/0.56  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.39/0.56  fof(dt_k3_tmap_1, axiom, ![X1, X2, X3, X4, X5]:(((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_pre_topc(X3,X1))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 0.39/0.56  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 0.39/0.56  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 0.39/0.56  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.39/0.56  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.39/0.56  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.39/0.56  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.39/0.56  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.39/0.56  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6))))))))))), inference(assume_negation,[status(cth)],[t80_tmap_1])).
% 0.39/0.56  fof(c_0_18, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&((esk4_0=esk1_0&r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0))&((~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0))&(r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.39/0.56  fof(c_0_19, plain, ![X15, X16, X17]:((v4_relat_1(X17,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))&(v5_relat_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.39/0.56  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_21, negated_conjecture, (esk4_0=esk1_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  fof(c_0_22, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|v1_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.39/0.56  fof(c_0_23, plain, ![X53, X54, X55, X56, X57]:(v2_struct_0(X53)|~v2_pre_topc(X53)|~l1_pre_topc(X53)|(v2_struct_0(X54)|~v2_pre_topc(X54)|~l1_pre_topc(X54)|(v2_struct_0(X55)|~m1_pre_topc(X55,X53)|(v2_struct_0(X56)|~m1_pre_topc(X56,X53)|(~v1_funct_1(X57)|~v1_funct_2(X57,u1_struct_0(X53),u1_struct_0(X54))|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X54))))|(~m1_pre_topc(X55,X56)|r2_funct_2(u1_struct_0(X55),u1_struct_0(X54),k3_tmap_1(X53,X54,X56,X55,k2_tmap_1(X53,X54,X57,X56)),k2_tmap_1(X53,X54,X57,X55)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_tmap_1])])])])).
% 0.39/0.56  fof(c_0_24, plain, ![X58, X59, X60]:(~v2_pre_topc(X58)|~l1_pre_topc(X58)|(~m1_pre_topc(X59,X58)|(~m1_pre_topc(X60,X59)|m1_pre_topc(X60,X58)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.39/0.56  fof(c_0_25, plain, ![X8, X9]:((~v4_relat_1(X9,X8)|r1_tarski(k1_relat_1(X9),X8)|~v1_relat_1(X9))&(~r1_tarski(k1_relat_1(X9),X8)|v4_relat_1(X9,X8)|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.39/0.56  cnf(c_0_26, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.56  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.39/0.56  cnf(c_0_28, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.56  fof(c_0_29, plain, ![X40, X41, X42, X43]:(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X41))))|(~m1_pre_topc(X43,X40)|k2_tmap_1(X40,X41,X42,X43)=k2_partfun1(u1_struct_0(X40),u1_struct_0(X41),X42,u1_struct_0(X43)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.39/0.56  cnf(c_0_30, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_31, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.56  cnf(c_0_32, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.39/0.56  fof(c_0_33, plain, ![X10, X11]:(~v1_relat_1(X11)|(~r1_tarski(k1_relat_1(X11),X10)|k7_relat_1(X11,X10)=X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.39/0.56  cnf(c_0_34, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.39/0.56  cnf(c_0_35, negated_conjecture, (v4_relat_1(esk7_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.39/0.56  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.39/0.56  fof(c_0_37, plain, ![X22, X23, X24, X25]:(~v1_funct_1(X24)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|k2_partfun1(X22,X23,X24,X25)=k7_relat_1(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.39/0.56  cnf(c_0_38, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.39/0.56  cnf(c_0_39, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(rw,[status(thm)],[c_0_30, c_0_21])).
% 0.39/0.56  cnf(c_0_40, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_42, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_43, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  fof(c_0_44, plain, ![X48, X49, X50, X51, X52]:(((v1_funct_1(k3_tmap_1(X48,X49,X50,X51,X52))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)|v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)|~m1_pre_topc(X50,X48)|~m1_pre_topc(X51,X48)|~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X49))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49))))))&(v1_funct_2(k3_tmap_1(X48,X49,X50,X51,X52),u1_struct_0(X51),u1_struct_0(X49))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)|v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)|~m1_pre_topc(X50,X48)|~m1_pre_topc(X51,X48)|~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X49))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49)))))))&(m1_subset_1(k3_tmap_1(X48,X49,X50,X51,X52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X49))))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)|v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)|~m1_pre_topc(X50,X48)|~m1_pre_topc(X51,X48)|~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X50),u1_struct_0(X49))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).
% 0.39/0.56  cnf(c_0_45, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X3,X4)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_31, c_0_32])).
% 0.39/0.56  cnf(c_0_46, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.56  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.39/0.56  cnf(c_0_48, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.39/0.56  cnf(c_0_49, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_50, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(X1),X2,u1_struct_0(esk1_0))=k2_tmap_1(esk1_0,X1,X2,esk1_0)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])]), c_0_42])).
% 0.39/0.56  cnf(c_0_51, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_43, c_0_21])).
% 0.39/0.56  cnf(c_0_52, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_53, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_54, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_55, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.39/0.56  cnf(c_0_56, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  fof(c_0_57, plain, ![X18, X19, X20, X21]:((v1_funct_1(k2_partfun1(X18,X19,X20,X21))|(~v1_funct_1(X20)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))&(m1_subset_1(k2_partfun1(X18,X19,X20,X21),k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|(~v1_funct_1(X20)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 0.39/0.56  cnf(c_0_58, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.39/0.56  cnf(c_0_59, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.39/0.56  fof(c_0_60, plain, ![X44, X45, X46, X47]:(((v1_funct_1(k2_tmap_1(X44,X45,X46,X47))|(~l1_struct_0(X44)|~l1_struct_0(X45)|~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))|~l1_struct_0(X47)))&(v1_funct_2(k2_tmap_1(X44,X45,X46,X47),u1_struct_0(X47),u1_struct_0(X45))|(~l1_struct_0(X44)|~l1_struct_0(X45)|~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))|~l1_struct_0(X47))))&(m1_subset_1(k2_tmap_1(X44,X45,X46,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45))))|(~l1_struct_0(X44)|~l1_struct_0(X45)|~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))|~l1_struct_0(X47)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 0.39/0.56  cnf(c_0_61, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(esk1_0,X1,esk1_0,X2,k2_tmap_1(esk1_0,X1,X3,esk1_0)),k2_tmap_1(esk1_0,X1,X3,X2))|~v2_pre_topc(X1)|~m1_pre_topc(X2,esk1_0)|~l1_pre_topc(X1)|~v1_funct_2(X3,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_39]), c_0_40]), c_0_41])]), c_0_42])).
% 0.39/0.56  cnf(c_0_62, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_63, negated_conjecture, (k7_relat_1(esk7_0,u1_struct_0(esk1_0))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_36])])).
% 0.39/0.56  cnf(c_0_64, negated_conjecture, (k7_relat_1(esk7_0,X1)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_27]), c_0_49])])).
% 0.39/0.56  cnf(c_0_65, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,u1_struct_0(esk1_0))=k2_tmap_1(esk1_0,esk2_0,esk7_0,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53]), c_0_49]), c_0_27])]), c_0_54])).
% 0.39/0.56  cnf(c_0_66, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(esk1_0,X1,X2,esk3_0,X3),u1_struct_0(esk3_0),u1_struct_0(X1))|~v2_pre_topc(X1)|~m1_pre_topc(X2,esk1_0)|~l1_pre_topc(X1)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_40]), c_0_41])]), c_0_42])).
% 0.39/0.56  cnf(c_0_67, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.39/0.56  cnf(c_0_68, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(X1),X2,u1_struct_0(esk3_0))=k2_tmap_1(esk1_0,X1,X2,esk3_0)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_56]), c_0_40]), c_0_41])]), c_0_42])).
% 0.39/0.56  cnf(c_0_69, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(esk1_0,X1,X2,esk3_0,X3))|~v2_pre_topc(X1)|~m1_pre_topc(X2,esk1_0)|~l1_pre_topc(X1)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_56]), c_0_40]), c_0_41])]), c_0_42])).
% 0.39/0.56  cnf(c_0_70, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(esk1_0,X1,X2,esk3_0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))|~v2_pre_topc(X1)|~m1_pre_topc(X2,esk1_0)|~l1_pre_topc(X1)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_56]), c_0_40]), c_0_41])]), c_0_42])).
% 0.39/0.56  cnf(c_0_71, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.39/0.56  fof(c_0_72, plain, ![X30]:(~l1_pre_topc(X30)|l1_struct_0(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.39/0.56  cnf(c_0_73, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.39/0.56  fof(c_0_74, plain, ![X26, X27, X28, X29]:((~r2_funct_2(X26,X27,X28,X29)|X28=X29|(~v1_funct_1(X28)|~v1_funct_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|~v1_funct_1(X29)|~v1_funct_2(X29,X26,X27)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&(X28!=X29|r2_funct_2(X26,X27,X28,X29)|(~v1_funct_1(X28)|~v1_funct_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|~v1_funct_1(X29)|~v1_funct_2(X29,X26,X27)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.39/0.56  cnf(c_0_75, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(X1),k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,k2_tmap_1(esk1_0,X1,X2,esk1_0)),k2_tmap_1(esk1_0,X1,X2,esk3_0))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_56]), c_0_62])).
% 0.39/0.56  cnf(c_0_76, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk7_0,esk1_0)=esk7_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.39/0.56  cnf(c_0_77, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2),u1_struct_0(esk3_0),u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_66, c_0_39])).
% 0.39/0.56  cnf(c_0_78, negated_conjecture, (v1_funct_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_27]), c_0_49])])).
% 0.39/0.56  cnf(c_0_79, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,u1_struct_0(esk3_0))=k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_51]), c_0_52]), c_0_53]), c_0_49]), c_0_27])]), c_0_54])).
% 0.39/0.56  cnf(c_0_80, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_69, c_0_39])).
% 0.39/0.56  cnf(c_0_81, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(esk1_0,X1,esk1_0,esk3_0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_70, c_0_39])).
% 0.39/0.56  cnf(c_0_82, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_51]), c_0_49]), c_0_27])])).
% 0.39/0.56  cnf(c_0_83, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.39/0.56  cnf(c_0_84, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_51]), c_0_49]), c_0_27])])).
% 0.39/0.56  cnf(c_0_85, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.39/0.56  cnf(c_0_86, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_51]), c_0_76]), c_0_52]), c_0_53]), c_0_49]), c_0_27])]), c_0_54])).
% 0.39/0.56  cnf(c_0_87, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_51]), c_0_52]), c_0_53]), c_0_49]), c_0_27])]), c_0_54])).
% 0.39/0.56  cnf(c_0_88, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.39/0.56  cnf(c_0_89, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_51]), c_0_52]), c_0_53]), c_0_49]), c_0_27])]), c_0_54])).
% 0.39/0.56  cnf(c_0_90, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_51]), c_0_52]), c_0_53]), c_0_49]), c_0_27])]), c_0_54])).
% 0.39/0.56  cnf(c_0_91, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_53])])).
% 0.39/0.56  cnf(c_0_92, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_83]), c_0_53])])).
% 0.39/0.56  fof(c_0_93, plain, ![X31, X32]:(~l1_pre_topc(X31)|(~m1_pre_topc(X32,X31)|l1_pre_topc(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.39/0.56  cnf(c_0_94, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0)=k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87]), c_0_88]), c_0_89]), c_0_90])])).
% 0.39/0.56  cnf(c_0_95, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_83]), c_0_41])])).
% 0.39/0.56  cnf(c_0_96, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk7_0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_83]), c_0_41])])).
% 0.39/0.56  cnf(c_0_97, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.39/0.56  cnf(c_0_98, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_99, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0)=k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)|~l1_struct_0(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])).
% 0.39/0.56  cnf(c_0_100, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_56]), c_0_41])])).
% 0.39/0.56  fof(c_0_101, plain, ![X34, X35, X36, X37, X38, X39]:((~r1_funct_2(X34,X35,X36,X37,X38,X39)|X38=X39|(v1_xboole_0(X35)|v1_xboole_0(X37)|~v1_funct_1(X38)|~v1_funct_2(X38,X34,X35)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~v1_funct_1(X39)|~v1_funct_2(X39,X36,X37)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))&(X38!=X39|r1_funct_2(X34,X35,X36,X37,X38,X39)|(v1_xboole_0(X35)|v1_xboole_0(X37)|~v1_funct_1(X38)|~v1_funct_2(X38,X34,X35)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|~v1_funct_1(X39)|~v1_funct_2(X39,X36,X37)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.39/0.56  cnf(c_0_102, negated_conjecture, (r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_103, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_104, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),esk6_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(rw,[status(thm)],[c_0_98, c_0_21])).
% 0.39/0.56  cnf(c_0_105, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0)=k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_83]), c_0_100])])).
% 0.39/0.56  cnf(c_0_106, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.39/0.56  cnf(c_0_107, negated_conjecture, (r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_102, c_0_21])).
% 0.39/0.56  cnf(c_0_108, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_109, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_110, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_111, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),esk6_0)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(rw,[status(thm)],[c_0_103, c_0_21])).
% 0.39/0.56  cnf(c_0_112, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),esk6_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(rw,[status(thm)],[c_0_104, c_0_105])).
% 0.39/0.56  cnf(c_0_113, negated_conjecture, (esk7_0=esk5_0|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_51]), c_0_108]), c_0_49]), c_0_109]), c_0_27]), c_0_110])])).
% 0.39/0.56  fof(c_0_114, plain, ![X33]:(v2_struct_0(X33)|~l1_struct_0(X33)|~v1_xboole_0(u1_struct_0(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.39/0.56  cnf(c_0_115, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),esk6_0)), inference(rw,[status(thm)],[c_0_111, c_0_105])).
% 0.39/0.56  cnf(c_0_116, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.39/0.56  cnf(c_0_117, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_114])).
% 0.39/0.56  cnf(c_0_118, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_113]), c_0_116])).
% 0.39/0.56  cnf(c_0_119, negated_conjecture, (~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_54])).
% 0.39/0.56  cnf(c_0_120, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_83]), c_0_53])]), ['proof']).
% 0.39/0.56  # SZS output end CNFRefutation
% 0.39/0.56  # Proof object total steps             : 121
% 0.39/0.56  # Proof object clause steps            : 86
% 0.39/0.56  # Proof object formula steps           : 35
% 0.39/0.56  # Proof object conjectures             : 69
% 0.39/0.56  # Proof object clause conjectures      : 66
% 0.39/0.56  # Proof object formula conjectures     : 3
% 0.39/0.56  # Proof object initial clauses used    : 38
% 0.39/0.56  # Proof object initial formulas used   : 17
% 0.39/0.56  # Proof object generating inferences   : 38
% 0.39/0.56  # Proof object simplifying inferences  : 116
% 0.39/0.56  # Training examples: 0 positive, 0 negative
% 0.39/0.56  # Parsed axioms                        : 17
% 0.39/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.56  # Initial clauses                      : 48
% 0.39/0.56  # Removed in clause preprocessing      : 0
% 0.39/0.56  # Initial clauses in saturation        : 48
% 0.39/0.56  # Processed clauses                    : 1732
% 0.39/0.56  # ...of these trivial                  : 129
% 0.39/0.56  # ...subsumed                          : 85
% 0.39/0.56  # ...remaining for further processing  : 1518
% 0.39/0.56  # Other redundant clauses eliminated   : 2
% 0.39/0.56  # Clauses deleted for lack of memory   : 0
% 0.39/0.56  # Backward-subsumed                    : 210
% 0.39/0.56  # Backward-rewritten                   : 404
% 0.39/0.56  # Generated clauses                    : 3753
% 0.39/0.56  # ...of the previous two non-trivial   : 3204
% 0.39/0.56  # Contextual simplify-reflections      : 59
% 0.39/0.56  # Paramodulations                      : 3751
% 0.39/0.56  # Factorizations                       : 0
% 0.39/0.56  # Equation resolutions                 : 2
% 0.39/0.56  # Propositional unsat checks           : 0
% 0.39/0.56  #    Propositional check models        : 0
% 0.39/0.56  #    Propositional check unsatisfiable : 0
% 0.39/0.56  #    Propositional clauses             : 0
% 0.39/0.56  #    Propositional clauses after purity: 0
% 0.39/0.56  #    Propositional unsat core size     : 0
% 0.39/0.56  #    Propositional preprocessing time  : 0.000
% 0.39/0.56  #    Propositional encoding time       : 0.000
% 0.39/0.56  #    Propositional solver time         : 0.000
% 0.39/0.56  #    Success case prop preproc time    : 0.000
% 0.39/0.56  #    Success case prop encoding time   : 0.000
% 0.39/0.56  #    Success case prop solver time     : 0.000
% 0.39/0.56  # Current number of processed clauses  : 855
% 0.39/0.56  #    Positive orientable unit clauses  : 691
% 0.39/0.56  #    Positive unorientable unit clauses: 0
% 0.39/0.56  #    Negative unit clauses             : 4
% 0.39/0.56  #    Non-unit-clauses                  : 160
% 0.39/0.56  # Current number of unprocessed clauses: 1522
% 0.39/0.56  # ...number of literals in the above   : 3984
% 0.39/0.56  # Current number of archived formulas  : 0
% 0.39/0.56  # Current number of archived clauses   : 661
% 0.39/0.56  # Clause-clause subsumption calls (NU) : 28986
% 0.39/0.56  # Rec. Clause-clause subsumption calls : 20505
% 0.39/0.56  # Non-unit clause-clause subsumptions  : 307
% 0.39/0.56  # Unit Clause-clause subsumption calls : 8817
% 0.39/0.56  # Rewrite failures with RHS unbound    : 0
% 0.39/0.56  # BW rewrite match attempts            : 24319
% 0.39/0.56  # BW rewrite match successes           : 95
% 0.39/0.56  # Condensation attempts                : 0
% 0.39/0.56  # Condensation successes               : 0
% 0.39/0.56  # Termbank termtop insertions          : 175160
% 0.39/0.56  
% 0.39/0.56  # -------------------------------------------------
% 0.39/0.56  # User time                : 0.214 s
% 0.39/0.56  # System time              : 0.009 s
% 0.39/0.56  # Total time               : 0.223 s
% 0.39/0.56  # Maximum resident set size: 1616 pages
%------------------------------------------------------------------------------
