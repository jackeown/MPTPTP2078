%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:36 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 327 expanded)
%              Number of clauses        :   43 (  95 expanded)
%              Number of leaves         :    4 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  455 (6122 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   31 (   7 average)
%              Maximal clause size      :   84 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t148_tmap_1,conjecture,(
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
                 => ( r1_tsep_1(X3,X4)
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
                           => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
                              & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                              & v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
                              & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_tmap_1)).

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

fof(t145_tmap_1,axiom,(
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
                 => ( r1_tsep_1(X3,X4)
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
                           => ( r4_tsep_1(X1,X3,X4)
                             => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
                                & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                                & v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
                                & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_tmap_1)).

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

fof(c_0_4,negated_conjecture,(
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
                   => ( r1_tsep_1(X3,X4)
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
                             => ( v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))
                                & v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                                & v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
                                & m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t148_tmap_1])).

fof(c_0_5,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( v1_funct_1(k10_tmap_1(X7,X8,X9,X10,X11,X12))
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X7)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X7)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X8))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X8)))) )
      & ( v1_funct_2(k10_tmap_1(X7,X8,X9,X10,X11,X12),u1_struct_0(k1_tsep_1(X7,X9,X10)),u1_struct_0(X8))
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X7)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X7)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X8))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X8)))) )
      & ( m1_subset_1(k10_tmap_1(X7,X8,X9,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X7,X9,X10)),u1_struct_0(X8))))
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,X7)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X7)
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X8))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X8)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).

fof(c_0_6,negated_conjecture,
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
    & r1_tsep_1(esk3_0,esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & v5_pre_topc(esk5_0,esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    & v5_pre_topc(esk6_0,esk4_0,esk2_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    & ( ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
      | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)
      | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])]),c_0_13]),c_0_14])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])]),c_0_13]),c_0_14])).

cnf(c_0_28,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_29,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( v1_funct_1(k10_tmap_1(X13,X14,X15,X16,X17,X18))
        | ~ r4_tsep_1(X13,X15,X16)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X14))
        | ~ v5_pre_topc(X18,X16,X14)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14))))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))
        | ~ v5_pre_topc(X17,X15,X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))
        | ~ r1_tsep_1(X15,X16)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( v1_funct_2(k10_tmap_1(X13,X14,X15,X16,X17,X18),u1_struct_0(k1_tsep_1(X13,X15,X16)),u1_struct_0(X14))
        | ~ r4_tsep_1(X13,X15,X16)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X14))
        | ~ v5_pre_topc(X18,X16,X14)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14))))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))
        | ~ v5_pre_topc(X17,X15,X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))
        | ~ r1_tsep_1(X15,X16)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( v5_pre_topc(k10_tmap_1(X13,X14,X15,X16,X17,X18),k1_tsep_1(X13,X15,X16),X14)
        | ~ r4_tsep_1(X13,X15,X16)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X14))
        | ~ v5_pre_topc(X18,X16,X14)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14))))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))
        | ~ v5_pre_topc(X17,X15,X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))
        | ~ r1_tsep_1(X15,X16)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(k10_tmap_1(X13,X14,X15,X16,X17,X18),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X13,X15,X16)),u1_struct_0(X14))))
        | ~ r4_tsep_1(X13,X15,X16)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X14))
        | ~ v5_pre_topc(X18,X16,X14)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14))))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))
        | ~ v5_pre_topc(X17,X15,X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))
        | ~ r1_tsep_1(X15,X16)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X13)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,X13)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t145_tmap_1])])])])])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])]),c_0_13]),c_0_14])).

cnf(c_0_34,plain,
    ( v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r4_tsep_1(X1,X3,X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v5_pre_topc(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ r1_tsep_1(X3,X4)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_36,plain,(
    ! [X19,X20,X21] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ v1_borsuk_1(X20,X19)
      | ~ m1_pre_topc(X20,X19)
      | ~ v1_borsuk_1(X21,X19)
      | ~ m1_pre_topc(X21,X19)
      | r4_tsep_1(X19,X20,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t87_tsep_1])])])])).

cnf(c_0_37,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( v5_pre_topc(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),k1_tsep_1(X1,X2,esk4_0),esk2_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r4_tsep_1(X1,X2,esk4_0)
    | ~ v5_pre_topc(X3,X2,esk2_0)
    | ~ r1_tsep_1(X2,esk4_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_8]),c_0_35]),c_0_9]),c_0_10]),c_0_11]),c_0_12])]),c_0_13]),c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_42,negated_conjecture,
    ( r1_tsep_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | r4_tsep_1(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_borsuk_1(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_borsuk_1(X3,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v1_borsuk_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_45,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( v5_pre_topc(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(X1,esk3_0,esk4_0),esk2_0)
    | v2_struct_0(X1)
    | ~ r4_tsep_1(X1,esk3_0,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_16]),c_0_41]),c_0_42]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( r4_tsep_1(esk1_0,X1,esk4_0)
    | ~ v1_borsuk_1(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_22]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( v1_borsuk_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_50,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_49])]),c_0_50]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t148_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v1_borsuk_1(X3,X1))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_borsuk_1(X4,X1))&m1_pre_topc(X4,X1))=>(r1_tsep_1(X3,X4)=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_tmap_1)).
% 0.13/0.38  fof(dt_k10_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))&~(v2_struct_0(X4)))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(X6))&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 0.13/0.38  fof(t145_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r1_tsep_1(X3,X4)=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(r4_tsep_1(X1,X3,X4)=>(((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_tmap_1)).
% 0.13/0.38  fof(t87_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_borsuk_1(X2,X1)&m1_pre_topc(X2,X1))=>![X3]:((v1_borsuk_1(X3,X1)&m1_pre_topc(X3,X1))=>r4_tsep_1(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_tsep_1)).
% 0.13/0.38  fof(c_0_4, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v1_borsuk_1(X3,X1))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_borsuk_1(X4,X1))&m1_pre_topc(X4,X1))=>(r1_tsep_1(X3,X4)=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:((((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(((v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))))))))))), inference(assume_negation,[status(cth)],[t148_tmap_1])).
% 0.13/0.38  fof(c_0_5, plain, ![X7, X8, X9, X10, X11, X12]:(((v1_funct_1(k10_tmap_1(X7,X8,X9,X10,X11,X12))|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)|v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)|v2_struct_0(X9)|~m1_pre_topc(X9,X7)|v2_struct_0(X10)|~m1_pre_topc(X10,X7)|~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))|~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X8))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X8))))))&(v1_funct_2(k10_tmap_1(X7,X8,X9,X10,X11,X12),u1_struct_0(k1_tsep_1(X7,X9,X10)),u1_struct_0(X8))|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)|v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)|v2_struct_0(X9)|~m1_pre_topc(X9,X7)|v2_struct_0(X10)|~m1_pre_topc(X10,X7)|~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))|~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X8))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X8)))))))&(m1_subset_1(k10_tmap_1(X7,X8,X9,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X7,X9,X10)),u1_struct_0(X8))))|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)|v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8)|v2_struct_0(X9)|~m1_pre_topc(X9,X7)|v2_struct_0(X10)|~m1_pre_topc(X10,X7)|~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X8))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X8))))|~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X8))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X8))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k10_tmap_1])])])])).
% 0.13/0.38  fof(c_0_6, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v1_borsuk_1(esk3_0,esk1_0))&m1_pre_topc(esk3_0,esk1_0))&(((~v2_struct_0(esk4_0)&v1_borsuk_1(esk4_0,esk1_0))&m1_pre_topc(esk4_0,esk1_0))&(r1_tsep_1(esk3_0,esk4_0)&((((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&v5_pre_topc(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&((((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&v5_pre_topc(esk6_0,esk4_0,esk2_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&(~v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))|~v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))|~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).
% 0.13/0.38  cnf(c_0_7, plain, (v1_funct_1(k10_tmap_1(X1,X2,X3,X4,X5,X6))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_8, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_9, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_10, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_11, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_12, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (v1_funct_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])]), c_0_13]), c_0_14])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_17, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_20, plain, (v1_funct_2(k10_tmap_1(X1,X2,X3,X4,X5,X6),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (v1_funct_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (v1_funct_2(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])]), c_0_13]), c_0_14])).
% 0.13/0.38  cnf(c_0_28, plain, (m1_subset_1(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  fof(c_0_29, plain, ![X13, X14, X15, X16, X17, X18]:((((v1_funct_1(k10_tmap_1(X13,X14,X15,X16,X17,X18))|~r4_tsep_1(X13,X15,X16)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X14))|~v5_pre_topc(X18,X16,X14)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14)))))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))|~v5_pre_topc(X17,X15,X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14)))))|~r1_tsep_1(X15,X16)|(v2_struct_0(X16)|~m1_pre_topc(X16,X13))|(v2_struct_0(X15)|~m1_pre_topc(X15,X13))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))&(v1_funct_2(k10_tmap_1(X13,X14,X15,X16,X17,X18),u1_struct_0(k1_tsep_1(X13,X15,X16)),u1_struct_0(X14))|~r4_tsep_1(X13,X15,X16)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X14))|~v5_pre_topc(X18,X16,X14)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14)))))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))|~v5_pre_topc(X17,X15,X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14)))))|~r1_tsep_1(X15,X16)|(v2_struct_0(X16)|~m1_pre_topc(X16,X13))|(v2_struct_0(X15)|~m1_pre_topc(X15,X13))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))))&(v5_pre_topc(k10_tmap_1(X13,X14,X15,X16,X17,X18),k1_tsep_1(X13,X15,X16),X14)|~r4_tsep_1(X13,X15,X16)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X14))|~v5_pre_topc(X18,X16,X14)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14)))))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))|~v5_pre_topc(X17,X15,X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14)))))|~r1_tsep_1(X15,X16)|(v2_struct_0(X16)|~m1_pre_topc(X16,X13))|(v2_struct_0(X15)|~m1_pre_topc(X15,X13))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13))))&(m1_subset_1(k10_tmap_1(X13,X14,X15,X16,X17,X18),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X13,X15,X16)),u1_struct_0(X14))))|~r4_tsep_1(X13,X15,X16)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X14))|~v5_pre_topc(X18,X16,X14)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14)))))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))|~v5_pre_topc(X17,X15,X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14)))))|~r1_tsep_1(X15,X16)|(v2_struct_0(X16)|~m1_pre_topc(X16,X13))|(v2_struct_0(X15)|~m1_pre_topc(X15,X13))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14))|(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t145_tmap_1])])])])])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (~v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))|~v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))|~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (v1_funct_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (v1_funct_2(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,esk4_0)),u1_struct_0(esk2_0))))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12])]), c_0_13]), c_0_14])).
% 0.13/0.38  cnf(c_0_34, plain, (v5_pre_topc(k10_tmap_1(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X3,X4),X2)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r4_tsep_1(X1,X3,X4)|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))|~v5_pre_topc(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v5_pre_topc(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~r1_tsep_1(X3,X4)|~m1_pre_topc(X4,X1)|~m1_pre_topc(X3,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  fof(c_0_36, plain, ![X19, X20, X21]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|(~v1_borsuk_1(X20,X19)|~m1_pre_topc(X20,X19)|(~v1_borsuk_1(X21,X19)|~m1_pre_topc(X21,X19)|r4_tsep_1(X19,X20,X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t87_tsep_1])])])])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))|~v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (v1_funct_2(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (m1_subset_1(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk3_0,esk4_0)),u1_struct_0(esk2_0))))|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (v5_pre_topc(k10_tmap_1(X1,esk2_0,X2,esk4_0,X3,esk6_0),k1_tsep_1(X1,X2,esk4_0),esk2_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r4_tsep_1(X1,X2,esk4_0)|~v5_pre_topc(X3,X2,esk2_0)|~r1_tsep_1(X2,esk4_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X3)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_8]), c_0_35]), c_0_9]), c_0_10]), c_0_11]), c_0_12])]), c_0_13]), c_0_14])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (r1_tsep_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_43, plain, (v2_struct_0(X1)|r4_tsep_1(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_borsuk_1(X2,X1)|~m1_pre_topc(X2,X1)|~v1_borsuk_1(X3,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (v1_borsuk_1(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)|~m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (m1_subset_1(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(esk1_0,esk3_0,esk4_0)),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (v5_pre_topc(k10_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(X1,esk3_0,esk4_0),esk2_0)|v2_struct_0(X1)|~r4_tsep_1(X1,esk3_0,esk4_0)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_16]), c_0_41]), c_0_42]), c_0_17]), c_0_18])]), c_0_19])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (r4_tsep_1(esk1_0,X1,esk4_0)|~v1_borsuk_1(X1,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_22]), c_0_24]), c_0_25])]), c_0_26])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (v1_borsuk_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (~v5_pre_topc(k10_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_tsep_1(esk1_0,esk3_0,esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_49])]), c_0_50]), c_0_26]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 52
% 0.13/0.38  # Proof object clause steps            : 43
% 0.13/0.38  # Proof object formula steps           : 9
% 0.13/0.38  # Proof object conjectures             : 41
% 0.13/0.38  # Proof object clause conjectures      : 38
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 27
% 0.13/0.38  # Proof object initial formulas used   : 4
% 0.13/0.38  # Proof object generating inferences   : 13
% 0.13/0.38  # Proof object simplifying inferences  : 81
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 4
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 30
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 30
% 0.13/0.38  # Processed clauses                    : 107
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 3
% 0.13/0.38  # ...remaining for further processing  : 104
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 3
% 0.13/0.38  # Generated clauses                    : 81
% 0.13/0.38  # ...of the previous two non-trivial   : 83
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 81
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 74
% 0.13/0.38  #    Positive orientable unit clauses  : 29
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 5
% 0.13/0.38  #    Non-unit-clauses                  : 40
% 0.13/0.38  # Current number of unprocessed clauses: 33
% 0.13/0.38  # ...number of literals in the above   : 329
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 30
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1118
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 10
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.38  # Unit Clause-clause subsumption calls : 83
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 24
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 10824
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.039 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.044 s
% 0.13/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
