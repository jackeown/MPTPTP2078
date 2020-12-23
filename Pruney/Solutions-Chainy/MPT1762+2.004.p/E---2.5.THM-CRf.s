%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:35 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 357 expanded)
%              Number of clauses        :   57 ( 123 expanded)
%              Number of leaves         :    8 (  87 expanded)
%              Depth                    :   21
%              Number of atoms          :  380 (4392 expanded)
%              Number of equality atoms :   45 ( 234 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_tmap_1,conjecture,(
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
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                           => ( ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ( r2_hidden(X7,u1_struct_0(X3))
                                   => k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X7) = k1_funct_1(X6,X7) ) )
                             => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t173_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X4,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,X1)
                           => ( r2_hidden(X6,X4)
                             => k3_funct_2(X1,X2,X3,X6) = k1_funct_1(X5,X6) ) )
                       => k2_partfun1(X1,X2,X3,X4) = X5 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d5_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

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

fof(c_0_8,negated_conjecture,(
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
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                       => ( m1_pre_topc(X3,X4)
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                             => ( ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X4))
                                   => ( r2_hidden(X7,u1_struct_0(X3))
                                     => k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X7) = k1_funct_1(X6,X7) ) )
                               => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t73_tmap_1])).

fof(c_0_9,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,X19)
      | l1_pre_topc(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_10,negated_conjecture,(
    ! [X35] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk2_0)
      & ~ v2_struct_0(esk5_0)
      & m1_pre_topc(esk5_0,esk2_0)
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))
      & m1_pre_topc(esk4_0,esk5_0)
      & v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
      & ( ~ m1_subset_1(X35,u1_struct_0(esk5_0))
        | ~ r2_hidden(X35,u1_struct_0(esk4_0))
        | k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X35) = k1_funct_1(esk7_0,X35) )
      & ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_11,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( m1_subset_1(esk1_5(X12,X13,X14,X15,X16),X12)
        | k2_partfun1(X12,X13,X14,X15) = X16
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X15,X13)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X13)))
        | v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(X12))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | v1_xboole_0(X13)
        | v1_xboole_0(X12) )
      & ( r2_hidden(esk1_5(X12,X13,X14,X15,X16),X15)
        | k2_partfun1(X12,X13,X14,X15) = X16
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X15,X13)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X13)))
        | v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(X12))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | v1_xboole_0(X13)
        | v1_xboole_0(X12) )
      & ( k3_funct_2(X12,X13,X14,esk1_5(X12,X13,X14,X15,X16)) != k1_funct_1(X16,esk1_5(X12,X13,X14,X15,X16))
        | k2_partfun1(X12,X13,X14,X15) = X16
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X15,X13)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X13)))
        | v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(X12))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | v1_xboole_0(X13)
        | v1_xboole_0(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t173_funct_2])])])])])])).

fof(c_0_12,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_pre_topc(X28,X27)
      | m1_subset_1(u1_struct_0(X28),k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_13,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)
    | k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

fof(c_0_23,plain,(
    ! [X21] :
      ( v2_struct_0(X21)
      | ~ l1_struct_0(X21)
      | ~ v1_xboole_0(u1_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_24,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(X1)
    | m1_subset_1(esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_32,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_33,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_34,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_22])])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_35]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_37]),c_0_15])])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_5(X1,X2,X3,X4,X5),X4)
    | k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_39])])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,plain,
    ( k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X3,esk1_5(X1,X2,X3,X4,X5)) != k1_funct_1(X5,esk1_5(X1,X2,X3,X4,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0)) = esk7_0
    | r2_hidden(esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_45,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_41]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(X1)
    | k3_funct_2(X1,u1_struct_0(esk3_0),X2,esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0)) != k1_funct_1(esk7_0,esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_48,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1) = k1_funct_1(esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | r2_hidden(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_25]),c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_50,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_34]),c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0)) != k1_funct_1(esk7_0,esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_25]),c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_52,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])).

fof(c_0_53,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,X22)
      | ~ m1_pre_topc(X25,X22)
      | ~ v1_funct_1(X26)
      | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X23))
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X23))))
      | ~ m1_pre_topc(X25,X24)
      | k3_tmap_1(X22,X23,X24,X25,X26) = k2_partfun1(u1_struct_0(X24),u1_struct_0(X23),X26,u1_struct_0(X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

cnf(c_0_54,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_52]),c_0_31])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_57,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_34]),c_0_22])])).

cnf(c_0_58,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0) = k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_25]),c_0_56]),c_0_46]),c_0_27]),c_0_28])]),c_0_42])).

cnf(c_0_59,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_57]),c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk5_0,esk4_0,esk6_0) = k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_21])).

cnf(c_0_61,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_62,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_63,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_34]),c_0_39])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_65,negated_conjecture,
    ( k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0) = k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_14]),c_0_61]),c_0_37]),c_0_15])]),c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_63]),c_0_42])).

fof(c_0_67,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ r2_funct_2(X8,X9,X10,X11)
        | X10 = X11
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( X10 != X11
        | r2_funct_2(X8,X9,X10,X11)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)),esk7_0) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_34]),c_0_46])])).

cnf(c_0_70,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_17]),c_0_18]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:25:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S059I
% 0.21/0.39  # and selection function SelectComplexExceptUniqMaxPosHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.028 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t73_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(r2_hidden(X7,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X7)=k1_funct_1(X6,X7)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tmap_1)).
% 0.21/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.39  fof(t173_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X4,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(![X6]:(m1_subset_1(X6,X1)=>(r2_hidden(X6,X4)=>k3_funct_2(X1,X2,X3,X6)=k1_funct_1(X5,X6)))=>k2_partfun1(X1,X2,X3,X4)=X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_funct_2)).
% 0.21/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.21/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.21/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.39  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.21/0.39  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.21/0.39  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(r2_hidden(X7,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X7)=k1_funct_1(X6,X7)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6)))))))))), inference(assume_negation,[status(cth)],[t73_tmap_1])).
% 0.21/0.39  fof(c_0_9, plain, ![X19, X20]:(~l1_pre_topc(X19)|(~m1_pre_topc(X20,X19)|l1_pre_topc(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.39  fof(c_0_10, negated_conjecture, ![X35]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk2_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))))&(m1_pre_topc(esk4_0,esk5_0)&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))&((~m1_subset_1(X35,u1_struct_0(esk5_0))|(~r2_hidden(X35,u1_struct_0(esk4_0))|k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X35)=k1_funct_1(esk7_0,X35)))&~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.21/0.39  fof(c_0_11, plain, ![X12, X13, X14, X15, X16]:((m1_subset_1(esk1_5(X12,X13,X14,X15,X16),X12)|k2_partfun1(X12,X13,X14,X15)=X16|(~v1_funct_1(X16)|~v1_funct_2(X16,X15,X13)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X13))))|(v1_xboole_0(X15)|~m1_subset_1(X15,k1_zfmisc_1(X12)))|(~v1_funct_1(X14)|~v1_funct_2(X14,X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))))|v1_xboole_0(X13)|v1_xboole_0(X12))&((r2_hidden(esk1_5(X12,X13,X14,X15,X16),X15)|k2_partfun1(X12,X13,X14,X15)=X16|(~v1_funct_1(X16)|~v1_funct_2(X16,X15,X13)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X13))))|(v1_xboole_0(X15)|~m1_subset_1(X15,k1_zfmisc_1(X12)))|(~v1_funct_1(X14)|~v1_funct_2(X14,X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))))|v1_xboole_0(X13)|v1_xboole_0(X12))&(k3_funct_2(X12,X13,X14,esk1_5(X12,X13,X14,X15,X16))!=k1_funct_1(X16,esk1_5(X12,X13,X14,X15,X16))|k2_partfun1(X12,X13,X14,X15)=X16|(~v1_funct_1(X16)|~v1_funct_2(X16,X15,X13)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X13))))|(v1_xboole_0(X15)|~m1_subset_1(X15,k1_zfmisc_1(X12)))|(~v1_funct_1(X14)|~v1_funct_2(X14,X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))))|v1_xboole_0(X13)|v1_xboole_0(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t173_funct_2])])])])])])).
% 0.21/0.39  fof(c_0_12, plain, ![X27, X28]:(~l1_pre_topc(X27)|(~m1_pre_topc(X28,X27)|m1_subset_1(u1_struct_0(X28),k1_zfmisc_1(u1_struct_0(X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.21/0.39  cnf(c_0_13, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_14, negated_conjecture, (m1_pre_topc(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_16, plain, (m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)|k2_partfun1(X1,X2,X3,X4)=X5|v1_xboole_0(X4)|v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_18, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_20, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.21/0.39  fof(c_0_23, plain, ![X21]:(v2_struct_0(X21)|~l1_struct_0(X21)|~v1_xboole_0(u1_struct_0(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(X1)|m1_subset_1(esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))|~v1_funct_2(X2,X1,u1_struct_0(esk3_0))|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.21/0.39  cnf(c_0_27, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_29, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.39  cnf(c_0_30, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28])])).
% 0.21/0.39  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  fof(c_0_32, plain, ![X18]:(~l1_pre_topc(X18)|l1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.39  cnf(c_0_33, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.21/0.39  cnf(c_0_34, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.39  cnf(c_0_35, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_22])])).
% 0.21/0.39  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_37, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_35]), c_0_36])).
% 0.21/0.39  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_37]), c_0_15])])).
% 0.21/0.39  cnf(c_0_40, plain, (r2_hidden(esk1_5(X1,X2,X3,X4,X5),X4)|k2_partfun1(X1,X2,X3,X4)=X5|v1_xboole_0(X4)|v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_41, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_39])])).
% 0.21/0.39  cnf(c_0_42, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_43, plain, (k2_partfun1(X1,X2,X3,X4)=X5|v1_xboole_0(X4)|v1_xboole_0(X2)|v1_xboole_0(X1)|k3_funct_2(X1,X2,X3,esk1_5(X1,X2,X3,X4,X5))!=k1_funct_1(X5,esk1_5(X1,X2,X3,X4,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_44, negated_conjecture, (k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0))=esk7_0|r2_hidden(esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))|~v1_funct_2(X2,X1,u1_struct_0(esk3_0))|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_17]), c_0_18]), c_0_19])])).
% 0.21/0.39  cnf(c_0_45, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_41]), c_0_42])).
% 0.21/0.39  cnf(c_0_46, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_47, negated_conjecture, (k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(X1)|k3_funct_2(X1,u1_struct_0(esk3_0),X2,esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0))!=k1_funct_1(esk7_0,esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))|~v1_funct_2(X2,X1,u1_struct_0(esk3_0))|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_17]), c_0_18]), c_0_19])])).
% 0.21/0.39  cnf(c_0_48, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1)=k1_funct_1(esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_49, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|r2_hidden(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_25]), c_0_26]), c_0_27]), c_0_28])])).
% 0.21/0.39  cnf(c_0_50, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_34]), c_0_46])])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0))!=k1_funct_1(esk7_0,esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_25]), c_0_26]), c_0_27]), c_0_28])])).
% 0.21/0.39  cnf(c_0_52, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])).
% 0.21/0.39  fof(c_0_53, plain, ![X22, X23, X24, X25, X26]:(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|(~m1_pre_topc(X24,X22)|(~m1_pre_topc(X25,X22)|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X23))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X23))))|(~m1_pre_topc(X25,X24)|k3_tmap_1(X22,X23,X24,X25,X26)=k2_partfun1(u1_struct_0(X24),u1_struct_0(X23),X26,u1_struct_0(X25)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.21/0.39  cnf(c_0_54, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_52]), c_0_31])).
% 0.21/0.39  cnf(c_0_55, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.39  cnf(c_0_56, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_57, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_34]), c_0_22])])).
% 0.21/0.39  cnf(c_0_58, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0)=k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,esk5_0)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_25]), c_0_56]), c_0_46]), c_0_27]), c_0_28])]), c_0_42])).
% 0.21/0.39  cnf(c_0_59, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_57]), c_0_36])).
% 0.21/0.39  cnf(c_0_60, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk5_0,esk4_0,esk6_0)=k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_58, c_0_21])).
% 0.21/0.39  cnf(c_0_61, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_62, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_63, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_34]), c_0_39])])).
% 0.21/0.39  cnf(c_0_64, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_65, negated_conjecture, (k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0)=k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_14]), c_0_61]), c_0_37]), c_0_15])]), c_0_62])).
% 0.21/0.39  cnf(c_0_66, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_63]), c_0_42])).
% 0.21/0.39  fof(c_0_67, plain, ![X8, X9, X10, X11]:((~r2_funct_2(X8,X9,X10,X11)|X10=X11|(~v1_funct_1(X10)|~v1_funct_2(X10,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|~v1_funct_1(X11)|~v1_funct_2(X11,X8,X9)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))&(X10!=X11|r2_funct_2(X8,X9,X10,X11)|(~v1_funct_1(X10)|~v1_funct_2(X10,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|~v1_funct_1(X11)|~v1_funct_2(X11,X8,X9)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.21/0.39  cnf(c_0_68, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)),esk7_0)), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.39  cnf(c_0_69, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_34]), c_0_46])])).
% 0.21/0.39  cnf(c_0_70, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.21/0.39  cnf(c_0_71, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk7_0,esk7_0)), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.21/0.39  cnf(c_0_72, plain, (r2_funct_2(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)), inference(er,[status(thm)],[c_0_70])).
% 0.21/0.39  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_17]), c_0_18]), c_0_19])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 74
% 0.21/0.39  # Proof object clause steps            : 57
% 0.21/0.39  # Proof object formula steps           : 17
% 0.21/0.39  # Proof object conjectures             : 50
% 0.21/0.39  # Proof object clause conjectures      : 47
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 28
% 0.21/0.39  # Proof object initial formulas used   : 8
% 0.21/0.39  # Proof object generating inferences   : 26
% 0.21/0.39  # Proof object simplifying inferences  : 65
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 8
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 29
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 29
% 0.21/0.39  # Processed clauses                    : 99
% 0.21/0.39  # ...of these trivial                  : 1
% 0.21/0.39  # ...subsumed                          : 0
% 0.21/0.39  # ...remaining for further processing  : 98
% 0.21/0.39  # Other redundant clauses eliminated   : 1
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 12
% 0.21/0.39  # Backward-rewritten                   : 7
% 0.21/0.39  # Generated clauses                    : 43
% 0.21/0.39  # ...of the previous two non-trivial   : 46
% 0.21/0.39  # Contextual simplify-reflections      : 2
% 0.21/0.39  # Paramodulations                      : 42
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 1
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 49
% 0.21/0.39  #    Positive orientable unit clauses  : 19
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 5
% 0.21/0.39  #    Non-unit-clauses                  : 25
% 0.21/0.39  # Current number of unprocessed clauses: 5
% 0.21/0.39  # ...number of literals in the above   : 27
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 48
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 410
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 31
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 14
% 0.21/0.39  # Unit Clause-clause subsumption calls : 23
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 5
% 0.21/0.39  # BW rewrite match successes           : 2
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 5122
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.035 s
% 0.21/0.39  # System time              : 0.004 s
% 0.21/0.39  # Total time               : 0.039 s
% 0.21/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
