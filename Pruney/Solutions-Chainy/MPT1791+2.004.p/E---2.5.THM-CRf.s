%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:13 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 481 expanded)
%              Number of clauses        :   45 ( 165 expanded)
%              Number of leaves         :    9 ( 119 expanded)
%              Depth                    :   11
%              Number of atoms          :  303 (2492 expanded)
%              Number of equality atoms :   40 ( 431 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t106_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(t103_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,u1_pre_topc(X1))
          <=> u1_pre_topc(X1) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(c_0_9,plain,(
    ! [X5] : m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_10,plain,(
    ! [X4] : k2_subset_1(X4) = X4 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t106_tmap_1])).

fof(c_0_12,plain,(
    ! [X20,X21] :
      ( ( u1_struct_0(k6_tmap_1(X20,X21)) = u1_struct_0(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( u1_pre_topc(k6_tmap_1(X20,X21)) = k5_tmap_1(X20,X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X16,X17] :
      ( ( v1_pre_topc(k6_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16))) )
      & ( v2_pre_topc(k6_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16))) )
      & ( l1_pre_topc(k6_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v3_pre_topc(esk5_0,esk4_0)
      | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) != k6_tmap_1(esk4_0,esk5_0) )
    & ( v3_pre_topc(esk5_0,esk4_0)
      | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = k6_tmap_1(esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_17,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( v1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X18,X19] :
      ( ( ~ r2_hidden(X19,u1_pre_topc(X18))
        | u1_pre_topc(X18) = k5_tmap_1(X18,X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( u1_pre_topc(X18) != k5_tmap_1(X18,X19)
        | r2_hidden(X19,u1_pre_topc(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

fof(c_0_22,plain,(
    ! [X7,X8,X9,X10] :
      ( ( r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ r1_tarski(X8,u1_pre_topc(X7))
        | r2_hidden(k5_setfam_1(u1_struct_0(X7),X8),u1_pre_topc(X7))
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(X9,u1_pre_topc(X7))
        | ~ r2_hidden(X10,u1_pre_topc(X7))
        | r2_hidden(k9_subset_1(u1_struct_0(X7),X9,X10),u1_pre_topc(X7))
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))
        | m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))
        | m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk2_1(X7),u1_pre_topc(X7))
        | m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk3_1(X7),u1_pre_topc(X7))
        | m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))
        | m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))
        | r1_tarski(esk1_1(X7),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))
        | r1_tarski(esk1_1(X7),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk2_1(X7),u1_pre_topc(X7))
        | r1_tarski(esk1_1(X7),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk3_1(X7),u1_pre_topc(X7))
        | r1_tarski(esk1_1(X7),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))
        | r1_tarski(esk1_1(X7),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk2_1(X7),u1_pre_topc(X7))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk3_1(X7),u1_pre_topc(X7))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))
        | ~ r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))
        | v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_23,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_28,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(X6)
      | ~ v1_pre_topc(X6)
      | X6 = g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_29,plain,
    ( u1_struct_0(k6_tmap_1(X1,u1_struct_0(X1))) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | v1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_32,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k5_tmap_1(X1,u1_struct_0(X1)) = u1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( k5_tmap_1(esk4_0,esk5_0) = u1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_36,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk4_0))) = u1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_40,plain,
    ( k5_tmap_1(X1,u1_struct_0(X1)) = u1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_18]),c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k5_tmap_1(esk4_0,u1_struct_0(esk4_0)) = u1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) = u1_pre_topc(esk4_0)
    | ~ r2_hidden(esk5_0,u1_pre_topc(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_24]),c_0_35]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk4_0,esk5_0)) = u1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( v1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_45,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))) = k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_47,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0))) = u1_pre_topc(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_25]),c_0_41]),c_0_26])]),c_0_27])).

cnf(c_0_48,negated_conjecture,
    ( ~ v3_pre_topc(esk5_0,esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) != k6_tmap_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = k6_tmap_1(esk4_0,esk5_0)
    | ~ r2_hidden(esk5_0,u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_42]),c_0_43]),c_0_44]),c_0_45])])).

fof(c_0_50,plain,(
    ! [X14,X15] :
      ( ( ~ v3_pre_topc(X15,X14)
        | r2_hidden(X15,u1_pre_topc(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( ~ r2_hidden(X15,u1_pre_topc(X14))
        | v3_pre_topc(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_51,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = k6_tmap_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_52,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( ~ v3_pre_topc(esk5_0,esk4_0)
    | ~ r2_hidden(esk5_0,u1_pre_topc(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( r2_hidden(X2,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | u1_pre_topc(X1) != k5_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k6_tmap_1(esk4_0,esk5_0)
    | v3_pre_topc(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(esk5_0,u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_26]),c_0_24])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk5_0,u1_pre_topc(esk4_0))
    | k5_tmap_1(esk4_0,esk5_0) != u1_pre_topc(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k6_tmap_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_26]),c_0_24])]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk5_0,u1_pre_topc(esk4_0))
    | u1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) != u1_pre_topc(esk4_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) = u1_pre_topc(esk4_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:30:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.030 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.19/0.40  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.40  fof(t106_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tmap_1)).
% 0.19/0.40  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.19/0.40  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.19/0.40  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.19/0.40  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.19/0.40  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.19/0.40  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.19/0.40  fof(c_0_9, plain, ![X5]:m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.19/0.40  fof(c_0_10, plain, ![X4]:k2_subset_1(X4)=X4, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.40  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t106_tmap_1])).
% 0.19/0.40  fof(c_0_12, plain, ![X20, X21]:((u1_struct_0(k6_tmap_1(X20,X21))=u1_struct_0(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(u1_pre_topc(k6_tmap_1(X20,X21))=k5_tmap_1(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.19/0.40  cnf(c_0_13, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.40  cnf(c_0_14, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.40  fof(c_0_15, plain, ![X16, X17]:(((v1_pre_topc(k6_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))))&(v2_pre_topc(k6_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16))))))&(l1_pre_topc(k6_tmap_1(X16,X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.19/0.40  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&((~v3_pre_topc(esk5_0,esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))!=k6_tmap_1(esk4_0,esk5_0))&(v3_pre_topc(esk5_0,esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=k6_tmap_1(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.19/0.40  cnf(c_0_17, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.40  cnf(c_0_19, plain, (v1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_20, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  fof(c_0_21, plain, ![X18, X19]:((~r2_hidden(X19,u1_pre_topc(X18))|u1_pre_topc(X18)=k5_tmap_1(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(u1_pre_topc(X18)!=k5_tmap_1(X18,X19)|r2_hidden(X19,u1_pre_topc(X18))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.19/0.40  fof(c_0_22, plain, ![X7, X8, X9, X10]:((((r2_hidden(u1_struct_0(X7),u1_pre_topc(X7))|~v2_pre_topc(X7)|~l1_pre_topc(X7))&(~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|(~r1_tarski(X8,u1_pre_topc(X7))|r2_hidden(k5_setfam_1(u1_struct_0(X7),X8),u1_pre_topc(X7)))|~v2_pre_topc(X7)|~l1_pre_topc(X7)))&(~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))|(~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X7)))|(~r2_hidden(X9,u1_pre_topc(X7))|~r2_hidden(X10,u1_pre_topc(X7))|r2_hidden(k9_subset_1(u1_struct_0(X7),X9,X10),u1_pre_topc(X7))))|~v2_pre_topc(X7)|~l1_pre_topc(X7)))&(((m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&((m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(((r2_hidden(esk2_1(X7),u1_pre_topc(X7))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(r2_hidden(esk3_1(X7),u1_pre_topc(X7))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))&(~r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))|(m1_subset_1(esk1_1(X7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X7))))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))))&(((m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&((m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(((r2_hidden(esk2_1(X7),u1_pre_topc(X7))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(r2_hidden(esk3_1(X7),u1_pre_topc(X7))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))&(~r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))|(r1_tarski(esk1_1(X7),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))))&((m1_subset_1(esk2_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&((m1_subset_1(esk3_1(X7),k1_zfmisc_1(u1_struct_0(X7)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(((r2_hidden(esk2_1(X7),u1_pre_topc(X7))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7))&(r2_hidden(esk3_1(X7),u1_pre_topc(X7))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))&(~r2_hidden(k9_subset_1(u1_struct_0(X7),esk2_1(X7),esk3_1(X7)),u1_pre_topc(X7))|(~r2_hidden(k5_setfam_1(u1_struct_0(X7),esk1_1(X7)),u1_pre_topc(X7))|~r2_hidden(u1_struct_0(X7),u1_pre_topc(X7)))|v2_pre_topc(X7)|~l1_pre_topc(X7)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.19/0.40  cnf(c_0_23, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  fof(c_0_28, plain, ![X6]:(~l1_pre_topc(X6)|(~v1_pre_topc(X6)|X6=g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.19/0.40  cnf(c_0_29, plain, (u1_struct_0(k6_tmap_1(X1,u1_struct_0(X1)))=u1_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.40  cnf(c_0_30, plain, (v2_struct_0(X1)|v1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.19/0.40  cnf(c_0_31, plain, (v2_struct_0(X1)|l1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 0.19/0.40  cnf(c_0_32, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_33, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_34, plain, (k5_tmap_1(X1,u1_struct_0(X1))=u1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_23, c_0_18])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (k5_tmap_1(esk4_0,esk5_0)=u1_pre_topc(k6_tmap_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 0.19/0.40  cnf(c_0_36, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, (u1_struct_0(k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))=u1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_25]), c_0_26])]), c_0_27])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (v1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_25]), c_0_26])]), c_0_27])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_25]), c_0_26])]), c_0_27])).
% 0.19/0.40  cnf(c_0_40, plain, (k5_tmap_1(X1,u1_struct_0(X1))=u1_pre_topc(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_18]), c_0_33])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (k5_tmap_1(esk4_0,u1_struct_0(esk4_0))=u1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_25]), c_0_26])]), c_0_27])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk4_0,esk5_0))=u1_pre_topc(esk4_0)|~r2_hidden(esk5_0,u1_pre_topc(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_24]), c_0_35]), c_0_25]), c_0_26])]), c_0_27])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (u1_struct_0(k6_tmap_1(esk4_0,esk5_0))=u1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (v1_pre_topc(k6_tmap_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 0.19/0.40  cnf(c_0_45, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0))))=k6_tmap_1(esk4_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))=u1_pre_topc(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_25]), c_0_41]), c_0_26])]), c_0_27])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (~v3_pre_topc(esk5_0,esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))!=k6_tmap_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_49, negated_conjecture, (g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=k6_tmap_1(esk4_0,esk5_0)|~r2_hidden(esk5_0,u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_42]), c_0_43]), c_0_44]), c_0_45])])).
% 0.19/0.40  fof(c_0_50, plain, ![X14, X15]:((~v3_pre_topc(X15,X14)|r2_hidden(X15,u1_pre_topc(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(~r2_hidden(X15,u1_pre_topc(X14))|v3_pre_topc(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, (v3_pre_topc(esk5_0,esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=k6_tmap_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_52, negated_conjecture, (g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=k6_tmap_1(esk4_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.40  cnf(c_0_53, negated_conjecture, (~v3_pre_topc(esk5_0,esk4_0)|~r2_hidden(esk5_0,u1_pre_topc(esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.40  cnf(c_0_54, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.40  cnf(c_0_55, plain, (r2_hidden(X2,u1_pre_topc(X1))|v2_struct_0(X1)|u1_pre_topc(X1)!=k5_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_56, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(esk4_0))=k6_tmap_1(esk4_0,esk5_0)|v3_pre_topc(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (~r2_hidden(esk5_0,u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_26]), c_0_24])])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (r2_hidden(esk5_0,u1_pre_topc(esk4_0))|k5_tmap_1(esk4_0,esk5_0)!=u1_pre_topc(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(esk4_0))=k6_tmap_1(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_26]), c_0_24])]), c_0_58])).
% 0.19/0.40  cnf(c_0_61, negated_conjecture, (r2_hidden(esk5_0,u1_pre_topc(esk4_0))|u1_pre_topc(k6_tmap_1(esk4_0,esk5_0))!=u1_pre_topc(esk4_0)), inference(rw,[status(thm)],[c_0_59, c_0_35])).
% 0.19/0.40  cnf(c_0_62, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk4_0,esk5_0))=u1_pre_topc(esk4_0)), inference(rw,[status(thm)],[c_0_47, c_0_60])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])]), c_0_58]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 64
% 0.19/0.40  # Proof object clause steps            : 45
% 0.19/0.40  # Proof object formula steps           : 19
% 0.19/0.40  # Proof object conjectures             : 30
% 0.19/0.40  # Proof object clause conjectures      : 27
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 18
% 0.19/0.40  # Proof object initial formulas used   : 9
% 0.19/0.40  # Proof object generating inferences   : 22
% 0.19/0.40  # Proof object simplifying inferences  : 63
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 9
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 36
% 0.19/0.40  # Removed in clause preprocessing      : 1
% 0.19/0.40  # Initial clauses in saturation        : 35
% 0.19/0.40  # Processed clauses                    : 205
% 0.19/0.40  # ...of these trivial                  : 2
% 0.19/0.40  # ...subsumed                          : 22
% 0.19/0.40  # ...remaining for further processing  : 181
% 0.19/0.40  # Other redundant clauses eliminated   : 0
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 2
% 0.19/0.40  # Backward-rewritten                   : 57
% 0.19/0.40  # Generated clauses                    : 593
% 0.19/0.40  # ...of the previous two non-trivial   : 516
% 0.19/0.40  # Contextual simplify-reflections      : 22
% 0.19/0.40  # Paramodulations                      : 593
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 0
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 87
% 0.19/0.40  #    Positive orientable unit clauses  : 12
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 2
% 0.19/0.40  #    Non-unit-clauses                  : 73
% 0.19/0.40  # Current number of unprocessed clauses: 371
% 0.19/0.40  # ...number of literals in the above   : 2079
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 95
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 1180
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 404
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 37
% 0.19/0.40  # Unit Clause-clause subsumption calls : 78
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 12
% 0.19/0.40  # BW rewrite match successes           : 8
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 32380
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.061 s
% 0.19/0.40  # System time              : 0.004 s
% 0.19/0.40  # Total time               : 0.065 s
% 0.19/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
