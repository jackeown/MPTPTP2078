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
% DateTime   : Thu Dec  3 11:12:39 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   87 (2957 expanded)
%              Number of clauses        :   68 (1092 expanded)
%              Number of leaves         :    9 ( 698 expanded)
%              Depth                    :   24
%              Number of atoms          :  265 (24205 expanded)
%              Number of equality atoms :   36 ( 709 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( ( v4_pre_topc(X4,X2)
                        & v4_tops_1(X4,X2) )
                     => v5_tops_1(X4,X2) )
                    & ( v5_tops_1(X3,X1)
                     => ( v4_pre_topc(X3,X1)
                        & v4_tops_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tops_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(d7_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v5_tops_1(X2,X1)
          <=> X2 = k2_pre_topc(X1,k1_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(d6_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
          <=> ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
              & r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(t49_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( ( ( v4_pre_topc(X4,X2)
                          & v4_tops_1(X4,X2) )
                       => v5_tops_1(X4,X2) )
                      & ( v5_tops_1(X3,X1)
                       => ( v4_pre_topc(X3,X1)
                          & v4_tops_1(X3,X1) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t106_tops_1])).

fof(c_0_10,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | m1_subset_1(k1_tops_1(X16,X17),k1_zfmisc_1(u1_struct_0(X16))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

fof(c_0_11,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( v5_tops_1(esk3_0,esk1_0)
      | v4_pre_topc(esk4_0,esk2_0) )
    & ( ~ v4_pre_topc(esk3_0,esk1_0)
      | ~ v4_tops_1(esk3_0,esk1_0)
      | v4_pre_topc(esk4_0,esk2_0) )
    & ( v5_tops_1(esk3_0,esk1_0)
      | v4_tops_1(esk4_0,esk2_0) )
    & ( ~ v4_pre_topc(esk3_0,esk1_0)
      | ~ v4_tops_1(esk3_0,esk1_0)
      | v4_tops_1(esk4_0,esk2_0) )
    & ( v5_tops_1(esk3_0,esk1_0)
      | ~ v5_tops_1(esk4_0,esk2_0) )
    & ( ~ v4_pre_topc(esk3_0,esk1_0)
      | ~ v4_tops_1(esk3_0,esk1_0)
      | ~ v5_tops_1(esk4_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X14,X15] :
      ( ( ~ v5_tops_1(X15,X14)
        | X15 = k2_pre_topc(X14,k1_tops_1(X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( X15 != k2_pre_topc(X14,k1_tops_1(X14,X15))
        | v5_tops_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tops_1])])])])).

fof(c_0_13,plain,(
    ! [X18,X19] :
      ( ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | v4_pre_topc(k2_pre_topc(X18,X19),X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_14,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( X1 = k2_pre_topc(X2,k1_tops_1(X2,X1))
    | ~ v5_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X10,X11] :
      ( ( ~ v4_pre_topc(X11,X10)
        | k2_pre_topc(X10,X11) = X11
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( ~ v2_pre_topc(X10)
        | k2_pre_topc(X10,X11) != X11
        | v4_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_19,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)) = esk3_0
    | ~ v5_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_15]),c_0_16])])).

cnf(c_0_23,negated_conjecture,
    ( v5_tops_1(esk3_0,esk1_0)
    | v4_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_24,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(k1_tops_1(X12,k2_pre_topc(X12,X13)),X13)
        | ~ v4_tops_1(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( r1_tarski(X13,k2_pre_topc(X12,k1_tops_1(X12,X13)))
        | ~ v4_tops_1(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( ~ r1_tarski(k1_tops_1(X12,k2_pre_topc(X12,X13)),X13)
        | ~ r1_tarski(X13,k2_pre_topc(X12,k1_tops_1(X12,X13)))
        | v4_tops_1(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).

cnf(c_0_25,negated_conjecture,
    ( v5_tops_1(esk3_0,esk1_0)
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_26,plain,(
    ! [X7,X8,X9] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ r1_tarski(X8,X9)
      | r1_tarski(k2_pre_topc(X7,X8),k2_pre_topc(X7,X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).

fof(c_0_27,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | r1_tarski(k1_tops_1(X20,X21),X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_28,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_16])])).

cnf(c_0_32,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)) = esk3_0
    | v4_pre_topc(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X1)))
    | ~ v4_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)) = esk3_0
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_25])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk4_0) = esk4_0
    | ~ v4_pre_topc(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk2_0)
    | v4_pre_topc(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_39,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk4_0,k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)))
    | ~ v4_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_30])])).

cnf(c_0_41,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | v4_pre_topc(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,X1),k2_pre_topc(esk2_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_30])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_29]),c_0_30])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_29]),c_0_30])])).

cnf(c_0_45,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | ~ v4_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_15]),c_0_16])])).

cnf(c_0_46,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk4_0) = esk4_0
    | v4_pre_topc(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk1_0)
    | r1_tarski(esk4_0,k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)),k2_pre_topc(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_50,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk4_0) = esk4_0
    | k2_pre_topc(esk1_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)) = esk4_0
    | v4_pre_topc(esk3_0,esk1_0)
    | ~ r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,plain,
    ( v5_tops_1(X1,X2)
    | X1 != k2_pre_topc(X2,k1_tops_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_54,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)) = esk4_0
    | k2_pre_topc(esk1_0,esk3_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( v5_tops_1(esk3_0,esk1_0)
    | ~ v5_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_56,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | v5_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_29]),c_0_30])])).

cnf(c_0_57,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | v5_tops_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_58,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)) = esk3_0
    | k2_pre_topc(esk1_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_57])).

cnf(c_0_59,plain,
    ( v4_tops_1(X2,X1)
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_61,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_15]),c_0_21]),c_0_16])])).

cnf(c_0_62,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_58]),c_0_45])).

cnf(c_0_63,negated_conjecture,
    ( v4_tops_1(esk3_0,esk1_0)
    | ~ r1_tarski(esk3_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_15]),c_0_16])])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk2_0)
    | ~ v4_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_66,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( v4_tops_1(esk3_0,esk1_0)
    | v4_pre_topc(esk4_0,esk2_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_32]),c_0_64])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_15]),c_0_16])])).

cnf(c_0_69,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk2_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_70,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | ~ v4_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_71,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_62]),c_0_68])]),c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | v4_tops_1(esk3_0,esk1_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_34]),c_0_64])])).

cnf(c_0_73,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_66])])).

cnf(c_0_74,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_71])])).

cnf(c_0_75,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_62]),c_0_68])]),c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)),esk4_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk4_0,k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_75])])).

cnf(c_0_78,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_76]),c_0_77])])).

cnf(c_0_79,negated_conjecture,
    ( v5_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_78]),c_0_29]),c_0_30])])).

cnf(c_0_80,negated_conjecture,
    ( ~ v4_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0)
    | ~ v5_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_81,negated_conjecture,
    ( v5_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_79])])).

cnf(c_0_82,negated_conjecture,
    ( ~ v5_tops_1(esk4_0,esk2_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_66])])).

cnf(c_0_83,negated_conjecture,
    ( v4_tops_1(esk3_0,esk1_0)
    | ~ r1_tarski(esk3_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_62]),c_0_68])])).

cnf(c_0_84,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_81])])).

cnf(c_0_85,negated_conjecture,
    ( ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_79])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84]),c_0_64])]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:12:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.12/0.38  # and selection function SelectNewComplexAHP.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.028 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t106_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((v4_pre_topc(X4,X2)&v4_tops_1(X4,X2))=>v5_tops_1(X4,X2))&(v5_tops_1(X3,X1)=>(v4_pre_topc(X3,X1)&v4_tops_1(X3,X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_tops_1)).
% 0.12/0.38  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.12/0.38  fof(d7_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v5_tops_1(X2,X1)<=>X2=k2_pre_topc(X1,k1_tops_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tops_1)).
% 0.12/0.38  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 0.12/0.38  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.12/0.38  fof(d6_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_tops_1(X2,X1)<=>(r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)&r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tops_1)).
% 0.12/0.38  fof(t49_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 0.12/0.38  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.12/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(((v4_pre_topc(X4,X2)&v4_tops_1(X4,X2))=>v5_tops_1(X4,X2))&(v5_tops_1(X3,X1)=>(v4_pre_topc(X3,X1)&v4_tops_1(X3,X1))))))))), inference(assume_negation,[status(cth)],[t106_tops_1])).
% 0.12/0.38  fof(c_0_10, plain, ![X16, X17]:(~l1_pre_topc(X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|m1_subset_1(k1_tops_1(X16,X17),k1_zfmisc_1(u1_struct_0(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.12/0.38  fof(c_0_11, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((((v5_tops_1(esk3_0,esk1_0)|v4_pre_topc(esk4_0,esk2_0))&(~v4_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|v4_pre_topc(esk4_0,esk2_0)))&((v5_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0))&(~v4_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0))))&((v5_tops_1(esk3_0,esk1_0)|~v5_tops_1(esk4_0,esk2_0))&(~v4_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|~v5_tops_1(esk4_0,esk2_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.12/0.38  fof(c_0_12, plain, ![X14, X15]:((~v5_tops_1(X15,X14)|X15=k2_pre_topc(X14,k1_tops_1(X14,X15))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(X15!=k2_pre_topc(X14,k1_tops_1(X14,X15))|v5_tops_1(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tops_1])])])])).
% 0.12/0.38  fof(c_0_13, plain, ![X18, X19]:(~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|v4_pre_topc(k2_pre_topc(X18,X19),X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 0.12/0.38  cnf(c_0_14, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_17, plain, (X1=k2_pre_topc(X2,k1_tops_1(X2,X1))|~v5_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  fof(c_0_18, plain, ![X10, X11]:((~v4_pre_topc(X11,X10)|k2_pre_topc(X10,X11)=X11|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))&(~v2_pre_topc(X10)|k2_pre_topc(X10,X11)!=X11|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.12/0.38  cnf(c_0_19, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0))=esk3_0|~v5_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_15]), c_0_16])])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (v5_tops_1(esk3_0,esk1_0)|v4_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  fof(c_0_24, plain, ![X12, X13]:(((r1_tarski(k1_tops_1(X12,k2_pre_topc(X12,X13)),X13)|~v4_tops_1(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(r1_tarski(X13,k2_pre_topc(X12,k1_tops_1(X12,X13)))|~v4_tops_1(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12)))&(~r1_tarski(k1_tops_1(X12,k2_pre_topc(X12,X13)),X13)|~r1_tarski(X13,k2_pre_topc(X12,k1_tops_1(X12,X13)))|v4_tops_1(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (v5_tops_1(esk3_0,esk1_0)|v4_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  fof(c_0_26, plain, ![X7, X8, X9]:(~l1_pre_topc(X7)|(~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))|(~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))|(~r1_tarski(X8,X9)|r1_tarski(k2_pre_topc(X7,X8),k2_pre_topc(X7,X9)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).
% 0.12/0.38  fof(c_0_27, plain, ![X20, X21]:(~l1_pre_topc(X20)|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|r1_tarski(k1_tops_1(X20,X21),X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.12/0.38  cnf(c_0_28, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_16])])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0))=esk3_0|v4_pre_topc(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.38  cnf(c_0_33, plain, (r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X1)))|~v4_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0))=esk3_0|v4_tops_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_22, c_0_25])).
% 0.12/0.38  cnf(c_0_35, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_36, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (k2_pre_topc(esk2_0,esk4_0)=esk4_0|~v4_pre_topc(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (v4_pre_topc(esk4_0,esk2_0)|v4_pre_topc(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.38  fof(c_0_39, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (r1_tarski(esk4_0,k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)))|~v4_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_29]), c_0_30])])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)|v4_pre_topc(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_31, c_0_34])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (r1_tarski(k2_pre_topc(esk2_0,X1),k2_pre_topc(esk2_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_29]), c_0_30])])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_29]), c_0_30])])).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_29]), c_0_30])])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=esk3_0|~v4_pre_topc(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_15]), c_0_16])])).
% 0.12/0.38  cnf(c_0_46, negated_conjecture, (k2_pre_topc(esk2_0,esk4_0)=esk4_0|v4_pre_topc(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.38  cnf(c_0_47, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.38  cnf(c_0_48, negated_conjecture, (v4_pre_topc(esk3_0,esk1_0)|r1_tarski(esk4_0,k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)),k2_pre_topc(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.12/0.38  cnf(c_0_50, negated_conjecture, (k2_pre_topc(esk2_0,esk4_0)=esk4_0|k2_pre_topc(esk1_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.38  cnf(c_0_51, negated_conjecture, (k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0))=esk4_0|v4_pre_topc(esk3_0,esk1_0)|~r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=esk3_0|r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)),esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.12/0.38  cnf(c_0_53, plain, (v5_tops_1(X1,X2)|X1!=k2_pre_topc(X2,k1_tops_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_54, negated_conjecture, (k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0))=esk4_0|k2_pre_topc(esk1_0,esk3_0)=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_45])).
% 0.12/0.38  cnf(c_0_55, negated_conjecture, (v5_tops_1(esk3_0,esk1_0)|~v5_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_56, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=esk3_0|v5_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_29]), c_0_30])])).
% 0.12/0.38  cnf(c_0_57, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=esk3_0|v5_tops_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0))=esk3_0|k2_pre_topc(esk1_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_22, c_0_57])).
% 0.12/0.38  cnf(c_0_59, plain, (v4_tops_1(X2,X1)|~r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)|~r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.38  cnf(c_0_60, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk1_0,esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_15]), c_0_21]), c_0_16])])).
% 0.12/0.38  cnf(c_0_62, negated_conjecture, (k2_pre_topc(esk1_0,esk3_0)=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_58]), c_0_45])).
% 0.12/0.38  cnf(c_0_63, negated_conjecture, (v4_tops_1(esk3_0,esk1_0)|~r1_tarski(esk3_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)))|~r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_15]), c_0_16])])).
% 0.12/0.38  cnf(c_0_64, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_60])).
% 0.12/0.38  cnf(c_0_65, negated_conjecture, (v4_pre_topc(esk4_0,esk2_0)|~v4_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_66, negated_conjecture, (v4_pre_topc(esk3_0,esk1_0)), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (v4_tops_1(esk3_0,esk1_0)|v4_pre_topc(esk4_0,esk2_0)|~r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_32]), c_0_64])])).
% 0.12/0.38  cnf(c_0_68, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_15]), c_0_16])])).
% 0.12/0.38  cnf(c_0_69, negated_conjecture, (v4_pre_topc(esk4_0,esk2_0)|~v4_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.12/0.38  cnf(c_0_70, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)|~v4_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_71, negated_conjecture, (v4_pre_topc(esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_62]), c_0_68])]), c_0_69])).
% 0.12/0.38  cnf(c_0_72, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)|v4_tops_1(esk3_0,esk1_0)|~r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_34]), c_0_64])])).
% 0.12/0.38  cnf(c_0_73, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)|~v4_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_66])])).
% 0.12/0.38  cnf(c_0_74, negated_conjecture, (k2_pre_topc(esk2_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_71])])).
% 0.12/0.38  cnf(c_0_75, negated_conjecture, (v4_tops_1(esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_62]), c_0_68])]), c_0_73])).
% 0.12/0.38  cnf(c_0_76, negated_conjecture, (r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)),esk4_0)), inference(rw,[status(thm)],[c_0_49, c_0_74])).
% 0.12/0.38  cnf(c_0_77, negated_conjecture, (r1_tarski(esk4_0,k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_75])])).
% 0.12/0.38  cnf(c_0_78, negated_conjecture, (k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_76]), c_0_77])])).
% 0.12/0.38  cnf(c_0_79, negated_conjecture, (v5_tops_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_78]), c_0_29]), c_0_30])])).
% 0.12/0.38  cnf(c_0_80, negated_conjecture, (~v4_pre_topc(esk3_0,esk1_0)|~v4_tops_1(esk3_0,esk1_0)|~v5_tops_1(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_81, negated_conjecture, (v5_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_79])])).
% 0.12/0.38  cnf(c_0_82, negated_conjecture, (~v5_tops_1(esk4_0,esk2_0)|~v4_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_66])])).
% 0.12/0.38  cnf(c_0_83, negated_conjecture, (v4_tops_1(esk3_0,esk1_0)|~r1_tarski(esk3_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_62]), c_0_68])])).
% 0.12/0.38  cnf(c_0_84, negated_conjecture, (k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_81])])).
% 0.12/0.38  cnf(c_0_85, negated_conjecture, (~v4_tops_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_79])])).
% 0.12/0.38  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84]), c_0_64])]), c_0_85]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 87
% 0.12/0.38  # Proof object clause steps            : 68
% 0.12/0.38  # Proof object formula steps           : 19
% 0.12/0.38  # Proof object conjectures             : 59
% 0.12/0.38  # Proof object clause conjectures      : 56
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 22
% 0.12/0.38  # Proof object initial formulas used   : 9
% 0.12/0.38  # Proof object generating inferences   : 31
% 0.12/0.38  # Proof object simplifying inferences  : 76
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 9
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 25
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 25
% 0.12/0.38  # Processed clauses                    : 148
% 0.12/0.38  # ...of these trivial                  : 3
% 0.12/0.38  # ...subsumed                          : 7
% 0.12/0.38  # ...remaining for further processing  : 138
% 0.12/0.38  # Other redundant clauses eliminated   : 2
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 2
% 0.12/0.38  # Backward-rewritten                   : 61
% 0.12/0.38  # Generated clauses                    : 152
% 0.12/0.38  # ...of the previous two non-trivial   : 157
% 0.12/0.38  # Contextual simplify-reflections      : 4
% 0.12/0.38  # Paramodulations                      : 150
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 2
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 49
% 0.12/0.38  #    Positive orientable unit clauses  : 26
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 1
% 0.12/0.38  #    Non-unit-clauses                  : 22
% 0.12/0.38  # Current number of unprocessed clauses: 53
% 0.12/0.38  # ...number of literals in the above   : 112
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 87
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 553
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 371
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.12/0.38  # Unit Clause-clause subsumption calls : 77
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 20
% 0.12/0.38  # BW rewrite match successes           : 9
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 5201
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.036 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.040 s
% 0.12/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
