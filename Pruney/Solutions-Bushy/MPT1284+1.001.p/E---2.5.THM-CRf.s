%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1284+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:02 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   87 (2517 expanded)
%              Number of clauses        :   68 ( 930 expanded)
%              Number of leaves         :    9 ( 594 expanded)
%              Depth                    :   23
%              Number of atoms          :  263 (20581 expanded)
%              Number of equality atoms :   37 ( 605 expanded)
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

fof(d6_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_tops_1(X2,X1)
          <=> ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
              & r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

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
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | m1_subset_1(k1_tops_1(X11,X12),k1_zfmisc_1(u1_struct_0(X11))) ) ),
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
    ! [X9,X10] :
      ( ( ~ v5_tops_1(X10,X9)
        | X10 = k2_pre_topc(X9,k1_tops_1(X9,X10))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( X10 != k2_pre_topc(X9,k1_tops_1(X9,X10))
        | v5_tops_1(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tops_1])])])])).

fof(c_0_13,plain,(
    ! [X13,X14] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | v4_pre_topc(k2_pre_topc(X13,X14),X13) ) ),
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
    ! [X20,X21] :
      ( ( ~ v4_pre_topc(X21,X20)
        | k2_pre_topc(X20,X21) = X21
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) )
      & ( ~ v2_pre_topc(X20)
        | k2_pre_topc(X20,X21) != X21
        | v4_pre_topc(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) ) ) ),
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

cnf(c_0_24,negated_conjecture,
    ( v5_tops_1(esk3_0,esk1_0)
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_25,plain,(
    ! [X17,X18,X19] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
      | ~ r1_tarski(X18,X19)
      | r1_tarski(k2_pre_topc(X17,X18),k2_pre_topc(X17,X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).

fof(c_0_26,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | r1_tarski(k1_tops_1(X15,X16),X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_27,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_16])])).

cnf(c_0_31,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)) = esk3_0
    | v4_pre_topc(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_32,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(k1_tops_1(X7,k2_pre_topc(X7,X8)),X8)
        | ~ v4_tops_1(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( r1_tarski(X8,k2_pre_topc(X7,k1_tops_1(X7,X8)))
        | ~ v4_tops_1(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( ~ r1_tarski(k1_tops_1(X7,k2_pre_topc(X7,X8)),X8)
        | ~ r1_tarski(X8,k2_pre_topc(X7,k1_tops_1(X7,X8)))
        | v4_tops_1(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_tops_1])])])])).

cnf(c_0_33,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)) = esk3_0
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_24])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk4_0) = esk4_0
    | ~ v4_pre_topc(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_37,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk2_0)
    | v4_pre_topc(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k2_pre_topc(X2,k1_tops_1(X2,X1)))
    | ~ v4_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | ~ v4_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_15]),c_0_16])])).

cnf(c_0_40,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk1_0)
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,X1),k2_pre_topc(esk2_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_29])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_28]),c_0_29])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_28]),c_0_29])])).

cnf(c_0_44,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk4_0) = esk4_0
    | v4_pre_topc(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_45,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk4_0,k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)))
    | ~ v4_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_28]),c_0_29])])).

cnf(c_0_47,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | v4_tops_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)),k2_pre_topc(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_49,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk4_0) = esk4_0
    | k2_pre_topc(esk1_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_44])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | r1_tarski(esk4_0,k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( v5_tops_1(X1,X2)
    | X1 != k2_pre_topc(X2,k1_tops_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_54,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)) = esk4_0
    | k2_pre_topc(esk1_0,esk3_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( v5_tops_1(esk3_0,esk1_0)
    | ~ v5_tops_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_56,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | v5_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_28]),c_0_29])])).

cnf(c_0_57,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0
    | v5_tops_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_58,plain,
    ( v4_tops_1(X2,X1)
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X2)),X2)
    | ~ r1_tarski(X2,k2_pre_topc(X1,k1_tops_1(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)) = esk3_0
    | k2_pre_topc(esk1_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( v4_tops_1(esk3_0,esk1_0)
    | ~ r1_tarski(esk3_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_15]),c_0_16])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk1_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_15]),c_0_21]),c_0_16])])).

cnf(c_0_64,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk3_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_60]),c_0_39])).

cnf(c_0_65,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk2_0)
    | v4_tops_1(esk3_0,esk1_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_31]),c_0_62])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_15]),c_0_16])])).

cnf(c_0_67,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | ~ v4_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_68,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk2_0)
    | ~ v4_pre_topc(esk3_0,esk1_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_69,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk2_0)
    | v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_64]),c_0_66])])).

cnf(c_0_71,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_40])).

cnf(c_0_72,negated_conjecture,
    ( v4_pre_topc(esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])]),c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,k2_pre_topc(esk1_0,esk3_0)),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_33]),c_0_62])]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( k2_pre_topc(esk2_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_72])])).

cnf(c_0_75,negated_conjecture,
    ( v4_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_64]),c_0_66])])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)),esk4_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk4_0,k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_75])])).

cnf(c_0_78,negated_conjecture,
    ( k2_pre_topc(esk2_0,k1_tops_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_76]),c_0_77])])).

cnf(c_0_79,negated_conjecture,
    ( v5_tops_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_78]),c_0_28]),c_0_29])])).

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
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_69])])).

cnf(c_0_83,negated_conjecture,
    ( v4_tops_1(esk3_0,esk1_0)
    | ~ r1_tarski(esk3_0,k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_64]),c_0_66])])).

cnf(c_0_84,negated_conjecture,
    ( k2_pre_topc(esk1_0,k1_tops_1(esk1_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_81])])).

cnf(c_0_85,negated_conjecture,
    ( ~ v4_tops_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_79])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84]),c_0_62])]),c_0_85]),
    [proof]).

%------------------------------------------------------------------------------
