%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:08 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 887 expanded)
%              Number of clauses        :   61 ( 405 expanded)
%              Number of leaves         :    9 ( 219 expanded)
%              Depth                    :   12
%              Number of atoms          :  200 (3018 expanded)
%              Number of equality atoms :   32 ( 397 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ~ ( X2 != k1_struct_0(X1)
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ~ r2_hidden(X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_pre_topc)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ~ ( X2 != k1_struct_0(X1)
                & ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ~ r2_hidden(X3,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_pre_topc])).

fof(c_0_10,negated_conjecture,(
    ! [X28] :
      ( l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & esk4_0 != k1_struct_0(esk3_0)
      & ( ~ m1_subset_1(X28,u1_struct_0(esk3_0))
        | ~ r2_hidden(X28,esk4_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

fof(c_0_11,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X21,X22)
      | m1_subset_1(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_12,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

fof(c_0_14,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_2(X5,X6),X5)
        | r1_xboole_0(X5,X6) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | r1_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_15,negated_conjecture,
    ( ~ r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

fof(c_0_17,plain,(
    ! [X11,X12] :
      ( v1_xboole_0(X12)
      | ~ r1_tarski(X12,X11)
      | ~ r1_xboole_0(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_18,negated_conjecture,
    ( r1_xboole_0(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_2(X1,u1_struct_0(esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

fof(c_0_20,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | r1_tarski(X15,X13)
        | X14 != k1_zfmisc_1(X13) )
      & ( ~ r1_tarski(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k1_zfmisc_1(X13) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | ~ r1_tarski(esk2_2(X17,X18),X17)
        | X18 = k1_zfmisc_1(X17) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | r1_tarski(esk2_2(X17,X18),X17)
        | X18 = k1_zfmisc_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_21,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X23,X24)
      | v1_xboole_0(X24)
      | r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_22,plain,(
    ! [X20] : ~ v1_xboole_0(k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

fof(c_0_29,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_30,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk3_0),X1)
    | ~ r2_hidden(esk1_2(u1_struct_0(esk3_0),X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_19])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_16])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_34]),
    [final]).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_tarski(esk2_2(X1,X2),X1)
    | X2 = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r1_tarski(u1_struct_0(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_37])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_43,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r2_hidden(esk2_2(X2,X1),k1_zfmisc_1(X2))
    | r2_hidden(esk2_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_15,c_0_40]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | ~ r1_tarski(u1_struct_0(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_41])).

cnf(c_0_46,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r2_hidden(esk2_2(X2,X1),X1)
    | ~ r2_hidden(esk2_2(X2,X1),X3)
    | ~ r1_xboole_0(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_zfmisc_1(X1)
    | r2_hidden(esk2_2(X1,u1_struct_0(esk3_0)),k1_zfmisc_1(X1))
    | ~ r2_hidden(esk2_2(X1,u1_struct_0(esk3_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43]),
    [final]).

cnf(c_0_48,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r2_hidden(esk2_2(X2,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(esk2_2(X2,X1),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43]),
    [final]).

cnf(c_0_49,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r1_tarski(esk2_2(X2,X1),X2)
    | ~ r2_hidden(esk2_2(X2,X1),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_39]),
    [final]).

cnf(c_0_50,plain,
    ( X2 = k1_zfmisc_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r1_tarski(esk2_2(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk4_0,X1)
    | ~ r1_xboole_0(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_32])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | ~ r1_tarski(u1_struct_0(esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_40]),
    [final]).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_19]),
    [final]).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_16]),
    [final]).

fof(c_0_55,plain,(
    ! [X25] :
      ( ~ l1_pre_topc(X25)
      | l1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_56,negated_conjecture,
    ( esk4_0 != k1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_57,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r2_hidden(esk2_2(X2,X1),X1)
    | ~ r1_xboole_0(k1_zfmisc_1(X2),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_43]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_zfmisc_1(X1)
    | ~ r2_hidden(esk2_2(X1,u1_struct_0(esk3_0)),k1_xboole_0)
    | ~ r2_hidden(esk2_2(X1,u1_struct_0(esk3_0)),X2)
    | ~ r1_xboole_0(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_47]),
    [final]).

cnf(c_0_59,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r2_hidden(esk2_2(X2,X1),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_43]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_zfmisc_1(X1)
    | r1_tarski(esk2_2(X1,u1_struct_0(esk3_0)),X1)
    | ~ r2_hidden(esk2_2(X1,u1_struct_0(esk3_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_39]),
    [final]).

cnf(c_0_61,plain,
    ( X1 = k1_zfmisc_1(X2)
    | r1_tarski(esk2_2(X2,X1),X2)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_39]),
    [final]).

cnf(c_0_62,plain,
    ( X1 = k1_zfmisc_1(X2)
    | ~ r2_hidden(esk2_2(X2,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(esk2_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_31]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,X1)
    | ~ r1_xboole_0(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_40]),
    [final]).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_2(X1,u1_struct_0(esk3_0)),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_40]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk3_0),X1)
    | ~ r2_hidden(esk1_2(u1_struct_0(esk3_0),X1),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_40]),
    [final]).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | ~ r2_hidden(u1_struct_0(esk3_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_31]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r1_tarski(u1_struct_0(esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_40]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_12,c_0_40]),
    [final]).

cnf(c_0_69,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_19]),
    [final]).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_16]),
    [final]).

cnf(c_0_71,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_16]),
    [final]).

cnf(c_0_72,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55]),
    [final]).

cnf(c_0_73,negated_conjecture,
    ( k1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_56,c_0_40]),
    [final]).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_40]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_40]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_40]),
    [final]).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_40]),
    [final]).

cnf(c_0_78,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_40]),
    [final]).

cnf(c_0_79,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:08:15 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.12/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  
% 0.12/0.38  # No proof found!
% 0.12/0.38  # SZS status CounterSatisfiable
% 0.12/0.38  # SZS output start Saturation
% 0.12/0.38  fof(t41_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((X2!=k1_struct_0(X1)&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r2_hidden(X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_pre_topc)).
% 0.12/0.38  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.12/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.12/0.38  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.12/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.12/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.12/0.38  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.12/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.12/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((X2!=k1_struct_0(X1)&![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~(r2_hidden(X3,X2)))))))), inference(assume_negation,[status(cth)],[t41_pre_topc])).
% 0.12/0.38  fof(c_0_10, negated_conjecture, ![X28]:(l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(esk4_0!=k1_struct_0(esk3_0)&(~m1_subset_1(X28,u1_struct_0(esk3_0))|~r2_hidden(X28,esk4_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).
% 0.12/0.38  fof(c_0_11, plain, ![X21, X22]:(~r2_hidden(X21,X22)|m1_subset_1(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.12/0.38  cnf(c_0_12, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_13, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.12/0.38  fof(c_0_14, plain, ![X5, X6, X8, X9, X10]:(((r2_hidden(esk1_2(X5,X6),X5)|r1_xboole_0(X5,X6))&(r2_hidden(esk1_2(X5,X6),X6)|r1_xboole_0(X5,X6)))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|~r1_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (~r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.38  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.12/0.38  fof(c_0_17, plain, ![X11, X12]:(v1_xboole_0(X12)|(~r1_tarski(X12,X11)|~r1_xboole_0(X12,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (r1_xboole_0(X1,u1_struct_0(esk3_0))|~r2_hidden(esk1_2(X1,u1_struct_0(esk3_0)),esk4_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.38  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.12/0.38  fof(c_0_20, plain, ![X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X15,X14)|r1_tarski(X15,X13)|X14!=k1_zfmisc_1(X13))&(~r1_tarski(X16,X13)|r2_hidden(X16,X14)|X14!=k1_zfmisc_1(X13)))&((~r2_hidden(esk2_2(X17,X18),X18)|~r1_tarski(esk2_2(X17,X18),X17)|X18=k1_zfmisc_1(X17))&(r2_hidden(esk2_2(X17,X18),X18)|r1_tarski(esk2_2(X17,X18),X17)|X18=k1_zfmisc_1(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.12/0.38  fof(c_0_21, plain, ![X23, X24]:(~m1_subset_1(X23,X24)|(v1_xboole_0(X24)|r2_hidden(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.12/0.38  fof(c_0_22, plain, ![X20]:~v1_xboole_0(k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.12/0.38  cnf(c_0_23, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (r1_xboole_0(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.38  cnf(c_0_25, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_26, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_28, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.12/0.38  fof(c_0_29, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (v1_xboole_0(esk4_0)|~r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.38  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_25]), ['final']).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (r1_xboole_0(u1_struct_0(esk3_0),X1)|~r2_hidden(esk1_2(u1_struct_0(esk3_0),X1),esk4_0)), inference(spm,[status(thm)],[c_0_15, c_0_19])).
% 0.12/0.38  cnf(c_0_34, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_35, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (r1_xboole_0(u1_struct_0(esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_16])).
% 0.12/0.38  cnf(c_0_38, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_34]), ['final']).
% 0.12/0.38  cnf(c_0_39, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_tarski(esk2_2(X1,X2),X1)|X2=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36]), ['final']).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|~r1_tarski(u1_struct_0(esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_23, c_0_37])).
% 0.12/0.38  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.12/0.38  cnf(c_0_43, plain, (X1=k1_zfmisc_1(X2)|r2_hidden(esk2_2(X2,X1),k1_zfmisc_1(X2))|r2_hidden(esk2_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_38, c_0_39]), ['final']).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (~r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_15, c_0_40]), ['final']).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|~r1_tarski(u1_struct_0(esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_41])).
% 0.12/0.38  cnf(c_0_46, plain, (X1=k1_zfmisc_1(X2)|r2_hidden(esk2_2(X2,X1),X1)|~r2_hidden(esk2_2(X2,X1),X3)|~r1_xboole_0(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_42, c_0_43]), ['final']).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (u1_struct_0(esk3_0)=k1_zfmisc_1(X1)|r2_hidden(esk2_2(X1,u1_struct_0(esk3_0)),k1_zfmisc_1(X1))|~r2_hidden(esk2_2(X1,u1_struct_0(esk3_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_43]), ['final']).
% 0.12/0.38  cnf(c_0_48, plain, (X1=k1_zfmisc_1(X2)|r2_hidden(esk2_2(X2,X1),k1_zfmisc_1(X2))|~r2_hidden(esk2_2(X2,X1),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43]), ['final']).
% 0.12/0.38  cnf(c_0_49, plain, (X1=k1_zfmisc_1(X2)|r1_tarski(esk2_2(X2,X1),X2)|~r2_hidden(esk2_2(X2,X1),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_42, c_0_39]), ['final']).
% 0.12/0.38  cnf(c_0_50, plain, (X2=k1_zfmisc_1(X1)|~r2_hidden(esk2_2(X1,X2),X2)|~r1_tarski(esk2_2(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_20]), ['final']).
% 0.12/0.38  cnf(c_0_51, negated_conjecture, (~r2_hidden(esk4_0,X1)|~r1_xboole_0(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_42, c_0_32])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|~r1_tarski(u1_struct_0(esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_45, c_0_40]), ['final']).
% 0.12/0.38  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_42, c_0_19]), ['final']).
% 0.12/0.38  cnf(c_0_54, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_42, c_0_16]), ['final']).
% 0.12/0.38  fof(c_0_55, plain, ![X25]:(~l1_pre_topc(X25)|l1_struct_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.12/0.38  cnf(c_0_56, negated_conjecture, (esk4_0!=k1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_57, plain, (X1=k1_zfmisc_1(X2)|r2_hidden(esk2_2(X2,X1),X1)|~r1_xboole_0(k1_zfmisc_1(X2),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_46, c_0_43]), ['final']).
% 0.12/0.38  cnf(c_0_58, negated_conjecture, (u1_struct_0(esk3_0)=k1_zfmisc_1(X1)|~r2_hidden(esk2_2(X1,u1_struct_0(esk3_0)),k1_xboole_0)|~r2_hidden(esk2_2(X1,u1_struct_0(esk3_0)),X2)|~r1_xboole_0(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_47]), ['final']).
% 0.12/0.38  cnf(c_0_59, plain, (X1=k1_zfmisc_1(X2)|r2_hidden(esk2_2(X2,X1),k1_zfmisc_1(X2))|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_48, c_0_43]), ['final']).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (u1_struct_0(esk3_0)=k1_zfmisc_1(X1)|r1_tarski(esk2_2(X1,u1_struct_0(esk3_0)),X1)|~r2_hidden(esk2_2(X1,u1_struct_0(esk3_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_39]), ['final']).
% 0.12/0.38  cnf(c_0_61, plain, (X1=k1_zfmisc_1(X2)|r1_tarski(esk2_2(X2,X1),X2)|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_49, c_0_39]), ['final']).
% 0.12/0.38  cnf(c_0_62, plain, (X1=k1_zfmisc_1(X2)|~r2_hidden(esk2_2(X2,X1),k1_zfmisc_1(X2))|~r2_hidden(esk2_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_50, c_0_31]), ['final']).
% 0.12/0.38  cnf(c_0_63, negated_conjecture, (~r2_hidden(k1_xboole_0,X1)|~r1_xboole_0(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_51, c_0_40]), ['final']).
% 0.12/0.38  cnf(c_0_64, negated_conjecture, (r1_xboole_0(X1,u1_struct_0(esk3_0))|~r2_hidden(esk1_2(X1,u1_struct_0(esk3_0)),k1_xboole_0)), inference(rw,[status(thm)],[c_0_18, c_0_40]), ['final']).
% 0.12/0.38  cnf(c_0_65, negated_conjecture, (r1_xboole_0(u1_struct_0(esk3_0),X1)|~r2_hidden(esk1_2(u1_struct_0(esk3_0),X1),k1_xboole_0)), inference(rw,[status(thm)],[c_0_33, c_0_40]), ['final']).
% 0.12/0.38  cnf(c_0_66, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|~r2_hidden(u1_struct_0(esk3_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_52, c_0_31]), ['final']).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|~r1_tarski(u1_struct_0(esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_41, c_0_40]), ['final']).
% 0.12/0.38  cnf(c_0_68, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_12, c_0_40]), ['final']).
% 0.12/0.38  cnf(c_0_69, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_53, c_0_19]), ['final']).
% 0.12/0.38  cnf(c_0_70, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_53, c_0_16]), ['final']).
% 0.12/0.38  cnf(c_0_71, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_54, c_0_16]), ['final']).
% 0.12/0.38  cnf(c_0_72, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55]), ['final']).
% 0.12/0.38  cnf(c_0_73, negated_conjecture, (k1_struct_0(esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_56, c_0_40]), ['final']).
% 0.12/0.38  cnf(c_0_74, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_27, c_0_40]), ['final']).
% 0.12/0.38  cnf(c_0_75, negated_conjecture, (r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_32, c_0_40]), ['final']).
% 0.12/0.38  cnf(c_0_76, negated_conjecture, (r1_xboole_0(k1_xboole_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_24, c_0_40]), ['final']).
% 0.12/0.38  cnf(c_0_77, negated_conjecture, (r1_xboole_0(u1_struct_0(esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_37, c_0_40]), ['final']).
% 0.12/0.38  cnf(c_0_78, negated_conjecture, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_36, c_0_40]), ['final']).
% 0.12/0.38  cnf(c_0_79, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.12/0.38  # SZS output end Saturation
% 0.12/0.38  # Proof object total steps             : 80
% 0.12/0.38  # Proof object clause steps            : 61
% 0.12/0.38  # Proof object formula steps           : 19
% 0.12/0.38  # Proof object conjectures             : 36
% 0.12/0.38  # Proof object clause conjectures      : 33
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 17
% 0.12/0.38  # Proof object initial formulas used   : 9
% 0.12/0.38  # Proof object generating inferences   : 29
% 0.12/0.38  # Proof object simplifying inferences  : 18
% 0.12/0.38  # Parsed axioms                        : 9
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 17
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 17
% 0.12/0.38  # Processed clauses                    : 80
% 0.12/0.38  # ...of these trivial                  : 1
% 0.12/0.38  # ...subsumed                          : 18
% 0.12/0.38  # ...remaining for further processing  : 61
% 0.12/0.38  # Other redundant clauses eliminated   : 2
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 14
% 0.12/0.38  # Generated clauses                    : 67
% 0.12/0.38  # ...of the previous two non-trivial   : 66
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 63
% 0.12/0.38  # Factorizations                       : 2
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
% 0.12/0.38  # Current number of processed clauses  : 45
% 0.12/0.38  #    Positive orientable unit clauses  : 7
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 2
% 0.12/0.38  #    Non-unit-clauses                  : 36
% 0.12/0.38  # Current number of unprocessed clauses: 0
% 0.12/0.38  # ...number of literals in the above   : 0
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 14
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 397
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 314
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 18
% 0.12/0.38  # Unit Clause-clause subsumption calls : 37
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 2
% 0.12/0.38  # BW rewrite match successes           : 2
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 2116
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.030 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.034 s
% 0.12/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
