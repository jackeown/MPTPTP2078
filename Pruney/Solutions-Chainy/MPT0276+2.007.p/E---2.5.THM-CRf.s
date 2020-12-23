%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:04 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   98 (4693 expanded)
%              Number of clauses        :   79 (2191 expanded)
%              Number of leaves         :    9 (1206 expanded)
%              Depth                    :   20
%              Number of atoms          :  233 (12573 expanded)
%              Number of equality atoms :  119 (7432 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t74_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k4_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X2)
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k4_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X2)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t74_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X20,X21,X22] :
      ( ~ r1_tarski(k4_xboole_0(X20,X21),X22)
      | r1_tarski(X20,k2_xboole_0(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

fof(c_0_11,plain,(
    ! [X16,X17] : k4_xboole_0(X16,X17) = k5_xboole_0(X16,k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,plain,(
    ! [X18,X19] : r1_tarski(k4_xboole_0(X18,X19),X18) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_13,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29,X30] :
      ( ( ~ r2_hidden(X26,X25)
        | X26 = X23
        | X26 = X24
        | X25 != k2_tarski(X23,X24) )
      & ( X27 != X23
        | r2_hidden(X27,X25)
        | X25 != k2_tarski(X23,X24) )
      & ( X27 != X24
        | r2_hidden(X27,X25)
        | X25 != k2_tarski(X23,X24) )
      & ( esk2_3(X28,X29,X30) != X28
        | ~ r2_hidden(esk2_3(X28,X29,X30),X30)
        | X30 = k2_tarski(X28,X29) )
      & ( esk2_3(X28,X29,X30) != X29
        | ~ r2_hidden(esk2_3(X28,X29,X30),X30)
        | X30 = k2_tarski(X28,X29) )
      & ( r2_hidden(esk2_3(X28,X29,X30),X30)
        | esk2_3(X28,X29,X30) = X28
        | esk2_3(X28,X29,X30) = X29
        | X30 = k2_tarski(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_14,plain,(
    ! [X33,X34] : k1_enumset1(X33,X33,X34) = k2_tarski(X33,X34) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0
    & k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0)
    & k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk4_0)
    & k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k2_tarski(esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_16,plain,(
    ! [X32] : k2_tarski(X32,X32) = k1_tarski(X32) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_18,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_30,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)) != k1_enumset1(esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_23]),c_0_23]),c_0_20])).

cnf(c_0_32,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k2_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_20])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk3_0,esk3_0,esk4_0))
    | r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk4_0,esk4_0,esk4_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_33,c_0_23])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X4,X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)) != k1_enumset1(esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_23]),c_0_23]),c_0_20])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_38,c_0_20])).

cnf(c_0_48,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_39,c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0)) = esk4_0
    | r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0)),k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_32])])).

cnf(c_0_53,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_20])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_46])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk3_0,esk3_0,esk4_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])]),c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0)) = esk4_0
    | esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_52])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_54])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_62,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_63,negated_conjecture,
    ( esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0)) = esk4_0
    | esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0)) = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0)) = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_57]),c_0_51])]),c_0_44])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_23]),c_0_20])).

cnf(c_0_67,plain,
    ( X3 = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_62,c_0_20])).

cnf(c_0_68,negated_conjecture,
    ( esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0)) = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_63]),c_0_50]),c_0_51])]),c_0_31])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | r2_hidden(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_64]),c_0_50])]),c_0_44])).

cnf(c_0_70,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_32]),c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_xboole_0),k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_32])]),c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_31]),c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,X1,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_xboole_0) = esk4_0
    | esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_xboole_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_77,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | esk2_3(X1,X2,X3) = X1
    | esk2_3(X1,X2,X3) = X2
    | X3 = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk1_3(k1_xboole_0,X1,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( esk1_3(k1_enumset1(esk3_0,esk3_0,esk3_0),esk5_0,k1_xboole_0) = esk3_0
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk5_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)) != k1_enumset1(esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_25]),c_0_23]),c_0_23]),c_0_20])).

cnf(c_0_82,plain,
    ( X3 = k1_enumset1(X1,X1,X2)
    | esk2_3(X1,X2,X3) = X2
    | esk2_3(X1,X2,X3) = X1
    | r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[c_0_77,c_0_23])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_hidden(esk1_3(k1_xboole_0,X1,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_73])).

cnf(c_0_84,negated_conjecture,
    ( esk1_3(k1_xboole_0,X1,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))) = esk4_0
    | esk1_3(k1_xboole_0,X1,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_79]),c_0_65]),c_0_69]),c_0_80])).

cnf(c_0_86,plain,
    ( X3 = k2_tarski(X1,X2)
    | esk2_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_87,negated_conjecture,
    ( esk2_3(X1,X2,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))) = X1
    | esk2_3(X1,X2,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))) = X2
    | r2_hidden(esk2_3(X1,X2,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))
    | k1_enumset1(X1,X1,X2) != k1_enumset1(esk3_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( esk1_3(k1_xboole_0,X1,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])])).

cnf(c_0_89,plain,
    ( X3 = k1_enumset1(X1,X1,X2)
    | esk2_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[c_0_86,c_0_23])).

cnf(c_0_90,negated_conjecture,
    ( esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))) = esk3_0
    | r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))) ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))) ),
    inference(rw,[status(thm)],[c_0_73,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])]),c_0_81])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),k1_enumset1(esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_92])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))) = esk4_0
    | esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_85])])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_96]),c_0_91])]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:19:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.78/0.98  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.78/0.98  # and selection function SelectNegativeLiterals.
% 0.78/0.98  #
% 0.78/0.98  # Preprocessing time       : 0.028 s
% 0.78/0.98  # Presaturation interreduction done
% 0.78/0.98  
% 0.78/0.98  # Proof found!
% 0.78/0.98  # SZS status Theorem
% 0.78/0.98  # SZS output start CNFRefutation
% 0.78/0.98  fof(t74_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X1))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X2))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_zfmisc_1)).
% 0.78/0.98  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.78/0.98  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.78/0.98  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.78/0.98  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.78/0.98  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.78/0.98  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.78/0.98  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.78/0.98  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.78/0.98  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:~((((k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X1))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X2))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t74_zfmisc_1])).
% 0.78/0.98  fof(c_0_10, plain, ![X20, X21, X22]:(~r1_tarski(k4_xboole_0(X20,X21),X22)|r1_tarski(X20,k2_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.78/0.98  fof(c_0_11, plain, ![X16, X17]:k4_xboole_0(X16,X17)=k5_xboole_0(X16,k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.78/0.98  fof(c_0_12, plain, ![X18, X19]:r1_tarski(k4_xboole_0(X18,X19),X18), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.78/0.98  fof(c_0_13, plain, ![X23, X24, X25, X26, X27, X28, X29, X30]:(((~r2_hidden(X26,X25)|(X26=X23|X26=X24)|X25!=k2_tarski(X23,X24))&((X27!=X23|r2_hidden(X27,X25)|X25!=k2_tarski(X23,X24))&(X27!=X24|r2_hidden(X27,X25)|X25!=k2_tarski(X23,X24))))&(((esk2_3(X28,X29,X30)!=X28|~r2_hidden(esk2_3(X28,X29,X30),X30)|X30=k2_tarski(X28,X29))&(esk2_3(X28,X29,X30)!=X29|~r2_hidden(esk2_3(X28,X29,X30),X30)|X30=k2_tarski(X28,X29)))&(r2_hidden(esk2_3(X28,X29,X30),X30)|(esk2_3(X28,X29,X30)=X28|esk2_3(X28,X29,X30)=X29)|X30=k2_tarski(X28,X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.78/0.98  fof(c_0_14, plain, ![X33, X34]:k1_enumset1(X33,X33,X34)=k2_tarski(X33,X34), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.78/0.98  fof(c_0_15, negated_conjecture, (((k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0&k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0))&k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk4_0))&k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k2_tarski(esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.78/0.98  fof(c_0_16, plain, ![X32]:k2_tarski(X32,X32)=k1_tarski(X32), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.78/0.98  fof(c_0_17, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.78/0.98  fof(c_0_18, plain, ![X14, X15]:((k4_xboole_0(X14,X15)!=k1_xboole_0|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|k4_xboole_0(X14,X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.78/0.98  cnf(c_0_19, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.78/0.98  cnf(c_0_20, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.78/0.98  cnf(c_0_21, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.78/0.98  cnf(c_0_22, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.78/0.98  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.78/0.98  cnf(c_0_24, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.78/0.98  cnf(c_0_25, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.78/0.98  cnf(c_0_26, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.98  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.78/0.98  cnf(c_0_28, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.78/0.98  cnf(c_0_29, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.78/0.98  cnf(c_0_30, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.78/0.98  cnf(c_0_31, negated_conjecture, (k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))!=k1_enumset1(esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_23]), c_0_23]), c_0_20])).
% 0.78/0.98  cnf(c_0_32, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_26, c_0_20])).
% 0.78/0.98  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.78/0.98  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.78/0.98  cnf(c_0_35, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k2_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.78/0.98  cnf(c_0_36, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_20])).
% 0.78/0.98  cnf(c_0_37, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.78/0.98  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.98  cnf(c_0_39, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.98  cnf(c_0_40, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X3,X3,X2))), inference(er,[status(thm)],[c_0_30])).
% 0.78/0.98  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk3_0,esk3_0,esk4_0))|r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk4_0,esk4_0,esk4_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32])])).
% 0.78/0.98  cnf(c_0_42, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_33, c_0_23])).
% 0.78/0.98  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X4,X2)), inference(rw,[status(thm)],[c_0_34, c_0_23])).
% 0.78/0.98  cnf(c_0_44, negated_conjecture, (k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))!=k1_enumset1(esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_23]), c_0_23]), c_0_20])).
% 0.78/0.98  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.98  cnf(c_0_46, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.78/0.98  cnf(c_0_47, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_38, c_0_20])).
% 0.78/0.98  cnf(c_0_48, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_39, c_0_20])).
% 0.78/0.98  cnf(c_0_49, negated_conjecture, (esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0))=esk4_0|r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.78/0.98  cnf(c_0_50, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).
% 0.78/0.98  cnf(c_0_51, plain, (r2_hidden(X1,k1_enumset1(X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).
% 0.78/0.98  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0)),k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_32])])).
% 0.78/0.98  cnf(c_0_53, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_20])).
% 0.78/0.98  cnf(c_0_54, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_46])).
% 0.78/0.98  cnf(c_0_55, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_47])).
% 0.78/0.98  cnf(c_0_56, negated_conjecture, (r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0)),k1_enumset1(esk3_0,esk3_0,esk4_0))|r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])]), c_0_31])).
% 0.78/0.98  cnf(c_0_57, negated_conjecture, (esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0))=esk4_0|esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_40, c_0_52])).
% 0.78/0.98  cnf(c_0_58, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_53])).
% 0.78/0.98  cnf(c_0_59, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_54])).
% 0.78/0.98  cnf(c_0_60, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_46])).
% 0.78/0.98  cnf(c_0_61, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.78/0.98  cnf(c_0_62, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.98  cnf(c_0_63, negated_conjecture, (esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0))=esk4_0|esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0))=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_40, c_0_56])).
% 0.78/0.98  cnf(c_0_64, negated_conjecture, (esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk3_0,esk3_0,esk4_0))=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_57]), c_0_51])]), c_0_44])).
% 0.78/0.98  cnf(c_0_65, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.78/0.98  cnf(c_0_66, negated_conjecture, (k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_23]), c_0_20])).
% 0.78/0.98  cnf(c_0_67, plain, (X3=k5_xboole_0(X1,k3_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_62, c_0_20])).
% 0.78/0.98  cnf(c_0_68, negated_conjecture, (esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_enumset1(esk4_0,esk4_0,esk4_0))=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_63]), c_0_50]), c_0_51])]), c_0_31])).
% 0.78/0.98  cnf(c_0_69, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|r2_hidden(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_64]), c_0_50])]), c_0_44])).
% 0.78/0.98  cnf(c_0_70, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(k1_xboole_0,X2,X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_32]), c_0_65])).
% 0.78/0.98  cnf(c_0_71, negated_conjecture, (r2_hidden(esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_xboole_0),k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_32])]), c_0_65])).
% 0.78/0.98  cnf(c_0_72, negated_conjecture, (r2_hidden(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))|r2_hidden(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_31]), c_0_69])).
% 0.78/0.98  cnf(c_0_73, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,X1,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))), inference(spm,[status(thm)],[c_0_66, c_0_70])).
% 0.78/0.98  cnf(c_0_74, negated_conjecture, (esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_xboole_0)=esk4_0|esk1_3(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0,k1_xboole_0)=esk3_0), inference(spm,[status(thm)],[c_0_40, c_0_71])).
% 0.78/0.98  cnf(c_0_75, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_40, c_0_72])).
% 0.78/0.98  cnf(c_0_76, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.78/0.98  cnf(c_0_77, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|esk2_3(X1,X2,X3)=X1|esk2_3(X1,X2,X3)=X2|X3=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.78/0.98  cnf(c_0_78, negated_conjecture, (r2_hidden(esk1_3(k1_xboole_0,X1,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_73])).
% 0.78/0.98  cnf(c_0_79, negated_conjecture, (esk1_3(k1_enumset1(esk3_0,esk3_0,esk3_0),esk5_0,k1_xboole_0)=esk3_0|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.78/0.98  cnf(c_0_80, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk3_0),esk5_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_75])).
% 0.78/0.98  cnf(c_0_81, negated_conjecture, (k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))!=k1_enumset1(esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_25]), c_0_23]), c_0_23]), c_0_20])).
% 0.78/0.98  cnf(c_0_82, plain, (X3=k1_enumset1(X1,X1,X2)|esk2_3(X1,X2,X3)=X2|esk2_3(X1,X2,X3)=X1|r2_hidden(esk2_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[c_0_77, c_0_23])).
% 0.78/0.98  cnf(c_0_83, negated_conjecture, (~r2_hidden(esk1_3(k1_xboole_0,X1,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),esk5_0)), inference(spm,[status(thm)],[c_0_58, c_0_73])).
% 0.78/0.98  cnf(c_0_84, negated_conjecture, (esk1_3(k1_xboole_0,X1,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))=esk4_0|esk1_3(k1_xboole_0,X1,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))=esk3_0), inference(spm,[status(thm)],[c_0_40, c_0_78])).
% 0.78/0.98  cnf(c_0_85, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_79]), c_0_65]), c_0_69]), c_0_80])).
% 0.78/0.98  cnf(c_0_86, plain, (X3=k2_tarski(X1,X2)|esk2_3(X1,X2,X3)!=X2|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.78/0.98  cnf(c_0_87, negated_conjecture, (esk2_3(X1,X2,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))=X1|esk2_3(X1,X2,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))=X2|r2_hidden(esk2_3(X1,X2,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))|k1_enumset1(X1,X1,X2)!=k1_enumset1(esk3_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.78/0.98  cnf(c_0_88, negated_conjecture, (esk1_3(k1_xboole_0,X1,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])])).
% 0.78/0.98  cnf(c_0_89, plain, (X3=k1_enumset1(X1,X1,X2)|esk2_3(X1,X2,X3)!=X2|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[c_0_86, c_0_23])).
% 0.78/0.98  cnf(c_0_90, negated_conjecture, (esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))=esk3_0|r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))), inference(er,[status(thm)],[c_0_87])).
% 0.78/0.98  cnf(c_0_91, negated_conjecture, (r2_hidden(esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))), inference(rw,[status(thm)],[c_0_73, c_0_88])).
% 0.78/0.98  cnf(c_0_92, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])]), c_0_81])).
% 0.78/0.98  cnf(c_0_93, negated_conjecture, (r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),k1_enumset1(esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_92])).
% 0.78/0.98  cnf(c_0_94, negated_conjecture, (~r2_hidden(esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0))),esk5_0)), inference(spm,[status(thm)],[c_0_58, c_0_92])).
% 0.78/0.98  cnf(c_0_95, negated_conjecture, (esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))=esk4_0|esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))=esk3_0), inference(spm,[status(thm)],[c_0_40, c_0_93])).
% 0.78/0.98  cnf(c_0_96, negated_conjecture, (esk2_3(esk3_0,esk3_0,k5_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),k3_xboole_0(k1_enumset1(esk3_0,esk3_0,esk4_0),esk5_0)))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_85])])).
% 0.78/0.98  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_96]), c_0_91])]), c_0_81]), ['proof']).
% 0.78/0.98  # SZS output end CNFRefutation
% 0.78/0.98  # Proof object total steps             : 98
% 0.78/0.98  # Proof object clause steps            : 79
% 0.78/0.98  # Proof object formula steps           : 19
% 0.78/0.98  # Proof object conjectures             : 41
% 0.78/0.98  # Proof object clause conjectures      : 38
% 0.78/0.98  # Proof object formula conjectures     : 3
% 0.78/0.98  # Proof object initial clauses used    : 20
% 0.78/0.98  # Proof object initial formulas used   : 9
% 0.78/0.98  # Proof object generating inferences   : 36
% 0.78/0.98  # Proof object simplifying inferences  : 69
% 0.78/0.98  # Training examples: 0 positive, 0 negative
% 0.78/0.98  # Parsed axioms                        : 10
% 0.78/0.98  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.98  # Initial clauses                      : 26
% 0.78/0.98  # Removed in clause preprocessing      : 3
% 0.78/0.98  # Initial clauses in saturation        : 23
% 0.78/0.98  # Processed clauses                    : 1732
% 0.78/0.98  # ...of these trivial                  : 106
% 0.78/0.98  # ...subsumed                          : 915
% 0.78/0.98  # ...remaining for further processing  : 711
% 0.78/0.98  # Other redundant clauses eliminated   : 839
% 0.78/0.98  # Clauses deleted for lack of memory   : 0
% 0.78/0.98  # Backward-subsumed                    : 51
% 0.78/0.98  # Backward-rewritten                   : 71
% 0.78/0.98  # Generated clauses                    : 58277
% 0.78/0.98  # ...of the previous two non-trivial   : 51873
% 0.78/0.98  # Contextual simplify-reflections      : 11
% 0.78/0.98  # Paramodulations                      : 57322
% 0.78/0.98  # Factorizations                       : 95
% 0.78/0.98  # Equation resolutions                 : 842
% 0.78/0.98  # Propositional unsat checks           : 0
% 0.78/0.98  #    Propositional check models        : 0
% 0.78/0.98  #    Propositional check unsatisfiable : 0
% 0.78/0.98  #    Propositional clauses             : 0
% 0.78/0.98  #    Propositional clauses after purity: 0
% 0.78/0.98  #    Propositional unsat core size     : 0
% 0.78/0.98  #    Propositional preprocessing time  : 0.000
% 0.78/0.98  #    Propositional encoding time       : 0.000
% 0.78/0.98  #    Propositional solver time         : 0.000
% 0.78/0.98  #    Success case prop preproc time    : 0.000
% 0.78/0.98  #    Success case prop encoding time   : 0.000
% 0.78/0.98  #    Success case prop solver time     : 0.000
% 0.78/0.98  # Current number of processed clauses  : 540
% 0.78/0.98  #    Positive orientable unit clauses  : 135
% 0.78/0.98  #    Positive unorientable unit clauses: 0
% 0.78/0.98  #    Negative unit clauses             : 6
% 0.78/0.98  #    Non-unit-clauses                  : 399
% 0.78/0.98  # Current number of unprocessed clauses: 49838
% 0.78/0.98  # ...number of literals in the above   : 247496
% 0.78/0.98  # Current number of archived formulas  : 0
% 0.78/0.98  # Current number of archived clauses   : 168
% 0.78/0.98  # Clause-clause subsumption calls (NU) : 25891
% 0.78/0.98  # Rec. Clause-clause subsumption calls : 14090
% 0.78/0.98  # Non-unit clause-clause subsumptions  : 757
% 0.78/0.98  # Unit Clause-clause subsumption calls : 4441
% 0.78/0.98  # Rewrite failures with RHS unbound    : 0
% 0.78/0.98  # BW rewrite match attempts            : 440
% 0.78/0.98  # BW rewrite match successes           : 30
% 0.78/0.98  # Condensation attempts                : 0
% 0.78/0.98  # Condensation successes               : 0
% 0.78/0.98  # Termbank termtop insertions          : 1338546
% 0.78/0.99  
% 0.78/0.99  # -------------------------------------------------
% 0.78/0.99  # User time                : 0.619 s
% 0.78/0.99  # System time              : 0.027 s
% 0.78/0.99  # Total time               : 0.646 s
% 0.78/0.99  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
