%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:00 EST 2020

% Result     : Theorem 1.36s
% Output     : CNFRefutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 286 expanded)
%              Number of clauses        :   45 ( 132 expanded)
%              Number of leaves         :    5 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  197 (1074 expanded)
%              Number of equality atoms :  107 ( 624 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
      <=> ( ~ r2_hidden(X1,X3)
          & ~ r2_hidden(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t72_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k4_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_7,negated_conjecture,
    ( ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k2_tarski(esk3_0,esk4_0)
      | r2_hidden(esk3_0,esk5_0)
      | r2_hidden(esk4_0,esk5_0) )
    & ( ~ r2_hidden(esk3_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k2_tarski(esk3_0,esk4_0) )
    & ( ~ r2_hidden(esk4_0,esk5_0)
      | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k2_tarski(esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

fof(c_0_8,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_9,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_10,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X19,X18)
        | X19 = X15
        | X19 = X16
        | X19 = X17
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X15
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X16
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( X20 != X17
        | r2_hidden(X20,X18)
        | X18 != k1_enumset1(X15,X16,X17) )
      & ( esk2_4(X21,X22,X23,X24) != X21
        | ~ r2_hidden(esk2_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( esk2_4(X21,X22,X23,X24) != X22
        | ~ r2_hidden(esk2_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( esk2_4(X21,X22,X23,X24) != X23
        | ~ r2_hidden(esk2_4(X21,X22,X23,X24),X24)
        | X24 = k1_enumset1(X21,X22,X23) )
      & ( r2_hidden(esk2_4(X21,X22,X23,X24),X24)
        | esk2_4(X21,X22,X23,X24) = X21
        | esk2_4(X21,X22,X23,X24) = X22
        | esk2_4(X21,X22,X23,X24) = X23
        | X24 = k1_enumset1(X21,X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k2_tarski(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X2,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) = k2_tarski(esk3_0,esk4_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_13]),c_0_14]),c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X2,X5) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)
    | ~ r2_hidden(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_13]),c_0_13]),c_0_14]),c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk4_0,esk5_0)
    | k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0) != k2_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X4)
    | esk2_4(X1,X2,X3,X4) = X1
    | esk2_4(X1,X2,X3,X4) = X2
    | esk2_4(X1,X2,X3,X4) = X3
    | X4 = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))
    | ~ r2_hidden(esk3_0,esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X1,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))
    | ~ r2_hidden(esk4_0,esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk4_0,esk5_0)
    | k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_13]),c_0_13]),c_0_14]),c_0_14])).

cnf(c_0_30,plain,
    ( X4 = k2_enumset1(X1,X1,X2,X3)
    | esk2_4(X1,X2,X3,X4) = X3
    | esk2_4(X1,X2,X3,X4) = X2
    | esk2_4(X1,X2,X3,X4) = X1
    | r2_hidden(esk2_4(X1,X2,X3,X4),X4) ),
    inference(rw,[status(thm)],[c_0_24,c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_35,negated_conjecture,
    ( esk2_4(X1,X2,X3,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = X1
    | esk2_4(X1,X2,X3,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = X2
    | esk2_4(X1,X2,X3,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = X3
    | r2_hidden(esk2_4(X1,X2,X3,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))
    | k2_enumset1(X1,X1,X2,X3) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_36,plain,
    ( X4 = k1_enumset1(X1,X2,X3)
    | esk2_4(X1,X2,X3,X4) != X3
    | ~ r2_hidden(esk2_4(X1,X2,X3,X4),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_38,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_14])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = esk4_0
    | esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = esk3_0
    | r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( X4 = k1_enumset1(X1,X2,X3)
    | esk2_4(X1,X2,X3,X4) != X1
    | ~ r2_hidden(esk2_4(X1,X2,X3,X4),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,plain,
    ( X4 = k2_enumset1(X1,X1,X2,X3)
    | esk2_4(X1,X2,X3,X4) != X3
    | ~ r2_hidden(esk2_4(X1,X2,X3,X4),X4) ),
    inference(rw,[status(thm)],[c_0_36,c_0_14])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k2_enumset1(X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = esk3_0
    | esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = esk4_0
    | r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,plain,
    ( X4 = k2_enumset1(X1,X1,X2,X3)
    | esk2_4(X1,X2,X3,X4) != X1
    | ~ r2_hidden(esk2_4(X1,X2,X3,X4),X4) ),
    inference(rw,[status(thm)],[c_0_41,c_0_14])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,X2) = k2_enumset1(X3,X3,X4,X5)
    | r2_hidden(esk2_4(X3,X4,X5,k4_xboole_0(X1,X2)),X2)
    | esk2_4(X3,X4,X5,k4_xboole_0(X1,X2)) != X5
    | ~ r2_hidden(esk2_4(X3,X4,X5,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = esk4_0
    | esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_46,c_0_14])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,X2) = k2_enumset1(X3,X3,X4,X5)
    | r2_hidden(esk2_4(X3,X4,X5,k4_xboole_0(X1,X2)),X2)
    | esk2_4(X3,X4,X5,k4_xboole_0(X1,X2)) != X3
    | ~ r2_hidden(esk2_4(X3,X4,X5,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)) = esk3_0
    | k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_28])]),c_0_32])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).

cnf(c_0_54,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])]),c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_54])]),c_0_31]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.36/1.57  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0Y
% 1.36/1.57  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.36/1.57  #
% 1.36/1.57  # Preprocessing time       : 0.027 s
% 1.36/1.57  # Presaturation interreduction done
% 1.36/1.57  
% 1.36/1.57  # Proof found!
% 1.36/1.57  # SZS status Theorem
% 1.36/1.57  # SZS output start CNFRefutation
% 1.36/1.57  fof(t72_zfmisc_1, conjecture, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 1.36/1.57  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.36/1.57  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.36/1.57  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.36/1.57  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 1.36/1.57  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3))))), inference(assume_negation,[status(cth)],[t72_zfmisc_1])).
% 1.36/1.57  fof(c_0_6, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 1.36/1.57  fof(c_0_7, negated_conjecture, ((k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k2_tarski(esk3_0,esk4_0)|(r2_hidden(esk3_0,esk5_0)|r2_hidden(esk4_0,esk5_0)))&((~r2_hidden(esk3_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k2_tarski(esk3_0,esk4_0))&(~r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k2_tarski(esk3_0,esk4_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).
% 1.36/1.57  fof(c_0_8, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.36/1.57  fof(c_0_9, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.36/1.57  fof(c_0_10, plain, ![X15, X16, X17, X18, X19, X20, X21, X22, X23, X24]:(((~r2_hidden(X19,X18)|(X19=X15|X19=X16|X19=X17)|X18!=k1_enumset1(X15,X16,X17))&(((X20!=X15|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17))&(X20!=X16|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17)))&(X20!=X17|r2_hidden(X20,X18)|X18!=k1_enumset1(X15,X16,X17))))&((((esk2_4(X21,X22,X23,X24)!=X21|~r2_hidden(esk2_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23))&(esk2_4(X21,X22,X23,X24)!=X22|~r2_hidden(esk2_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23)))&(esk2_4(X21,X22,X23,X24)!=X23|~r2_hidden(esk2_4(X21,X22,X23,X24),X24)|X24=k1_enumset1(X21,X22,X23)))&(r2_hidden(esk2_4(X21,X22,X23,X24),X24)|(esk2_4(X21,X22,X23,X24)=X21|esk2_4(X21,X22,X23,X24)=X22|esk2_4(X21,X22,X23,X24)=X23)|X24=k1_enumset1(X21,X22,X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 1.36/1.57  cnf(c_0_11, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.36/1.57  cnf(c_0_12, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k2_tarski(esk3_0,esk4_0)|~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.36/1.57  cnf(c_0_13, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.36/1.57  cnf(c_0_14, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.36/1.57  cnf(c_0_15, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X2,X5)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.36/1.57  cnf(c_0_16, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)=k2_tarski(esk3_0,esk4_0)|~r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.36/1.57  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.36/1.57  cnf(c_0_18, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_11])).
% 1.36/1.57  cnf(c_0_19, negated_conjecture, (k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)=k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)|~r2_hidden(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_13]), c_0_14]), c_0_14])).
% 1.36/1.57  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X2,X5)), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 1.36/1.57  cnf(c_0_21, negated_conjecture, (k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)=k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)|~r2_hidden(esk4_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_13]), c_0_13]), c_0_14]), c_0_14])).
% 1.36/1.57  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_17, c_0_14])).
% 1.36/1.57  cnf(c_0_23, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_tarski(esk3_0,esk4_0),esk5_0)!=k2_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.36/1.57  cnf(c_0_24, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X4)|esk2_4(X1,X2,X3,X4)=X1|esk2_4(X1,X2,X3,X4)=X2|esk2_4(X1,X2,X3,X4)=X3|X4=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.36/1.57  cnf(c_0_25, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))|~r2_hidden(esk3_0,esk5_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.36/1.57  cnf(c_0_26, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X1,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).
% 1.36/1.57  cnf(c_0_27, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))|~r2_hidden(esk4_0,esk5_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_21])).
% 1.36/1.57  cnf(c_0_28, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])])).
% 1.36/1.57  cnf(c_0_29, negated_conjecture, (r2_hidden(esk3_0,esk5_0)|r2_hidden(esk4_0,esk5_0)|k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_13]), c_0_13]), c_0_14]), c_0_14])).
% 1.36/1.57  cnf(c_0_30, plain, (X4=k2_enumset1(X1,X1,X2,X3)|esk2_4(X1,X2,X3,X4)=X3|esk2_4(X1,X2,X3,X4)=X2|esk2_4(X1,X2,X3,X4)=X1|r2_hidden(esk2_4(X1,X2,X3,X4),X4)), inference(rw,[status(thm)],[c_0_24, c_0_14])).
% 1.36/1.57  cnf(c_0_31, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.36/1.57  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.36/1.57  cnf(c_0_33, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.36/1.57  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.36/1.57  cnf(c_0_35, negated_conjecture, (esk2_4(X1,X2,X3,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=X1|esk2_4(X1,X2,X3,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=X2|esk2_4(X1,X2,X3,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=X3|r2_hidden(esk2_4(X1,X2,X3,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))|k2_enumset1(X1,X1,X2,X3)!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])).
% 1.36/1.57  cnf(c_0_36, plain, (X4=k1_enumset1(X1,X2,X3)|esk2_4(X1,X2,X3,X4)!=X3|~r2_hidden(esk2_4(X1,X2,X3,X4),X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.36/1.57  cnf(c_0_37, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.36/1.57  cnf(c_0_38, plain, (X1=X5|X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_14])).
% 1.36/1.57  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_34])).
% 1.36/1.57  cnf(c_0_40, negated_conjecture, (esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=esk4_0|esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=esk3_0|r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))), inference(er,[status(thm)],[c_0_35])).
% 1.36/1.57  cnf(c_0_41, plain, (X4=k1_enumset1(X1,X2,X3)|esk2_4(X1,X2,X3,X4)!=X1|~r2_hidden(esk2_4(X1,X2,X3,X4),X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.36/1.57  cnf(c_0_42, plain, (X4=k2_enumset1(X1,X1,X2,X3)|esk2_4(X1,X2,X3,X4)!=X3|~r2_hidden(esk2_4(X1,X2,X3,X4),X4)), inference(rw,[status(thm)],[c_0_36, c_0_14])).
% 1.36/1.57  cnf(c_0_43, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_37])).
% 1.36/1.57  cnf(c_0_44, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k2_enumset1(X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_38])).
% 1.36/1.57  cnf(c_0_45, negated_conjecture, (esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=esk3_0|esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=esk4_0|r2_hidden(esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.36/1.57  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.36/1.57  cnf(c_0_47, plain, (X4=k2_enumset1(X1,X1,X2,X3)|esk2_4(X1,X2,X3,X4)!=X1|~r2_hidden(esk2_4(X1,X2,X3,X4),X4)), inference(rw,[status(thm)],[c_0_41, c_0_14])).
% 1.36/1.57  cnf(c_0_48, plain, (k4_xboole_0(X1,X2)=k2_enumset1(X3,X3,X4,X5)|r2_hidden(esk2_4(X3,X4,X5,k4_xboole_0(X1,X2)),X2)|esk2_4(X3,X4,X5,k4_xboole_0(X1,X2))!=X5|~r2_hidden(esk2_4(X3,X4,X5,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.36/1.57  cnf(c_0_49, negated_conjecture, (esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=esk4_0|esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=esk3_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 1.36/1.57  cnf(c_0_50, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_46, c_0_14])).
% 1.36/1.57  cnf(c_0_51, plain, (k4_xboole_0(X1,X2)=k2_enumset1(X3,X3,X4,X5)|r2_hidden(esk2_4(X3,X4,X5,k4_xboole_0(X1,X2)),X2)|esk2_4(X3,X4,X5,k4_xboole_0(X1,X2))!=X3|~r2_hidden(esk2_4(X3,X4,X5,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_47, c_0_43])).
% 1.36/1.57  cnf(c_0_52, negated_conjecture, (esk2_4(esk3_0,esk3_0,esk4_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0))=esk3_0|k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)=k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_28])]), c_0_32])).
% 1.36/1.57  cnf(c_0_53, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).
% 1.36/1.57  cnf(c_0_54, negated_conjecture, (k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0),esk5_0)=k2_enumset1(esk3_0,esk3_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])]), c_0_31])).
% 1.36/1.57  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_54])]), c_0_31]), c_0_32]), ['proof']).
% 1.36/1.57  # SZS output end CNFRefutation
% 1.36/1.57  # Proof object total steps             : 56
% 1.36/1.57  # Proof object clause steps            : 45
% 1.36/1.57  # Proof object formula steps           : 11
% 1.36/1.57  # Proof object conjectures             : 20
% 1.36/1.57  # Proof object clause conjectures      : 17
% 1.36/1.57  # Proof object formula conjectures     : 3
% 1.36/1.57  # Proof object initial clauses used    : 15
% 1.36/1.57  # Proof object initial formulas used   : 5
% 1.36/1.57  # Proof object generating inferences   : 12
% 1.36/1.57  # Proof object simplifying inferences  : 41
% 1.36/1.57  # Training examples: 0 positive, 0 negative
% 1.36/1.57  # Parsed axioms                        : 5
% 1.36/1.57  # Removed by relevancy pruning/SinE    : 0
% 1.36/1.57  # Initial clauses                      : 19
% 1.36/1.57  # Removed in clause preprocessing      : 2
% 1.36/1.57  # Initial clauses in saturation        : 17
% 1.36/1.57  # Processed clauses                    : 2777
% 1.36/1.57  # ...of these trivial                  : 30
% 1.36/1.57  # ...subsumed                          : 2486
% 1.36/1.57  # ...remaining for further processing  : 261
% 1.36/1.57  # Other redundant clauses eliminated   : 707
% 1.36/1.57  # Clauses deleted for lack of memory   : 0
% 1.36/1.57  # Backward-subsumed                    : 9
% 1.36/1.57  # Backward-rewritten                   : 10
% 1.36/1.57  # Generated clauses                    : 37073
% 1.36/1.57  # ...of the previous two non-trivial   : 34379
% 1.36/1.57  # Contextual simplify-reflections      : 2
% 1.36/1.57  # Paramodulations                      : 36068
% 1.36/1.57  # Factorizations                       : 300
% 1.36/1.57  # Equation resolutions                 : 708
% 1.36/1.57  # Propositional unsat checks           : 0
% 1.36/1.57  #    Propositional check models        : 0
% 1.36/1.57  #    Propositional check unsatisfiable : 0
% 1.36/1.57  #    Propositional clauses             : 0
% 1.36/1.57  #    Propositional clauses after purity: 0
% 1.36/1.57  #    Propositional unsat core size     : 0
% 1.36/1.57  #    Propositional preprocessing time  : 0.000
% 1.36/1.57  #    Propositional encoding time       : 0.000
% 1.36/1.57  #    Propositional solver time         : 0.000
% 1.36/1.57  #    Success case prop preproc time    : 0.000
% 1.36/1.57  #    Success case prop encoding time   : 0.000
% 1.36/1.57  #    Success case prop solver time     : 0.000
% 1.36/1.57  # Current number of processed clauses  : 218
% 1.36/1.57  #    Positive orientable unit clauses  : 19
% 1.36/1.57  #    Positive unorientable unit clauses: 4
% 1.36/1.57  #    Negative unit clauses             : 11
% 1.36/1.57  #    Non-unit-clauses                  : 184
% 1.36/1.57  # Current number of unprocessed clauses: 31598
% 1.36/1.57  # ...number of literals in the above   : 309282
% 1.36/1.57  # Current number of archived formulas  : 0
% 1.36/1.57  # Current number of archived clauses   : 38
% 1.36/1.57  # Clause-clause subsumption calls (NU) : 12928
% 1.36/1.57  # Rec. Clause-clause subsumption calls : 5600
% 1.36/1.57  # Non-unit clause-clause subsumptions  : 711
% 1.36/1.57  # Unit Clause-clause subsumption calls : 622
% 1.36/1.57  # Rewrite failures with RHS unbound    : 419
% 1.36/1.57  # BW rewrite match attempts            : 326
% 1.36/1.57  # BW rewrite match successes           : 28
% 1.36/1.57  # Condensation attempts                : 0
% 1.36/1.57  # Condensation successes               : 0
% 1.36/1.57  # Termbank termtop insertions          : 1055211
% 1.36/1.57  
% 1.36/1.57  # -------------------------------------------------
% 1.36/1.57  # User time                : 1.197 s
% 1.36/1.57  # System time              : 0.028 s
% 1.36/1.57  # Total time               : 1.225 s
% 1.36/1.57  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
