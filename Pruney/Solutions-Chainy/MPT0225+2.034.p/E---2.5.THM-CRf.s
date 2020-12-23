%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:07 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 (1094 expanded)
%              Number of clauses        :   48 ( 505 expanded)
%              Number of leaves         :    6 ( 291 expanded)
%              Depth                    :   18
%              Number of atoms          :  159 (4151 expanded)
%              Number of equality atoms :   88 (1888 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t20_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(c_0_6,plain,(
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

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
      <=> X1 != X2 ) ),
    inference(assume_negation,[status(cth)],[t20_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X14
        | X15 != k1_tarski(X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k1_tarski(X14) )
      & ( ~ r2_hidden(esk2_2(X18,X19),X19)
        | esk2_2(X18,X19) != X18
        | X19 = k1_tarski(X18) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | esk2_2(X18,X19) = X18
        | X19 = k1_tarski(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_11,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_16,negated_conjecture,
    ( ( k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) != k1_tarski(esk3_0)
      | esk3_0 = esk4_0 )
    & ( k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) = k1_tarski(esk3_0)
      | esk3_0 != esk4_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_17,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) = k1_tarski(esk3_0)
    | esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X3)
    | ~ r2_hidden(esk1_3(X3,X3,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(X3,X3)
    | r2_hidden(esk1_3(X3,X3,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) = k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)
    | esk4_0 != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_18]),c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k4_xboole_0(X1,X1)
    | esk4_0 != esk3_0
    | ~ r2_hidden(esk1_3(X1,X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_29])).

cnf(c_0_34,plain,
    ( esk1_3(X1,X1,k2_enumset1(X2,X2,X2,X2)) = X2
    | k2_enumset1(X2,X2,X2,X2) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_22])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).

cnf(c_0_37,negated_conjecture,
    ( k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) = k4_xboole_0(X1,X1)
    | ~ r2_hidden(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_30])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_31]),c_0_35])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_41,plain,
    ( esk2_2(X1,X2) = X1
    | X2 = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( esk2_2(esk4_0,X1) = esk4_0
    | r2_hidden(esk2_2(esk4_0,X1),X1)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_43,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_44,negated_conjecture,
    ( esk2_2(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = esk4_0
    | r2_hidden(esk2_2(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_36])).

cnf(c_0_45,plain,
    ( X2 = k2_enumset1(X1,X1,X1,X1)
    | esk2_2(X1,X2) != X1
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( esk2_2(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = esk4_0
    | esk2_2(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( esk3_0 = esk4_0
    | k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0)) != k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))
    | esk2_2(X2,k2_enumset1(X1,X1,X1,X1)) != X2
    | ~ r2_hidden(esk2_2(X2,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( esk2_2(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)) = esk3_0
    | esk4_0 != esk3_0 ),
    inference(ef,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( esk4_0 = esk3_0
    | k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_18]),c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_51,negated_conjecture,
    ( esk4_0 != esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_36])]),c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( esk2_2(X1,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) = X1
    | r2_hidden(esk2_2(X1,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))
    | k2_enumset1(X1,X1,X1,X1) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_41]),c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( esk2_2(esk3_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) = esk3_0
    | r2_hidden(esk2_2(esk3_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_55,negated_conjecture,
    ( esk4_0 = esk3_0
    | esk2_2(X1,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) != X1
    | k2_enumset1(X1,X1,X1,X1) != k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ r2_hidden(esk2_2(X1,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( esk2_2(esk3_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_53]),c_0_30])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_51])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:00:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.19/0.50  # and selection function SelectComplexExceptRRHorn.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.027 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.50  fof(t20_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.19/0.50  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.50  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.50  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.50  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.50  fof(c_0_6, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.50  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2)), inference(assume_negation,[status(cth)],[t20_zfmisc_1])).
% 0.19/0.50  fof(c_0_8, plain, ![X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X16,X15)|X16=X14|X15!=k1_tarski(X14))&(X17!=X14|r2_hidden(X17,X15)|X15!=k1_tarski(X14)))&((~r2_hidden(esk2_2(X18,X19),X19)|esk2_2(X18,X19)!=X18|X19=k1_tarski(X18))&(r2_hidden(esk2_2(X18,X19),X19)|esk2_2(X18,X19)=X18|X19=k1_tarski(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.50  fof(c_0_9, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.50  fof(c_0_10, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.50  fof(c_0_11, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.50  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_13, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_14, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_15, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  fof(c_0_16, negated_conjecture, ((k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))!=k1_tarski(esk3_0)|esk3_0=esk4_0)&(k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))=k1_tarski(esk3_0)|esk3_0!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.50  cnf(c_0_17, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.50  cnf(c_0_18, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.50  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.50  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.50  cnf(c_0_21, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_12])).
% 0.19/0.50  cnf(c_0_22, plain, (X1=k4_xboole_0(X2,X2)|r2_hidden(esk1_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.50  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.50  cnf(c_0_24, negated_conjecture, (k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))=k1_tarski(esk3_0)|esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_25, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])).
% 0.19/0.50  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(X3,X3)|~r2_hidden(esk1_3(X3,X3,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.50  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k4_xboole_0(X3,X3)|r2_hidden(esk1_3(X3,X3,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_23, c_0_22])).
% 0.19/0.50  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.50  cnf(c_0_29, negated_conjecture, (k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)|esk4_0!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_18]), c_0_18]), c_0_18]), c_0_19]), c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_20])).
% 0.19/0.50  cnf(c_0_30, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.50  cnf(c_0_31, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.50  cnf(c_0_32, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_18]), c_0_19]), c_0_20])).
% 0.19/0.50  cnf(c_0_33, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k4_xboole_0(X1,X1)|esk4_0!=esk3_0|~r2_hidden(esk1_3(X1,X1,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_29])).
% 0.19/0.50  cnf(c_0_34, plain, (esk1_3(X1,X1,k2_enumset1(X2,X2,X2,X2))=X2|k2_enumset1(X2,X2,X2,X2)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_30, c_0_22])).
% 0.19/0.50  cnf(c_0_35, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_21, c_0_31])).
% 0.19/0.50  cnf(c_0_36, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).
% 0.19/0.50  cnf(c_0_37, negated_conjecture, (k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)=k4_xboole_0(X1,X1)|~r2_hidden(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_30])).
% 0.19/0.50  cnf(c_0_38, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_31]), c_0_35])).
% 0.19/0.50  cnf(c_0_39, plain, (r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.50  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.19/0.50  cnf(c_0_41, plain, (esk2_2(X1,X2)=X1|X2=k2_enumset1(X1,X1,X1,X1)|r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_18]), c_0_19]), c_0_20])).
% 0.19/0.50  cnf(c_0_42, negated_conjecture, (esk2_2(esk4_0,X1)=esk4_0|r2_hidden(esk2_2(esk4_0,X1),X1)|~r2_hidden(esk3_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.50  cnf(c_0_43, plain, (X2=k1_tarski(X1)|~r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.50  cnf(c_0_44, negated_conjecture, (esk2_2(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=esk4_0|r2_hidden(esk2_2(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)),k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_42, c_0_36])).
% 0.19/0.50  cnf(c_0_45, plain, (X2=k2_enumset1(X1,X1,X1,X1)|esk2_2(X1,X2)!=X1|~r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_18]), c_0_19]), c_0_20])).
% 0.19/0.50  cnf(c_0_46, negated_conjecture, (esk2_2(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=esk4_0|esk2_2(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_30, c_0_44])).
% 0.19/0.50  cnf(c_0_47, negated_conjecture, (esk3_0=esk4_0|k4_xboole_0(k1_tarski(esk3_0),k1_tarski(esk4_0))!=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_48, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))|esk2_2(X2,k2_enumset1(X1,X1,X1,X1))!=X2|~r2_hidden(esk2_2(X2,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_36, c_0_45])).
% 0.19/0.50  cnf(c_0_49, negated_conjecture, (esk2_2(esk4_0,k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0))=esk3_0|esk4_0!=esk3_0), inference(ef,[status(thm)],[c_0_46])).
% 0.19/0.50  cnf(c_0_50, negated_conjecture, (esk4_0=esk3_0|k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_18]), c_0_18]), c_0_18]), c_0_19]), c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_20])).
% 0.19/0.50  cnf(c_0_51, negated_conjecture, (esk4_0!=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_36])]), c_0_40])).
% 0.19/0.50  cnf(c_0_52, negated_conjecture, (esk2_2(X1,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))=X1|r2_hidden(esk2_2(X1,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))|k2_enumset1(X1,X1,X1,X1)!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_41]), c_0_51])).
% 0.19/0.50  cnf(c_0_53, negated_conjecture, (esk2_2(esk3_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))=esk3_0|r2_hidden(esk2_2(esk3_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))), inference(er,[status(thm)],[c_0_52])).
% 0.19/0.50  cnf(c_0_54, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.50  cnf(c_0_55, negated_conjecture, (esk4_0=esk3_0|esk2_2(X1,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))!=X1|k2_enumset1(X1,X1,X1,X1)!=k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0)|~r2_hidden(esk2_2(X1,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))),k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))), inference(spm,[status(thm)],[c_0_50, c_0_45])).
% 0.19/0.50  cnf(c_0_56, negated_conjecture, (esk2_2(esk3_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_53]), c_0_30])).
% 0.19/0.50  cnf(c_0_57, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_54])).
% 0.19/0.50  cnf(c_0_58, negated_conjecture, (~r2_hidden(esk3_0,k4_xboole_0(k2_enumset1(esk3_0,esk3_0,esk3_0,esk3_0),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_51])).
% 0.19/0.50  cnf(c_0_59, plain, (r2_hidden(X1,k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X2))|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_57, c_0_36])).
% 0.19/0.50  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_40]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 61
% 0.19/0.50  # Proof object clause steps            : 48
% 0.19/0.50  # Proof object formula steps           : 13
% 0.19/0.50  # Proof object conjectures             : 21
% 0.19/0.50  # Proof object clause conjectures      : 18
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 14
% 0.19/0.50  # Proof object initial formulas used   : 6
% 0.19/0.50  # Proof object generating inferences   : 23
% 0.19/0.50  # Proof object simplifying inferences  : 46
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 6
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 15
% 0.19/0.50  # Removed in clause preprocessing      : 3
% 0.19/0.50  # Initial clauses in saturation        : 12
% 0.19/0.50  # Processed clauses                    : 532
% 0.19/0.50  # ...of these trivial                  : 29
% 0.19/0.50  # ...subsumed                          : 312
% 0.19/0.50  # ...remaining for further processing  : 191
% 0.19/0.50  # Other redundant clauses eliminated   : 401
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 19
% 0.19/0.50  # Backward-rewritten                   : 3
% 0.19/0.50  # Generated clauses                    : 5939
% 0.19/0.50  # ...of the previous two non-trivial   : 4557
% 0.19/0.50  # Contextual simplify-reflections      : 5
% 0.19/0.50  # Paramodulations                      : 5524
% 0.19/0.50  # Factorizations                       : 14
% 0.19/0.50  # Equation resolutions                 : 402
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 152
% 0.19/0.50  #    Positive orientable unit clauses  : 4
% 0.19/0.50  #    Positive unorientable unit clauses: 1
% 0.19/0.50  #    Negative unit clauses             : 4
% 0.19/0.50  #    Non-unit-clauses                  : 143
% 0.19/0.50  # Current number of unprocessed clauses: 3979
% 0.19/0.50  # ...number of literals in the above   : 25078
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 37
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 1914
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 1101
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 123
% 0.19/0.50  # Unit Clause-clause subsumption calls : 139
% 0.19/0.50  # Rewrite failures with RHS unbound    : 58
% 0.19/0.50  # BW rewrite match attempts            : 40
% 0.19/0.50  # BW rewrite match successes           : 8
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 131736
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.155 s
% 0.19/0.50  # System time              : 0.006 s
% 0.19/0.50  # Total time               : 0.161 s
% 0.19/0.50  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
