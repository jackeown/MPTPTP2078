%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0139+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:06 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   20 (  35 expanded)
%              Number of clauses        :    9 (  14 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  35 expanded)
%              Number of equality atoms :   19 (  34 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(l62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(assume_negation,[status(cth)],[t55_enumset1])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X11] : k3_enumset1(X7,X8,X9,X10,X11) = k2_xboole_0(k1_enumset1(X7,X8,X9),k2_tarski(X10,X11)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

fof(c_0_7,plain,(
    ! [X18,X19,X20] : k1_enumset1(X18,X19,X20) = k2_xboole_0(k2_tarski(X18,X19),k1_tarski(X20)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_8,plain,(
    ! [X12,X13,X14,X15,X16,X17] : k4_enumset1(X12,X13,X14,X15,X16,X17) = k2_xboole_0(k1_enumset1(X12,X13,X14),k1_enumset1(X15,X16,X17)) ),
    inference(variable_rename,[status(thm)],[l62_enumset1])).

fof(c_0_9,negated_conjecture,(
    k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_10,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)),k2_tarski(X4,X5)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)),k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_11]),c_0_11])).

fof(c_0_16,plain,(
    ! [X21,X22,X23] : k2_xboole_0(k2_xboole_0(X21,X22),X23) = k2_xboole_0(X21,k2_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_17,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0)),k2_xboole_0(k2_tarski(esk4_0,esk5_0),k1_tarski(esk6_0))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0)),k2_tarski(esk4_0,esk5_0)),k1_tarski(esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18]),c_0_18]),c_0_18])]),
    [proof]).

%------------------------------------------------------------------------------
