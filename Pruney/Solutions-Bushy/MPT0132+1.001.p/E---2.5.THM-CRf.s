%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0132+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:05 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   22 (  48 expanded)
%              Number of clauses        :   11 (  21 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  48 expanded)
%              Number of equality atoms :   21 (  47 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(assume_negation,[status(cth)],[t48_enumset1])).

fof(c_0_6,plain,(
    ! [X8,X9,X10,X11,X12] : k3_enumset1(X8,X9,X10,X11,X12) = k2_xboole_0(k1_enumset1(X8,X9,X10),k2_tarski(X11,X12)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

fof(c_0_7,plain,(
    ! [X13,X14,X15] : k1_enumset1(X13,X14,X15) = k2_xboole_0(k1_tarski(X13),k2_tarski(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_8,negated_conjecture,(
    k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_enumset1(esk3_0,esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X16,X17,X18] : k1_enumset1(X16,X17,X18) = k2_xboole_0(k2_tarski(X16,X17),k1_tarski(X18)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

cnf(c_0_12,negated_conjecture,
    ( k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_enumset1(esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)),k2_tarski(X4,X5)) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_14,plain,(
    ! [X19,X20,X21] : k2_xboole_0(k2_xboole_0(X19,X20),X21) = k2_xboole_0(X19,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k2_tarski(esk2_0,esk3_0)),k2_tarski(esk4_0,esk5_0)) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k2_xboole_0(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_10]),c_0_13])).

cnf(c_0_17,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k2_tarski(esk2_0,esk3_0),k2_tarski(esk4_0,esk5_0))) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k2_xboole_0(k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),X4)) = k2_xboole_0(k2_tarski(X1,X2),k2_xboole_0(k1_tarski(X3),X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_18])]),
    [proof]).

%------------------------------------------------------------------------------
