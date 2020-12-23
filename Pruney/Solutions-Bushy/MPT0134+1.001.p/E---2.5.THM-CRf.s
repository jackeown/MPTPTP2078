%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0134+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:05 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(assume_negation,[status(cth)],[t50_enumset1])).

fof(c_0_7,plain,(
    ! [X8,X9,X10,X11,X12] : k3_enumset1(X8,X9,X10,X11,X12) = k2_xboole_0(k1_enumset1(X8,X9,X10),k2_tarski(X11,X12)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

fof(c_0_8,plain,(
    ! [X13,X14] : k2_tarski(X13,X14) = k2_xboole_0(k1_tarski(X13),k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_9,negated_conjecture,(
    k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k1_tarski(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_10,plain,(
    ! [X15,X16,X17,X18] : k2_enumset1(X15,X16,X17,X18) = k2_xboole_0(k1_enumset1(X15,X16,X17),k1_tarski(X18)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_11,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_14,plain,(
    ! [X19,X20,X21] : k2_xboole_0(k2_xboole_0(X19,X20),X21) = k2_xboole_0(X19,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_15,negated_conjecture,
    ( k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k2_xboole_0(k1_tarski(esk4_0),k1_tarski(esk5_0))) != k2_xboole_0(k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_tarski(esk4_0)),k1_tarski(esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    c_0_18).

cnf(c_0_22,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    c_0_19).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(ar,[status(thm)],[c_0_20,c_0_21,c_0_22]),
    [proof]).

%------------------------------------------------------------------------------
