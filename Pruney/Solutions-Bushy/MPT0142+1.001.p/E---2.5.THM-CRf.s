%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0142+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   22 (  34 expanded)
%              Number of clauses        :   11 (  15 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  34 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(l68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(assume_negation,[status(cth)],[t58_enumset1])).

fof(c_0_6,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14] : k5_enumset1(X8,X9,X10,X11,X12,X13,X14) = k2_xboole_0(k2_enumset1(X8,X9,X10,X11),k1_enumset1(X12,X13,X14)) ),
    inference(variable_rename,[status(thm)],[l68_enumset1])).

fof(c_0_7,plain,(
    ! [X15,X16,X17,X18] : k2_enumset1(X15,X16,X17,X18) = k2_xboole_0(k1_tarski(X15),k1_enumset1(X16,X17,X18)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_8,negated_conjecture,(
    k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X19,X20,X21,X22] : k2_enumset1(X19,X20,X21,X22) = k2_xboole_0(k1_enumset1(X19,X20,X21),k1_tarski(X22)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_12,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k1_enumset1(X5,X6,X7)) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_14,plain,(
    ! [X23,X24,X25] : k2_xboole_0(k2_xboole_0(X23,X24),X25) = k2_xboole_0(X23,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k1_enumset1(esk2_0,esk3_0,esk4_0)),k1_enumset1(esk5_0,esk6_0,esk7_0)) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k2_xboole_0(k1_tarski(esk4_0),k1_enumset1(esk5_0,esk6_0,esk7_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_10]),c_0_13])).

cnf(c_0_17,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k2_xboole_0(k1_tarski(esk4_0),k1_enumset1(esk5_0,esk6_0,esk7_0))) != k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_enumset1(esk2_0,esk3_0,esk4_0),k1_enumset1(esk5_0,esk6_0,esk7_0))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k1_enumset1(X1,X2,X3),k2_xboole_0(k1_tarski(X4),X5)) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_enumset1(X2,X3,X4),X5)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])]),
    [proof]).

%------------------------------------------------------------------------------
