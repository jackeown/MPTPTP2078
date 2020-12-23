%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0206+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:13 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t132_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_enumset1)).

fof(l142_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(t54_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_enumset1(X7,X8,X9)) ),
    inference(assume_negation,[status(cth)],[t132_enumset1])).

fof(c_0_6,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17,X18] : k7_enumset1(X10,X11,X12,X13,X14,X15,X16,X17,X18) = k2_xboole_0(k2_enumset1(X10,X11,X12,X13),k3_enumset1(X14,X15,X16,X17,X18)) ),
    inference(variable_rename,[status(thm)],[l142_enumset1])).

fof(c_0_7,plain,(
    ! [X19,X20,X21,X22,X23] : k3_enumset1(X19,X20,X21,X22,X23) = k2_xboole_0(k2_tarski(X19,X20),k1_enumset1(X21,X22,X23)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

fof(c_0_8,negated_conjecture,(
    k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X27,X28,X29,X30,X31,X32] : k4_enumset1(X27,X28,X29,X30,X31,X32) = k2_xboole_0(k2_enumset1(X27,X28,X29,X30),k2_tarski(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t54_enumset1])).

cnf(c_0_10,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_xboole_0(k2_tarski(X5,X6),k1_enumset1(X7,X8,X9))) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_15,plain,(
    ! [X24,X25,X26] : k2_xboole_0(k2_xboole_0(X24,X25),X26) = k2_xboole_0(X24,k2_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_xboole_0(k2_tarski(esk5_0,esk6_0),k1_enumset1(esk7_0,esk8_0,esk9_0))) != k2_xboole_0(k2_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k2_tarski(esk5_0,esk6_0)),k1_enumset1(esk7_0,esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_17,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17])]),
    [proof]).

%------------------------------------------------------------------------------
