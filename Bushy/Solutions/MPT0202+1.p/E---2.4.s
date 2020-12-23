%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : enumset1__t128_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:57 EDT 2019

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t128_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_tarski(X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t128_enumset1.p',t128_enumset1)).

fof(l142_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t128_enumset1.p',l142_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t128_enumset1.p',l53_enumset1)).

fof(t57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t128_enumset1.p',t57_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t128_enumset1.p',commutativity_k2_tarski)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t128_enumset1.p',commutativity_k2_xboole_0)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t128_enumset1.p',t4_xboole_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_tarski(X1,X2),k5_enumset1(X3,X4,X5,X6,X7,X8,X9)) ),
    inference(assume_negation,[status(cth)],[t128_enumset1])).

fof(c_0_8,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31,X32] : k7_enumset1(X24,X25,X26,X27,X28,X29,X30,X31,X32) = k2_xboole_0(k2_enumset1(X24,X25,X26,X27),k3_enumset1(X28,X29,X30,X31,X32)) ),
    inference(variable_rename,[status(thm)],[l142_enumset1])).

fof(c_0_9,plain,(
    ! [X33,X34,X35,X36] : k2_enumset1(X33,X34,X35,X36) = k2_xboole_0(k2_tarski(X33,X34),k2_tarski(X35,X36)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_10,negated_conjecture,(
    k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k5_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46] : k5_enumset1(X40,X41,X42,X43,X44,X45,X46) = k2_xboole_0(k2_tarski(X40,X41),k3_enumset1(X42,X43,X44,X45,X46)) ),
    inference(variable_rename,[status(thm)],[t57_enumset1])).

cnf(c_0_12,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X19,X20] : k2_tarski(X19,X20) = k2_tarski(X20,X19) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_15,plain,(
    ! [X21,X22] : k2_xboole_0(X21,X22) = k2_xboole_0(X22,X21) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_16,plain,(
    ! [X37,X38,X39] : k2_xboole_0(k2_xboole_0(X37,X38),X39) = k2_xboole_0(X37,k2_xboole_0(X38,X39)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_17,negated_conjecture,
    ( k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k5_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)),k3_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k2_xboole_0(k2_tarski(esk3_0,esk4_0),k3_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    c_0_20).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    c_0_21).

cnf(c_0_26,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    c_0_22).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(ar,[status(thm)],[c_0_23,c_0_24,c_0_25,c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
