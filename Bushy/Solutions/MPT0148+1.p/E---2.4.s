%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : enumset1__t64_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:02 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   25 (  31 expanded)
%              Number of clauses        :   12 (  14 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  31 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t64_enumset1.p',t64_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t64_enumset1.p',t47_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t64_enumset1.p',t46_enumset1)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t64_enumset1.p',l75_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t64_enumset1.p',commutativity_k2_xboole_0)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t64_enumset1.p',t4_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(assume_negation,[status(cth)],[t64_enumset1])).

fof(c_0_7,plain,(
    ! [X32,X33,X34,X35,X36] : k3_enumset1(X32,X33,X34,X35,X36) = k2_xboole_0(k1_tarski(X32),k2_enumset1(X33,X34,X35,X36)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_8,plain,(
    ! [X28,X29,X30,X31] : k2_enumset1(X28,X29,X30,X31) = k2_xboole_0(k1_enumset1(X28,X29,X30),k1_tarski(X31)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

fof(c_0_9,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] : k6_enumset1(X20,X21,X22,X23,X24,X25,X26,X27) = k2_xboole_0(k2_enumset1(X20,X21,X22,X23),k2_enumset1(X24,X25,X26,X27)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

fof(c_0_10,negated_conjecture,(
    k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X17,X18] : k2_xboole_0(X17,X18) = k2_xboole_0(X18,X17) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_15,plain,(
    ! [X37,X38,X39] : k2_xboole_0(k2_xboole_0(X37,X38),X39) = k2_xboole_0(X37,k2_xboole_0(X38,X39)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_16,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_enumset1(X2,X3,X4),k1_tarski(X5))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_12]),c_0_12])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_tarski(esk4_0)),k2_xboole_0(k1_enumset1(esk5_0,esk6_0,esk7_0),k1_tarski(esk8_0))) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_enumset1(esk5_0,esk6_0,esk7_0),k1_tarski(esk8_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    c_0_19).

cnf(c_0_23,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    c_0_20).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(ar,[status(thm)],[c_0_21,c_0_22,c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
