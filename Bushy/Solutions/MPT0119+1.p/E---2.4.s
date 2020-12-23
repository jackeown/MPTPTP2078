%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t112_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:21 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   21 (  59 expanded)
%              Number of clauses        :   10 (  24 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  59 expanded)
%              Number of equality atoms :   20 (  58 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t112_xboole_1,conjecture,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t112_xboole_1.p',t112_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t112_xboole_1.p',d6_xboole_0)).

fof(t111_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t112_xboole_1.p',t111_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t112_xboole_1.p',commutativity_k3_xboole_0)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t112_xboole_1.p',t23_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(assume_negation,[status(cth)],[t112_xboole_1])).

fof(c_0_6,negated_conjecture,(
    k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk3_0,esk2_0)) != k3_xboole_0(k5_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X13,X14] : k5_xboole_0(X13,X14) = k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X14,X13)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_8,plain,(
    ! [X17,X18,X19] : k4_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X19,X18)) = k3_xboole_0(k4_xboole_0(X17,X19),X18) ),
    inference(variable_rename,[status(thm)],[t111_xboole_1])).

fof(c_0_9,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_10,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk3_0,esk2_0)) != k3_xboole_0(k5_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk3_0,esk2_0)),k4_xboole_0(k3_xboole_0(esk3_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))) != k3_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk3_0,esk1_0)),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_11])).

cnf(c_0_15,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_16,plain,(
    ! [X20,X21,X22] : k3_xboole_0(X20,k2_xboole_0(X21,X22)) = k2_xboole_0(k3_xboole_0(X20,X21),k3_xboole_0(X20,X22)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_17,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k3_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk1_0))) != k3_xboole_0(esk2_0,k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk3_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_13]),c_0_13]),c_0_13]),c_0_13]),c_0_13])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) = k3_xboole_0(k4_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_13]),c_0_18]),c_0_13]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
