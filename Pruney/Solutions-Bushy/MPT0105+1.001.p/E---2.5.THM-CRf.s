%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0105+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:03 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   23 (  35 expanded)
%              Number of clauses        :   10 (  14 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  35 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t98_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(c_0_6,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_7,plain,(
    ! [X11,X12,X13] : k4_xboole_0(k4_xboole_0(X11,X12),X13) = k4_xboole_0(X11,k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_8,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t98_xboole_1])).

cnf(c_0_10,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X8] : k2_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_13,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_16,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X3,k4_xboole_0(X1,X2))) = k5_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_10]),c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_14]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])]),
    [proof]).

%------------------------------------------------------------------------------
