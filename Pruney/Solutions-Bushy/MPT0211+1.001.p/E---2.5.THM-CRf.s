%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0211+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:13 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   19 (  31 expanded)
%              Number of clauses        :    8 (  12 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  31 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t137_enumset1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(t112_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X1,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X2,X1),k2_tarski(X3,X1)) = k1_enumset1(X1,X2,X3) ),
    inference(assume_negation,[status(cth)],[t137_enumset1])).

fof(c_0_6,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_8,plain,(
    ! [X7,X8,X9,X10] : k2_enumset1(X7,X8,X9,X10) = k2_xboole_0(k2_tarski(X7,X8),k2_tarski(X9,X10)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14] : k2_enumset1(X11,X12,X13,X14) = k2_enumset1(X12,X14,X11,X13) ),
    inference(variable_rename,[status(thm)],[t112_enumset1])).

cnf(c_0_10,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k1_enumset1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X5,X6] : k2_tarski(X5,X6) = k2_tarski(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk3_0,esk1_0)) != k2_xboole_0(k2_tarski(esk1_0,esk1_0),k2_tarski(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_xboole_0(k2_tarski(X2,X4),k2_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_12]),c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16]),c_0_17]),c_0_16])]),
    [proof]).

%------------------------------------------------------------------------------
