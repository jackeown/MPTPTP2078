%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0058+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:33 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   26 (  35 expanded)
%              Number of clauses        :   13 (  16 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  35 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(assume_negation,[status(cth)],[t51_xboole_1])).

fof(c_0_7,negated_conjecture,(
    k2_xboole_0(k3_xboole_0(esk16_0,esk17_0),k4_xboole_0(esk16_0,esk17_0)) != esk16_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X219,X220] : k4_xboole_0(X219,k4_xboole_0(X219,X220)) = k3_xboole_0(X219,X220) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_9,negated_conjecture,
    ( k2_xboole_0(k3_xboole_0(esk16_0,esk17_0),k4_xboole_0(esk16_0,esk17_0)) != esk16_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_12,plain,(
    ! [X146,X147] : k2_xboole_0(X146,k3_xboole_0(X146,X147)) = X146 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_13,plain,(
    ! [X217,X218] : k4_xboole_0(X217,k3_xboole_0(X217,X218)) = k4_xboole_0(X217,X218) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_14,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0)),k4_xboole_0(esk16_0,esk17_0)) != esk16_0 ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X195,X196] : k2_xboole_0(X195,k4_xboole_0(X196,X195)) = k2_xboole_0(X195,X196) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk16_0,esk17_0),k4_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0))) != esk16_0 ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_17,c_0_10])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(esk16_0,k4_xboole_0(esk16_0,esk17_0)) != esk16_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_15])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
