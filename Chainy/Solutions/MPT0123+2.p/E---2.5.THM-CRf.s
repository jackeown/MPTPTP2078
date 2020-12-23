%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0123+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:37 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   31 (  46 expanded)
%              Number of clauses        :   16 (  21 expanded)
%              Number of leaves         :    7 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  50 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t116_xboole_1,conjecture,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] : k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t116_xboole_1])).

fof(c_0_8,negated_conjecture,(
    k3_xboole_0(esk14_0,k3_xboole_0(esk15_0,esk16_0)) != k3_xboole_0(k3_xboole_0(esk14_0,esk15_0),k3_xboole_0(esk14_0,esk16_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X183,X184,X185] : k3_xboole_0(k3_xboole_0(X183,X184),X185) = k3_xboole_0(X183,k3_xboole_0(X184,X185)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_10,plain,(
    ! [X11,X12] : k3_xboole_0(X11,X12) = k3_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_11,plain,(
    ! [X222,X223] :
      ( ~ r1_tarski(X222,X223)
      | k3_xboole_0(X222,X223) = X222 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_12,plain,(
    ! [X13,X14] : k5_xboole_0(X13,X14) = k5_xboole_0(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_13,plain,(
    ! [X407,X408,X409] : k5_xboole_0(k5_xboole_0(X407,X408),X409) = k5_xboole_0(X407,k5_xboole_0(X408,X409)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_14,negated_conjecture,
    ( k3_xboole_0(esk14_0,k3_xboole_0(esk15_0,esk16_0)) != k3_xboole_0(k3_xboole_0(esk14_0,esk15_0),k3_xboole_0(esk14_0,esk16_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k3_xboole_0(esk14_0,k3_xboole_0(esk15_0,k3_xboole_0(esk14_0,esk16_0))) != k3_xboole_0(esk14_0,k3_xboole_0(esk15_0,esk16_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    c_0_16).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    c_0_18).

cnf(c_0_24,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    c_0_15).

cnf(c_0_25,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    c_0_19).

fof(c_0_26,plain,(
    ! [X186,X187] : r1_tarski(k3_xboole_0(X186,X187),X186) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk15_0,k3_xboole_0(esk14_0,esk16_0)),esk14_0) ),
    inference(ar,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22,c_0_23,c_0_24,c_0_25])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_29,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_16]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
