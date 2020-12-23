%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0060+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:34 EST 2020

% Result     : Theorem 19.61s
% Output     : CNFRefutation 19.61s
% Verified   : 
% Statistics : Number of formulae       :   30 (  57 expanded)
%              Number of clauses        :   15 (  24 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  57 expanded)
%              Number of equality atoms :   29 (  56 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',commutativity_k2_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t53_xboole_1])).

fof(c_0_8,plain,(
    ! [X221,X222,X223] : k3_xboole_0(X221,k4_xboole_0(X222,X223)) = k4_xboole_0(k3_xboole_0(X221,X222),X223) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_9,plain,(
    ! [X219,X220] : k4_xboole_0(X219,k4_xboole_0(X219,X220)) = k3_xboole_0(X219,X220) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_10,negated_conjecture,(
    k4_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0)) != k3_xboole_0(k4_xboole_0(esk16_0,esk17_0),k4_xboole_0(esk16_0,esk18_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_11,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X201,X202,X203] : k4_xboole_0(k4_xboole_0(X201,X202),X203) = k4_xboole_0(X201,k2_xboole_0(X202,X203)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_14,negated_conjecture,
    ( k4_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0)) != k3_xboole_0(k4_xboole_0(esk16_0,esk17_0),k4_xboole_0(esk16_0,esk18_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X215,X216] : k4_xboole_0(X215,k2_xboole_0(X215,X216)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_18,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_19,plain,(
    ! [X136] : k2_xboole_0(X136,k1_xboole_0) = X136 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_20,negated_conjecture,
    ( k4_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0)) != k4_xboole_0(k4_xboole_0(esk16_0,esk17_0),k4_xboole_0(k4_xboole_0(esk16_0,esk17_0),k4_xboole_0(esk16_0,esk18_0))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k4_xboole_0(esk16_0,k2_xboole_0(esk17_0,k4_xboole_0(esk16_0,k2_xboole_0(esk17_0,k4_xboole_0(esk16_0,esk18_0))))) != k4_xboole_0(esk16_0,k2_xboole_0(esk17_0,esk18_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_16]),c_0_16])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X4))))) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_21]),c_0_16]),c_0_16]),c_0_16])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
