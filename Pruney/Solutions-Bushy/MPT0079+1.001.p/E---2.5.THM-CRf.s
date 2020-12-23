%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0079+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:00 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   39 (  99 expanded)
%              Number of clauses        :   22 (  40 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   56 ( 166 expanded)
%              Number of equality atoms :   34 (  97 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t72_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X4,X2) )
     => X3 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_8,plain,(
    ! [X17,X18] : r1_tarski(X17,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_9,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
          & r1_xboole_0(X3,X1)
          & r1_xboole_0(X4,X2) )
       => X3 = X2 ) ),
    inference(assume_negation,[status(cth)],[t72_xboole_1])).

fof(c_0_11,plain,(
    ! [X11] : k2_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0)
    & r1_xboole_0(esk3_0,esk1_0)
    & r1_xboole_0(esk4_0,esk2_0)
    & esk3_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( ( ~ r1_xboole_0(X9,X10)
        | k3_xboole_0(X9,X10) = k1_xboole_0 )
      & ( k3_xboole_0(X9,X10) != k1_xboole_0
        | r1_xboole_0(X9,X10) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X12,X13,X14] : k3_xboole_0(X12,k2_xboole_0(X13,X14)) = k2_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X12,X14)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_17])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(k3_xboole_0(X1,esk1_0),k3_xboole_0(X1,esk2_0)) = k2_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_27]),c_0_26]),c_0_28]),c_0_29]),c_0_17]),c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk1_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_30])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_12]),c_0_26]),c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( esk3_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_31]),c_0_36]),c_0_37]),
    [proof]).

%------------------------------------------------------------------------------
