%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:50 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 (137313 expanded)
%              Number of clauses        :   80 (64044 expanded)
%              Number of leaves         :    9 (35794 expanded)
%              Depth                    :   34
%              Number of atoms          :  106 (158252 expanded)
%              Number of equality atoms :   84 (123242 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t108_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(c_0_9,plain,(
    ! [X20,X21] : k2_xboole_0(X20,X21) = k5_xboole_0(X20,k4_xboole_0(X21,X20)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_10,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_11,plain,(
    ! [X18,X19] : k3_xboole_0(X18,X19) = k5_xboole_0(k5_xboole_0(X18,X19),k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,X2)
       => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t108_xboole_1])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_18,plain,(
    ! [X15,X16,X17] : k5_xboole_0(k5_xboole_0(X15,X16),X17) = k5_xboole_0(X15,k5_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & ~ r1_tarski(k3_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_21,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_22,plain,(
    ! [X10,X11] : r1_tarski(k3_xboole_0(X10,X11),X10) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_31,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

fof(c_0_32,plain,(
    ! [X12,X13,X14] : k3_xboole_0(X12,k4_xboole_0(X13,X14)) = k4_xboole_0(k3_xboole_0(X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),X1))) = k5_xboole_0(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_30]),c_0_24])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X1,X2)))) = X2 ),
    inference(spm,[status(thm)],[c_0_25,c_0_31])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(spm,[status(thm)],[c_0_25,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk2_0)) = k3_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))) = k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_13]),c_0_13])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X1)) = k3_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_37]),c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1))) = k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_38]),c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))) = k3_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_27])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X1,X3))) = k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_41]),c_0_24])).

cnf(c_0_46,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk2_0))) = k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),X1) = k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_24]),c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))) = k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_47]),c_0_41])).

cnf(c_0_49,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,X2)),X3))) = k5_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_37]),c_0_24])).

cnf(c_0_50,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))) = k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))) = k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))) = k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_46]),c_0_24]),c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_51]),c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))) = k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))) = k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_54]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk1_0)) = k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0))) = k5_xboole_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_57])).

cnf(c_0_59,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,X1)))) = k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_58]),c_0_24]),c_0_24]),c_0_24])).

cnf(c_0_60,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) = k5_xboole_0(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_29]),c_0_27]),c_0_30])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_27]),c_0_40])).

cnf(c_0_62,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk2_0))) = k5_xboole_0(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,esk2_0))) = k3_xboole_0(X1,k5_xboole_0(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk2_0)) = k5_xboole_0(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),X1)) = k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_42]),c_0_34])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk2_0))) = k5_xboole_0(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_64]),c_0_24]),c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))) = k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_42])).

cnf(c_0_69,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)) = k3_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_67]),c_0_38]),c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)) = k5_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_38]),c_0_30])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),X1)) = k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_34]),c_0_42])).

cnf(c_0_72,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0) = k5_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_53])).

cnf(c_0_75,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))) = k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_41])).

cnf(c_0_77,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk1_0) = k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_60])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0)))) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_52]),c_0_37])).

cnf(c_0_79,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk1_0)) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_74,c_0_56])).

cnf(c_0_80,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1))) = k5_xboole_0(esk2_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_75]),c_0_24])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,esk1_0))) = k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_76]),c_0_42]),c_0_41]),c_0_53]),c_0_56]),c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk2_0))) = k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0))) = k5_xboole_0(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk2_0))) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_79,c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk2_0)) = k5_xboole_0(esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85]),c_0_41])).

cnf(c_0_87,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,esk1_0)) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_78,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_86]),c_0_27]),c_0_86]),c_0_77]),c_0_85]),c_0_87])).

cnf(c_0_89,plain,
    ( r1_tarski(k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_61])).

cnf(c_0_90,negated_conjecture,
    ( k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))) = k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,X1))) = k5_xboole_0(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_87]),c_0_24])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1))) = k3_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_29])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,X1),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_90]),c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk3_0,esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_94,c_0_27])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_27])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.20/0.40  # and selection function SelectNewComplexAHP.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.026 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.40  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.40  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.40  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.40  fof(t108_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 0.20/0.40  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.40  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.40  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.40  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.40  fof(c_0_9, plain, ![X20, X21]:k2_xboole_0(X20,X21)=k5_xboole_0(X20,k4_xboole_0(X21,X20)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.40  fof(c_0_10, plain, ![X6, X7]:k4_xboole_0(X6,X7)=k5_xboole_0(X6,k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.40  fof(c_0_11, plain, ![X18, X19]:k3_xboole_0(X18,X19)=k5_xboole_0(k5_xboole_0(X18,X19),k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.20/0.40  cnf(c_0_12, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_13, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  fof(c_0_14, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.40  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t108_xboole_1])).
% 0.20/0.40  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.40  fof(c_0_18, plain, ![X15, X16, X17]:k5_xboole_0(k5_xboole_0(X15,X16),X17)=k5_xboole_0(X15,k5_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.40  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  fof(c_0_20, negated_conjecture, (r1_tarski(esk1_0,esk2_0)&~r1_tarski(k3_xboole_0(esk1_0,esk3_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.40  fof(c_0_21, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.40  fof(c_0_22, plain, ![X10, X11]:r1_tarski(k3_xboole_0(X10,X11),X10), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.40  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.40  cnf(c_0_24, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_25, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_17])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_28, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_29, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.40  cnf(c_0_30, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.20/0.40  cnf(c_0_31, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.20/0.40  fof(c_0_32, plain, ![X12, X13, X14]:k3_xboole_0(X12,k4_xboole_0(X13,X14))=k4_xboole_0(k3_xboole_0(X12,X13),X14), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.40  cnf(c_0_33, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_27])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),X1)))=k5_xboole_0(esk2_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_30]), c_0_24])).
% 0.20/0.40  cnf(c_0_35, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X1,X2))))=X2), inference(spm,[status(thm)],[c_0_25, c_0_31])).
% 0.20/0.40  cnf(c_0_36, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.40  cnf(c_0_37, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(spm,[status(thm)],[c_0_25, c_0_28])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk2_0))=k3_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_33, c_0_30])).
% 0.20/0.40  cnf(c_0_39, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))=k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.40  cnf(c_0_40, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_13]), c_0_13])).
% 0.20/0.40  cnf(c_0_41, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X1))=k3_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_37]), c_0_27])).
% 0.20/0.40  cnf(c_0_42, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1)))=k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_38]), c_0_24])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))))=k3_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_39, c_0_38])).
% 0.20/0.40  cnf(c_0_44, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_40, c_0_27])).
% 0.20/0.40  cnf(c_0_45, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X1,X3)))=k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_41]), c_0_24])).
% 0.20/0.40  cnf(c_0_46, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk2_0)))=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))),X1)=k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_24]), c_0_45])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))=k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_47]), c_0_41])).
% 0.20/0.40  cnf(c_0_49, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,X2)),X3)))=k5_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_37]), c_0_24])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))))=esk1_0), inference(spm,[status(thm)],[c_0_37, c_0_48])).
% 0.20/0.40  cnf(c_0_51, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))))=k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_41])).
% 0.20/0.40  cnf(c_0_52, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))=k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0))), inference(spm,[status(thm)],[c_0_34, c_0_37])).
% 0.20/0.40  cnf(c_0_53, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))=k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_46]), c_0_24]), c_0_41])).
% 0.20/0.40  cnf(c_0_54, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_51]), c_0_47])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))=k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))=k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_54]), c_0_53])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk1_0))=k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.40  cnf(c_0_58, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0)))=k5_xboole_0(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_34, c_0_57])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,X1))))=k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_58]), c_0_24]), c_0_24]), c_0_24])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))=k5_xboole_0(esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_29]), c_0_27]), c_0_30])).
% 0.20/0.40  cnf(c_0_61, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_27]), c_0_40])).
% 0.20/0.40  cnf(c_0_62, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk2_0)))=k5_xboole_0(esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_46, c_0_60])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(X1,k3_xboole_0(X1,esk2_0)))=k3_xboole_0(X1,k5_xboole_0(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_61, c_0_60])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk2_0))=k5_xboole_0(esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),X1))=k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_42]), c_0_34])).
% 0.20/0.40  cnf(c_0_66, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,X2))=k3_xboole_0(X2,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_41, c_0_27])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk2_0)))=k5_xboole_0(esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_64]), c_0_24]), c_0_64])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))=k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_42])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, (k3_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))=k3_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_67]), c_0_38]), c_0_66])).
% 0.20/0.40  cnf(c_0_70, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))=k5_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_38]), c_0_30])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),X1))=k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_34]), c_0_42])).
% 0.20/0.40  cnf(c_0_72, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk2_0)=k5_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.20/0.40  cnf(c_0_73, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[c_0_30, c_0_70])).
% 0.20/0.40  cnf(c_0_74, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))=esk1_0), inference(spm,[status(thm)],[c_0_37, c_0_53])).
% 0.20/0.40  cnf(c_0_75, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk2_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])).
% 0.20/0.40  cnf(c_0_76, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))=k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,esk1_0))), inference(spm,[status(thm)],[c_0_34, c_0_41])).
% 0.20/0.40  cnf(c_0_77, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk1_0)=k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk2_0))), inference(rw,[status(thm)],[c_0_56, c_0_60])).
% 0.20/0.40  cnf(c_0_78, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0))))=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_52]), c_0_37])).
% 0.20/0.40  cnf(c_0_79, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk1_0))=esk1_0), inference(rw,[status(thm)],[c_0_74, c_0_56])).
% 0.20/0.40  cnf(c_0_80, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,X1)))=k5_xboole_0(esk2_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_75]), c_0_24])).
% 0.20/0.40  cnf(c_0_81, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,esk1_0)))=k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_76]), c_0_42]), c_0_41]), c_0_53]), c_0_56]), c_0_77])).
% 0.20/0.40  cnf(c_0_82, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk2_0)))=k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[c_0_57, c_0_77])).
% 0.20/0.40  cnf(c_0_83, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk1_0)))=k5_xboole_0(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_59, c_0_78])).
% 0.20/0.40  cnf(c_0_84, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk2_0)))=esk1_0), inference(rw,[status(thm)],[c_0_79, c_0_77])).
% 0.20/0.40  cnf(c_0_85, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,esk2_0))=k5_xboole_0(esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_83])).
% 0.20/0.40  cnf(c_0_86, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85]), c_0_41])).
% 0.20/0.40  cnf(c_0_87, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,esk1_0))=esk1_0), inference(rw,[status(thm)],[c_0_78, c_0_83])).
% 0.20/0.40  cnf(c_0_88, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_86]), c_0_27]), c_0_86]), c_0_77]), c_0_85]), c_0_87])).
% 0.20/0.40  cnf(c_0_89, plain, (r1_tarski(k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))),X2)), inference(spm,[status(thm)],[c_0_28, c_0_61])).
% 0.20/0.40  cnf(c_0_90, negated_conjecture, (k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)))=k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1))), inference(spm,[status(thm)],[c_0_40, c_0_88])).
% 0.20/0.40  cnf(c_0_91, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,X1)))=k5_xboole_0(esk1_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_87]), c_0_24])).
% 0.20/0.40  cnf(c_0_92, negated_conjecture, (r1_tarski(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1)),esk2_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.20/0.40  cnf(c_0_93, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,X1)))=k3_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_91, c_0_29])).
% 0.20/0.40  cnf(c_0_94, negated_conjecture, (~r1_tarski(k3_xboole_0(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_95, negated_conjecture, (r1_tarski(k3_xboole_0(esk1_0,X1),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_90]), c_0_93])).
% 0.20/0.40  cnf(c_0_96, negated_conjecture, (~r1_tarski(k3_xboole_0(esk3_0,esk1_0),esk2_0)), inference(rw,[status(thm)],[c_0_94, c_0_27])).
% 0.20/0.40  cnf(c_0_97, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_95, c_0_27])).
% 0.20/0.40  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 99
% 0.20/0.40  # Proof object clause steps            : 80
% 0.20/0.40  # Proof object formula steps           : 19
% 0.20/0.40  # Proof object conjectures             : 59
% 0.20/0.40  # Proof object clause conjectures      : 56
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 10
% 0.20/0.40  # Proof object initial formulas used   : 9
% 0.20/0.40  # Proof object generating inferences   : 50
% 0.20/0.40  # Proof object simplifying inferences  : 70
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 9
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 10
% 0.20/0.40  # Removed in clause preprocessing      : 2
% 0.20/0.41  # Initial clauses in saturation        : 8
% 0.20/0.41  # Processed clauses                    : 290
% 0.20/0.41  # ...of these trivial                  : 110
% 0.20/0.41  # ...subsumed                          : 8
% 0.20/0.41  # ...remaining for further processing  : 172
% 0.20/0.41  # Other redundant clauses eliminated   : 0
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 0
% 0.20/0.41  # Backward-rewritten                   : 94
% 0.20/0.41  # Generated clauses                    : 2137
% 0.20/0.41  # ...of the previous two non-trivial   : 1656
% 0.20/0.41  # Contextual simplify-reflections      : 0
% 0.20/0.41  # Paramodulations                      : 2137
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 0
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 70
% 0.20/0.41  #    Positive orientable unit clauses  : 67
% 0.20/0.41  #    Positive unorientable unit clauses: 2
% 0.20/0.41  #    Negative unit clauses             : 0
% 0.20/0.41  #    Non-unit-clauses                  : 1
% 0.20/0.41  # Current number of unprocessed clauses: 1317
% 0.20/0.41  # ...number of literals in the above   : 1317
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 104
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.41  # Unit Clause-clause subsumption calls : 12
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 159
% 0.20/0.41  # BW rewrite match successes           : 47
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 37002
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.057 s
% 0.20/0.41  # System time              : 0.004 s
% 0.20/0.41  # Total time               : 0.061 s
% 0.20/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
