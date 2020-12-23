%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:00 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   93 (2747 expanded)
%              Number of clauses        :   66 (1249 expanded)
%              Number of leaves         :   13 ( 727 expanded)
%              Depth                    :   19
%              Number of atoms          :  105 (3329 expanded)
%              Number of equality atoms :   84 (2470 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t117_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X3,X2)
     => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(c_0_13,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_14,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_15,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_16,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X6] : k2_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_20,plain,(
    ! [X27,X28] : k2_xboole_0(X27,X28) = k5_xboole_0(X27,k4_xboole_0(X28,X27)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_21,plain,(
    ! [X8,X9] :
      ( ( k4_xboole_0(X8,X9) != k1_xboole_0
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | k4_xboole_0(X8,X9) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_17]),c_0_17])).

fof(c_0_24,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X3,X2)
       => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t117_xboole_1])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_32,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_33,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    & k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_17])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_17])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_30])).

cnf(c_0_42,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_44,plain,(
    ! [X24,X25,X26] : k5_xboole_0(k5_xboole_0(X24,X25),X26) = k5_xboole_0(X24,k5_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_39]),c_0_43])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0)) = k5_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_46]),c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,X3))) = k5_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_49]),c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_46]),c_0_47]),c_0_37]),c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(k1_xboole_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_56,plain,(
    ! [X21,X22,X23] : k3_xboole_0(X21,k4_xboole_0(X22,X23)) = k4_xboole_0(k3_xboole_0(X21,X22),X23) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_57,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))) = k5_xboole_0(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(esk3_0,X1)) = k5_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) != k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k3_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_27]),c_0_17]),c_0_17]),c_0_17]),c_0_17]),c_0_17])).

fof(c_0_60,plain,(
    ! [X12,X13,X14] : k3_xboole_0(k3_xboole_0(X12,X13),X14) = k3_xboole_0(X12,k3_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)) = k5_xboole_0(k1_xboole_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_57]),c_0_51]),c_0_58])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_45])).

cnf(c_0_64,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k3_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_65,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_17]),c_0_17])).

cnf(c_0_67,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(X1,esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_41]),c_0_47])).

cnf(c_0_68,negated_conjecture,
    ( k5_xboole_0(X1,k5_xboole_0(esk2_0,esk3_0)) = k5_xboole_0(X1,k5_xboole_0(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_62]),c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0),k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0))))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_43]),c_0_43]),c_0_47])).

cnf(c_0_70,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_66,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,esk2_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0))))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_42]),c_0_37])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,X1))) = k5_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_71]),c_0_47])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_22]),c_0_37])).

cnf(c_0_76,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_30])).

cnf(c_0_77,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk3_0) = k5_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_41]),c_0_45])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_75])).

cnf(c_0_80,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_37])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_37]),c_0_65])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(esk2_0,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0)))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_85,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,X2))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_80])).

cnf(c_0_86,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X3,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_65])).

cnf(c_0_87,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_37])).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,k5_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0)))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_89,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X3,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,esk2_0)) = k5_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_78]),c_0_78])).

cnf(c_0_91,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,X1)) = k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_52])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89]),c_0_90]),c_0_91]),c_0_41]),c_0_45]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.55  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 0.19/0.55  # and selection function SelectNewComplexAHP.
% 0.19/0.55  #
% 0.19/0.55  # Preprocessing time       : 0.027 s
% 0.19/0.55  
% 0.19/0.55  # Proof found!
% 0.19/0.55  # SZS status Theorem
% 0.19/0.55  # SZS output start CNFRefutation
% 0.19/0.55  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.55  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.55  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.55  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.19/0.55  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.55  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.55  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.55  fof(t117_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_xboole_1)).
% 0.19/0.55  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.55  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.19/0.55  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.55  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.19/0.55  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 0.19/0.55  fof(c_0_13, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.55  fof(c_0_14, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.55  fof(c_0_15, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.55  cnf(c_0_16, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.55  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.55  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.55  fof(c_0_19, plain, ![X6]:k2_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.19/0.55  fof(c_0_20, plain, ![X27, X28]:k2_xboole_0(X27,X28)=k5_xboole_0(X27,k4_xboole_0(X28,X27)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.55  fof(c_0_21, plain, ![X8, X9]:((k4_xboole_0(X8,X9)!=k1_xboole_0|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|k4_xboole_0(X8,X9)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.55  cnf(c_0_22, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.55  cnf(c_0_23, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_17]), c_0_17])).
% 0.19/0.55  fof(c_0_24, plain, ![X7]:k3_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.55  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t117_xboole_1])).
% 0.19/0.55  cnf(c_0_26, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.55  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.55  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.55  cnf(c_0_29, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.55  cnf(c_0_30, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.55  fof(c_0_31, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.55  fof(c_0_32, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.19/0.55  fof(c_0_33, negated_conjecture, (r1_tarski(esk3_0,esk2_0)&k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.19/0.55  cnf(c_0_34, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_17])).
% 0.19/0.55  cnf(c_0_35, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k1_xboole_0|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_17])).
% 0.19/0.55  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.55  cnf(c_0_37, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.55  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.55  cnf(c_0_39, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.55  cnf(c_0_40, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_34, c_0_30])).
% 0.19/0.55  cnf(c_0_41, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_30])).
% 0.19/0.55  cnf(c_0_42, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_22, c_0_37])).
% 0.19/0.55  cnf(c_0_43, negated_conjecture, (k3_xboole_0(esk3_0,esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.55  fof(c_0_44, plain, ![X24, X25, X26]:k5_xboole_0(k5_xboole_0(X24,X25),X26)=k5_xboole_0(X24,k5_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.55  cnf(c_0_45, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.55  cnf(c_0_46, negated_conjecture, (r1_tarski(k5_xboole_0(esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.55  cnf(c_0_47, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.55  cnf(c_0_48, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_39]), c_0_43])).
% 0.19/0.55  cnf(c_0_49, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_45, c_0_41])).
% 0.19/0.55  cnf(c_0_50, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0))=k5_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_46]), c_0_37])).
% 0.19/0.55  cnf(c_0_51, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.55  cnf(c_0_52, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,X3)))=k5_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_49]), c_0_47])).
% 0.19/0.55  cnf(c_0_53, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_46]), c_0_47]), c_0_37]), c_0_50])).
% 0.19/0.55  cnf(c_0_54, negated_conjecture, (k5_xboole_0(k1_xboole_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_51, c_0_40])).
% 0.19/0.55  cnf(c_0_55, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.55  fof(c_0_56, plain, ![X21, X22, X23]:k3_xboole_0(X21,k4_xboole_0(X22,X23))=k4_xboole_0(k3_xboole_0(X21,X22),X23), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.19/0.55  cnf(c_0_57, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))=k5_xboole_0(X1,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_45])).
% 0.19/0.55  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k1_xboole_0,k5_xboole_0(esk3_0,X1))=k5_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_54])).
% 0.19/0.55  cnf(c_0_59, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))!=k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k3_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_27]), c_0_17]), c_0_17]), c_0_17]), c_0_17]), c_0_17])).
% 0.19/0.55  fof(c_0_60, plain, ![X12, X13, X14]:k3_xboole_0(k3_xboole_0(X12,X13),X14)=k3_xboole_0(X12,k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 0.19/0.55  cnf(c_0_61, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.55  cnf(c_0_62, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))=k5_xboole_0(k1_xboole_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_57]), c_0_51]), c_0_58])).
% 0.19/0.55  cnf(c_0_63, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_45])).
% 0.19/0.55  cnf(c_0_64, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k3_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37]), c_0_37])).
% 0.19/0.55  cnf(c_0_65, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.55  cnf(c_0_66, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_17]), c_0_17])).
% 0.19/0.55  cnf(c_0_67, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(X1,esk3_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_41]), c_0_47])).
% 0.19/0.55  cnf(c_0_68, negated_conjecture, (k5_xboole_0(X1,k5_xboole_0(esk2_0,esk3_0))=k5_xboole_0(X1,k5_xboole_0(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_62]), c_0_63])).
% 0.19/0.55  cnf(c_0_69, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0),k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)))))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_43]), c_0_43]), c_0_47])).
% 0.19/0.55  cnf(c_0_70, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3)))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_66, c_0_65])).
% 0.19/0.55  cnf(c_0_71, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,esk2_0))=esk3_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.55  cnf(c_0_72, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)))))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.55  cnf(c_0_73, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))=k5_xboole_0(X1,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_42]), c_0_37])).
% 0.19/0.55  cnf(c_0_74, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,X1)))=k5_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_71]), c_0_47])).
% 0.19/0.55  cnf(c_0_75, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_22]), c_0_37])).
% 0.19/0.55  cnf(c_0_76, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_65, c_0_30])).
% 0.19/0.55  cnf(c_0_77, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0))))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.55  cnf(c_0_78, negated_conjecture, (k5_xboole_0(esk2_0,esk3_0)=k5_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_41]), c_0_45])).
% 0.19/0.55  cnf(c_0_79, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_75])).
% 0.19/0.55  cnf(c_0_80, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_76, c_0_37])).
% 0.19/0.55  cnf(c_0_81, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),k5_xboole_0(esk1_0,k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0))))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.55  cnf(c_0_82, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.55  cnf(c_0_83, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_37]), c_0_65])).
% 0.19/0.55  cnf(c_0_84, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(esk2_0,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 0.19/0.55  cnf(c_0_85, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,X2)))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_70, c_0_80])).
% 0.19/0.55  cnf(c_0_86, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X3,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_37, c_0_65])).
% 0.19/0.55  cnf(c_0_87, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,k3_xboole_0(X1,X3)))=k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_70, c_0_37])).
% 0.19/0.55  cnf(c_0_88, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,k5_xboole_0(esk1_0,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.55  cnf(c_0_89, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X3,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 0.19/0.55  cnf(c_0_90, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,esk2_0))=k5_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_78]), c_0_78])).
% 0.19/0.55  cnf(c_0_91, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,X1))=k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_74, c_0_52])).
% 0.19/0.55  cnf(c_0_92, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89]), c_0_90]), c_0_91]), c_0_41]), c_0_45]), c_0_37])]), ['proof']).
% 0.19/0.55  # SZS output end CNFRefutation
% 0.19/0.55  # Proof object total steps             : 93
% 0.19/0.55  # Proof object clause steps            : 66
% 0.19/0.55  # Proof object formula steps           : 27
% 0.19/0.55  # Proof object conjectures             : 31
% 0.19/0.55  # Proof object clause conjectures      : 28
% 0.19/0.55  # Proof object formula conjectures     : 3
% 0.19/0.55  # Proof object initial clauses used    : 14
% 0.19/0.55  # Proof object initial formulas used   : 13
% 0.19/0.55  # Proof object generating inferences   : 34
% 0.19/0.55  # Proof object simplifying inferences  : 61
% 0.19/0.55  # Training examples: 0 positive, 0 negative
% 0.19/0.55  # Parsed axioms                        : 13
% 0.19/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.55  # Initial clauses                      : 15
% 0.19/0.55  # Removed in clause preprocessing      : 2
% 0.19/0.55  # Initial clauses in saturation        : 13
% 0.19/0.55  # Processed clauses                    : 2495
% 0.19/0.55  # ...of these trivial                  : 544
% 0.19/0.55  # ...subsumed                          : 1525
% 0.19/0.55  # ...remaining for further processing  : 426
% 0.19/0.55  # Other redundant clauses eliminated   : 0
% 0.19/0.55  # Clauses deleted for lack of memory   : 0
% 0.19/0.55  # Backward-subsumed                    : 21
% 0.19/0.55  # Backward-rewritten                   : 119
% 0.19/0.55  # Generated clauses                    : 24539
% 0.19/0.55  # ...of the previous two non-trivial   : 14141
% 0.19/0.55  # Contextual simplify-reflections      : 0
% 0.19/0.55  # Paramodulations                      : 24511
% 0.19/0.55  # Factorizations                       : 0
% 0.19/0.55  # Equation resolutions                 : 28
% 0.19/0.55  # Propositional unsat checks           : 0
% 0.19/0.55  #    Propositional check models        : 0
% 0.19/0.55  #    Propositional check unsatisfiable : 0
% 0.19/0.55  #    Propositional clauses             : 0
% 0.19/0.55  #    Propositional clauses after purity: 0
% 0.19/0.55  #    Propositional unsat core size     : 0
% 0.19/0.55  #    Propositional preprocessing time  : 0.000
% 0.19/0.55  #    Propositional encoding time       : 0.000
% 0.19/0.55  #    Propositional solver time         : 0.000
% 0.19/0.55  #    Success case prop preproc time    : 0.000
% 0.19/0.55  #    Success case prop encoding time   : 0.000
% 0.19/0.55  #    Success case prop solver time     : 0.000
% 0.19/0.55  # Current number of processed clauses  : 286
% 0.19/0.55  #    Positive orientable unit clauses  : 188
% 0.19/0.55  #    Positive unorientable unit clauses: 12
% 0.19/0.55  #    Negative unit clauses             : 0
% 0.19/0.55  #    Non-unit-clauses                  : 86
% 0.19/0.55  # Current number of unprocessed clauses: 11319
% 0.19/0.55  # ...number of literals in the above   : 14916
% 0.19/0.55  # Current number of archived formulas  : 0
% 0.19/0.55  # Current number of archived clauses   : 142
% 0.19/0.55  # Clause-clause subsumption calls (NU) : 3705
% 0.19/0.55  # Rec. Clause-clause subsumption calls : 3705
% 0.19/0.55  # Non-unit clause-clause subsumptions  : 1148
% 0.19/0.55  # Unit Clause-clause subsumption calls : 310
% 0.19/0.55  # Rewrite failures with RHS unbound    : 64
% 0.19/0.55  # BW rewrite match attempts            : 1307
% 0.19/0.55  # BW rewrite match successes           : 349
% 0.19/0.55  # Condensation attempts                : 0
% 0.19/0.55  # Condensation successes               : 0
% 0.19/0.55  # Termbank termtop insertions          : 296436
% 0.19/0.55  
% 0.19/0.55  # -------------------------------------------------
% 0.19/0.55  # User time                : 0.200 s
% 0.19/0.55  # System time              : 0.013 s
% 0.19/0.55  # Total time               : 0.212 s
% 0.19/0.55  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
