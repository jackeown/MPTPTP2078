%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:01 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   83 (9726 expanded)
%              Number of clauses        :   62 (4496 expanded)
%              Number of leaves         :   10 (2613 expanded)
%              Depth                    :   21
%              Number of atoms          :   90 (10662 expanded)
%              Number of equality atoms :   73 (9023 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t117_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X3,X2)
     => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(c_0_10,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,X7)
      | k2_xboole_0(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_11,plain,(
    ! [X23,X24] : k2_xboole_0(X23,X24) = k5_xboole_0(X23,k4_xboole_0(X24,X23)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_15,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_16,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_17,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k3_xboole_0(X13,X14)) = k4_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_18,plain,(
    ! [X10,X11,X12] : k4_xboole_0(k4_xboole_0(X10,X11),X12) = k4_xboole_0(X10,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_19,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X17,X18,X19] : k3_xboole_0(X17,k4_xboole_0(X18,X19)) = k4_xboole_0(k3_xboole_0(X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_22])).

fof(c_0_28,plain,(
    ! [X20,X21,X22] : k4_xboole_0(X20,k4_xboole_0(X21,X22)) = k2_xboole_0(k4_xboole_0(X20,X21),k3_xboole_0(X20,X22)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_13])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_22]),c_0_22])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_32])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X3,X2)
       => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t117_xboole_1])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_13]),c_0_22])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_29])).

fof(c_0_42,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    & k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,X2))))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_35])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_34])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_26])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_27]),c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k5_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk3_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_46])).

cnf(c_0_50,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_36])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),X2) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_47]),c_0_48]),c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),esk2_0) = k4_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_49])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_44])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_51]),c_0_47])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk3_0,X1),esk2_0) = k4_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_41]),c_0_52])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_53]),c_0_41]),c_0_54])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X1),X2) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_44]),c_0_55]),c_0_48]),c_0_41])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk2_0) = k4_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_51])).

cnf(c_0_60,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_57]),c_0_58])).

cnf(c_0_61,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_27])).

cnf(c_0_62,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1)) = k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_59]),c_0_47]),c_0_58])).

cnf(c_0_63,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),X3) = k4_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X1,X3)))) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_31])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X3,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_29])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k5_xboole_0(X3,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_44])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_67])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_57]),c_0_55]),c_0_48]),c_0_41]),c_0_54])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_13]),c_0_22])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),X1)) = k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_69]),c_0_70]),c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)),k4_xboole_0(esk1_0,esk2_0))) != k4_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_72,c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( k5_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk2_0,X1),esk3_0)) = k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0))))) != k4_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_35]),c_0_27])).

cnf(c_0_77,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X2),X4)) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_71]),c_0_43])).

cnf(c_0_78,plain,
    ( k5_xboole_0(k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_79,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(esk2_0,X2)) = k4_xboole_0(X1,k4_xboole_0(esk2_0,k4_xboole_0(X2,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_75]),c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,esk1_0))) != k4_xboole_0(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_29])).

cnf(c_0_81,negated_conjecture,
    ( k5_xboole_0(k4_xboole_0(X1,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,X1))) = k4_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_49])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n022.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 16:43:10 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 2.04/2.24  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 2.04/2.24  # and selection function SelectNewComplexAHP.
% 2.04/2.24  #
% 2.04/2.24  # Preprocessing time       : 0.026 s
% 2.04/2.24  
% 2.04/2.24  # Proof found!
% 2.04/2.24  # SZS status Theorem
% 2.04/2.24  # SZS output start CNFRefutation
% 2.04/2.24  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.04/2.24  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.04/2.24  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.04/2.24  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.04/2.24  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.04/2.24  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.04/2.24  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.04/2.24  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.04/2.24  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.04/2.24  fof(t117_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_xboole_1)).
% 2.04/2.24  fof(c_0_10, plain, ![X6, X7]:(~r1_tarski(X6,X7)|k2_xboole_0(X6,X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 2.04/2.24  fof(c_0_11, plain, ![X23, X24]:k2_xboole_0(X23,X24)=k5_xboole_0(X23,k4_xboole_0(X24,X23)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 2.04/2.24  cnf(c_0_12, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.04/2.24  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.04/2.24  fof(c_0_14, plain, ![X8, X9]:r1_tarski(k4_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 2.04/2.24  fof(c_0_15, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 2.04/2.24  fof(c_0_16, plain, ![X15, X16]:k4_xboole_0(X15,k4_xboole_0(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 2.04/2.24  fof(c_0_17, plain, ![X13, X14]:k4_xboole_0(X13,k3_xboole_0(X13,X14))=k4_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 2.04/2.24  fof(c_0_18, plain, ![X10, X11, X12]:k4_xboole_0(k4_xboole_0(X10,X11),X12)=k4_xboole_0(X10,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 2.04/2.24  cnf(c_0_19, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 2.04/2.24  cnf(c_0_20, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.04/2.24  cnf(c_0_21, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.04/2.24  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.04/2.24  cnf(c_0_23, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.04/2.24  fof(c_0_24, plain, ![X17, X18, X19]:k3_xboole_0(X17,k4_xboole_0(X18,X19))=k4_xboole_0(k3_xboole_0(X17,X18),X19), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 2.04/2.24  cnf(c_0_25, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.04/2.24  cnf(c_0_26, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=X1), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 2.04/2.24  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_22])).
% 2.04/2.24  fof(c_0_28, plain, ![X20, X21, X22]:k4_xboole_0(X20,k4_xboole_0(X21,X22))=k2_xboole_0(k4_xboole_0(X20,X21),k3_xboole_0(X20,X22)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 2.04/2.24  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_22])).
% 2.04/2.24  cnf(c_0_30, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.04/2.24  cnf(c_0_31, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_25, c_0_13])).
% 2.04/2.24  cnf(c_0_32, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))=X1), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 2.04/2.24  cnf(c_0_33, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.04/2.24  cnf(c_0_34, plain, (k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_26, c_0_29])).
% 2.04/2.24  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_22]), c_0_22])).
% 2.04/2.24  cnf(c_0_36, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_27]), c_0_32])).
% 2.04/2.24  fof(c_0_37, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t117_xboole_1])).
% 2.04/2.24  cnf(c_0_38, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_13]), c_0_22])).
% 2.04/2.24  cnf(c_0_39, plain, (k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_34, c_0_27])).
% 2.04/2.24  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 2.04/2.24  cnf(c_0_41, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_36, c_0_29])).
% 2.04/2.24  fof(c_0_42, negated_conjecture, (r1_tarski(esk3_0,esk2_0)&k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 2.04/2.24  cnf(c_0_43, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,X2)))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_38, c_0_35])).
% 2.04/2.24  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_34])).
% 2.04/2.24  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_29, c_0_27])).
% 2.04/2.24  cnf(c_0_46, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.04/2.24  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_26])).
% 2.04/2.24  cnf(c_0_48, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_27]), c_0_45])).
% 2.04/2.24  cnf(c_0_49, negated_conjecture, (k5_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk3_0))=esk2_0), inference(spm,[status(thm)],[c_0_19, c_0_46])).
% 2.04/2.24  cnf(c_0_50, plain, (r1_tarski(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_20, c_0_36])).
% 2.04/2.24  cnf(c_0_51, plain, (k4_xboole_0(k4_xboole_0(X1,X1),X2)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_47]), c_0_48]), c_0_41])).
% 2.04/2.24  cnf(c_0_52, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),esk2_0)=k4_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_31, c_0_49])).
% 2.04/2.24  cnf(c_0_53, plain, (r1_tarski(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3)))), inference(spm,[status(thm)],[c_0_50, c_0_44])).
% 2.04/2.24  cnf(c_0_54, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_51]), c_0_47])).
% 2.04/2.24  cnf(c_0_55, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_45])).
% 2.04/2.24  cnf(c_0_56, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk3_0,X1),esk2_0)=k4_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_41]), c_0_52])).
% 2.04/2.24  cnf(c_0_57, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X3))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_53]), c_0_41]), c_0_54])).
% 2.04/2.24  cnf(c_0_58, plain, (k5_xboole_0(k4_xboole_0(X1,X1),X2)=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_44]), c_0_55]), c_0_48]), c_0_41])).
% 2.04/2.24  cnf(c_0_59, negated_conjecture, (k4_xboole_0(esk3_0,esk2_0)=k4_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_56, c_0_51])).
% 2.04/2.24  cnf(c_0_60, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2)=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_57]), c_0_58])).
% 2.04/2.24  cnf(c_0_61, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_20, c_0_27])).
% 2.04/2.24  cnf(c_0_62, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,X1))=k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_59]), c_0_47]), c_0_58])).
% 2.04/2.24  cnf(c_0_63, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))),X3)=k4_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_36, c_0_27])).
% 2.04/2.24  cnf(c_0_64, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X1,X3))))=X1), inference(spm,[status(thm)],[c_0_44, c_0_31])).
% 2.04/2.24  cnf(c_0_65, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X3,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_31, c_0_60])).
% 2.04/2.24  cnf(c_0_66, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,X1),k4_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_29])).
% 2.04/2.24  cnf(c_0_67, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k5_xboole_0(X3,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 2.04/2.24  cnf(c_0_68, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 2.04/2.24  cnf(c_0_69, negated_conjecture, (r1_tarski(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0)))), inference(spm,[status(thm)],[c_0_66, c_0_44])).
% 2.04/2.24  cnf(c_0_70, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k4_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_31, c_0_67])).
% 2.04/2.24  cnf(c_0_71, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_57]), c_0_55]), c_0_48]), c_0_41]), c_0_54])).
% 2.04/2.24  cnf(c_0_72, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)!=k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_13]), c_0_22])).
% 2.04/2.24  cnf(c_0_73, negated_conjecture, (k5_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),X1))=k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_69]), c_0_70]), c_0_71])).
% 2.04/2.24  cnf(c_0_74, negated_conjecture, (k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),esk1_0)),k4_xboole_0(esk1_0,esk2_0)))!=k4_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_72, c_0_27])).
% 2.04/2.24  cnf(c_0_75, negated_conjecture, (k5_xboole_0(esk3_0,k4_xboole_0(k4_xboole_0(esk2_0,X1),esk3_0))=k4_xboole_0(esk2_0,k4_xboole_0(X1,esk3_0))), inference(spm,[status(thm)],[c_0_73, c_0_70])).
% 2.04/2.24  cnf(c_0_76, negated_conjecture, (k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk1_0)))))!=k4_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_35]), c_0_27])).
% 2.04/2.24  cnf(c_0_77, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X2),X4))=k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_71]), c_0_43])).
% 2.04/2.24  cnf(c_0_78, plain, (k5_xboole_0(k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,X2))))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 2.04/2.24  cnf(c_0_79, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(esk2_0,X2))=k4_xboole_0(X1,k4_xboole_0(esk2_0,k4_xboole_0(X2,esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_75]), c_0_70])).
% 2.04/2.24  cnf(c_0_80, negated_conjecture, (k5_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,esk1_0)))!=k4_xboole_0(esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77]), c_0_29])).
% 2.04/2.24  cnf(c_0_81, negated_conjecture, (k5_xboole_0(k4_xboole_0(X1,esk2_0),k4_xboole_0(k4_xboole_0(esk2_0,esk3_0),k4_xboole_0(esk2_0,X1)))=k4_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_49])).
% 2.04/2.24  cnf(c_0_82, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])]), ['proof']).
% 2.04/2.24  # SZS output end CNFRefutation
% 2.04/2.24  # Proof object total steps             : 83
% 2.04/2.24  # Proof object clause steps            : 62
% 2.04/2.24  # Proof object formula steps           : 21
% 2.04/2.24  # Proof object conjectures             : 21
% 2.04/2.24  # Proof object clause conjectures      : 18
% 2.04/2.24  # Proof object formula conjectures     : 3
% 2.04/2.24  # Proof object initial clauses used    : 11
% 2.04/2.24  # Proof object initial formulas used   : 10
% 2.04/2.24  # Proof object generating inferences   : 39
% 2.04/2.24  # Proof object simplifying inferences  : 47
% 2.04/2.24  # Training examples: 0 positive, 0 negative
% 2.04/2.24  # Parsed axioms                        : 10
% 2.04/2.24  # Removed by relevancy pruning/SinE    : 0
% 2.04/2.24  # Initial clauses                      : 11
% 2.04/2.24  # Removed in clause preprocessing      : 2
% 2.04/2.24  # Initial clauses in saturation        : 9
% 2.04/2.24  # Processed clauses                    : 6583
% 2.04/2.24  # ...of these trivial                  : 2392
% 2.04/2.24  # ...subsumed                          : 3322
% 2.04/2.24  # ...remaining for further processing  : 869
% 2.04/2.24  # Other redundant clauses eliminated   : 0
% 2.04/2.24  # Clauses deleted for lack of memory   : 0
% 2.04/2.24  # Backward-subsumed                    : 1
% 2.04/2.24  # Backward-rewritten                   : 304
% 2.04/2.24  # Generated clauses                    : 348874
% 2.04/2.24  # ...of the previous two non-trivial   : 196625
% 2.04/2.24  # Contextual simplify-reflections      : 0
% 2.04/2.24  # Paramodulations                      : 348874
% 2.04/2.24  # Factorizations                       : 0
% 2.04/2.24  # Equation resolutions                 : 0
% 2.04/2.24  # Propositional unsat checks           : 0
% 2.04/2.24  #    Propositional check models        : 0
% 2.04/2.24  #    Propositional check unsatisfiable : 0
% 2.04/2.24  #    Propositional clauses             : 0
% 2.04/2.24  #    Propositional clauses after purity: 0
% 2.04/2.24  #    Propositional unsat core size     : 0
% 2.04/2.24  #    Propositional preprocessing time  : 0.000
% 2.04/2.24  #    Propositional encoding time       : 0.000
% 2.04/2.24  #    Propositional solver time         : 0.000
% 2.04/2.24  #    Success case prop preproc time    : 0.000
% 2.04/2.24  #    Success case prop encoding time   : 0.000
% 2.04/2.24  #    Success case prop solver time     : 0.000
% 2.04/2.24  # Current number of processed clauses  : 564
% 2.04/2.24  #    Positive orientable unit clauses  : 537
% 2.04/2.24  #    Positive unorientable unit clauses: 26
% 2.04/2.24  #    Negative unit clauses             : 0
% 2.04/2.24  #    Non-unit-clauses                  : 1
% 2.04/2.24  # Current number of unprocessed clauses: 187954
% 2.04/2.24  # ...number of literals in the above   : 187954
% 2.04/2.24  # Current number of archived formulas  : 0
% 2.04/2.24  # Current number of archived clauses   : 307
% 2.04/2.24  # Clause-clause subsumption calls (NU) : 0
% 2.04/2.24  # Rec. Clause-clause subsumption calls : 0
% 2.04/2.24  # Non-unit clause-clause subsumptions  : 0
% 2.04/2.24  # Unit Clause-clause subsumption calls : 492
% 2.04/2.24  # Rewrite failures with RHS unbound    : 106
% 2.04/2.24  # BW rewrite match attempts            : 7519
% 2.04/2.24  # BW rewrite match successes           : 887
% 2.04/2.24  # Condensation attempts                : 0
% 2.04/2.24  # Condensation successes               : 0
% 2.04/2.24  # Termbank termtop insertions          : 4975698
% 2.04/2.25  
% 2.04/2.25  # -------------------------------------------------
% 2.04/2.25  # User time                : 1.811 s
% 2.04/2.25  # System time              : 0.105 s
% 2.04/2.25  # Total time               : 1.916 s
% 2.04/2.25  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
