%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:59 EST 2020

% Result     : Theorem 19.74s
% Output     : CNFRefutation 19.74s
% Verified   : 
% Statistics : Number of formulae       :  147 (146599 expanded)
%              Number of clauses        :  118 (64992 expanded)
%              Number of leaves         :   14 (40795 expanded)
%              Depth                    :   35
%              Number of atoms          :  153 (151897 expanded)
%              Number of equality atoms :  125 (138619 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t117_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X3,X2)
     => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

fof(c_0_14,plain,(
    ! [X15,X16] : r1_tarski(k4_xboole_0(X15,X16),X15) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_15,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_16,plain,(
    ! [X17] : k4_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_17,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k3_xboole_0(X13,X14) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_18,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_21,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k4_xboole_0(X18,X19)) = k3_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_22,plain,(
    ! [X24,X25,X26] : k5_xboole_0(k5_xboole_0(X24,X25),X26) = k5_xboole_0(X24,k5_xboole_0(X25,X26)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_23,plain,(
    ! [X23] : k5_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_24,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_25,plain,(
    ! [X27,X28] : k2_xboole_0(X27,X28) = k5_xboole_0(X27,k4_xboole_0(X28,X27)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_26,c_0_19])).

fof(c_0_36,plain,(
    ! [X11,X12] : k3_xboole_0(X11,k2_xboole_0(X11,X12)) = X11 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_19]),c_0_19])).

cnf(c_0_39,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_34]),c_0_19]),c_0_19])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_29])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_37])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_39]),c_0_29])).

cnf(c_0_47,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_35]),c_0_42])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_34]),c_0_19])).

fof(c_0_49,plain,(
    ! [X20,X21,X22] : k3_xboole_0(X20,k4_xboole_0(X21,X22)) = k4_xboole_0(k3_xboole_0(X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_50,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_35]),c_0_47])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_50]),c_0_29])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_19]),c_0_19])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_29])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_55]),c_0_32])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))) = k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_56]),c_0_56])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_58]),c_0_31])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1))) = k3_xboole_0(X2,k3_xboole_0(X3,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_46]),c_0_60]),c_0_60])).

cnf(c_0_62,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_61])).

cnf(c_0_63,plain,
    ( r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X3,X1)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_48]),c_0_31]),c_0_31])).

fof(c_0_64,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_65,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_58]),c_0_32])).

cnf(c_0_66,plain,
    ( k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_58])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_60]),c_0_29]),c_0_31]),c_0_60])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_66]),c_0_32])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_67]),c_0_57])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_68])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_69])).

fof(c_0_73,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X3,X2)
       => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t117_xboole_1])).

cnf(c_0_74,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_31]),c_0_72]),c_0_60])).

fof(c_0_75,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    & k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_73])])])).

cnf(c_0_76,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_56])).

cnf(c_0_77,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_60]),c_0_31]),c_0_69])).

cnf(c_0_78,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X1),X2) = k5_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_58])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_76]),c_0_60]),c_0_31]),c_0_60])).

cnf(c_0_81,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_79])).

cnf(c_0_82,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_29])).

cnf(c_0_83,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = X1 ),
    inference(spm,[status(thm)],[c_0_48,c_0_41])).

cnf(c_0_84,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,X2))) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_46]),c_0_60])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3))) = k5_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_69]),c_0_31])).

cnf(c_0_86,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1))) = k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_81])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X2,X1)))) = k5_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_60])).

cnf(c_0_89,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_32,c_0_58])).

cnf(c_0_90,plain,
    ( k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_48]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_72]),c_0_85]),c_0_29]),c_0_72]),c_0_85])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_72]),c_0_31])).

cnf(c_0_92,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,X1)) = k3_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_37]),c_0_60]),c_0_86]),c_0_60])).

cnf(c_0_93,plain,
    ( r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X2,X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_72])).

cnf(c_0_94,plain,
    ( k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_41])).

cnf(c_0_95,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_41]),c_0_31]),c_0_91]),c_0_91]),c_0_60])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_92])).

cnf(c_0_97,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_37]),c_0_31]),c_0_91]),c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk3_0),k3_xboole_0(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_29])).

cnf(c_0_99,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X3,k3_xboole_0(X1,X2)))) = k5_xboole_0(X3,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_56])).

cnf(c_0_100,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_97]),c_0_29])).

cnf(c_0_101,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(esk2_0,X1)) = k3_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_98])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_29]),c_0_29]),c_0_74]),c_0_60]),c_0_72])).

cnf(c_0_103,negated_conjecture,
    ( k3_xboole_0(k3_xboole_0(esk2_0,X1),k3_xboole_0(X1,esk3_0)) = k3_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_101])).

cnf(c_0_104,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_102]),c_0_60])).

cnf(c_0_105,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0))) = k5_xboole_0(k3_xboole_0(esk2_0,X1),k3_xboole_0(X1,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_103]),c_0_54])).

cnf(c_0_106,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_99]),c_0_85])).

cnf(c_0_107,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,X1)) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_72])).

cnf(c_0_108,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))) = X1 ),
    inference(spm,[status(thm)],[c_0_48,c_0_29])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k3_xboole_0(esk2_0,X1),k3_xboole_0(X1,esk3_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_105])).

cnf(c_0_110,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k5_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_95])).

cnf(c_0_111,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(X1,k3_xboole_0(esk3_0,X1))) = k5_xboole_0(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_29]),c_0_72])).

cnf(c_0_112,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X3,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_84]),c_0_89]),c_0_76]),c_0_107]),c_0_60]),c_0_60]),c_0_61])).

cnf(c_0_113,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_114,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_108,c_0_81])).

cnf(c_0_115,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X1 ),
    inference(spm,[status(thm)],[c_0_83,c_0_29])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,k5_xboole_0(esk3_0,esk2_0)),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_57]),c_0_56]),c_0_29]),c_0_81]),c_0_72])).

cnf(c_0_117,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),X3) = k5_xboole_0(X3,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_110]),c_0_89])).

cnf(c_0_118,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk2_0,X1)) = k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(esk3_0,X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_111])).

cnf(c_0_119,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_106,c_0_112])).

cnf(c_0_120,negated_conjecture,
    ( k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0)) != k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k3_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_34]),c_0_19]),c_0_19]),c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_121,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))) = k5_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_114]),c_0_31]),c_0_31]),c_0_58]),c_0_32]),c_0_31]),c_0_31]),c_0_58]),c_0_32]),c_0_29])).

cnf(c_0_122,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_115,c_0_81])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_116,c_0_29])).

cnf(c_0_124,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(esk3_0,X1)),esk2_0) = k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_117])).

cnf(c_0_125,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_119]),c_0_60])).

cnf(c_0_126,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0)))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29]),c_0_29])).

cnf(c_0_127,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_121]),c_0_31]),c_0_31]),c_0_31]),c_0_60]),c_0_60]),c_0_60]),c_0_29]),c_0_122])).

cnf(c_0_128,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1)) = k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_123]),c_0_29])).

cnf(c_0_129,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)),esk2_0) = k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_124,c_0_29])).

cnf(c_0_130,plain,
    ( k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_125,c_0_104])).

cnf(c_0_131,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_xboole_0(X1,esk2_0)) = k3_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_29])).

cnf(c_0_132,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_81]),c_0_81]),c_0_31])).

cnf(c_0_133,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk3_0) = k5_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_127])).

cnf(c_0_134,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk2_0,X1),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_128]),c_0_58])).

cnf(c_0_135,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,esk3_0),esk2_0)) = k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_136,negated_conjecture,
    ( k3_xboole_0(X1,k5_xboole_0(esk3_0,esk2_0)) = k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_131]),c_0_117]),c_0_29]),c_0_81]),c_0_72])).

cnf(c_0_137,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0))))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_133]),c_0_133])).

cnf(c_0_138,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),k3_xboole_0(X1,esk2_0)) = k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_134]),c_0_32]),c_0_107]),c_0_60])).

cnf(c_0_139,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(esk2_0,k5_xboole_0(X1,esk3_0))) = k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_135,c_0_29])).

cnf(c_0_140,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk2_0)),X2) = k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X2)) ),
    inference(spm,[status(thm)],[c_0_125,c_0_136])).

cnf(c_0_141,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),k3_xboole_0(esk2_0,esk1_0)))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_106]),c_0_104]),c_0_57]),c_0_60])).

cnf(c_0_142,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),k3_xboole_0(esk2_0,X1)) = k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_138,c_0_29])).

cnf(c_0_143,negated_conjecture,
    ( k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X2)) = k3_xboole_0(X1,k3_xboole_0(esk2_0,k3_xboole_0(k5_xboole_0(X1,esk3_0),X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_139]),c_0_125]),c_0_140])).

cnf(c_0_144,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0))) != k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_141,c_0_142])).

cnf(c_0_145,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1) = k5_xboole_0(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_143]),c_0_57]),c_0_29]),c_0_104]),c_0_106]),c_0_92]),c_0_72])).

cnf(c_0_146,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_144,c_0_145]),c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 19.74/19.88  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 19.74/19.88  # and selection function SelectNewComplexAHP.
% 19.74/19.88  #
% 19.74/19.88  # Preprocessing time       : 0.026 s
% 19.74/19.88  
% 19.74/19.88  # Proof found!
% 19.74/19.88  # SZS status Theorem
% 19.74/19.88  # SZS output start CNFRefutation
% 19.74/19.88  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 19.74/19.88  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 19.74/19.88  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 19.74/19.88  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 19.74/19.88  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 19.74/19.88  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 19.74/19.88  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 19.74/19.88  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 19.74/19.88  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 19.74/19.88  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 19.74/19.88  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 19.74/19.88  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 19.74/19.88  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 19.74/19.88  fof(t117_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_xboole_1)).
% 19.74/19.88  fof(c_0_14, plain, ![X15, X16]:r1_tarski(k4_xboole_0(X15,X16),X15), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 19.74/19.88  fof(c_0_15, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 19.74/19.88  fof(c_0_16, plain, ![X17]:k4_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t3_boole])).
% 19.74/19.88  fof(c_0_17, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k3_xboole_0(X13,X14)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 19.74/19.88  cnf(c_0_18, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 19.74/19.88  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 19.74/19.88  fof(c_0_20, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 19.74/19.88  fof(c_0_21, plain, ![X18, X19]:k4_xboole_0(X18,k4_xboole_0(X18,X19))=k3_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 19.74/19.88  fof(c_0_22, plain, ![X24, X25, X26]:k5_xboole_0(k5_xboole_0(X24,X25),X26)=k5_xboole_0(X24,k5_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 19.74/19.88  fof(c_0_23, plain, ![X23]:k5_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t5_boole])).
% 19.74/19.88  fof(c_0_24, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 19.74/19.88  fof(c_0_25, plain, ![X27, X28]:k2_xboole_0(X27,X28)=k5_xboole_0(X27,k4_xboole_0(X28,X27)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 19.74/19.88  cnf(c_0_26, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.74/19.88  cnf(c_0_27, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 19.74/19.88  cnf(c_0_28, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 19.74/19.88  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 19.74/19.88  cnf(c_0_30, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 19.74/19.88  cnf(c_0_31, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 19.74/19.88  cnf(c_0_32, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 19.74/19.88  cnf(c_0_33, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 19.74/19.88  cnf(c_0_34, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 19.74/19.89  cnf(c_0_35, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_26, c_0_19])).
% 19.74/19.89  fof(c_0_36, plain, ![X11, X12]:k3_xboole_0(X11,k2_xboole_0(X11,X12))=X11, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 19.74/19.89  cnf(c_0_37, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 19.74/19.89  cnf(c_0_38, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_19]), c_0_19])).
% 19.74/19.89  cnf(c_0_39, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 19.74/19.89  cnf(c_0_40, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 19.74/19.89  cnf(c_0_41, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_34]), c_0_19]), c_0_19])).
% 19.74/19.89  cnf(c_0_42, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_35, c_0_29])).
% 19.74/19.89  cnf(c_0_43, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 19.74/19.89  cnf(c_0_44, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X1)), inference(spm,[status(thm)],[c_0_28, c_0_37])).
% 19.74/19.89  cnf(c_0_45, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_38, c_0_37])).
% 19.74/19.89  cnf(c_0_46, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,X1)))=k5_xboole_0(X1,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_39]), c_0_29])).
% 19.74/19.89  cnf(c_0_47, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_35]), c_0_42])).
% 19.74/19.89  cnf(c_0_48, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_34]), c_0_19])).
% 19.74/19.89  fof(c_0_49, plain, ![X20, X21, X22]:k3_xboole_0(X20,k4_xboole_0(X21,X22))=k4_xboole_0(k3_xboole_0(X20,X21),X22), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 19.74/19.89  cnf(c_0_50, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 19.74/19.89  cnf(c_0_51, plain, (k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0))=k3_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 19.74/19.89  cnf(c_0_52, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_35]), c_0_47])).
% 19.74/19.89  cnf(c_0_53, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 19.74/19.89  cnf(c_0_54, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_50]), c_0_29])).
% 19.74/19.89  cnf(c_0_55, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 19.74/19.89  cnf(c_0_56, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_19]), c_0_19])).
% 19.74/19.89  cnf(c_0_57, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_54, c_0_29])).
% 19.74/19.89  cnf(c_0_58, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_55]), c_0_32])).
% 19.74/19.89  cnf(c_0_59, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3))))=k3_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_56]), c_0_56])).
% 19.74/19.89  cnf(c_0_60, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_58]), c_0_31])).
% 19.74/19.89  cnf(c_0_61, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1)))=k3_xboole_0(X2,k3_xboole_0(X3,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_46]), c_0_60]), c_0_60])).
% 19.74/19.89  cnf(c_0_62, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,X1))),X1)), inference(spm,[status(thm)],[c_0_28, c_0_61])).
% 19.74/19.89  cnf(c_0_63, plain, (r1_tarski(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X3,X1)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_48]), c_0_31]), c_0_31])).
% 19.74/19.89  fof(c_0_64, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 19.74/19.89  cnf(c_0_65, plain, (r1_tarski(k5_xboole_0(X1,X2),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_58]), c_0_32])).
% 19.74/19.89  cnf(c_0_66, plain, (k1_xboole_0=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_58])).
% 19.74/19.89  cnf(c_0_67, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_64])).
% 19.74/19.89  cnf(c_0_68, plain, (r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_60]), c_0_29]), c_0_31]), c_0_60])).
% 19.74/19.89  cnf(c_0_69, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_66]), c_0_32])).
% 19.74/19.89  cnf(c_0_70, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_67]), c_0_57])).
% 19.74/19.89  cnf(c_0_71, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1))))=X1), inference(spm,[status(thm)],[c_0_27, c_0_68])).
% 19.74/19.89  cnf(c_0_72, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_60, c_0_69])).
% 19.74/19.89  fof(c_0_73, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t117_xboole_1])).
% 19.74/19.89  cnf(c_0_74, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1)))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_31]), c_0_72]), c_0_60])).
% 19.74/19.89  fof(c_0_75, negated_conjecture, (r1_tarski(esk3_0,esk2_0)&k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_73])])])).
% 19.74/19.89  cnf(c_0_76, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))), inference(spm,[status(thm)],[c_0_60, c_0_56])).
% 19.74/19.89  cnf(c_0_77, plain, (k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_60]), c_0_31]), c_0_69])).
% 19.74/19.89  cnf(c_0_78, plain, (k3_xboole_0(k5_xboole_0(X1,X1),X2)=k5_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_52, c_0_58])).
% 19.74/19.89  cnf(c_0_79, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 19.74/19.89  cnf(c_0_80, plain, (k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_76]), c_0_60]), c_0_31]), c_0_60])).
% 19.74/19.89  cnf(c_0_81, negated_conjecture, (k3_xboole_0(esk3_0,esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_27, c_0_79])).
% 19.74/19.89  cnf(c_0_82, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_50, c_0_29])).
% 19.74/19.89  cnf(c_0_83, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=X1), inference(spm,[status(thm)],[c_0_48, c_0_41])).
% 19.74/19.89  cnf(c_0_84, plain, (k3_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X3,X2)))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_46]), c_0_60])).
% 19.74/19.89  cnf(c_0_85, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3)))=k5_xboole_0(X2,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_69]), c_0_31])).
% 19.74/19.89  cnf(c_0_86, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)))=k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))), inference(spm,[status(thm)],[c_0_56, c_0_81])).
% 19.74/19.89  cnf(c_0_87, plain, (r1_tarski(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 19.74/19.89  cnf(c_0_88, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X2,X1))))=k5_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_84, c_0_60])).
% 19.74/19.89  cnf(c_0_89, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_32, c_0_58])).
% 19.74/19.89  cnf(c_0_90, plain, (k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_48]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_72]), c_0_85]), c_0_29]), c_0_72]), c_0_85])).
% 19.74/19.89  cnf(c_0_91, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_72]), c_0_31])).
% 19.74/19.89  cnf(c_0_92, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(esk2_0,X1))=k3_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_37]), c_0_60]), c_0_86]), c_0_60])).
% 19.74/19.89  cnf(c_0_93, plain, (r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X2,X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_72])).
% 19.74/19.89  cnf(c_0_94, plain, (k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_90, c_0_41])).
% 19.74/19.89  cnf(c_0_95, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_41]), c_0_31]), c_0_91]), c_0_91]), c_0_60])).
% 19.74/19.89  cnf(c_0_96, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_82, c_0_92])).
% 19.74/19.89  cnf(c_0_97, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_37]), c_0_31]), c_0_91]), c_0_95])).
% 19.74/19.89  cnf(c_0_98, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk3_0),k3_xboole_0(esk2_0,X1))), inference(spm,[status(thm)],[c_0_96, c_0_29])).
% 19.74/19.89  cnf(c_0_99, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X3,k3_xboole_0(X1,X2))))=k5_xboole_0(X3,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))), inference(spm,[status(thm)],[c_0_41, c_0_56])).
% 19.74/19.89  cnf(c_0_100, plain, (k3_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_97]), c_0_29])).
% 19.74/19.89  cnf(c_0_101, negated_conjecture, (k3_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(esk2_0,X1))=k3_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_27, c_0_98])).
% 19.74/19.89  cnf(c_0_102, plain, (k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X2,X1)))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_29]), c_0_29]), c_0_74]), c_0_60]), c_0_72])).
% 19.74/19.89  cnf(c_0_103, negated_conjecture, (k3_xboole_0(k3_xboole_0(esk2_0,X1),k3_xboole_0(X1,esk3_0))=k3_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_101])).
% 19.74/19.89  cnf(c_0_104, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_102]), c_0_60])).
% 19.74/19.89  cnf(c_0_105, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)))=k5_xboole_0(k3_xboole_0(esk2_0,X1),k3_xboole_0(X1,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_103]), c_0_54])).
% 19.74/19.89  cnf(c_0_106, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_99]), c_0_85])).
% 19.74/19.89  cnf(c_0_107, plain, (k3_xboole_0(X1,k5_xboole_0(X2,X1))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_104, c_0_72])).
% 19.74/19.89  cnf(c_0_108, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))))=X1), inference(spm,[status(thm)],[c_0_48, c_0_29])).
% 19.74/19.89  cnf(c_0_109, negated_conjecture, (r1_tarski(k5_xboole_0(k3_xboole_0(esk2_0,X1),k3_xboole_0(X1,esk3_0)),esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_105])).
% 19.74/19.89  cnf(c_0_110, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k5_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_60, c_0_95])).
% 19.74/19.89  cnf(c_0_111, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(X1,k3_xboole_0(esk3_0,X1)))=k5_xboole_0(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_29]), c_0_72])).
% 19.74/19.89  cnf(c_0_112, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X3,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_84]), c_0_89]), c_0_76]), c_0_107]), c_0_60]), c_0_60]), c_0_61])).
% 19.74/19.89  cnf(c_0_113, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 19.74/19.89  cnf(c_0_114, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))=esk3_0), inference(spm,[status(thm)],[c_0_108, c_0_81])).
% 19.74/19.89  cnf(c_0_115, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))))=X1), inference(spm,[status(thm)],[c_0_83, c_0_29])).
% 19.74/19.89  cnf(c_0_116, negated_conjecture, (r1_tarski(k3_xboole_0(X1,k5_xboole_0(esk3_0,esk2_0)),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_57]), c_0_56]), c_0_29]), c_0_81]), c_0_72])).
% 19.74/19.89  cnf(c_0_117, plain, (k5_xboole_0(k3_xboole_0(X1,X2),X3)=k5_xboole_0(X3,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_110]), c_0_89])).
% 19.74/19.89  cnf(c_0_118, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk2_0,X1))=k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(esk3_0,X1)),esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_111])).
% 19.74/19.89  cnf(c_0_119, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_106, c_0_112])).
% 19.74/19.89  cnf(c_0_120, negated_conjecture, (k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk3_0))!=k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)),k5_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k3_xboole_0(k3_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))),k5_xboole_0(esk1_0,k3_xboole_0(esk1_0,esk2_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_34]), c_0_19]), c_0_19]), c_0_19]), c_0_19]), c_0_19])).
% 19.74/19.89  cnf(c_0_121, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))=k5_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_114]), c_0_31]), c_0_31]), c_0_58]), c_0_32]), c_0_31]), c_0_31]), c_0_58]), c_0_32]), c_0_29])).
% 19.74/19.89  cnf(c_0_122, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))=esk2_0), inference(spm,[status(thm)],[c_0_115, c_0_81])).
% 19.74/19.89  cnf(c_0_123, negated_conjecture, (r1_tarski(k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1),esk2_0)), inference(spm,[status(thm)],[c_0_116, c_0_29])).
% 19.74/19.89  cnf(c_0_124, negated_conjecture, (k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(esk3_0,X1)),esk2_0)=k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_117])).
% 19.74/19.89  cnf(c_0_125, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_119]), c_0_60])).
% 19.74/19.89  cnf(c_0_126, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,esk2_0)),esk1_0))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29]), c_0_29])).
% 19.74/19.89  cnf(c_0_127, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_121]), c_0_31]), c_0_31]), c_0_31]), c_0_60]), c_0_60]), c_0_60]), c_0_29]), c_0_122])).
% 19.74/19.89  cnf(c_0_128, negated_conjecture, (k3_xboole_0(esk2_0,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1))=k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_123]), c_0_29])).
% 19.74/19.89  cnf(c_0_129, negated_conjecture, (k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,esk3_0)),esk2_0)=k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_124, c_0_29])).
% 19.74/19.89  cnf(c_0_130, plain, (k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_125, c_0_104])).
% 19.74/19.89  cnf(c_0_131, negated_conjecture, (k3_xboole_0(esk3_0,k3_xboole_0(X1,esk2_0))=k3_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_92, c_0_29])).
% 19.74/19.89  cnf(c_0_132, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk2_0,esk3_0),esk1_0)))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_81]), c_0_81]), c_0_31])).
% 19.74/19.89  cnf(c_0_133, negated_conjecture, (k5_xboole_0(esk2_0,esk3_0)=k5_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_60, c_0_127])).
% 19.74/19.89  cnf(c_0_134, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk2_0,X1),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_128]), c_0_58])).
% 19.74/19.89  cnf(c_0_135, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(X1,esk3_0),esk2_0))=k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk2_0))), inference(rw,[status(thm)],[c_0_129, c_0_130])).
% 19.74/19.89  cnf(c_0_136, negated_conjecture, (k3_xboole_0(X1,k5_xboole_0(esk3_0,esk2_0))=k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_131]), c_0_117]), c_0_29]), c_0_81]), c_0_72])).
% 19.74/19.89  cnf(c_0_137, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k5_xboole_0(k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0),k3_xboole_0(k5_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk1_0)),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0)))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_132, c_0_133]), c_0_133])).
% 19.74/19.89  cnf(c_0_138, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),k3_xboole_0(X1,esk2_0))=k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_134]), c_0_32]), c_0_107]), c_0_60])).
% 19.74/19.89  cnf(c_0_139, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(esk2_0,k5_xboole_0(X1,esk3_0)))=k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_135, c_0_29])).
% 19.74/19.89  cnf(c_0_140, negated_conjecture, (k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,esk3_0),k3_xboole_0(X1,esk2_0)),X2)=k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X2))), inference(spm,[status(thm)],[c_0_125, c_0_136])).
% 19.74/19.89  cnf(c_0_141, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),k3_xboole_0(esk2_0,esk1_0))))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137, c_0_106]), c_0_104]), c_0_57]), c_0_60])).
% 19.74/19.89  cnf(c_0_142, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),k3_xboole_0(esk2_0,X1))=k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_138, c_0_29])).
% 19.74/19.89  cnf(c_0_143, negated_conjecture, (k3_xboole_0(X1,k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X2))=k3_xboole_0(X1,k3_xboole_0(esk2_0,k3_xboole_0(k5_xboole_0(X1,esk3_0),X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_139]), c_0_125]), c_0_140])).
% 19.74/19.89  cnf(c_0_144, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),esk1_0)))!=k5_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk1_0))), inference(rw,[status(thm)],[c_0_141, c_0_142])).
% 19.74/19.89  cnf(c_0_145, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk3_0,esk2_0),X1)=k5_xboole_0(k3_xboole_0(esk3_0,X1),k3_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_143]), c_0_57]), c_0_29]), c_0_104]), c_0_106]), c_0_92]), c_0_72])).
% 19.74/19.89  cnf(c_0_146, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_144, c_0_145]), c_0_69])]), ['proof']).
% 19.74/19.89  # SZS output end CNFRefutation
% 19.74/19.89  # Proof object total steps             : 147
% 19.74/19.89  # Proof object clause steps            : 118
% 19.74/19.89  # Proof object formula steps           : 29
% 19.74/19.89  # Proof object conjectures             : 43
% 19.74/19.89  # Proof object clause conjectures      : 40
% 19.74/19.89  # Proof object formula conjectures     : 3
% 19.74/19.89  # Proof object initial clauses used    : 15
% 19.74/19.89  # Proof object initial formulas used   : 14
% 19.74/19.89  # Proof object generating inferences   : 85
% 19.74/19.89  # Proof object simplifying inferences  : 156
% 19.74/19.89  # Training examples: 0 positive, 0 negative
% 19.74/19.89  # Parsed axioms                        : 14
% 19.74/19.89  # Removed by relevancy pruning/SinE    : 0
% 19.74/19.89  # Initial clauses                      : 15
% 19.74/19.89  # Removed in clause preprocessing      : 2
% 19.74/19.89  # Initial clauses in saturation        : 13
% 19.74/19.89  # Processed clauses                    : 48766
% 19.74/19.89  # ...of these trivial                  : 13712
% 19.74/19.89  # ...subsumed                          : 32053
% 19.74/19.89  # ...remaining for further processing  : 3001
% 19.74/19.89  # Other redundant clauses eliminated   : 0
% 19.74/19.89  # Clauses deleted for lack of memory   : 0
% 19.74/19.89  # Backward-subsumed                    : 0
% 19.74/19.89  # Backward-rewritten                   : 1619
% 19.74/19.89  # Generated clauses                    : 2354913
% 19.74/19.89  # ...of the previous two non-trivial   : 1211982
% 19.74/19.89  # Contextual simplify-reflections      : 0
% 19.74/19.89  # Paramodulations                      : 2354913
% 19.74/19.89  # Factorizations                       : 0
% 19.74/19.89  # Equation resolutions                 : 0
% 19.74/19.89  # Propositional unsat checks           : 0
% 19.74/19.89  #    Propositional check models        : 0
% 19.74/19.89  #    Propositional check unsatisfiable : 0
% 19.74/19.89  #    Propositional clauses             : 0
% 19.74/19.89  #    Propositional clauses after purity: 0
% 19.74/19.89  #    Propositional unsat core size     : 0
% 19.74/19.89  #    Propositional preprocessing time  : 0.000
% 19.74/19.89  #    Propositional encoding time       : 0.000
% 19.74/19.89  #    Propositional solver time         : 0.000
% 19.74/19.89  #    Success case prop preproc time    : 0.000
% 19.74/19.89  #    Success case prop encoding time   : 0.000
% 19.74/19.89  #    Success case prop solver time     : 0.000
% 19.74/19.89  # Current number of processed clauses  : 1382
% 19.74/19.89  #    Positive orientable unit clauses  : 1366
% 19.74/19.89  #    Positive unorientable unit clauses: 15
% 19.74/19.89  #    Negative unit clauses             : 0
% 19.74/19.89  #    Non-unit-clauses                  : 1
% 19.74/19.89  # Current number of unprocessed clauses: 1149005
% 19.74/19.89  # ...number of literals in the above   : 1149005
% 19.74/19.89  # Current number of archived formulas  : 0
% 19.74/19.89  # Current number of archived clauses   : 1621
% 19.74/19.89  # Clause-clause subsumption calls (NU) : 0
% 19.74/19.89  # Rec. Clause-clause subsumption calls : 0
% 19.74/19.89  # Non-unit clause-clause subsumptions  : 0
% 19.74/19.89  # Unit Clause-clause subsumption calls : 7045
% 19.74/19.89  # Rewrite failures with RHS unbound    : 2569
% 19.74/19.89  # BW rewrite match attempts            : 86471
% 19.74/19.89  # BW rewrite match successes           : 5589
% 19.74/19.89  # Condensation attempts                : 0
% 19.74/19.89  # Condensation successes               : 0
% 19.74/19.89  # Termbank termtop insertions          : 51396420
% 19.76/19.96  
% 19.76/19.96  # -------------------------------------------------
% 19.76/19.96  # User time                : 18.819 s
% 19.76/19.96  # System time              : 0.794 s
% 19.76/19.96  # Total time               : 19.613 s
% 19.76/19.96  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
