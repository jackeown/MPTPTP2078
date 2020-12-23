%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:12 EST 2020

% Result     : Theorem 12.53s
% Output     : CNFRefutation 12.53s
% Verified   : 
% Statistics : Number of formulae       :  153 (27468 expanded)
%              Number of clauses        :  128 (12927 expanded)
%              Number of leaves         :   12 (7270 expanded)
%              Depth                    :   28
%              Number of atoms          :  153 (27468 expanded)
%              Number of equality atoms :  152 (27467 expanded)
%              Maximal formula depth    :    4 (   1 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(l98_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(t98_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(c_0_12,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k5_xboole_0(k5_xboole_0(X26,X27),k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_13,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X4] : k2_xboole_0(X4,X4) = X4 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k3_xboole_0(X15,X16)) = k4_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_18,plain,(
    ! [X7,X8] : k5_xboole_0(X7,X8) = k4_xboole_0(k2_xboole_0(X7,X8),k3_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[l98_xboole_1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,plain,(
    ! [X23,X24,X25] : k5_xboole_0(k5_xboole_0(X23,X24),X25) = k5_xboole_0(X23,k5_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X11] : k4_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_24,plain,(
    ! [X19,X20,X21] : k3_xboole_0(X19,k4_xboole_0(X20,X21)) = k4_xboole_0(k3_xboole_0(X19,X20),X21) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_25,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(X1,k4_xboole_0(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X12,X13,X14] : k4_xboole_0(k4_xboole_0(X12,X13),X14) = k4_xboole_0(X12,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_16]),c_0_20])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X1)))) = X1 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_16]),c_0_16])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_27])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_29])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,X1) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_38])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_39,c_0_27])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X2),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_40])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X1),X2)) = k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_40])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_41])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_38,c_0_41])).

fof(c_0_47,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_34]),c_0_38])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X2),X3)) = k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_43])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_34]),c_0_34])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_45]),c_0_46]),c_0_41])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_48]),c_0_34])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)) = k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_48]),c_0_44])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_20]),c_0_20])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))))))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_36]),c_0_36]),c_0_36]),c_0_36])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_53]),c_0_34])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_53]),c_0_43]),c_0_29]),c_0_54])).

fof(c_0_60,plain,(
    ! [X22] : k5_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))) = k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_27]),c_0_27])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_61]),c_0_42])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_62]),c_0_40]),c_0_29])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_63])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_34])).

cnf(c_0_68,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X2,X2)) = k4_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_65]),c_0_40])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_53])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_53]),c_0_29]),c_0_66]),c_0_46])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_72,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X2),X3)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_64])).

cnf(c_0_73,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X2),X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_69]),c_0_70]),c_0_34])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_64]),c_0_28])).

cnf(c_0_76,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,X2),X1),X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_37]),c_0_27]),c_0_27]),c_0_42])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_41])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X2),X1)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_64]),c_0_64]),c_0_48])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_74])).

cnf(c_0_80,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_34])).

cnf(c_0_81,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X2)),X3) = k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_36]),c_0_40]),c_0_29])).

cnf(c_0_82,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_40]),c_0_29]),c_0_40])).

cnf(c_0_83,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,X2),X1),X2) = k4_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_76]),c_0_63]),c_0_77])).

cnf(c_0_84,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X2)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_78]),c_0_46]),c_0_45]),c_0_38])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),X2)) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_79]),c_0_79])).

cnf(c_0_86,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_64]),c_0_54])).

cnf(c_0_87,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X1)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_75,c_0_80])).

cnf(c_0_88,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_64]),c_0_29])).

cnf(c_0_89,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_36]),c_0_36]),c_0_36])).

cnf(c_0_90,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,X1),X2))) = k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_44]),c_0_44]),c_0_64]),c_0_48])).

cnf(c_0_91,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2)),X2) = k4_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_83])).

cnf(c_0_92,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_84]),c_0_48]),c_0_64]),c_0_29]),c_0_51]),c_0_64]),c_0_29])).

cnf(c_0_93,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_85]),c_0_86]),c_0_29]),c_0_29]),c_0_46])).

cnf(c_0_94,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_87]),c_0_64]),c_0_29]),c_0_64]),c_0_29])).

cnf(c_0_95,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_29]),c_0_69]),c_0_29]),c_0_40]),c_0_29]),c_0_29]),c_0_69]),c_0_29])).

cnf(c_0_96,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_65]),c_0_53])).

cnf(c_0_97,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_64]),c_0_29]),c_0_94])).

cnf(c_0_98,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X1,X2),X2)) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_99,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_53])).

cnf(c_0_100,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_97]),c_0_40])).

cnf(c_0_101,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),X3)) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_27])).

cnf(c_0_102,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_99]),c_0_44]),c_0_36])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_74]),c_0_74])).

cnf(c_0_104,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X1,X1))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_80])).

cnf(c_0_105,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X2),X4))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_64]),c_0_36])).

cnf(c_0_106,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X1),X3) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_75]),c_0_64]),c_0_64])).

cnf(c_0_107,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2),X3)) = k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_42]),c_0_42])).

cnf(c_0_108,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X2)),k4_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X1,k4_xboole_0(X2,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_29])).

cnf(c_0_109,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_65])).

cnf(c_0_110,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X1)) = k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_75]),c_0_44])).

cnf(c_0_111,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2) = k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_37]),c_0_42])).

cnf(c_0_112,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)))) = k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_57]),c_0_102]),c_0_102]),c_0_40]),c_0_29])).

cnf(c_0_113,plain,
    ( k4_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_103]),c_0_29])).

cnf(c_0_114,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X2),X1)) = k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X2)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_64])).

cnf(c_0_115,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_71]),c_0_43])).

cnf(c_0_116,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X3),X1)) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_68])).

cnf(c_0_117,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X2),X4)) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_105]),c_0_28])).

cnf(c_0_118,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X2))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_36]),c_0_36])).

cnf(c_0_119,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_65]),c_0_36]),c_0_82]),c_0_109])).

cnf(c_0_120,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k5_xboole_0(X2,X1))) = k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(rw,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_121,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_112]),c_0_40])).

cnf(c_0_122,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_41]),c_0_27]),c_0_41])).

cnf(c_0_123,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_113]),c_0_36])).

cnf(c_0_124,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X2),X3),X1)) = k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_82]),c_0_87]),c_0_87])).

cnf(c_0_125,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X2),X3) = k4_xboole_0(k4_xboole_0(X1,X1),k5_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_111]),c_0_82])).

cnf(c_0_126,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_48])).

fof(c_0_127,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t98_xboole_1])).

cnf(c_0_128,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_64]),c_0_48])).

cnf(c_0_129,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X2)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_118]),c_0_28])).

cnf(c_0_130,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k5_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_82]),c_0_121])).

cnf(c_0_131,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)) = k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[c_0_122,c_0_113])).

cnf(c_0_132,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_123]),c_0_28])).

cnf(c_0_133,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X2),k5_xboole_0(X3,X1))) = k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_134,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),k5_xboole_0(X2,k5_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,X1),k5_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_68]),c_0_125]),c_0_45])).

cnf(c_0_135,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_126]),c_0_28])).

fof(c_0_136,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_127])])])).

cnf(c_0_137,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_37]),c_0_36]),c_0_42]),c_0_129])).

cnf(c_0_138,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1),k5_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_66]),c_0_113]),c_0_113])).

cnf(c_0_139,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(k1_xboole_0,X2),X2)) = k5_xboole_0(X1,k4_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_131])).

cnf(c_0_140,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3),X4)) = k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_42]),c_0_42])).

cnf(c_0_141,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X3),X1)) = k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X3,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_73])).

cnf(c_0_142,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X2)),X3))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_135]),c_0_36])).

cnf(c_0_143,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_136])).

cnf(c_0_144,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2)) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_27]),c_0_139]),c_0_46]),c_0_140]),c_0_141]),c_0_28]),c_0_27]),c_0_139]),c_0_46])).

cnf(c_0_145,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X2)),X3)) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_142]),c_0_28])).

cnf(c_0_146,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_143,c_0_20])).

cnf(c_0_147,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),k4_xboole_0(X3,X3)) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_144,c_0_27])).

cnf(c_0_148,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_64]),c_0_145])).

cnf(c_0_149,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_61])).

cnf(c_0_150,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_146,c_0_27])).

cnf(c_0_151,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_61]),c_0_36]),c_0_148]),c_0_48]),c_0_149])).

cnf(c_0_152,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_150,c_0_151])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:32:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 12.53/12.68  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 12.53/12.68  # and selection function SelectNewComplexAHP.
% 12.53/12.68  #
% 12.53/12.68  # Preprocessing time       : 0.027 s
% 12.53/12.68  # Presaturation interreduction done
% 12.53/12.68  
% 12.53/12.68  # Proof found!
% 12.53/12.68  # SZS status Theorem
% 12.53/12.68  # SZS output start CNFRefutation
% 12.53/12.68  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 12.53/12.68  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.53/12.68  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 12.53/12.68  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 12.53/12.68  fof(l98_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 12.53/12.68  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 12.53/12.68  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 12.53/12.68  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 12.53/12.68  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.53/12.68  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 12.53/12.68  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 12.53/12.68  fof(t98_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 12.53/12.68  fof(c_0_12, plain, ![X26, X27]:k2_xboole_0(X26,X27)=k5_xboole_0(k5_xboole_0(X26,X27),k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 12.53/12.68  fof(c_0_13, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 12.53/12.68  fof(c_0_14, plain, ![X4]:k2_xboole_0(X4,X4)=X4, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 12.53/12.68  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 12.53/12.68  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 12.53/12.68  fof(c_0_17, plain, ![X15, X16]:k4_xboole_0(X15,k3_xboole_0(X15,X16))=k4_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 12.53/12.68  fof(c_0_18, plain, ![X7, X8]:k5_xboole_0(X7,X8)=k4_xboole_0(k2_xboole_0(X7,X8),k3_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[l98_xboole_1])).
% 12.53/12.68  cnf(c_0_19, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 12.53/12.68  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 12.53/12.68  fof(c_0_21, plain, ![X23, X24, X25]:k5_xboole_0(k5_xboole_0(X23,X24),X25)=k5_xboole_0(X23,k5_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 12.53/12.68  cnf(c_0_22, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 12.53/12.68  fof(c_0_23, plain, ![X11]:k4_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t3_boole])).
% 12.53/12.68  fof(c_0_24, plain, ![X19, X20, X21]:k3_xboole_0(X19,k4_xboole_0(X20,X21))=k4_xboole_0(k3_xboole_0(X19,X20),X21), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 12.53/12.68  cnf(c_0_25, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 12.53/12.68  cnf(c_0_26, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k4_xboole_0(X1,k4_xboole_0(X1,X1)))=X1), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 12.53/12.68  cnf(c_0_27, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 12.53/12.68  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_16])).
% 12.53/12.68  cnf(c_0_29, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 12.53/12.68  fof(c_0_30, plain, ![X12, X13, X14]:k4_xboole_0(k4_xboole_0(X12,X13),X14)=k4_xboole_0(X12,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 12.53/12.68  cnf(c_0_31, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 12.53/12.68  cnf(c_0_32, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_16]), c_0_20])).
% 12.53/12.68  cnf(c_0_33, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X1))))=X1), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 12.53/12.68  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 12.53/12.68  cnf(c_0_35, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 12.53/12.68  cnf(c_0_36, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_16]), c_0_16])).
% 12.53/12.68  cnf(c_0_37, plain, (k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_27])).
% 12.53/12.68  cnf(c_0_38, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 12.53/12.68  cnf(c_0_39, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[c_0_35, c_0_20])).
% 12.53/12.68  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)))=k4_xboole_0(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_36, c_0_29])).
% 12.53/12.68  cnf(c_0_41, plain, (k5_xboole_0(X1,X1)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_38])).
% 12.53/12.68  cnf(c_0_42, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_39, c_0_27])).
% 12.53/12.68  cnf(c_0_43, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3)))=k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X2),X3)), inference(spm,[status(thm)],[c_0_36, c_0_40])).
% 12.53/12.68  cnf(c_0_44, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X1),X2))=k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_28, c_0_40])).
% 12.53/12.68  cnf(c_0_45, plain, (k5_xboole_0(k4_xboole_0(X1,X1),X2)=k5_xboole_0(X1,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_27, c_0_41])).
% 12.53/12.68  cnf(c_0_46, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[c_0_38, c_0_41])).
% 12.53/12.68  fof(c_0_47, plain, ![X9, X10]:k2_xboole_0(X9,k4_xboole_0(X10,X9))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 12.53/12.68  cnf(c_0_48, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_34]), c_0_38])).
% 12.53/12.68  cnf(c_0_49, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X2),X3))=k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3))), inference(spm,[status(thm)],[c_0_28, c_0_43])).
% 12.53/12.68  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_34]), c_0_34])).
% 12.53/12.68  cnf(c_0_51, plain, (k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_45]), c_0_46]), c_0_41])).
% 12.53/12.68  cnf(c_0_52, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 12.53/12.68  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_48]), c_0_34])).
% 12.53/12.68  cnf(c_0_54, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2))=k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_48]), c_0_44])).
% 12.53/12.68  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)))=X1), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 12.53/12.68  cnf(c_0_56, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_20]), c_0_20])).
% 12.53/12.68  cnf(c_0_57, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))))))))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_36]), c_0_36]), c_0_36]), c_0_36])).
% 12.53/12.68  cnf(c_0_58, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_53]), c_0_34])).
% 12.53/12.68  cnf(c_0_59, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_53]), c_0_43]), c_0_29]), c_0_54])).
% 12.53/12.68  fof(c_0_60, plain, ![X22]:k5_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t5_boole])).
% 12.53/12.68  cnf(c_0_61, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))))=k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_27]), c_0_27])).
% 12.53/12.68  cnf(c_0_62, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1)))=k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 12.53/12.68  cnf(c_0_63, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_60])).
% 12.53/12.68  cnf(c_0_64, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_61]), c_0_42])).
% 12.53/12.68  cnf(c_0_65, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_62]), c_0_40]), c_0_29])).
% 12.53/12.68  cnf(c_0_66, plain, (k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_63])).
% 12.53/12.68  cnf(c_0_67, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_64, c_0_34])).
% 12.53/12.68  cnf(c_0_68, plain, (k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X2,X2))=k4_xboole_0(k4_xboole_0(X1,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_65]), c_0_40])).
% 12.53/12.68  cnf(c_0_69, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k1_xboole_0,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_64, c_0_53])).
% 12.53/12.68  cnf(c_0_70, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_53]), c_0_29]), c_0_66]), c_0_46])).
% 12.53/12.68  cnf(c_0_71, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_36, c_0_28])).
% 12.53/12.68  cnf(c_0_72, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X2),X3))=k5_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X1),X3)), inference(spm,[status(thm)],[c_0_45, c_0_64])).
% 12.53/12.68  cnf(c_0_73, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X2),X1))=k4_xboole_0(X1,k4_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 12.53/12.68  cnf(c_0_74, plain, (k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_69]), c_0_70]), c_0_34])).
% 12.53/12.68  cnf(c_0_75, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2)=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_64]), c_0_28])).
% 12.53/12.68  cnf(c_0_76, plain, (k5_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,X2),X1),X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X2,X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_37]), c_0_27]), c_0_27]), c_0_42])).
% 12.53/12.68  cnf(c_0_77, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k4_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_27, c_0_41])).
% 12.53/12.68  cnf(c_0_78, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X2),X1))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_64]), c_0_64]), c_0_48])).
% 12.53/12.68  cnf(c_0_79, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_74])).
% 12.53/12.68  cnf(c_0_80, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_75, c_0_34])).
% 12.53/12.68  cnf(c_0_81, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X2)),X3)=k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_36]), c_0_40]), c_0_29])).
% 12.53/12.68  cnf(c_0_82, plain, (k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))=k4_xboole_0(k4_xboole_0(X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_40]), c_0_29]), c_0_40])).
% 12.53/12.68  cnf(c_0_83, plain, (k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,X2),X1),X2)=k4_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_76]), c_0_63]), c_0_77])).
% 12.53/12.68  cnf(c_0_84, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X2)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_78]), c_0_46]), c_0_45]), c_0_38])).
% 12.53/12.68  cnf(c_0_85, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)),X2))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_79]), c_0_79])).
% 12.53/12.68  cnf(c_0_86, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_64]), c_0_54])).
% 12.53/12.68  cnf(c_0_87, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,X1))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_75, c_0_80])).
% 12.53/12.68  cnf(c_0_88, plain, (k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)))=k4_xboole_0(k4_xboole_0(X1,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_64]), c_0_29])).
% 12.53/12.68  cnf(c_0_89, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)))))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_36]), c_0_36]), c_0_36])).
% 12.53/12.68  cnf(c_0_90, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,X1),X2)))=k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_44]), c_0_44]), c_0_64]), c_0_48])).
% 12.53/12.68  cnf(c_0_91, plain, (k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2)),X2)=k4_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_48, c_0_83])).
% 12.53/12.68  cnf(c_0_92, plain, (k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)))=k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_84]), c_0_48]), c_0_64]), c_0_29]), c_0_51]), c_0_64]), c_0_29])).
% 12.53/12.68  cnf(c_0_93, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_85]), c_0_86]), c_0_29]), c_0_29]), c_0_46])).
% 12.53/12.68  cnf(c_0_94, plain, (k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))=k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_87]), c_0_64]), c_0_29]), c_0_64]), c_0_29])).
% 12.53/12.68  cnf(c_0_95, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))))=k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_29]), c_0_69]), c_0_29]), c_0_40]), c_0_29]), c_0_29]), c_0_69]), c_0_29])).
% 12.53/12.68  cnf(c_0_96, plain, (k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_65]), c_0_53])).
% 12.53/12.68  cnf(c_0_97, plain, (k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)),X2)=k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_64]), c_0_29]), c_0_94])).
% 12.53/12.68  cnf(c_0_98, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X1,X2),X2))=k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 12.53/12.68  cnf(c_0_99, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k1_xboole_0,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_75, c_0_53])).
% 12.53/12.68  cnf(c_0_100, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X2,X3)),X3)=k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_97]), c_0_40])).
% 12.53/12.68  cnf(c_0_101, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),X3))=k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_98, c_0_27])).
% 12.53/12.68  cnf(c_0_102, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))))=k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_99]), c_0_44]), c_0_36])).
% 12.53/12.68  cnf(c_0_103, plain, (k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_74]), c_0_74])).
% 12.53/12.68  cnf(c_0_104, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X1,X1)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_64, c_0_80])).
% 12.53/12.68  cnf(c_0_105, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X2),X4)))=k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_64]), c_0_36])).
% 12.53/12.68  cnf(c_0_106, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X1),X3)=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_75]), c_0_64]), c_0_64])).
% 12.53/12.68  cnf(c_0_107, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2),X3))=k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_42]), c_0_42])).
% 12.53/12.68  cnf(c_0_108, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X2)),k4_xboole_0(k1_xboole_0,X2))=k4_xboole_0(X1,k4_xboole_0(X2,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_29])).
% 12.53/12.68  cnf(c_0_109, plain, (k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2))=k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_54, c_0_65])).
% 12.53/12.68  cnf(c_0_110, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X1))=k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_75]), c_0_44])).
% 12.53/12.68  cnf(c_0_111, plain, (k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)=k4_xboole_0(k1_xboole_0,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_37]), c_0_42])).
% 12.53/12.68  cnf(c_0_112, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))))=k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_57]), c_0_102]), c_0_102]), c_0_40]), c_0_29])).
% 12.53/12.68  cnf(c_0_113, plain, (k4_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_103]), c_0_29])).
% 12.53/12.68  cnf(c_0_114, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),X2),X1))=k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X2))), inference(spm,[status(thm)],[c_0_73, c_0_64])).
% 12.53/12.68  cnf(c_0_115, plain, (k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,X2),X3)))=k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_71]), c_0_43])).
% 12.53/12.68  cnf(c_0_116, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X3),X1))=k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X3))), inference(spm,[status(thm)],[c_0_104, c_0_68])).
% 12.53/12.68  cnf(c_0_117, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X2),X4))=k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_105]), c_0_28])).
% 12.53/12.68  cnf(c_0_118, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X2)))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_36]), c_0_36])).
% 12.53/12.68  cnf(c_0_119, plain, (k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X2))=k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_65]), c_0_36]), c_0_82]), c_0_109])).
% 12.53/12.68  cnf(c_0_120, plain, (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,k5_xboole_0(X2,X1)))=k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))), inference(rw,[status(thm)],[c_0_110, c_0_111])).
% 12.53/12.68  cnf(c_0_121, plain, (k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)))=k4_xboole_0(k4_xboole_0(X1,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_112]), c_0_40])).
% 12.53/12.68  cnf(c_0_122, plain, (k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(k1_xboole_0,X1))=k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_41]), c_0_27]), c_0_41])).
% 12.53/12.68  cnf(c_0_123, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3)))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_113]), c_0_36])).
% 12.53/12.68  cnf(c_0_124, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k4_xboole_0(X2,X2),X3),X1))=k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_82]), c_0_87]), c_0_87])).
% 12.53/12.68  cnf(c_0_125, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),X2),X3)=k4_xboole_0(k4_xboole_0(X1,X1),k5_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_111]), c_0_82])).
% 12.53/12.68  cnf(c_0_126, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X2))))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_36, c_0_48])).
% 12.53/12.68  fof(c_0_127, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(assume_negation,[status(cth)],[t98_xboole_1])).
% 12.53/12.68  cnf(c_0_128, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_64]), c_0_48])).
% 12.53/12.68  cnf(c_0_129, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X1),X2))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_118]), c_0_28])).
% 12.53/12.68  cnf(c_0_130, plain, (k4_xboole_0(k4_xboole_0(X1,X1),k5_xboole_0(X2,X1))=k4_xboole_0(k4_xboole_0(X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_82]), c_0_121])).
% 12.53/12.68  cnf(c_0_131, plain, (k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X1))=k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[c_0_122, c_0_113])).
% 12.53/12.68  cnf(c_0_132, plain, (k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_123]), c_0_28])).
% 12.53/12.68  cnf(c_0_133, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X2),k5_xboole_0(X3,X1)))=k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X2),X3))), inference(rw,[status(thm)],[c_0_124, c_0_125])).
% 12.53/12.68  cnf(c_0_134, plain, (k4_xboole_0(k4_xboole_0(X1,X1),k5_xboole_0(X2,k5_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,X1),k5_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_68]), c_0_125]), c_0_45])).
% 12.53/12.68  cnf(c_0_135, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_126]), c_0_28])).
% 12.53/12.68  fof(c_0_136, negated_conjecture, k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_127])])])).
% 12.53/12.68  cnf(c_0_137, plain, (k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_37]), c_0_36]), c_0_42]), c_0_129])).
% 12.53/12.68  cnf(c_0_138, plain, (k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1),k5_xboole_0(X2,X1))=k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_66]), c_0_113]), c_0_113])).
% 12.53/12.68  cnf(c_0_139, plain, (k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(k1_xboole_0,X2),X2))=k5_xboole_0(X1,k4_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_66, c_0_131])).
% 12.53/12.68  cnf(c_0_140, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(k5_xboole_0(k1_xboole_0,X2),X3),X4))=k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_42]), c_0_42])).
% 12.53/12.68  cnf(c_0_141, plain, (k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X3,X3),X1))=k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X3,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_73])).
% 12.53/12.68  cnf(c_0_142, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X2)),X3)))=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_135]), c_0_36])).
% 12.53/12.68  cnf(c_0_143, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_136])).
% 12.53/12.68  cnf(c_0_144, plain, (k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X2))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_27]), c_0_139]), c_0_46]), c_0_140]), c_0_141]), c_0_28]), c_0_27]), c_0_139]), c_0_46])).
% 12.53/12.68  cnf(c_0_145, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X2)),X3))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_142]), c_0_28])).
% 12.53/12.68  cnf(c_0_146, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[c_0_143, c_0_20])).
% 12.53/12.68  cnf(c_0_147, plain, (k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),k4_xboole_0(X3,X3))=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_144, c_0_27])).
% 12.53/12.68  cnf(c_0_148, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X1,X2))))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_64]), c_0_145])).
% 12.53/12.68  cnf(c_0_149, plain, (k4_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_37, c_0_61])).
% 12.53/12.68  cnf(c_0_150, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))))!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[c_0_146, c_0_27])).
% 12.53/12.68  cnf(c_0_151, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_61]), c_0_36]), c_0_148]), c_0_48]), c_0_149])).
% 12.53/12.68  cnf(c_0_152, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_150, c_0_151])]), ['proof']).
% 12.53/12.68  # SZS output end CNFRefutation
% 12.53/12.68  # Proof object total steps             : 153
% 12.53/12.68  # Proof object clause steps            : 128
% 12.53/12.68  # Proof object formula steps           : 25
% 12.53/12.68  # Proof object conjectures             : 7
% 12.53/12.68  # Proof object clause conjectures      : 4
% 12.53/12.68  # Proof object formula conjectures     : 3
% 12.53/12.68  # Proof object initial clauses used    : 12
% 12.53/12.68  # Proof object initial formulas used   : 12
% 12.53/12.68  # Proof object generating inferences   : 95
% 12.53/12.68  # Proof object simplifying inferences  : 164
% 12.53/12.68  # Training examples: 0 positive, 0 negative
% 12.53/12.68  # Parsed axioms                        : 13
% 12.53/12.68  # Removed by relevancy pruning/SinE    : 0
% 12.53/12.68  # Initial clauses                      : 14
% 12.53/12.68  # Removed in clause preprocessing      : 2
% 12.53/12.68  # Initial clauses in saturation        : 12
% 12.53/12.68  # Processed clauses                    : 12689
% 12.53/12.68  # ...of these trivial                  : 2502
% 12.53/12.68  # ...subsumed                          : 8800
% 12.53/12.68  # ...remaining for further processing  : 1387
% 12.53/12.68  # Other redundant clauses eliminated   : 0
% 12.53/12.68  # Clauses deleted for lack of memory   : 0
% 12.53/12.68  # Backward-subsumed                    : 23
% 12.53/12.68  # Backward-rewritten                   : 541
% 12.53/12.68  # Generated clauses                    : 1003903
% 12.53/12.68  # ...of the previous two non-trivial   : 689016
% 12.53/12.68  # Contextual simplify-reflections      : 0
% 12.53/12.68  # Paramodulations                      : 1003883
% 12.53/12.68  # Factorizations                       : 0
% 12.53/12.68  # Equation resolutions                 : 20
% 12.53/12.68  # Propositional unsat checks           : 0
% 12.53/12.68  #    Propositional check models        : 0
% 12.53/12.68  #    Propositional check unsatisfiable : 0
% 12.53/12.68  #    Propositional clauses             : 0
% 12.53/12.68  #    Propositional clauses after purity: 0
% 12.53/12.68  #    Propositional unsat core size     : 0
% 12.53/12.68  #    Propositional preprocessing time  : 0.000
% 12.53/12.68  #    Propositional encoding time       : 0.000
% 12.53/12.68  #    Propositional solver time         : 0.000
% 12.53/12.68  #    Success case prop preproc time    : 0.000
% 12.53/12.68  #    Success case prop encoding time   : 0.000
% 12.53/12.68  #    Success case prop solver time     : 0.000
% 12.53/12.68  # Current number of processed clauses  : 811
% 12.53/12.68  #    Positive orientable unit clauses  : 633
% 12.53/12.68  #    Positive unorientable unit clauses: 3
% 12.53/12.68  #    Negative unit clauses             : 0
% 12.53/12.68  #    Non-unit-clauses                  : 175
% 12.53/12.68  # Current number of unprocessed clauses: 673366
% 12.53/12.68  # ...number of literals in the above   : 796320
% 12.53/12.68  # Current number of archived formulas  : 0
% 12.53/12.68  # Current number of archived clauses   : 578
% 12.53/12.68  # Clause-clause subsumption calls (NU) : 110353
% 12.53/12.68  # Rec. Clause-clause subsumption calls : 110353
% 12.53/12.68  # Non-unit clause-clause subsumptions  : 8762
% 12.53/12.68  # Unit Clause-clause subsumption calls : 1747
% 12.53/12.68  # Rewrite failures with RHS unbound    : 0
% 12.53/12.68  # BW rewrite match attempts            : 27014
% 12.53/12.68  # BW rewrite match successes           : 517
% 12.53/12.68  # Condensation attempts                : 0
% 12.53/12.68  # Condensation successes               : 0
% 12.53/12.68  # Termbank termtop insertions          : 25285382
% 12.57/12.72  
% 12.57/12.72  # -------------------------------------------------
% 12.57/12.72  # User time                : 11.876 s
% 12.57/12.72  # System time              : 0.508 s
% 12.57/12.72  # Total time               : 12.385 s
% 12.57/12.72  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
