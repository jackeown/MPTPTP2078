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
% DateTime   : Thu Dec  3 10:34:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 613 expanded)
%              Number of clauses        :   63 ( 270 expanded)
%              Number of leaves         :   16 ( 171 expanded)
%              Depth                    :   17
%              Number of atoms          :   96 ( 613 expanded)
%              Number of equality atoms :   95 ( 612 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t95_xboole_1,conjecture,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(c_0_16,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k3_xboole_0(X19,X20)) = k4_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_17,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_18,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_19,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_20,plain,(
    ! [X14] : k3_xboole_0(X14,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_21,plain,(
    ! [X29,X30] : k2_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(X29,X30)) = X29 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k3_xboole_0(X12,X13)) = X12 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_24]),c_0_22])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

fof(c_0_32,plain,(
    ! [X16,X17,X18] : k4_xboole_0(k4_xboole_0(X16,X17),X18) = k4_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_26])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_37,plain,(
    ! [X11] : k2_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_38,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_39,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_40,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_41,plain,(
    ! [X23,X24,X25] : k3_xboole_0(X23,k4_xboole_0(X24,X25)) = k4_xboole_0(k3_xboole_0(X23,X24),X25) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_38]),c_0_25])).

cnf(c_0_46,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_23])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_31]),c_0_45])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_47])).

fof(c_0_52,plain,(
    ! [X31,X32] : k2_xboole_0(X31,X32) = k2_xboole_0(k5_xboole_0(X31,X32),k3_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X3)) = k4_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k5_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_50]),c_0_44]),c_0_51])).

fof(c_0_55,plain,(
    ! [X26,X27,X28] : k2_xboole_0(k2_xboole_0(X26,X27),X28) = k2_xboole_0(X26,k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k3_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_24]),c_0_48])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_29]),c_0_24])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_24])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_56,c_0_46])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_23])).

cnf(c_0_64,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_50]),c_0_44]),c_0_23])).

cnf(c_0_65,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_47]),c_0_24]),c_0_58])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_59,c_0_48])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X2,X1))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_60]),c_0_24])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_61,c_0_33])).

cnf(c_0_69,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_23])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_61])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_65]),c_0_22])).

fof(c_0_72,plain,(
    ! [X10] : k2_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_73,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,k2_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_23])).

cnf(c_0_74,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_75,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_51])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_77,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X1,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_23]),c_0_75])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_62])).

cnf(c_0_79,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_76])).

cnf(c_0_80,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_58])).

cnf(c_0_81,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X1,k2_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_46])).

cnf(c_0_82,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k3_xboole_0(X2,k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_23]),c_0_48])).

cnf(c_0_83,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

fof(c_0_84,negated_conjecture,(
    ~ ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t95_xboole_1])).

cnf(c_0_85,plain,
    ( k3_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_34]),c_0_82])).

cnf(c_0_86,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_46])).

fof(c_0_87,negated_conjecture,(
    k3_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_84])])])).

cnf(c_0_88,plain,
    ( k4_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_85]),c_0_36]),c_0_86]),c_0_34])).

cnf(c_0_89,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_46])).

cnf(c_0_90,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_88]),c_0_89]),c_0_44])).

cnf(c_0_92,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_51])).

cnf(c_0_93,negated_conjecture,
    ( k5_xboole_0(k2_xboole_0(esk1_0,esk2_0),k5_xboole_0(esk1_0,esk2_0)) != k3_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_90,c_0_51])).

cnf(c_0_94,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_62]),c_0_51]),c_0_48]),c_0_92]),c_0_58])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.20/0.43  # and selection function SelectNewComplexAHP.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.026 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.20/0.43  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.43  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.43  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.43  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.43  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.20/0.43  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.20/0.43  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.20/0.43  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.43  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.43  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.20/0.43  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.43  fof(t93_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 0.20/0.43  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.20/0.43  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.20/0.43  fof(t95_xboole_1, conjecture, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.43  fof(c_0_16, plain, ![X19, X20]:k4_xboole_0(X19,k3_xboole_0(X19,X20))=k4_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.20/0.43  fof(c_0_17, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.43  fof(c_0_18, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.43  fof(c_0_19, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.43  fof(c_0_20, plain, ![X14]:k3_xboole_0(X14,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.43  fof(c_0_21, plain, ![X29, X30]:k2_xboole_0(k3_xboole_0(X29,X30),k4_xboole_0(X29,X30))=X29, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.20/0.43  cnf(c_0_22, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.43  cnf(c_0_23, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.43  cnf(c_0_25, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_26, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  fof(c_0_27, plain, ![X12, X13]:k2_xboole_0(X12,k3_xboole_0(X12,X13))=X12, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.20/0.43  cnf(c_0_28, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_29, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.43  cnf(c_0_30, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_24]), c_0_22])).
% 0.20/0.43  cnf(c_0_31, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.20/0.43  fof(c_0_32, plain, ![X16, X17, X18]:k4_xboole_0(k4_xboole_0(X16,X17),X18)=k4_xboole_0(X16,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.20/0.43  cnf(c_0_33, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.43  cnf(c_0_34, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_25]), c_0_26])).
% 0.20/0.43  cnf(c_0_35, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.20/0.43  cnf(c_0_36, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  fof(c_0_37, plain, ![X11]:k2_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.43  cnf(c_0_38, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.43  fof(c_0_39, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.43  fof(c_0_40, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.20/0.43  fof(c_0_41, plain, ![X23, X24, X25]:k3_xboole_0(X23,k4_xboole_0(X24,X25))=k4_xboole_0(k3_xboole_0(X23,X24),X25), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.43  cnf(c_0_42, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_28, c_0_23])).
% 0.20/0.43  cnf(c_0_43, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.43  cnf(c_0_44, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.43  cnf(c_0_45, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_38]), c_0_25])).
% 0.20/0.43  cnf(c_0_46, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.43  cnf(c_0_47, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.43  cnf(c_0_48, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.43  cnf(c_0_49, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_23])).
% 0.20/0.43  cnf(c_0_50, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_31]), c_0_45])).
% 0.20/0.43  cnf(c_0_51, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_47])).
% 0.20/0.43  fof(c_0_52, plain, ![X31, X32]:k2_xboole_0(X31,X32)=k2_xboole_0(k5_xboole_0(X31,X32),k3_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t93_xboole_1])).
% 0.20/0.43  cnf(c_0_53, plain, (k3_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X3))=k4_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.43  cnf(c_0_54, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k5_xboole_0(X1,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_50]), c_0_44]), c_0_51])).
% 0.20/0.43  fof(c_0_55, plain, ![X26, X27, X28]:k2_xboole_0(k2_xboole_0(X26,X27),X28)=k2_xboole_0(X26,k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.20/0.43  cnf(c_0_56, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.43  cnf(c_0_57, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k3_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_24]), c_0_48])).
% 0.20/0.43  cnf(c_0_58, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_29]), c_0_24])).
% 0.20/0.43  cnf(c_0_59, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_24])).
% 0.20/0.43  cnf(c_0_60, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.43  cnf(c_0_61, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.43  cnf(c_0_62, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_56, c_0_46])).
% 0.20/0.43  cnf(c_0_63, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_33, c_0_23])).
% 0.20/0.43  cnf(c_0_64, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_50]), c_0_44]), c_0_23])).
% 0.20/0.43  cnf(c_0_65, plain, (k4_xboole_0(X1,k5_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_47]), c_0_24]), c_0_58])).
% 0.20/0.43  cnf(c_0_66, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_59, c_0_48])).
% 0.20/0.43  cnf(c_0_67, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X2,X1)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_60]), c_0_24])).
% 0.20/0.43  cnf(c_0_68, plain, (k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3))=k2_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_61, c_0_33])).
% 0.20/0.43  cnf(c_0_69, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_62, c_0_23])).
% 0.20/0.43  cnf(c_0_70, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_61])).
% 0.20/0.43  cnf(c_0_71, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_65]), c_0_22])).
% 0.20/0.43  fof(c_0_72, plain, ![X10]:k2_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.20/0.43  cnf(c_0_73, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,k2_xboole_0(X2,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_23])).
% 0.20/0.43  cnf(c_0_74, plain, (k2_xboole_0(X1,k5_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.20/0.43  cnf(c_0_75, plain, (k3_xboole_0(X1,k5_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_71, c_0_51])).
% 0.20/0.43  cnf(c_0_76, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.43  cnf(c_0_77, plain, (k3_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X1,k2_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_23]), c_0_75])).
% 0.20/0.43  cnf(c_0_78, plain, (k4_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_62])).
% 0.20/0.43  cnf(c_0_79, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_61, c_0_76])).
% 0.20/0.43  cnf(c_0_80, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_63, c_0_58])).
% 0.20/0.43  cnf(c_0_81, plain, (k3_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X1,k2_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_46])).
% 0.20/0.43  cnf(c_0_82, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k3_xboole_0(X2,k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_23]), c_0_48])).
% 0.20/0.43  cnf(c_0_83, plain, (k4_xboole_0(k5_xboole_0(X1,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.20/0.43  fof(c_0_84, negated_conjecture, ~(![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t95_xboole_1])).
% 0.20/0.43  cnf(c_0_85, plain, (k3_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_34]), c_0_82])).
% 0.20/0.43  cnf(c_0_86, plain, (k4_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_46])).
% 0.20/0.43  fof(c_0_87, negated_conjecture, k3_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_84])])])).
% 0.20/0.43  cnf(c_0_88, plain, (k4_xboole_0(k5_xboole_0(X1,k2_xboole_0(X2,X1)),X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_85]), c_0_36]), c_0_86]), c_0_34])).
% 0.20/0.43  cnf(c_0_89, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_60, c_0_46])).
% 0.20/0.43  cnf(c_0_90, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.20/0.43  cnf(c_0_91, plain, (k5_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_88]), c_0_89]), c_0_44])).
% 0.20/0.43  cnf(c_0_92, plain, (k4_xboole_0(X1,k5_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_65, c_0_51])).
% 0.20/0.43  cnf(c_0_93, negated_conjecture, (k5_xboole_0(k2_xboole_0(esk1_0,esk2_0),k5_xboole_0(esk1_0,esk2_0))!=k3_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_90, c_0_51])).
% 0.20/0.43  cnf(c_0_94, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_62]), c_0_51]), c_0_48]), c_0_92]), c_0_58])).
% 0.20/0.43  cnf(c_0_95, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 96
% 0.20/0.43  # Proof object clause steps            : 63
% 0.20/0.43  # Proof object formula steps           : 33
% 0.20/0.43  # Proof object conjectures             : 6
% 0.20/0.43  # Proof object clause conjectures      : 3
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 16
% 0.20/0.43  # Proof object initial formulas used   : 16
% 0.20/0.43  # Proof object generating inferences   : 42
% 0.20/0.43  # Proof object simplifying inferences  : 42
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 16
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 16
% 0.20/0.43  # Removed in clause preprocessing      : 0
% 0.20/0.43  # Initial clauses in saturation        : 16
% 0.20/0.43  # Processed clauses                    : 637
% 0.20/0.43  # ...of these trivial                  : 321
% 0.20/0.43  # ...subsumed                          : 127
% 0.20/0.43  # ...remaining for further processing  : 189
% 0.20/0.43  # Other redundant clauses eliminated   : 0
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 0
% 0.20/0.43  # Backward-rewritten                   : 50
% 0.20/0.43  # Generated clauses                    : 8704
% 0.20/0.43  # ...of the previous two non-trivial   : 4347
% 0.20/0.43  # Contextual simplify-reflections      : 0
% 0.20/0.43  # Paramodulations                      : 8704
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 0
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 123
% 0.20/0.43  #    Positive orientable unit clauses  : 119
% 0.20/0.43  #    Positive unorientable unit clauses: 4
% 0.20/0.43  #    Negative unit clauses             : 0
% 0.20/0.43  #    Non-unit-clauses                  : 0
% 0.20/0.43  # Current number of unprocessed clauses: 3598
% 0.20/0.43  # ...number of literals in the above   : 3598
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 66
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.43  # Unit Clause-clause subsumption calls : 6
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 277
% 0.20/0.43  # BW rewrite match successes           : 126
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 62551
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.084 s
% 0.20/0.43  # System time              : 0.004 s
% 0.20/0.43  # Total time               : 0.089 s
% 0.20/0.43  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
