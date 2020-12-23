%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:58 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 (85673 expanded)
%              Number of clauses        :  100 (37198 expanded)
%              Number of leaves         :    9 (24237 expanded)
%              Depth                    :   27
%              Number of atoms          :  119 (85673 expanded)
%              Number of equality atoms :  118 (85672 expanded)
%              Maximal formula depth    :    4 (   1 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(t94_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(c_0_9,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_10,plain,(
    ! [X10] : k4_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_11,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_12,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X11,X12,X13] : k4_xboole_0(k4_xboole_0(X11,X12),X13) = k4_xboole_0(X11,k2_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_14,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k3_xboole_0(X14,X15)) = k4_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X1) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_16])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_18]),c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_24])).

fof(c_0_29,plain,(
    ! [X18,X19] : k2_xboole_0(X18,X19) = k2_xboole_0(k5_xboole_0(X18,X19),k3_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),k3_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_23]),c_0_23])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),X1) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_25]),c_0_24])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_24])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_27]),c_0_16]),c_0_26])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_27])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_24])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_22]),c_0_18])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_31]),c_0_32]),c_0_15]),c_0_24])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_25]),c_0_18])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_23]),c_0_22]),c_0_15])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_33])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_34]),c_0_22]),c_0_18])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_16])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_36])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_37]),c_0_23]),c_0_24])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,X1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_36])).

cnf(c_0_48,plain,
    ( k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X1)) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_40]),c_0_36])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_16,c_0_45])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_27]),c_0_20])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_42]),c_0_42])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X1,X1)) = k2_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,X1) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_47]),c_0_37]),c_0_48]),c_0_49])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_42])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_16])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_24])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = k2_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_59,plain,
    ( k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_15]),c_0_56]),c_0_57])).

cnf(c_0_60,plain,
    ( k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k2_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_58]),c_0_49])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_21])).

cnf(c_0_62,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_59])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X1),k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_16,c_0_60])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k5_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_54]),c_0_32]),c_0_15])).

cnf(c_0_65,plain,
    ( k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),k5_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_61])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),X1) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_32]),c_0_18])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_64]),c_0_32]),c_0_15])).

cnf(c_0_69,plain,
    ( k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),k5_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_65,c_0_45])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_66]),c_0_56]),c_0_23]),c_0_67]),c_0_36]),c_0_53])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_68,c_0_58])).

cnf(c_0_72,plain,
    ( k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_69,c_0_58])).

cnf(c_0_73,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_70]),c_0_71]),c_0_54])).

cnf(c_0_74,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_75,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X1),k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_16,c_0_72])).

cnf(c_0_76,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_24])).

cnf(c_0_77,plain,
    ( k2_xboole_0(X1,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_58])).

cnf(c_0_78,plain,
    ( k4_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_77])).

cnf(c_0_79,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k4_xboole_0(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_16])).

cnf(c_0_80,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_58])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,k1_xboole_0))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_23]),c_0_40])).

cnf(c_0_82,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_80]),c_0_18])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_24])).

cnf(c_0_84,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_59])).

cnf(c_0_85,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_24])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_14]),c_0_14])).

cnf(c_0_87,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X1),X2) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_82])).

cnf(c_0_88,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X1,k4_xboole_0(X1,X2))) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_27])).

cnf(c_0_89,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_83]),c_0_18])).

cnf(c_0_90,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_84]),c_0_85])).

cnf(c_0_91,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_18]),c_0_20]),c_0_50]),c_0_59]),c_0_16]),c_0_86])).

cnf(c_0_92,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_87]),c_0_87]),c_0_40])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_53]),c_0_90]),c_0_91]),c_0_92])).

cnf(c_0_94,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_22]),c_0_20])).

cnf(c_0_95,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_20]),c_0_20])).

cnf(c_0_96,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_92]),c_0_18])).

cnf(c_0_97,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_14])).

cnf(c_0_98,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_18]),c_0_27])).

cnf(c_0_99,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_90])).

cnf(c_0_100,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3)) = k3_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_94]),c_0_18])).

cnf(c_0_101,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_92]),c_0_28]),c_0_59]),c_0_24])).

cnf(c_0_102,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_24]),c_0_97])).

cnf(c_0_103,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,X2))) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_14]),c_0_20])).

fof(c_0_104,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t94_xboole_1])).

cnf(c_0_105,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_98,c_0_24])).

cnf(c_0_106,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_27]),c_0_42]),c_0_42]),c_0_99]),c_0_100]),c_0_42])).

cnf(c_0_107,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X1))) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_101])).

cnf(c_0_108,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k5_xboole_0(X1,X2),X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_102])).

cnf(c_0_109,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_43]),c_0_56]),c_0_59]),c_0_103])).

fof(c_0_110,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_104])])])).

cnf(c_0_111,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107])).

cnf(c_0_112,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_92]),c_0_102])).

cnf(c_0_113,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_109]),c_0_15])).

cnf(c_0_114,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_115,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_90]),c_0_113])).

cnf(c_0_116,negated_conjecture,
    ( k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k5_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_114,c_0_86])).

cnf(c_0_117,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_115]),c_0_112]),c_0_43])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116,c_0_117])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:38:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.49  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.21/0.49  # and selection function SelectNewComplexAHP.
% 0.21/0.49  #
% 0.21/0.49  # Preprocessing time       : 0.025 s
% 0.21/0.49  # Presaturation interreduction done
% 0.21/0.49  
% 0.21/0.49  # Proof found!
% 0.21/0.49  # SZS status Theorem
% 0.21/0.49  # SZS output start CNFRefutation
% 0.21/0.49  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.21/0.49  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.21/0.49  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.21/0.49  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.49  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.21/0.49  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.21/0.49  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.49  fof(t93_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 0.21/0.49  fof(t94_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.21/0.49  fof(c_0_9, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.21/0.49  fof(c_0_10, plain, ![X10]:k4_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.21/0.49  fof(c_0_11, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.21/0.49  fof(c_0_12, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.49  fof(c_0_13, plain, ![X11, X12, X13]:k4_xboole_0(k4_xboole_0(X11,X12),X13)=k4_xboole_0(X11,k2_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.21/0.49  cnf(c_0_14, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.49  cnf(c_0_15, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.49  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.49  fof(c_0_17, plain, ![X14, X15]:k4_xboole_0(X14,k3_xboole_0(X14,X15))=k4_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.21/0.49  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.49  fof(c_0_19, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.49  cnf(c_0_20, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.49  cnf(c_0_21, plain, (k2_xboole_0(X1,k4_xboole_0(k1_xboole_0,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.21/0.49  cnf(c_0_22, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.49  cnf(c_0_23, plain, (k4_xboole_0(X1,X1)=k3_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_15])).
% 0.21/0.49  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.49  cnf(c_0_25, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_20])).
% 0.21/0.49  cnf(c_0_26, plain, (k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X1))=k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_18]), c_0_16])).
% 0.21/0.49  cnf(c_0_27, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_18]), c_0_22])).
% 0.21/0.49  cnf(c_0_28, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_20]), c_0_24])).
% 0.21/0.49  fof(c_0_29, plain, ![X18, X19]:k2_xboole_0(X18,X19)=k2_xboole_0(k5_xboole_0(X18,X19),k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t93_xboole_1])).
% 0.21/0.49  cnf(c_0_30, plain, (k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),k3_xboole_0(X1,k1_xboole_0))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_23]), c_0_23])).
% 0.21/0.49  cnf(c_0_31, plain, (k4_xboole_0(k2_xboole_0(X1,k1_xboole_0),X1)=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_25]), c_0_24])).
% 0.21/0.49  cnf(c_0_32, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_22, c_0_24])).
% 0.21/0.49  cnf(c_0_33, plain, (k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_18]), c_0_27]), c_0_16]), c_0_26])).
% 0.21/0.49  cnf(c_0_34, plain, (k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_21]), c_0_27])).
% 0.21/0.49  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.49  cnf(c_0_36, plain, (k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(k1_xboole_0,X1))=k5_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_30, c_0_24])).
% 0.21/0.49  cnf(c_0_37, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_22]), c_0_18])).
% 0.21/0.49  cnf(c_0_38, plain, (k3_xboole_0(X1,k2_xboole_0(X1,k1_xboole_0))=k2_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_31]), c_0_32]), c_0_15]), c_0_24])).
% 0.21/0.49  cnf(c_0_39, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k1_xboole_0))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_25]), c_0_18])).
% 0.21/0.49  cnf(c_0_40, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_23]), c_0_22]), c_0_15])).
% 0.21/0.49  cnf(c_0_41, plain, (k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X1))=k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))), inference(rw,[status(thm)],[c_0_26, c_0_33])).
% 0.21/0.49  cnf(c_0_42, plain, (k4_xboole_0(k1_xboole_0,X1)=k3_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_34]), c_0_22]), c_0_18])).
% 0.21/0.49  cnf(c_0_43, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_16])).
% 0.21/0.49  cnf(c_0_44, plain, (k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(k1_xboole_0,X1))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_36])).
% 0.21/0.49  cnf(c_0_45, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.21/0.49  cnf(c_0_46, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_37]), c_0_23]), c_0_24])).
% 0.21/0.49  cnf(c_0_47, plain, (k5_xboole_0(X1,X1)=k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_36])).
% 0.21/0.49  cnf(c_0_48, plain, (k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X1))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_40]), c_0_36])).
% 0.21/0.49  cnf(c_0_49, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_16, c_0_45])).
% 0.21/0.49  cnf(c_0_50, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_27]), c_0_20])).
% 0.21/0.49  cnf(c_0_51, plain, (k4_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2)=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_42]), c_0_42])).
% 0.21/0.49  cnf(c_0_52, plain, (k2_xboole_0(X1,k5_xboole_0(X1,X1))=k2_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_43, c_0_40])).
% 0.21/0.49  cnf(c_0_53, plain, (k5_xboole_0(X1,X1)=k3_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_47]), c_0_37]), c_0_48]), c_0_49])).
% 0.21/0.49  cnf(c_0_54, plain, (k2_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[c_0_21, c_0_42])).
% 0.21/0.49  cnf(c_0_55, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 0.21/0.49  cnf(c_0_56, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_50, c_0_16])).
% 0.21/0.49  cnf(c_0_57, plain, (k4_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2)=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_51, c_0_24])).
% 0.21/0.49  cnf(c_0_58, plain, (k5_xboole_0(k1_xboole_0,X1)=k2_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.21/0.49  cnf(c_0_59, plain, (k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_15]), c_0_56]), c_0_57])).
% 0.21/0.49  cnf(c_0_60, plain, (k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k2_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_58]), c_0_49])).
% 0.21/0.49  cnf(c_0_61, plain, (k5_xboole_0(k1_xboole_0,X1)=k5_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_21])).
% 0.21/0.49  cnf(c_0_62, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_56, c_0_59])).
% 0.21/0.49  cnf(c_0_63, plain, (k2_xboole_0(k2_xboole_0(X1,X1),k3_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_16, c_0_60])).
% 0.21/0.49  cnf(c_0_64, plain, (k4_xboole_0(X1,k5_xboole_0(k1_xboole_0,X1))=k3_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_54]), c_0_32]), c_0_15])).
% 0.21/0.49  cnf(c_0_65, plain, (k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),k5_xboole_0(k1_xboole_0,X1))=k2_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_61])).
% 0.21/0.49  cnf(c_0_66, plain, (k4_xboole_0(k2_xboole_0(X1,X1),X1)=k3_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.21/0.49  cnf(c_0_67, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_32]), c_0_18])).
% 0.21/0.49  cnf(c_0_68, plain, (k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_64]), c_0_32]), c_0_15])).
% 0.21/0.49  cnf(c_0_69, plain, (k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),k5_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[c_0_65, c_0_45])).
% 0.21/0.49  cnf(c_0_70, plain, (k5_xboole_0(X1,k2_xboole_0(X1,X1))=k3_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_66]), c_0_56]), c_0_23]), c_0_67]), c_0_36]), c_0_53])).
% 0.21/0.49  cnf(c_0_71, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X1))=X1), inference(spm,[status(thm)],[c_0_68, c_0_58])).
% 0.21/0.49  cnf(c_0_72, plain, (k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),k2_xboole_0(X1,X1))=X1), inference(spm,[status(thm)],[c_0_69, c_0_58])).
% 0.21/0.49  cnf(c_0_73, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_70]), c_0_71]), c_0_54])).
% 0.21/0.49  cnf(c_0_74, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_20]), c_0_20]), c_0_20])).
% 0.21/0.49  cnf(c_0_75, plain, (k2_xboole_0(k2_xboole_0(X1,X1),k3_xboole_0(X1,k1_xboole_0))=X1), inference(spm,[status(thm)],[c_0_16, c_0_72])).
% 0.21/0.49  cnf(c_0_76, plain, (k2_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=k5_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_24])).
% 0.21/0.49  cnf(c_0_77, plain, (k2_xboole_0(X1,k5_xboole_0(k1_xboole_0,X1))=k5_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_73, c_0_58])).
% 0.21/0.49  cnf(c_0_78, plain, (k4_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_77])).
% 0.21/0.49  cnf(c_0_79, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k4_xboole_0(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_55, c_0_16])).
% 0.21/0.49  cnf(c_0_80, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_78, c_0_58])).
% 0.21/0.49  cnf(c_0_81, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,k1_xboole_0)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_23]), c_0_40])).
% 0.21/0.49  cnf(c_0_82, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_80]), c_0_18])).
% 0.21/0.49  cnf(c_0_83, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1)))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_81, c_0_24])).
% 0.21/0.49  cnf(c_0_84, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_28, c_0_59])).
% 0.21/0.49  cnf(c_0_85, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_46, c_0_24])).
% 0.21/0.49  cnf(c_0_86, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_14]), c_0_14])).
% 0.21/0.49  cnf(c_0_87, plain, (k3_xboole_0(k2_xboole_0(X1,X1),X2)=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_82])).
% 0.21/0.49  cnf(c_0_88, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X1,k4_xboole_0(X1,X2)))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_43, c_0_27])).
% 0.21/0.49  cnf(c_0_89, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_83]), c_0_18])).
% 0.21/0.49  cnf(c_0_90, plain, (k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_84]), c_0_85])).
% 0.21/0.49  cnf(c_0_91, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)))=k5_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_18]), c_0_20]), c_0_50]), c_0_59]), c_0_16]), c_0_86])).
% 0.21/0.49  cnf(c_0_92, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_87]), c_0_87]), c_0_40])).
% 0.21/0.49  cnf(c_0_93, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_53]), c_0_90]), c_0_91]), c_0_92])).
% 0.21/0.49  cnf(c_0_94, plain, (k4_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_22]), c_0_20])).
% 0.21/0.49  cnf(c_0_95, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_20]), c_0_20])).
% 0.21/0.49  cnf(c_0_96, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_92]), c_0_18])).
% 0.21/0.49  cnf(c_0_97, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_55, c_0_14])).
% 0.21/0.49  cnf(c_0_98, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_18]), c_0_27])).
% 0.21/0.49  cnf(c_0_99, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_46, c_0_90])).
% 0.21/0.49  cnf(c_0_100, plain, (k3_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3))=k3_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_94]), c_0_18])).
% 0.21/0.49  cnf(c_0_101, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_92]), c_0_28]), c_0_59]), c_0_24])).
% 0.21/0.49  cnf(c_0_102, plain, (k4_xboole_0(X1,k5_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_24]), c_0_97])).
% 0.21/0.49  cnf(c_0_103, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,X2)))=k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_14]), c_0_20])).
% 0.21/0.49  fof(c_0_104, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t94_xboole_1])).
% 0.21/0.49  cnf(c_0_105, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_98, c_0_24])).
% 0.21/0.49  cnf(c_0_106, plain, (k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2)=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_27]), c_0_42]), c_0_42]), c_0_99]), c_0_100]), c_0_42])).
% 0.21/0.49  cnf(c_0_107, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X1)))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_98, c_0_101])).
% 0.21/0.49  cnf(c_0_108, plain, (k4_xboole_0(X1,k2_xboole_0(k5_xboole_0(X1,X2),X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_20, c_0_102])).
% 0.21/0.49  cnf(c_0_109, plain, (k3_xboole_0(k1_xboole_0,k5_xboole_0(X1,X2))=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_43]), c_0_56]), c_0_59]), c_0_103])).
% 0.21/0.49  fof(c_0_110, negated_conjecture, k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_104])])])).
% 0.21/0.49  cnf(c_0_111, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=k4_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_107])).
% 0.21/0.49  cnf(c_0_112, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_92]), c_0_102])).
% 0.21/0.49  cnf(c_0_113, plain, (k4_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_109]), c_0_15])).
% 0.21/0.49  cnf(c_0_114, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.21/0.49  cnf(c_0_115, plain, (k4_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_90]), c_0_113])).
% 0.21/0.49  cnf(c_0_116, negated_conjecture, (k5_xboole_0(k3_xboole_0(esk1_0,esk2_0),k5_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_114, c_0_86])).
% 0.21/0.49  cnf(c_0_117, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_115]), c_0_112]), c_0_43])).
% 0.21/0.49  cnf(c_0_118, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_116, c_0_117])]), ['proof']).
% 0.21/0.49  # SZS output end CNFRefutation
% 0.21/0.49  # Proof object total steps             : 119
% 0.21/0.49  # Proof object clause steps            : 100
% 0.21/0.49  # Proof object formula steps           : 19
% 0.21/0.49  # Proof object conjectures             : 6
% 0.21/0.49  # Proof object clause conjectures      : 3
% 0.21/0.49  # Proof object formula conjectures     : 3
% 0.21/0.49  # Proof object initial clauses used    : 9
% 0.21/0.49  # Proof object initial formulas used   : 9
% 0.21/0.49  # Proof object generating inferences   : 79
% 0.21/0.49  # Proof object simplifying inferences  : 107
% 0.21/0.49  # Training examples: 0 positive, 0 negative
% 0.21/0.49  # Parsed axioms                        : 9
% 0.21/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.49  # Initial clauses                      : 9
% 0.21/0.49  # Removed in clause preprocessing      : 0
% 0.21/0.49  # Initial clauses in saturation        : 9
% 0.21/0.49  # Processed clauses                    : 897
% 0.21/0.49  # ...of these trivial                  : 294
% 0.21/0.49  # ...subsumed                          : 322
% 0.21/0.49  # ...remaining for further processing  : 281
% 0.21/0.49  # Other redundant clauses eliminated   : 0
% 0.21/0.49  # Clauses deleted for lack of memory   : 0
% 0.21/0.49  # Backward-subsumed                    : 1
% 0.21/0.49  # Backward-rewritten                   : 118
% 0.21/0.49  # Generated clauses                    : 12296
% 0.21/0.49  # ...of the previous two non-trivial   : 8505
% 0.21/0.49  # Contextual simplify-reflections      : 0
% 0.21/0.49  # Paramodulations                      : 12296
% 0.21/0.49  # Factorizations                       : 0
% 0.21/0.49  # Equation resolutions                 : 0
% 0.21/0.49  # Propositional unsat checks           : 0
% 0.21/0.49  #    Propositional check models        : 0
% 0.21/0.49  #    Propositional check unsatisfiable : 0
% 0.21/0.49  #    Propositional clauses             : 0
% 0.21/0.49  #    Propositional clauses after purity: 0
% 0.21/0.49  #    Propositional unsat core size     : 0
% 0.21/0.49  #    Propositional preprocessing time  : 0.000
% 0.21/0.49  #    Propositional encoding time       : 0.000
% 0.21/0.49  #    Propositional solver time         : 0.000
% 0.21/0.49  #    Success case prop preproc time    : 0.000
% 0.21/0.49  #    Success case prop encoding time   : 0.000
% 0.21/0.49  #    Success case prop solver time     : 0.000
% 0.21/0.49  # Current number of processed clauses  : 153
% 0.21/0.49  #    Positive orientable unit clauses  : 146
% 0.21/0.49  #    Positive unorientable unit clauses: 7
% 0.21/0.49  #    Negative unit clauses             : 0
% 0.21/0.49  #    Non-unit-clauses                  : 0
% 0.21/0.49  # Current number of unprocessed clauses: 7206
% 0.21/0.49  # ...number of literals in the above   : 7206
% 0.21/0.49  # Current number of archived formulas  : 0
% 0.21/0.49  # Current number of archived clauses   : 128
% 0.21/0.49  # Clause-clause subsumption calls (NU) : 0
% 0.21/0.49  # Rec. Clause-clause subsumption calls : 0
% 0.21/0.49  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.49  # Unit Clause-clause subsumption calls : 72
% 0.21/0.49  # Rewrite failures with RHS unbound    : 0
% 0.21/0.49  # BW rewrite match attempts            : 488
% 0.21/0.49  # BW rewrite match successes           : 129
% 0.21/0.49  # Condensation attempts                : 0
% 0.21/0.49  # Condensation successes               : 0
% 0.21/0.49  # Termbank termtop insertions          : 126601
% 0.21/0.49  
% 0.21/0.49  # -------------------------------------------------
% 0.21/0.49  # User time                : 0.134 s
% 0.21/0.49  # System time              : 0.010 s
% 0.21/0.49  # Total time               : 0.144 s
% 0.21/0.49  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
