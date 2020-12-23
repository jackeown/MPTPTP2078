%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:04 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  135 (75473 expanded)
%              Number of clauses        :  116 (32562 expanded)
%              Number of leaves         :    9 (21455 expanded)
%              Depth                    :   26
%              Number of atoms          :  135 (75473 expanded)
%              Number of equality atoms :  134 (75472 expanded)
%              Maximal formula depth    :    4 (   1 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t95_xboole_1,conjecture,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(c_0_9,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_10,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X14,X15),X16) = k4_xboole_0(X14,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_14,plain,(
    ! [X11,X12] : k2_xboole_0(X11,k4_xboole_0(X12,X11)) = k2_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_15,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X1) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X10] : k2_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_11])).

cnf(c_0_25,plain,
    ( k3_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_28,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_11]),c_0_11])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_11]),c_0_26]),c_0_26])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_22,c_0_26])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_26])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

cnf(c_0_33,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_19])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_11]),c_0_11]),c_0_30]),c_0_26]),c_0_29]),c_0_30])).

cnf(c_0_36,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_31]),c_0_16]),c_0_33]),c_0_34]),c_0_12])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_35]),c_0_32]),c_0_22])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_36]),c_0_34]),c_0_25]),c_0_25])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_16]),c_0_27]),c_0_37])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_38]),c_0_22])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_17]),c_0_17])).

fof(c_0_43,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_44,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_11])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_35]),c_0_41])).

cnf(c_0_46,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_18]),c_0_42])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_16]),c_0_45])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_19])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_47])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_37]),c_0_11])).

cnf(c_0_53,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_26])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k4_xboole_0(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_26])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,k1_xboole_0))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_18]),c_0_49])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_35]),c_0_35])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_50])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_11])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,X2)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_19]),c_0_52])).

cnf(c_0_60,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_53]),c_0_54])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,k1_xboole_0))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_55]),c_0_17]),c_0_26]),c_0_27]),c_0_37]),c_0_47])).

cnf(c_0_62,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X3,k4_xboole_0(X1,X2))) = k5_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_17])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_47]),c_0_47])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_19])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_16]),c_0_19])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_11]),c_0_50]),c_0_17])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_59]),c_0_34]),c_0_50])).

cnf(c_0_68,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k5_xboole_0(X1,X2),X3)) = k3_xboole_0(k4_xboole_0(X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_59]),c_0_60])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1))) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_19])).

cnf(c_0_70,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_37]),c_0_18]),c_0_63]),c_0_26]),c_0_18])).

cnf(c_0_71,plain,
    ( k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_16]),c_0_64]),c_0_31])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_19])).

cnf(c_0_73,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),X3) = k3_xboole_0(k4_xboole_0(X3,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_44]),c_0_68]),c_0_60])).

cnf(c_0_74,plain,
    ( k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_50]),c_0_35]),c_0_35]),c_0_70]),c_0_35])).

cnf(c_0_75,plain,
    ( k2_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_32,c_0_37])).

cnf(c_0_76,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_18]),c_0_21]),c_0_71]),c_0_72])).

cnf(c_0_77,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_11]),c_0_17]),c_0_21]),c_0_71]),c_0_26]),c_0_63])).

cnf(c_0_78,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_73])).

cnf(c_0_79,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_63])).

cnf(c_0_80,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_63])).

cnf(c_0_81,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_74])).

cnf(c_0_82,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_50]),c_0_11]),c_0_26]),c_0_29]),c_0_11])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_71])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_85,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_17])).

cnf(c_0_86,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k3_xboole_0(X1,k4_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_60]),c_0_78])).

cnf(c_0_87,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X2,X1))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k5_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_88,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(k5_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_79])).

cnf(c_0_89,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_67]),c_0_59]),c_0_17])).

cnf(c_0_90,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k5_xboole_0(X2,X1),X3)) = k3_xboole_0(X2,k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_80]),c_0_60]),c_0_78])).

cnf(c_0_91,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_78])).

cnf(c_0_92,plain,
    ( k2_xboole_0(k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1))) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_56]),c_0_26]),c_0_81])).

cnf(c_0_93,plain,
    ( k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_11]),c_0_82]),c_0_76])).

cnf(c_0_94,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_83]),c_0_75]),c_0_26])).

cnf(c_0_95,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_82])).

cnf(c_0_96,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_71])).

cnf(c_0_97,plain,
    ( k3_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,X3),X3)) = k3_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_86]),c_0_88]),c_0_17]),c_0_82]),c_0_89])).

cnf(c_0_98,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k3_xboole_0(X2,k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_79]),c_0_44]),c_0_90]),c_0_60]),c_0_78])).

cnf(c_0_99,plain,
    ( k3_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_67]),c_0_17])).

cnf(c_0_100,plain,
    ( k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_60]),c_0_34]),c_0_12]),c_0_45]),c_0_26]),c_0_77]),c_0_84])).

cnf(c_0_101,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_94,c_0_26])).

cnf(c_0_102,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2))) = k4_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_81]),c_0_95])).

cnf(c_0_103,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2) = k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_60]),c_0_35])).

cnf(c_0_104,plain,
    ( k2_xboole_0(X1,k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_96]),c_0_82])).

cnf(c_0_105,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_97]),c_0_78]),c_0_17]),c_0_37]),c_0_98]),c_0_99]),c_0_37])).

cnf(c_0_106,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k5_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_67])).

cnf(c_0_107,plain,
    ( k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_100,c_0_50])).

cnf(c_0_108,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,X1)) = k2_xboole_0(X2,k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_59]),c_0_26]),c_0_26])).

cnf(c_0_109,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k2_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_80]),c_0_26]),c_0_26])).

cnf(c_0_110,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_101]),c_0_18])).

cnf(c_0_111,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_19]),c_0_103]),c_0_104])).

cnf(c_0_112,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_105]),c_0_106]),c_0_19]),c_0_79])).

cnf(c_0_113,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k5_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_83]),c_0_26]),c_0_107]),c_0_63])).

cnf(c_0_114,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,X1)) = k2_xboole_0(X2,k5_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_19]),c_0_109])).

cnf(c_0_115,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_105]),c_0_18])).

cnf(c_0_116,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_35]),c_0_22])).

cnf(c_0_117,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_19])).

fof(c_0_118,negated_conjecture,(
    ~ ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t95_xboole_1])).

cnf(c_0_119,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_70]),c_0_113]),c_0_17]),c_0_37])).

cnf(c_0_120,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X1,X2)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_121,plain,
    ( k4_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_76]),c_0_26]),c_0_92])).

cnf(c_0_122,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_27,c_0_37])).

fof(c_0_123,negated_conjecture,(
    k3_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_118])])])).

cnf(c_0_124,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_112])).

cnf(c_0_125,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(k3_xboole_0(X2,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_121,c_0_19])).

cnf(c_0_126,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,k1_xboole_0))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_122]),c_0_18])).

cnf(c_0_127,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_128,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_115]),c_0_80]),c_0_63])).

cnf(c_0_129,plain,
    ( k5_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2)) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_61,c_0_125])).

cnf(c_0_130,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_126,c_0_125])).

cnf(c_0_131,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3)) = k3_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_66]),c_0_11])).

cnf(c_0_132,negated_conjecture,
    ( k5_xboole_0(k2_xboole_0(esk1_0,esk2_0),k5_xboole_0(esk1_0,esk2_0)) != k3_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_127,c_0_63])).

cnf(c_0_133,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_26]),c_0_130]),c_0_131]),c_0_30])).

cnf(c_0_134,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_133])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:58:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.63  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.46/0.63  # and selection function SelectNewComplexAHP.
% 0.46/0.63  #
% 0.46/0.63  # Preprocessing time       : 0.014 s
% 0.46/0.63  # Presaturation interreduction done
% 0.46/0.63  
% 0.46/0.63  # Proof found!
% 0.46/0.63  # SZS status Theorem
% 0.46/0.63  # SZS output start CNFRefutation
% 0.46/0.63  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.46/0.63  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.46/0.63  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.46/0.63  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.46/0.63  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.46/0.63  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.46/0.63  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.46/0.63  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.46/0.63  fof(t95_xboole_1, conjecture, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.46/0.63  fof(c_0_9, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.46/0.63  fof(c_0_10, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.46/0.63  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.46/0.63  cnf(c_0_12, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.46/0.63  fof(c_0_13, plain, ![X14, X15, X16]:k4_xboole_0(k4_xboole_0(X14,X15),X16)=k4_xboole_0(X14,k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.46/0.63  fof(c_0_14, plain, ![X11, X12]:k2_xboole_0(X11,k4_xboole_0(X12,X11))=k2_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.46/0.63  fof(c_0_15, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.46/0.63  cnf(c_0_16, plain, (k4_xboole_0(X1,X1)=k3_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.46/0.63  cnf(c_0_17, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.46/0.63  cnf(c_0_18, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.46/0.63  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.63  fof(c_0_20, plain, ![X10]:k2_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.46/0.63  cnf(c_0_21, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])).
% 0.46/0.63  cnf(c_0_22, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.46/0.63  fof(c_0_23, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.46/0.63  cnf(c_0_24, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_11, c_0_11])).
% 0.46/0.63  cnf(c_0_25, plain, (k3_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.46/0.63  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.46/0.63  cnf(c_0_27, plain, (k2_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=k2_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_18, c_0_16])).
% 0.46/0.63  cnf(c_0_28, plain, (k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k3_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_11]), c_0_11])).
% 0.46/0.63  cnf(c_0_29, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_11]), c_0_26]), c_0_26])).
% 0.46/0.63  cnf(c_0_30, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_22, c_0_26])).
% 0.46/0.63  cnf(c_0_31, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_21, c_0_26])).
% 0.46/0.63  cnf(c_0_32, plain, (k2_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=k2_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_27, c_0_19])).
% 0.46/0.63  cnf(c_0_33, plain, (k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0))=k3_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_19])).
% 0.46/0.63  cnf(c_0_34, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_24, c_0_19])).
% 0.46/0.63  cnf(c_0_35, plain, (k4_xboole_0(k1_xboole_0,X1)=k3_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_25]), c_0_11]), c_0_11]), c_0_30]), c_0_26]), c_0_29]), c_0_30])).
% 0.46/0.63  cnf(c_0_36, plain, (k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1))=k3_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_31]), c_0_16]), c_0_33]), c_0_34]), c_0_12])).
% 0.46/0.63  cnf(c_0_37, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_35]), c_0_32]), c_0_22])).
% 0.46/0.63  cnf(c_0_38, plain, (k4_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1))=k4_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_36]), c_0_34]), c_0_25]), c_0_25])).
% 0.46/0.63  cnf(c_0_39, plain, (k2_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_16]), c_0_27]), c_0_37])).
% 0.46/0.63  cnf(c_0_40, plain, (k2_xboole_0(k3_xboole_0(X1,X1),k4_xboole_0(k1_xboole_0,X1))=k3_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_38]), c_0_22])).
% 0.46/0.63  cnf(c_0_41, plain, (k2_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_39, c_0_19])).
% 0.46/0.63  cnf(c_0_42, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_17]), c_0_17])).
% 0.46/0.63  fof(c_0_43, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.46/0.63  cnf(c_0_44, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_17, c_0_11])).
% 0.46/0.63  cnf(c_0_45, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_35]), c_0_41])).
% 0.46/0.63  cnf(c_0_46, plain, (k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_18]), c_0_42])).
% 0.46/0.63  cnf(c_0_47, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.46/0.63  cnf(c_0_48, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_18, c_0_17])).
% 0.46/0.63  cnf(c_0_49, plain, (k4_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_16]), c_0_45])).
% 0.46/0.63  cnf(c_0_50, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_19])).
% 0.46/0.63  cnf(c_0_51, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_44, c_0_47])).
% 0.46/0.63  cnf(c_0_52, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_37]), c_0_11])).
% 0.46/0.63  cnf(c_0_53, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_48, c_0_26])).
% 0.46/0.63  cnf(c_0_54, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k4_xboole_0(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_44, c_0_26])).
% 0.46/0.63  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,k1_xboole_0)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_18]), c_0_49])).
% 0.46/0.63  cnf(c_0_56, plain, (k4_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2)=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_35]), c_0_35])).
% 0.46/0.63  cnf(c_0_57, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_34, c_0_50])).
% 0.46/0.63  cnf(c_0_58, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_11])).
% 0.46/0.63  cnf(c_0_59, plain, (k4_xboole_0(X1,k5_xboole_0(X1,X2))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_19]), c_0_52])).
% 0.46/0.63  cnf(c_0_60, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(k4_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_53]), c_0_54])).
% 0.46/0.63  cnf(c_0_61, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,k1_xboole_0)))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_55]), c_0_17]), c_0_26]), c_0_27]), c_0_37]), c_0_47])).
% 0.46/0.63  cnf(c_0_62, plain, (k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X3,k4_xboole_0(X1,X2)))=k5_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_47, c_0_17])).
% 0.46/0.63  cnf(c_0_63, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_47]), c_0_47])).
% 0.46/0.63  cnf(c_0_64, plain, (k4_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2)=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_56, c_0_19])).
% 0.46/0.63  cnf(c_0_65, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_16]), c_0_19])).
% 0.46/0.63  cnf(c_0_66, plain, (k4_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_11]), c_0_50]), c_0_17])).
% 0.46/0.63  cnf(c_0_67, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_59]), c_0_34]), c_0_50])).
% 0.46/0.63  cnf(c_0_68, plain, (k4_xboole_0(X1,k2_xboole_0(k5_xboole_0(X1,X2),X3))=k3_xboole_0(k4_xboole_0(X2,X3),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_59]), c_0_60])).
% 0.46/0.63  cnf(c_0_69, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1)))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_61, c_0_19])).
% 0.46/0.63  cnf(c_0_70, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_37]), c_0_18]), c_0_63]), c_0_26]), c_0_18])).
% 0.46/0.63  cnf(c_0_71, plain, (k3_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_16]), c_0_64]), c_0_31])).
% 0.46/0.63  cnf(c_0_72, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_65, c_0_19])).
% 0.46/0.63  cnf(c_0_73, plain, (k3_xboole_0(k4_xboole_0(X1,X2),X3)=k3_xboole_0(k4_xboole_0(X3,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_44]), c_0_68]), c_0_60])).
% 0.46/0.63  cnf(c_0_74, plain, (k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2)=k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_50]), c_0_35]), c_0_35]), c_0_70]), c_0_35])).
% 0.46/0.63  cnf(c_0_75, plain, (k2_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[c_0_32, c_0_37])).
% 0.46/0.63  cnf(c_0_76, plain, (k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_18]), c_0_21]), c_0_71]), c_0_72])).
% 0.46/0.63  cnf(c_0_77, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)))=k5_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_11]), c_0_17]), c_0_21]), c_0_71]), c_0_26]), c_0_63])).
% 0.46/0.63  cnf(c_0_78, plain, (k3_xboole_0(k4_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_19, c_0_73])).
% 0.46/0.63  cnf(c_0_79, plain, (k3_xboole_0(X1,k5_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_67, c_0_63])).
% 0.46/0.63  cnf(c_0_80, plain, (k4_xboole_0(X1,k5_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_59, c_0_63])).
% 0.46/0.63  cnf(c_0_81, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2))=k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),X1)), inference(spm,[status(thm)],[c_0_63, c_0_74])).
% 0.46/0.63  cnf(c_0_82, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=k2_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_50]), c_0_11]), c_0_26]), c_0_29]), c_0_11])).
% 0.46/0.63  cnf(c_0_83, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_31, c_0_71])).
% 0.46/0.63  cnf(c_0_84, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 0.46/0.63  cnf(c_0_85, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_70, c_0_17])).
% 0.46/0.63  cnf(c_0_86, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k3_xboole_0(X1,k4_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_60]), c_0_78])).
% 0.46/0.63  cnf(c_0_87, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X2,X1)))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k5_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_48, c_0_47])).
% 0.46/0.63  cnf(c_0_88, plain, (k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(k5_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_57, c_0_79])).
% 0.46/0.63  cnf(c_0_89, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_67]), c_0_59]), c_0_17])).
% 0.46/0.63  cnf(c_0_90, plain, (k4_xboole_0(X1,k2_xboole_0(k5_xboole_0(X2,X1),X3))=k3_xboole_0(X2,k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_80]), c_0_60]), c_0_78])).
% 0.46/0.63  cnf(c_0_91, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_60, c_0_78])).
% 0.46/0.63  cnf(c_0_92, plain, (k2_xboole_0(k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)),k4_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1)))=k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_56]), c_0_26]), c_0_81])).
% 0.46/0.63  cnf(c_0_93, plain, (k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_11]), c_0_82]), c_0_76])).
% 0.46/0.63  cnf(c_0_94, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_83]), c_0_75]), c_0_26])).
% 0.46/0.63  cnf(c_0_95, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_82])).
% 0.46/0.63  cnf(c_0_96, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_21, c_0_71])).
% 0.46/0.63  cnf(c_0_97, plain, (k3_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,X3),X3))=k3_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_86]), c_0_88]), c_0_17]), c_0_82]), c_0_89])).
% 0.46/0.63  cnf(c_0_98, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k3_xboole_0(X2,k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_79]), c_0_44]), c_0_90]), c_0_60]), c_0_78])).
% 0.46/0.63  cnf(c_0_99, plain, (k3_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_67]), c_0_17])).
% 0.46/0.63  cnf(c_0_100, plain, (k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_60]), c_0_34]), c_0_12]), c_0_45]), c_0_26]), c_0_77]), c_0_84])).
% 0.46/0.63  cnf(c_0_101, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_94, c_0_26])).
% 0.46/0.63  cnf(c_0_102, plain, (k2_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)))=k4_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_81]), c_0_95])).
% 0.46/0.63  cnf(c_0_103, plain, (k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2)=k3_xboole_0(k1_xboole_0,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_60]), c_0_35])).
% 0.46/0.63  cnf(c_0_104, plain, (k2_xboole_0(X1,k3_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)))=k2_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_96]), c_0_82])).
% 0.46/0.63  cnf(c_0_105, plain, (k4_xboole_0(k5_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_97]), c_0_78]), c_0_17]), c_0_37]), c_0_98]), c_0_99]), c_0_37])).
% 0.46/0.63  cnf(c_0_106, plain, (k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(k5_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_57, c_0_67])).
% 0.46/0.63  cnf(c_0_107, plain, (k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_100, c_0_50])).
% 0.46/0.63  cnf(c_0_108, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,X1))=k2_xboole_0(X2,k5_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_59]), c_0_26]), c_0_26])).
% 0.46/0.63  cnf(c_0_109, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k2_xboole_0(X2,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_80]), c_0_26]), c_0_26])).
% 0.46/0.63  cnf(c_0_110, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_101]), c_0_18])).
% 0.46/0.63  cnf(c_0_111, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_19]), c_0_103]), c_0_104])).
% 0.46/0.63  cnf(c_0_112, plain, (k4_xboole_0(k5_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_105]), c_0_106]), c_0_19]), c_0_79])).
% 0.46/0.63  cnf(c_0_113, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k5_xboole_0(X1,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_83]), c_0_26]), c_0_107]), c_0_63])).
% 0.46/0.63  cnf(c_0_114, plain, (k2_xboole_0(X1,k5_xboole_0(X2,X1))=k2_xboole_0(X2,k5_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_19]), c_0_109])).
% 0.46/0.63  cnf(c_0_115, plain, (k2_xboole_0(X1,k5_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_105]), c_0_18])).
% 0.46/0.63  cnf(c_0_116, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k1_xboole_0,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_35]), c_0_22])).
% 0.46/0.63  cnf(c_0_117, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_111, c_0_19])).
% 0.46/0.63  fof(c_0_118, negated_conjecture, ~(![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t95_xboole_1])).
% 0.46/0.63  cnf(c_0_119, plain, (k5_xboole_0(X1,k2_xboole_0(X1,X2))=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_70]), c_0_113]), c_0_17]), c_0_37])).
% 0.46/0.63  cnf(c_0_120, plain, (k2_xboole_0(X1,k5_xboole_0(X1,X2))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_114, c_0_115])).
% 0.46/0.63  cnf(c_0_121, plain, (k4_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2))=k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_76]), c_0_26]), c_0_92])).
% 0.46/0.63  cnf(c_0_122, plain, (k2_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_27, c_0_37])).
% 0.46/0.63  fof(c_0_123, negated_conjecture, k3_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_118])])])).
% 0.46/0.63  cnf(c_0_124, plain, (k5_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_112])).
% 0.46/0.63  cnf(c_0_125, plain, (k4_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))=k2_xboole_0(k3_xboole_0(X2,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_121, c_0_19])).
% 0.46/0.63  cnf(c_0_126, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,k1_xboole_0)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_122]), c_0_18])).
% 0.46/0.63  cnf(c_0_127, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_123])).
% 0.46/0.63  cnf(c_0_128, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_115]), c_0_80]), c_0_63])).
% 0.46/0.63  cnf(c_0_129, plain, (k5_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_61, c_0_125])).
% 0.46/0.63  cnf(c_0_130, plain, (k2_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,k1_xboole_0),X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_126, c_0_125])).
% 0.46/0.63  cnf(c_0_131, plain, (k3_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3))=k3_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_66]), c_0_11])).
% 0.46/0.63  cnf(c_0_132, negated_conjecture, (k5_xboole_0(k2_xboole_0(esk1_0,esk2_0),k5_xboole_0(esk1_0,esk2_0))!=k3_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_127, c_0_63])).
% 0.46/0.63  cnf(c_0_133, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_26]), c_0_130]), c_0_131]), c_0_30])).
% 0.46/0.63  cnf(c_0_134, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132, c_0_133])]), ['proof']).
% 0.46/0.63  # SZS output end CNFRefutation
% 0.46/0.63  # Proof object total steps             : 135
% 0.46/0.63  # Proof object clause steps            : 116
% 0.46/0.63  # Proof object formula steps           : 19
% 0.46/0.63  # Proof object conjectures             : 6
% 0.46/0.63  # Proof object clause conjectures      : 3
% 0.46/0.63  # Proof object formula conjectures     : 3
% 0.46/0.63  # Proof object initial clauses used    : 9
% 0.46/0.63  # Proof object initial formulas used   : 9
% 0.46/0.63  # Proof object generating inferences   : 92
% 0.46/0.63  # Proof object simplifying inferences  : 159
% 0.46/0.63  # Training examples: 0 positive, 0 negative
% 0.46/0.63  # Parsed axioms                        : 9
% 0.46/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.63  # Initial clauses                      : 9
% 0.46/0.63  # Removed in clause preprocessing      : 0
% 0.46/0.63  # Initial clauses in saturation        : 9
% 0.46/0.63  # Processed clauses                    : 2168
% 0.46/0.63  # ...of these trivial                  : 681
% 0.46/0.63  # ...subsumed                          : 1037
% 0.46/0.63  # ...remaining for further processing  : 450
% 0.46/0.63  # Other redundant clauses eliminated   : 0
% 0.46/0.63  # Clauses deleted for lack of memory   : 0
% 0.46/0.63  # Backward-subsumed                    : 0
% 0.46/0.63  # Backward-rewritten                   : 184
% 0.46/0.63  # Generated clauses                    : 47963
% 0.46/0.63  # ...of the previous two non-trivial   : 35766
% 0.46/0.63  # Contextual simplify-reflections      : 0
% 0.46/0.63  # Paramodulations                      : 47963
% 0.46/0.63  # Factorizations                       : 0
% 0.46/0.63  # Equation resolutions                 : 0
% 0.46/0.63  # Propositional unsat checks           : 0
% 0.46/0.63  #    Propositional check models        : 0
% 0.46/0.63  #    Propositional check unsatisfiable : 0
% 0.46/0.63  #    Propositional clauses             : 0
% 0.46/0.63  #    Propositional clauses after purity: 0
% 0.46/0.63  #    Propositional unsat core size     : 0
% 0.46/0.63  #    Propositional preprocessing time  : 0.000
% 0.46/0.63  #    Propositional encoding time       : 0.000
% 0.46/0.63  #    Propositional solver time         : 0.000
% 0.46/0.63  #    Success case prop preproc time    : 0.000
% 0.46/0.63  #    Success case prop encoding time   : 0.000
% 0.46/0.63  #    Success case prop solver time     : 0.000
% 0.46/0.63  # Current number of processed clauses  : 257
% 0.46/0.63  #    Positive orientable unit clauses  : 244
% 0.46/0.63  #    Positive unorientable unit clauses: 13
% 0.46/0.63  #    Negative unit clauses             : 0
% 0.46/0.63  #    Non-unit-clauses                  : 0
% 0.46/0.63  # Current number of unprocessed clauses: 33032
% 0.46/0.63  # ...number of literals in the above   : 33032
% 0.46/0.63  # Current number of archived formulas  : 0
% 0.46/0.63  # Current number of archived clauses   : 193
% 0.46/0.63  # Clause-clause subsumption calls (NU) : 0
% 0.46/0.63  # Rec. Clause-clause subsumption calls : 0
% 0.46/0.63  # Non-unit clause-clause subsumptions  : 0
% 0.46/0.63  # Unit Clause-clause subsumption calls : 141
% 0.46/0.63  # Rewrite failures with RHS unbound    : 0
% 0.46/0.63  # BW rewrite match attempts            : 1264
% 0.46/0.63  # BW rewrite match successes           : 379
% 0.46/0.63  # Condensation attempts                : 0
% 0.46/0.63  # Condensation successes               : 0
% 0.46/0.63  # Termbank termtop insertions          : 546191
% 0.46/0.63  
% 0.46/0.63  # -------------------------------------------------
% 0.46/0.63  # User time                : 0.282 s
% 0.46/0.63  # System time              : 0.017 s
% 0.46/0.63  # Total time               : 0.299 s
% 0.46/0.63  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
