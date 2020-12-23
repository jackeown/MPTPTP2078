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
% DateTime   : Thu Dec  3 10:32:26 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  127 (768702 expanded)
%              Number of clauses        :  110 (341317 expanded)
%              Number of leaves         :    8 (213692 expanded)
%              Depth                    :   31
%              Number of atoms          :  127 (768702 expanded)
%              Number of equality atoms :  126 (768701 expanded)
%              Maximal formula depth    :    4 (   1 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(t55_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

fof(c_0_8,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X9,X8)) = k2_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_9,plain,(
    ! [X16,X17] : k4_xboole_0(X16,k4_xboole_0(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_10,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_15,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X18,X19,X20] : k4_xboole_0(X18,k4_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X18,X19),k3_xboole_0(X18,X20)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

fof(c_0_18,plain,(
    ! [X10,X11,X12] : k4_xboole_0(k4_xboole_0(X10,X11),X12) = k4_xboole_0(X10,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X1) = k2_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_12]),c_0_11])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_12])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_21]),c_0_21])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_21])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X1,X1)) = k3_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_12])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k3_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_11]),c_0_16])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,k4_xboole_0(X2,X1))) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_11])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k3_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_13])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X2)) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_26])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_13])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X2)) = k2_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_34,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) = k3_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_12]),c_0_21]),c_0_12])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_20])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_21]),c_0_21]),c_0_32])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_12])).

cnf(c_0_38,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k3_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_13]),c_0_23])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X1))) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_33])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X2,X2),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_31])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_12])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_38])).

fof(c_0_43,plain,(
    ! [X13,X14,X15] : k4_xboole_0(k2_xboole_0(X13,X14),X15) = k2_xboole_0(k4_xboole_0(X13,X15),k4_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X1),X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_13])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = k2_xboole_0(k4_xboole_0(X2,X2),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_16])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),X2) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_22])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_20])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X1))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_11]),c_0_44])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X1,X2))) = k3_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_28])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X2)) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_35]),c_0_13])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,X2))) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_45]),c_0_22]),c_0_46])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(X1,k2_xboole_0(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_21]),c_0_11])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_42])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X2)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_42]),c_0_51])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_52]),c_0_11]),c_0_13]),c_0_35])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X2,X1))) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_59,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_24])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X2,X1))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_53]),c_0_26]),c_0_11])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X2)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_54]),c_0_55]),c_0_35])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_13])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_57])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X1)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_16])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k2_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_46]),c_0_59]),c_0_42]),c_0_12]),c_0_16])).

cnf(c_0_66,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X1))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_48])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X2)) = k4_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_61]),c_0_42]),c_0_16]),c_0_62]),c_0_63]),c_0_53])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X2,X1))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_16])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_64]),c_0_34]),c_0_20]),c_0_12]),c_0_20]),c_0_12])).

cnf(c_0_70,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X1),X2) = k3_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_65])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X2,X1))) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_48]),c_0_21]),c_0_66]),c_0_21]),c_0_41])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k4_xboole_0(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_13])).

cnf(c_0_73,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,X2))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_67]),c_0_11])).

cnf(c_0_74,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_68])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_56]),c_0_63]),c_0_72])).

cnf(c_0_76,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_65,c_0_69])).

cnf(c_0_77,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_69]),c_0_46]),c_0_74]),c_0_73])).

cnf(c_0_78,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k4_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_13]),c_0_63]),c_0_72]),c_0_75])).

cnf(c_0_79,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_77]),c_0_13])).

cnf(c_0_80,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X2))) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_63]),c_0_78]),c_0_79])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_13])).

cnf(c_0_82,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X2,X1))) = k4_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_11]),c_0_47])).

cnf(c_0_83,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k4_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_80]),c_0_12]),c_0_42]),c_0_78]),c_0_42])).

cnf(c_0_84,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X4,X2))) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X3,X4)),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_21])).

cnf(c_0_85,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_81]),c_0_42]),c_0_16]),c_0_56]),c_0_63]),c_0_79]),c_0_21]),c_0_13]),c_0_79])).

cnf(c_0_86,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_63])).

cnf(c_0_87,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_11]),c_0_63]),c_0_79]),c_0_21]),c_0_13]),c_0_79]),c_0_85])).

cnf(c_0_88,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X3,X1),k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_12]),c_0_13])).

cnf(c_0_89,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_16])).

cnf(c_0_90,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X1),X2) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_77])).

cnf(c_0_91,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_86,c_0_79])).

cnf(c_0_92,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,k2_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_87])).

cnf(c_0_93,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_21]),c_0_80])).

cnf(c_0_94,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_87]),c_0_11])).

cnf(c_0_95,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k4_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_90]),c_0_69]),c_0_46]),c_0_77]),c_0_91]),c_0_12]),c_0_42]),c_0_78])).

cnf(c_0_96,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3) = k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X3)),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_92]),c_0_84])).

cnf(c_0_97,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_93]),c_0_11]),c_0_13]),c_0_11])).

cnf(c_0_98,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_99,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_90]),c_0_77])).

cnf(c_0_100,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_95]),c_0_11]),c_0_13]),c_0_94])).

cnf(c_0_101,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_16])).

cnf(c_0_102,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X1) = k4_xboole_0(X2,k2_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_92])).

cnf(c_0_103,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X1),X2) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_70,c_0_76])).

cnf(c_0_104,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_98]),c_0_12])).

cnf(c_0_105,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_106,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k3_xboole_0(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_12])).

cnf(c_0_107,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_101,c_0_75])).

cnf(c_0_108,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_102]),c_0_26]),c_0_11])).

cnf(c_0_109,plain,
    ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_103])).

cnf(c_0_110,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_105]),c_0_105])).

cnf(c_0_111,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k3_xboole_0(k3_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_106,c_0_16])).

fof(c_0_112,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t55_xboole_1])).

cnf(c_0_113,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k2_xboole_0(X1,X2)) = k4_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_114,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_104]),c_0_109]),c_0_22]),c_0_110]),c_0_110])).

cnf(c_0_115,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X4,X3)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X4),X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_21])).

cnf(c_0_116,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X2,X3))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_47]),c_0_46])).

cnf(c_0_117,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_108]),c_0_110]),c_0_72]),c_0_111]),c_0_16]),c_0_74])).

cnf(c_0_118,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X3))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_77]),c_0_32])).

fof(c_0_119,negated_conjecture,(
    k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_112])])])).

cnf(c_0_120,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k3_xboole_0(X2,X1)) = k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_113]),c_0_114]),c_0_115]),c_0_13]),c_0_11]),c_0_46]),c_0_116]),c_0_117])).

cnf(c_0_121,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_76]),c_0_35]),c_0_12])).

cnf(c_0_122,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k2_xboole_0(X3,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_47]),c_0_46])).

cnf(c_0_123,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k3_xboole_0(X2,X1)),X3) = k2_xboole_0(X3,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_118]),c_0_115]),c_0_13]),c_0_79]),c_0_21]),c_0_13]),c_0_79]),c_0_85]),c_0_118])).

cnf(c_0_124,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_119])).

cnf(c_0_125,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_67]),c_0_46]),c_0_47]),c_0_70]),c_0_76]),c_0_21]),c_0_121]),c_0_46]),c_0_122]),c_0_123])).

cnf(c_0_126,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124,c_0_125]),c_0_13])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:47:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.51/1.67  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 1.51/1.67  # and selection function SelectNewComplexAHP.
% 1.51/1.67  #
% 1.51/1.67  # Preprocessing time       : 0.026 s
% 1.51/1.67  # Presaturation interreduction done
% 1.51/1.67  
% 1.51/1.67  # Proof found!
% 1.51/1.67  # SZS status Theorem
% 1.51/1.67  # SZS output start CNFRefutation
% 1.51/1.67  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.51/1.67  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.51/1.67  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.51/1.67  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.51/1.67  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 1.51/1.67  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.51/1.67  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 1.51/1.67  fof(t55_xboole_1, conjecture, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_xboole_1)).
% 1.51/1.67  fof(c_0_8, plain, ![X8, X9]:k2_xboole_0(X8,k4_xboole_0(X9,X8))=k2_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 1.51/1.67  fof(c_0_9, plain, ![X16, X17]:k4_xboole_0(X16,k4_xboole_0(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.51/1.67  fof(c_0_10, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.51/1.67  cnf(c_0_11, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.51/1.67  cnf(c_0_12, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.51/1.67  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.51/1.67  fof(c_0_14, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.51/1.67  cnf(c_0_15, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 1.51/1.67  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.51/1.67  fof(c_0_17, plain, ![X18, X19, X20]:k4_xboole_0(X18,k4_xboole_0(X19,X20))=k2_xboole_0(k4_xboole_0(X18,X19),k3_xboole_0(X18,X20)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 1.51/1.67  fof(c_0_18, plain, ![X10, X11, X12]:k4_xboole_0(k4_xboole_0(X10,X11),X12)=k4_xboole_0(X10,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.51/1.67  cnf(c_0_19, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 1.51/1.67  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.51/1.67  cnf(c_0_21, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.51/1.67  cnf(c_0_22, plain, (k3_xboole_0(X1,X1)=k2_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_12]), c_0_11])).
% 1.51/1.67  cnf(c_0_23, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_21, c_0_12])).
% 1.51/1.67  cnf(c_0_24, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_20, c_0_22])).
% 1.51/1.67  cnf(c_0_25, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_21]), c_0_21])).
% 1.51/1.67  cnf(c_0_26, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_11, c_0_21])).
% 1.51/1.67  cnf(c_0_27, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X1,X1))=k3_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_12])).
% 1.51/1.67  cnf(c_0_28, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k3_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_11]), c_0_16])).
% 1.51/1.67  cnf(c_0_29, plain, (k2_xboole_0(X1,k3_xboole_0(X1,k4_xboole_0(X2,X1)))=k2_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_11])).
% 1.51/1.67  cnf(c_0_30, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k3_xboole_0(X2,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_28, c_0_13])).
% 1.51/1.67  cnf(c_0_31, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X2))=k2_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_26])).
% 1.51/1.67  cnf(c_0_32, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_26, c_0_13])).
% 1.51/1.67  cnf(c_0_33, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X2))=k2_xboole_0(X1,k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_31, c_0_16])).
% 1.51/1.67  cnf(c_0_34, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))=k3_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_12]), c_0_21]), c_0_12])).
% 1.51/1.67  cnf(c_0_35, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_13, c_0_20])).
% 1.51/1.67  cnf(c_0_36, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_21]), c_0_21]), c_0_32])).
% 1.51/1.67  cnf(c_0_37, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_12])).
% 1.51/1.67  cnf(c_0_38, plain, (k3_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k3_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_13]), c_0_23])).
% 1.51/1.67  cnf(c_0_39, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X1)))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_33])).
% 1.51/1.67  cnf(c_0_40, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X2,X2),X1)), inference(spm,[status(thm)],[c_0_13, c_0_31])).
% 1.51/1.67  cnf(c_0_41, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_12, c_0_12])).
% 1.51/1.67  cnf(c_0_42, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X2,X1),X3)), inference(spm,[status(thm)],[c_0_16, c_0_38])).
% 1.51/1.67  fof(c_0_43, plain, ![X13, X14, X15]:k4_xboole_0(k2_xboole_0(X13,X14),X15)=k2_xboole_0(k4_xboole_0(X13,X15),k4_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 1.51/1.67  cnf(c_0_44, plain, (k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X1),X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_13])).
% 1.51/1.67  cnf(c_0_45, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=k2_xboole_0(k4_xboole_0(X2,X2),X1)), inference(spm,[status(thm)],[c_0_40, c_0_16])).
% 1.51/1.67  cnf(c_0_46, plain, (k4_xboole_0(k2_xboole_0(X1,X1),X2)=k4_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_22])).
% 1.51/1.67  cnf(c_0_47, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.51/1.67  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_15, c_0_20])).
% 1.51/1.67  cnf(c_0_49, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X1)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_11]), c_0_44])).
% 1.51/1.67  cnf(c_0_50, plain, (k4_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X1,X2)))=k3_xboole_0(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_12, c_0_28])).
% 1.51/1.67  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X2))=k2_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_35]), c_0_13])).
% 1.51/1.67  cnf(c_0_52, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,X2)))=k4_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_45]), c_0_22]), c_0_46])).
% 1.51/1.67  cnf(c_0_53, plain, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X1,X2)),X2)=k4_xboole_0(X1,k2_xboole_0(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_21]), c_0_11])).
% 1.51/1.67  cnf(c_0_54, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k4_xboole_0(k3_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[c_0_30, c_0_42])).
% 1.51/1.67  cnf(c_0_55, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X2))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_49, c_0_42])).
% 1.51/1.67  cnf(c_0_56, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_42]), c_0_51])).
% 1.51/1.67  cnf(c_0_57, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,k4_xboole_0(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_52]), c_0_11]), c_0_13]), c_0_35])).
% 1.51/1.67  cnf(c_0_58, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X2,X1)))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_48])).
% 1.51/1.67  cnf(c_0_59, plain, (k2_xboole_0(k2_xboole_0(X1,X1),k4_xboole_0(X1,X2))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_13, c_0_24])).
% 1.51/1.67  cnf(c_0_60, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X2,X1)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_53]), c_0_26]), c_0_11])).
% 1.51/1.67  cnf(c_0_61, plain, (k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X2))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_54]), c_0_55]), c_0_35])).
% 1.51/1.67  cnf(c_0_62, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_56, c_0_13])).
% 1.51/1.67  cnf(c_0_63, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_48, c_0_57])).
% 1.51/1.67  cnf(c_0_64, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X1))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_16])).
% 1.51/1.67  cnf(c_0_65, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X2,k2_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_46]), c_0_59]), c_0_42]), c_0_12]), c_0_16])).
% 1.51/1.67  cnf(c_0_66, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X1)))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_60, c_0_48])).
% 1.51/1.67  cnf(c_0_67, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X2))=k4_xboole_0(X1,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_61]), c_0_42]), c_0_16]), c_0_62]), c_0_63]), c_0_53])).
% 1.51/1.67  cnf(c_0_68, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X2,X1)))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_37, c_0_16])).
% 1.51/1.67  cnf(c_0_69, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_64]), c_0_34]), c_0_20]), c_0_12]), c_0_20]), c_0_12])).
% 1.51/1.67  cnf(c_0_70, plain, (k3_xboole_0(k2_xboole_0(X1,X1),X2)=k3_xboole_0(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_16, c_0_65])).
% 1.51/1.67  cnf(c_0_71, plain, (k4_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X2,X1)))=k4_xboole_0(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_48]), c_0_21]), c_0_66]), c_0_21]), c_0_41])).
% 1.51/1.67  cnf(c_0_72, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k4_xboole_0(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_23, c_0_13])).
% 1.51/1.67  cnf(c_0_73, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,X2)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_67]), c_0_11])).
% 1.51/1.67  cnf(c_0_74, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_68])).
% 1.51/1.67  cnf(c_0_75, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k4_xboole_0(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_56]), c_0_63]), c_0_72])).
% 1.51/1.67  cnf(c_0_76, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_65, c_0_69])).
% 1.51/1.67  cnf(c_0_77, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_69]), c_0_46]), c_0_74]), c_0_73])).
% 1.51/1.67  cnf(c_0_78, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k4_xboole_0(X2,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_13]), c_0_63]), c_0_72]), c_0_75])).
% 1.51/1.67  cnf(c_0_79, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_77]), c_0_13])).
% 1.51/1.67  cnf(c_0_80, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X2)))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_63]), c_0_78]), c_0_79])).
% 1.51/1.67  cnf(c_0_81, plain, (k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_61, c_0_13])).
% 1.51/1.67  cnf(c_0_82, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X2,X1)))=k4_xboole_0(k2_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_11]), c_0_47])).
% 1.51/1.67  cnf(c_0_83, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k4_xboole_0(X2,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_80]), c_0_12]), c_0_42]), c_0_78]), c_0_42])).
% 1.51/1.67  cnf(c_0_84, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k2_xboole_0(X4,X2)))=k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X3,X4)),X2)), inference(spm,[status(thm)],[c_0_47, c_0_21])).
% 1.51/1.67  cnf(c_0_85, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_81]), c_0_42]), c_0_16]), c_0_56]), c_0_63]), c_0_79]), c_0_21]), c_0_13]), c_0_79])).
% 1.51/1.67  cnf(c_0_86, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_56, c_0_63])).
% 1.51/1.67  cnf(c_0_87, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,k3_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_11]), c_0_63]), c_0_79]), c_0_21]), c_0_13]), c_0_79]), c_0_85])).
% 1.51/1.67  cnf(c_0_88, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X1,X2)))=k4_xboole_0(k2_xboole_0(X3,X1),k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_12]), c_0_13])).
% 1.51/1.67  cnf(c_0_89, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X3))=k4_xboole_0(X2,k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_35, c_0_16])).
% 1.51/1.67  cnf(c_0_90, plain, (k2_xboole_0(k2_xboole_0(X1,X1),X2)=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_13, c_0_77])).
% 1.51/1.67  cnf(c_0_91, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[c_0_86, c_0_79])).
% 1.51/1.67  cnf(c_0_92, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,k2_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_67, c_0_87])).
% 1.51/1.67  cnf(c_0_93, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_21]), c_0_80])).
% 1.51/1.67  cnf(c_0_94, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_87]), c_0_11])).
% 1.51/1.67  cnf(c_0_95, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k4_xboole_0(X2,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_90]), c_0_69]), c_0_46]), c_0_77]), c_0_91]), c_0_12]), c_0_42]), c_0_78])).
% 1.51/1.67  cnf(c_0_96, plain, (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X3)=k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X3)),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_92]), c_0_84])).
% 1.51/1.67  cnf(c_0_97, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_93]), c_0_11]), c_0_13]), c_0_11])).
% 1.51/1.67  cnf(c_0_98, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_21]), c_0_21]), c_0_21])).
% 1.51/1.67  cnf(c_0_99, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_90]), c_0_77])).
% 1.51/1.67  cnf(c_0_100, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_95]), c_0_11]), c_0_13]), c_0_94])).
% 1.51/1.67  cnf(c_0_101, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k4_xboole_0(k3_xboole_0(X2,X1),X2)), inference(spm,[status(thm)],[c_0_54, c_0_16])).
% 1.51/1.67  cnf(c_0_102, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),X1)=k4_xboole_0(X2,k2_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_92])).
% 1.51/1.67  cnf(c_0_103, plain, (k3_xboole_0(k2_xboole_0(X1,X1),X2)=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_70, c_0_76])).
% 1.51/1.67  cnf(c_0_104, plain, (k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_98]), c_0_12])).
% 1.51/1.67  cnf(c_0_105, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 1.51/1.67  cnf(c_0_106, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k3_xboole_0(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_38, c_0_12])).
% 1.51/1.67  cnf(c_0_107, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k4_xboole_0(X2,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_101, c_0_75])).
% 1.51/1.67  cnf(c_0_108, plain, (k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_102]), c_0_26]), c_0_11])).
% 1.51/1.67  cnf(c_0_109, plain, (k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_103])).
% 1.51/1.67  cnf(c_0_110, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_105]), c_0_105])).
% 1.51/1.67  cnf(c_0_111, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X3))=k3_xboole_0(k3_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_106, c_0_16])).
% 1.51/1.67  fof(c_0_112, negated_conjecture, ~(![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(assume_negation,[status(cth)],[t55_xboole_1])).
% 1.51/1.67  cnf(c_0_113, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k2_xboole_0(X1,X2))=k4_xboole_0(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 1.51/1.67  cnf(c_0_114, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X2,k2_xboole_0(X3,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_104]), c_0_109]), c_0_22]), c_0_110]), c_0_110])).
% 1.51/1.67  cnf(c_0_115, plain, (k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X4,X3))=k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X4),X3)), inference(spm,[status(thm)],[c_0_47, c_0_21])).
% 1.51/1.67  cnf(c_0_116, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X2,X3)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_47]), c_0_46])).
% 1.51/1.67  cnf(c_0_117, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_108]), c_0_110]), c_0_72]), c_0_111]), c_0_16]), c_0_74])).
% 1.51/1.67  cnf(c_0_118, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X3)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_77]), c_0_32])).
% 1.51/1.67  fof(c_0_119, negated_conjecture, k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_112])])])).
% 1.51/1.67  cnf(c_0_120, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k3_xboole_0(X2,X1))=k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_113]), c_0_114]), c_0_115]), c_0_13]), c_0_11]), c_0_46]), c_0_116]), c_0_117])).
% 1.51/1.67  cnf(c_0_121, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_76]), c_0_35]), c_0_12])).
% 1.51/1.67  cnf(c_0_122, plain, (k2_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k2_xboole_0(X3,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_47]), c_0_46])).
% 1.51/1.67  cnf(c_0_123, plain, (k2_xboole_0(k4_xboole_0(X1,k3_xboole_0(X2,X1)),X3)=k2_xboole_0(X3,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_118]), c_0_115]), c_0_13]), c_0_79]), c_0_21]), c_0_13]), c_0_79]), c_0_85]), c_0_118])).
% 1.51/1.67  cnf(c_0_124, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_119])).
% 1.51/1.67  cnf(c_0_125, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_67]), c_0_46]), c_0_47]), c_0_70]), c_0_76]), c_0_21]), c_0_121]), c_0_46]), c_0_122]), c_0_123])).
% 1.51/1.67  cnf(c_0_126, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_124, c_0_125]), c_0_13])]), ['proof']).
% 1.51/1.67  # SZS output end CNFRefutation
% 1.51/1.67  # Proof object total steps             : 127
% 1.51/1.67  # Proof object clause steps            : 110
% 1.51/1.67  # Proof object formula steps           : 17
% 1.51/1.67  # Proof object conjectures             : 5
% 1.51/1.67  # Proof object clause conjectures      : 2
% 1.51/1.67  # Proof object formula conjectures     : 3
% 1.51/1.67  # Proof object initial clauses used    : 8
% 1.51/1.67  # Proof object initial formulas used   : 8
% 1.51/1.67  # Proof object generating inferences   : 88
% 1.51/1.67  # Proof object simplifying inferences  : 166
% 1.51/1.67  # Training examples: 0 positive, 0 negative
% 1.51/1.67  # Parsed axioms                        : 8
% 1.51/1.67  # Removed by relevancy pruning/SinE    : 0
% 1.51/1.67  # Initial clauses                      : 8
% 1.51/1.67  # Removed in clause preprocessing      : 0
% 1.51/1.67  # Initial clauses in saturation        : 8
% 1.51/1.67  # Processed clauses                    : 5788
% 1.51/1.67  # ...of these trivial                  : 1253
% 1.51/1.67  # ...subsumed                          : 4017
% 1.51/1.67  # ...remaining for further processing  : 518
% 1.51/1.67  # Other redundant clauses eliminated   : 0
% 1.51/1.67  # Clauses deleted for lack of memory   : 0
% 1.51/1.67  # Backward-subsumed                    : 3
% 1.51/1.67  # Backward-rewritten                   : 222
% 1.51/1.67  # Generated clauses                    : 119999
% 1.51/1.67  # ...of the previous two non-trivial   : 104226
% 1.51/1.67  # Contextual simplify-reflections      : 0
% 1.51/1.67  # Paramodulations                      : 119999
% 1.51/1.67  # Factorizations                       : 0
% 1.51/1.67  # Equation resolutions                 : 0
% 1.51/1.67  # Propositional unsat checks           : 0
% 1.51/1.67  #    Propositional check models        : 0
% 1.51/1.67  #    Propositional check unsatisfiable : 0
% 1.51/1.67  #    Propositional clauses             : 0
% 1.51/1.67  #    Propositional clauses after purity: 0
% 1.51/1.67  #    Propositional unsat core size     : 0
% 1.51/1.67  #    Propositional preprocessing time  : 0.000
% 1.51/1.67  #    Propositional encoding time       : 0.000
% 1.51/1.67  #    Propositional solver time         : 0.000
% 1.51/1.67  #    Success case prop preproc time    : 0.000
% 1.51/1.67  #    Success case prop encoding time   : 0.000
% 1.51/1.67  #    Success case prop solver time     : 0.000
% 1.51/1.67  # Current number of processed clauses  : 285
% 1.51/1.67  #    Positive orientable unit clauses  : 261
% 1.51/1.67  #    Positive unorientable unit clauses: 24
% 1.51/1.67  #    Negative unit clauses             : 0
% 1.51/1.67  #    Non-unit-clauses                  : 0
% 1.51/1.67  # Current number of unprocessed clauses: 94866
% 1.51/1.67  # ...number of literals in the above   : 94866
% 1.51/1.67  # Current number of archived formulas  : 0
% 1.51/1.67  # Current number of archived clauses   : 233
% 1.51/1.67  # Clause-clause subsumption calls (NU) : 0
% 1.51/1.67  # Rec. Clause-clause subsumption calls : 0
% 1.51/1.67  # Non-unit clause-clause subsumptions  : 0
% 1.51/1.67  # Unit Clause-clause subsumption calls : 771
% 1.51/1.67  # Rewrite failures with RHS unbound    : 0
% 1.51/1.67  # BW rewrite match attempts            : 2911
% 1.51/1.67  # BW rewrite match successes           : 704
% 1.51/1.67  # Condensation attempts                : 0
% 1.51/1.67  # Condensation successes               : 0
% 1.51/1.67  # Termbank termtop insertions          : 1928735
% 1.51/1.68  
% 1.51/1.68  # -------------------------------------------------
% 1.51/1.68  # User time                : 1.241 s
% 1.51/1.68  # System time              : 0.088 s
% 1.51/1.68  # Total time               : 1.329 s
% 1.51/1.68  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
