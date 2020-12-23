%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:11 EST 2020

% Result     : Theorem 1.08s
% Output     : CNFRefutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :   88 (42053 expanded)
%              Number of clauses        :   67 (19864 expanded)
%              Number of leaves         :   10 (11094 expanded)
%              Depth                    :   30
%              Number of atoms          :   88 (42053 expanded)
%              Number of equality atoms :   87 (42052 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t98_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(c_0_10,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k5_xboole_0(k5_xboole_0(X26,X27),k3_xboole_0(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_11,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_12,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k2_xboole_0(X12,X13)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X9,X10,X11] : k4_xboole_0(k4_xboole_0(X9,X10),X11) = k4_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,plain,(
    ! [X23,X24,X25] : k5_xboole_0(k5_xboole_0(X23,X24),X25) = k5_xboole_0(X23,k5_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_17])).

fof(c_0_23,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_24,plain,(
    ! [X8] : k4_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3))))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X17] : k5_xboole_0(X17,k1_xboole_0) = X17 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_29,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_17]),c_0_17])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))) = k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_21]),c_0_21])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,X2))) = k4_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_35]),c_0_30])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_35]),c_0_30]),c_0_35]),c_0_37]),c_0_33]),c_0_35]),c_0_30])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_36]),c_0_26])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X4,X2)) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_26]),c_0_26]),c_0_40]),c_0_26])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_40])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(X1,k5_xboole_0(X3,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_41]),c_0_35]),c_0_33]),c_0_34])).

cnf(c_0_45,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_34])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_35]),c_0_30])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,X1))) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_39]),c_0_21])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X2,k4_xboole_0(X3,X2))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_46])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_47]),c_0_30]),c_0_21]),c_0_48]),c_0_49]),c_0_34])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3),X1),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_50])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_43]),c_0_30])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_51])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X3,k5_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_34])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_39]),c_0_21])).

cnf(c_0_57,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_54]),c_0_30]),c_0_35]),c_0_37]),c_0_33]),c_0_50]),c_0_43]),c_0_30]),c_0_21]),c_0_34]),c_0_45]),c_0_34])).

cnf(c_0_58,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3)))) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_21]),c_0_21])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k5_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_34]),c_0_45]),c_0_59]),c_0_45]),c_0_45]),c_0_21])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_60]),c_0_39])).

cnf(c_0_62,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k5_xboole_0(X1,X4))))) = k5_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_58]),c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X2),X3))) = k5_xboole_0(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_61]),c_0_21])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X1,X2))) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_52]),c_0_40]),c_0_43]),c_0_33]),c_0_41]),c_0_40]),c_0_43]),c_0_33]),c_0_34])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X3,k4_xboole_0(X1,X2)))) = k5_xboole_0(X3,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_34]),c_0_45]),c_0_61]),c_0_45]),c_0_21])).

cnf(c_0_66,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X2)),X3)) = k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_64]),c_0_21])).

cnf(c_0_67,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,X3)))) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_61]),c_0_21]),c_0_45]),c_0_45]),c_0_21])).

cnf(c_0_68,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3) = k4_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_50])).

cnf(c_0_69,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_34])).

cnf(c_0_70,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_26])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4))),X4),X3) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X3,X4)),X2),X4) ),
    inference(spm,[status(thm)],[c_0_68,c_0_68])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X3),X2))) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_69]),c_0_65])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X1,X2))) = k5_xboole_0(k4_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_52])).

cnf(c_0_75,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_73])).

fof(c_0_76,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t98_xboole_1])).

cnf(c_0_77,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X2),X3)))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_33]),c_0_34])).

fof(c_0_78,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_76])])])).

cnf(c_0_79,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X2)))) = X1 ),
    inference(spm,[status(thm)],[c_0_77,c_0_30])).

cnf(c_0_80,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_81,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_79,c_0_41])).

cnf(c_0_82,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[c_0_80,c_0_17])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_34]),c_0_21])).

cnf(c_0_84,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_34]),c_0_21])).

cnf(c_0_86,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) = k5_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.08/1.27  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 1.08/1.27  # and selection function SelectNewComplexAHP.
% 1.08/1.27  #
% 1.08/1.27  # Preprocessing time       : 0.026 s
% 1.08/1.27  # Presaturation interreduction done
% 1.08/1.27  
% 1.08/1.27  # Proof found!
% 1.08/1.27  # SZS status Theorem
% 1.08/1.27  # SZS output start CNFRefutation
% 1.08/1.27  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 1.08/1.27  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.08/1.27  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.08/1.27  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.08/1.27  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 1.08/1.27  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.08/1.27  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.08/1.27  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 1.08/1.27  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 1.08/1.27  fof(t98_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.08/1.27  fof(c_0_10, plain, ![X26, X27]:k2_xboole_0(X26,X27)=k5_xboole_0(k5_xboole_0(X26,X27),k3_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 1.08/1.27  fof(c_0_11, plain, ![X14, X15]:k4_xboole_0(X14,k4_xboole_0(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.08/1.27  fof(c_0_12, plain, ![X12, X13]:k4_xboole_0(X12,k2_xboole_0(X12,X13))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 1.08/1.27  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.08/1.27  cnf(c_0_14, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.08/1.27  fof(c_0_15, plain, ![X9, X10, X11]:k4_xboole_0(k4_xboole_0(X9,X10),X11)=k4_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.08/1.27  cnf(c_0_16, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.08/1.27  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 1.08/1.27  fof(c_0_18, plain, ![X23, X24, X25]:k5_xboole_0(k5_xboole_0(X23,X24),X25)=k5_xboole_0(X23,k5_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 1.08/1.27  cnf(c_0_19, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.08/1.27  cnf(c_0_20, plain, (k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 1.08/1.27  cnf(c_0_21, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.08/1.27  cnf(c_0_22, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))))), inference(rw,[status(thm)],[c_0_19, c_0_17])).
% 1.08/1.27  fof(c_0_23, plain, ![X6, X7]:k2_xboole_0(X6,k4_xboole_0(X7,X6))=k2_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 1.08/1.27  fof(c_0_24, plain, ![X8]:k4_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t3_boole])).
% 1.08/1.27  cnf(c_0_25, plain, (k4_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))=k1_xboole_0), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 1.08/1.27  cnf(c_0_26, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_22, c_0_21])).
% 1.08/1.27  cnf(c_0_27, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.08/1.27  fof(c_0_28, plain, ![X17]:k5_xboole_0(X17,k1_xboole_0)=X17, inference(variable_rename,[status(thm)],[t5_boole])).
% 1.08/1.27  fof(c_0_29, plain, ![X4, X5]:k5_xboole_0(X4,X5)=k5_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 1.08/1.27  cnf(c_0_30, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.08/1.27  cnf(c_0_31, plain, (k4_xboole_0(k4_xboole_0(X1,X1),X2)=k1_xboole_0), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 1.08/1.27  cnf(c_0_32, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_17]), c_0_17])).
% 1.08/1.27  cnf(c_0_33, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.08/1.27  cnf(c_0_34, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.08/1.27  cnf(c_0_35, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 1.08/1.27  cnf(c_0_36, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))))=k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_21]), c_0_21])).
% 1.08/1.27  cnf(c_0_37, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.08/1.27  cnf(c_0_38, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X2,X2)))=k4_xboole_0(k4_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_35]), c_0_30])).
% 1.08/1.27  cnf(c_0_39, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_35]), c_0_30]), c_0_35]), c_0_37]), c_0_33]), c_0_35]), c_0_30])).
% 1.08/1.27  cnf(c_0_40, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_36]), c_0_26])).
% 1.08/1.27  cnf(c_0_41, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 1.08/1.27  cnf(c_0_42, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X4,X2))=k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_26]), c_0_26]), c_0_40]), c_0_26])).
% 1.08/1.27  cnf(c_0_43, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_40])).
% 1.08/1.27  cnf(c_0_44, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3)=k4_xboole_0(X1,k5_xboole_0(X3,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_41]), c_0_35]), c_0_33]), c_0_34])).
% 1.08/1.27  cnf(c_0_45, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_21, c_0_34])).
% 1.08/1.27  cnf(c_0_46, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X2)=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_35]), c_0_30])).
% 1.08/1.27  cnf(c_0_47, plain, (k4_xboole_0(X1,k5_xboole_0(X1,k4_xboole_0(X2,X1)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 1.08/1.27  cnf(c_0_48, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,X1)))=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_39]), c_0_21])).
% 1.08/1.27  cnf(c_0_49, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X2,k4_xboole_0(X3,X2)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_40]), c_0_46])).
% 1.08/1.27  cnf(c_0_50, plain, (k4_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,X2)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_47]), c_0_30]), c_0_21]), c_0_48]), c_0_49]), c_0_34])).
% 1.08/1.27  cnf(c_0_51, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X3),X1),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_50])).
% 1.08/1.27  cnf(c_0_52, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_43]), c_0_30])).
% 1.08/1.27  cnf(c_0_53, plain, (k4_xboole_0(k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_51])).
% 1.08/1.27  cnf(c_0_54, plain, (k4_xboole_0(k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.08/1.27  cnf(c_0_55, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X3,k5_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_45, c_0_34])).
% 1.08/1.27  cnf(c_0_56, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2)))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_39]), c_0_21])).
% 1.08/1.27  cnf(c_0_57, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_54]), c_0_30]), c_0_35]), c_0_37]), c_0_33]), c_0_50]), c_0_43]), c_0_30]), c_0_21]), c_0_34]), c_0_45]), c_0_34])).
% 1.08/1.27  cnf(c_0_58, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X3))))=k5_xboole_0(X3,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_21]), c_0_21])).
% 1.08/1.27  cnf(c_0_59, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))=k5_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 1.08/1.27  cnf(c_0_60, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_34]), c_0_45]), c_0_59]), c_0_45]), c_0_45]), c_0_21])).
% 1.08/1.27  cnf(c_0_61, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_60]), c_0_39])).
% 1.08/1.27  cnf(c_0_62, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X3,k5_xboole_0(X1,X4)))))=k5_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_58]), c_0_21]), c_0_21]), c_0_21])).
% 1.08/1.27  cnf(c_0_63, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X1,X2),X3)))=k5_xboole_0(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_61]), c_0_21])).
% 1.08/1.27  cnf(c_0_64, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X1,X2)))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_52]), c_0_40]), c_0_43]), c_0_33]), c_0_41]), c_0_40]), c_0_43]), c_0_33]), c_0_34])).
% 1.08/1.27  cnf(c_0_65, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(X3,k4_xboole_0(X1,X2))))=k5_xboole_0(X3,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_34]), c_0_45]), c_0_61]), c_0_45]), c_0_21])).
% 1.08/1.27  cnf(c_0_66, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k5_xboole_0(k4_xboole_0(X2,k4_xboole_0(X1,X2)),X3))=k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_64]), c_0_21])).
% 1.08/1.27  cnf(c_0_67, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X1,X3))))=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_61]), c_0_21]), c_0_45]), c_0_45]), c_0_21])).
% 1.08/1.27  cnf(c_0_68, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X3)=k4_xboole_0(k4_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[c_0_44, c_0_50])).
% 1.08/1.27  cnf(c_0_69, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X2)))=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_34])).
% 1.08/1.27  cnf(c_0_70, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_26])).
% 1.08/1.27  cnf(c_0_71, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4))),X4),X3)=k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X3,X4)),X2),X4)), inference(spm,[status(thm)],[c_0_68, c_0_68])).
% 1.08/1.27  cnf(c_0_72, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X3),X2)))=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_69]), c_0_65])).
% 1.08/1.27  cnf(c_0_73, plain, (k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 1.08/1.27  cnf(c_0_74, plain, (k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X1,X2)))=k5_xboole_0(k4_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_72, c_0_52])).
% 1.08/1.27  cnf(c_0_75, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_73])).
% 1.08/1.27  fof(c_0_76, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(assume_negation,[status(cth)],[t98_xboole_1])).
% 1.08/1.27  cnf(c_0_77, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,X2),X3))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_33]), c_0_34])).
% 1.08/1.27  fof(c_0_78, negated_conjecture, k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_76])])])).
% 1.08/1.27  cnf(c_0_79, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X2))))=X1), inference(spm,[status(thm)],[c_0_77, c_0_30])).
% 1.08/1.27  cnf(c_0_80, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 1.08/1.27  cnf(c_0_81, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,X2))))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_79, c_0_41])).
% 1.08/1.27  cnf(c_0_82, negated_conjecture, (k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[c_0_80, c_0_17])).
% 1.08/1.27  cnf(c_0_83, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_34]), c_0_21])).
% 1.08/1.27  cnf(c_0_84, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[c_0_36, c_0_81])).
% 1.08/1.27  cnf(c_0_85, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))))!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_34]), c_0_21])).
% 1.08/1.27  cnf(c_0_86, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X1))))=k5_xboole_0(X2,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 1.08/1.27  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])]), ['proof']).
% 1.08/1.27  # SZS output end CNFRefutation
% 1.08/1.27  # Proof object total steps             : 88
% 1.08/1.27  # Proof object clause steps            : 67
% 1.08/1.27  # Proof object formula steps           : 21
% 1.08/1.27  # Proof object conjectures             : 7
% 1.08/1.27  # Proof object clause conjectures      : 4
% 1.08/1.27  # Proof object formula conjectures     : 3
% 1.08/1.27  # Proof object initial clauses used    : 10
% 1.08/1.27  # Proof object initial formulas used   : 10
% 1.08/1.27  # Proof object generating inferences   : 43
% 1.08/1.27  # Proof object simplifying inferences  : 90
% 1.08/1.27  # Training examples: 0 positive, 0 negative
% 1.08/1.27  # Parsed axioms                        : 13
% 1.08/1.27  # Removed by relevancy pruning/SinE    : 0
% 1.08/1.27  # Initial clauses                      : 13
% 1.08/1.27  # Removed in clause preprocessing      : 2
% 1.08/1.27  # Initial clauses in saturation        : 11
% 1.08/1.27  # Processed clauses                    : 1605
% 1.08/1.27  # ...of these trivial                  : 771
% 1.08/1.27  # ...subsumed                          : 460
% 1.08/1.27  # ...remaining for further processing  : 374
% 1.08/1.27  # Other redundant clauses eliminated   : 0
% 1.08/1.27  # Clauses deleted for lack of memory   : 0
% 1.08/1.27  # Backward-subsumed                    : 0
% 1.08/1.27  # Backward-rewritten                   : 72
% 1.08/1.27  # Generated clauses                    : 153717
% 1.08/1.27  # ...of the previous two non-trivial   : 57002
% 1.08/1.27  # Contextual simplify-reflections      : 0
% 1.08/1.27  # Paramodulations                      : 153717
% 1.08/1.27  # Factorizations                       : 0
% 1.08/1.27  # Equation resolutions                 : 0
% 1.08/1.27  # Propositional unsat checks           : 0
% 1.08/1.27  #    Propositional check models        : 0
% 1.08/1.27  #    Propositional check unsatisfiable : 0
% 1.08/1.27  #    Propositional clauses             : 0
% 1.08/1.27  #    Propositional clauses after purity: 0
% 1.08/1.27  #    Propositional unsat core size     : 0
% 1.08/1.27  #    Propositional preprocessing time  : 0.000
% 1.08/1.27  #    Propositional encoding time       : 0.000
% 1.08/1.27  #    Propositional solver time         : 0.000
% 1.08/1.27  #    Success case prop preproc time    : 0.000
% 1.08/1.27  #    Success case prop encoding time   : 0.000
% 1.08/1.27  #    Success case prop solver time     : 0.000
% 1.08/1.27  # Current number of processed clauses  : 291
% 1.08/1.27  #    Positive orientable unit clauses  : 287
% 1.08/1.27  #    Positive unorientable unit clauses: 4
% 1.08/1.27  #    Negative unit clauses             : 0
% 1.08/1.27  #    Non-unit-clauses                  : 0
% 1.08/1.27  # Current number of unprocessed clauses: 55263
% 1.08/1.27  # ...number of literals in the above   : 55264
% 1.08/1.27  # Current number of archived formulas  : 0
% 1.08/1.27  # Current number of archived clauses   : 85
% 1.08/1.27  # Clause-clause subsumption calls (NU) : 0
% 1.08/1.27  # Rec. Clause-clause subsumption calls : 0
% 1.08/1.27  # Non-unit clause-clause subsumptions  : 0
% 1.08/1.27  # Unit Clause-clause subsumption calls : 28
% 1.08/1.27  # Rewrite failures with RHS unbound    : 0
% 1.08/1.27  # BW rewrite match attempts            : 5340
% 1.08/1.27  # BW rewrite match successes           : 108
% 1.08/1.27  # Condensation attempts                : 0
% 1.08/1.27  # Condensation successes               : 0
% 1.08/1.27  # Termbank termtop insertions          : 2008501
% 1.08/1.27  
% 1.08/1.27  # -------------------------------------------------
% 1.08/1.27  # User time                : 0.883 s
% 1.08/1.27  # System time              : 0.049 s
% 1.08/1.27  # Total time               : 0.932 s
% 1.08/1.27  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
