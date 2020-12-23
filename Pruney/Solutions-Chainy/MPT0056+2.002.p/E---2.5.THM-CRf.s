%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:20 EST 2020

% Result     : Theorem 1.33s
% Output     : CNFRefutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  142 (7270611 expanded)
%              Number of clauses        :  129 (3072484 expanded)
%              Number of leaves         :    6 (2099063 expanded)
%              Depth                    :   38
%              Number of atoms          :  142 (7270611 expanded)
%              Number of equality atoms :  141 (7270610 expanded)
%              Maximal formula depth    :    5 (   1 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t49_xboole_1,conjecture,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(c_0_6,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_7,plain,(
    ! [X8,X9,X10] : k4_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_8,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_9,plain,(
    ! [X11,X12] : k4_xboole_0(X11,k3_xboole_0(X11,X12)) = k4_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_10,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k3_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_13]),c_0_15])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_11]),c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_18]),c_0_12])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_12]),c_0_16]),c_0_15]),c_0_20]),c_0_12])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_14]),c_0_11])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_18])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X1,X2))) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_23])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,k2_xboole_0(X1,X1))) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_13]),c_0_12]),c_0_12]),c_0_22])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_14]),c_0_12])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k4_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_15]),c_0_26])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,k2_xboole_0(X1,X1))) = k3_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_27]),c_0_11])).

cnf(c_0_31,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_14]),c_0_28]),c_0_15])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_11])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X1),k2_xboole_0(X1,k2_xboole_0(X1,X1))) = k4_xboole_0(k3_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X1) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_20]),c_0_11]),c_0_15]),c_0_31]),c_0_32])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X2)) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_29])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k2_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X1),k2_xboole_0(X1,k2_xboole_0(X1,X1))) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_22])).

cnf(c_0_38,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X1),k2_xboole_0(X1,k2_xboole_0(X1,X1))) = k3_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_33]),c_0_11]),c_0_15]),c_0_23])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_22]),c_0_11])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_20]),c_0_12]),c_0_13])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k4_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_15])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1)) = k2_xboole_0(k3_xboole_0(X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_15]),c_0_38]),c_0_39]),c_0_15]),c_0_38])).

cnf(c_0_44,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X1),X2) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_40])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_41]),c_0_13]),c_0_15]),c_0_20])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_34]),c_0_42])).

cnf(c_0_47,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X1),k2_xboole_0(X1,X1)) = k2_xboole_0(k3_xboole_0(X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_15]),c_0_40]),c_0_15]),c_0_40]),c_0_43]),c_0_15]),c_0_40])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_12]),c_0_12]),c_0_12])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_34]),c_0_17])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X1)) = k3_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_45]),c_0_11])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),k2_xboole_0(k3_xboole_0(X1,X1),X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49]),c_0_13]),c_0_33]),c_0_34]),c_0_22])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),k3_xboole_0(X1,X1)) = k4_xboole_0(k2_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_50])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X1)) = k2_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_51]),c_0_13]),c_0_52]),c_0_13])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_46])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),X1) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_22]),c_0_55]),c_0_48]),c_0_54]),c_0_22]),c_0_22])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),k3_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_40])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_55]),c_0_11])).

cnf(c_0_59,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_13]),c_0_16])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_32])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_56]),c_0_12])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),k3_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_44]),c_0_22])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X1))) = k4_xboole_0(k2_xboole_0(X1,X1),k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_58]),c_0_22]),c_0_15])).

cnf(c_0_64,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X3))) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_22]),c_0_12])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k3_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_23])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3)) = k3_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_28]),c_0_11])).

cnf(c_0_67,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X1)) = k2_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_61]),c_0_13])).

cnf(c_0_68,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),k2_xboole_0(X2,X1)) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_11]),c_0_44]),c_0_64]),c_0_15]),c_0_55])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X2))) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_20]),c_0_12]),c_0_12]),c_0_48]),c_0_12])).

cnf(c_0_70,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X2,X3))) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_22]),c_0_12]),c_0_48])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X2,X1))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_36]),c_0_66]),c_0_40])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k4_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_67]),c_0_68]),c_0_48]),c_0_69]),c_0_55]),c_0_70]),c_0_68]),c_0_48]),c_0_69])).

cnf(c_0_73,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_71]),c_0_14])).

cnf(c_0_74,plain,
    ( k3_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_72]),c_0_73]),c_0_15])).

cnf(c_0_75,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_70]),c_0_16])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_74]),c_0_13]),c_0_13]),c_0_75]),c_0_15]),c_0_20])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_76]),c_0_55]),c_0_48]),c_0_69])).

cnf(c_0_78,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_11])).

cnf(c_0_79,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X1,X2))) = k3_xboole_0(k4_xboole_0(X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_77]),c_0_17])).

cnf(c_0_80,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_12]),c_0_12])).

cnf(c_0_81,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k3_xboole_0(X2,X1),X2)) = k2_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_29])).

cnf(c_0_82,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_15])).

cnf(c_0_83,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X1),k4_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_22])).

cnf(c_0_84,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(X1,X1)) = k2_xboole_0(k4_xboole_0(X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_56]),c_0_15]),c_0_40]),c_0_78])).

cnf(c_0_85,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X1),k4_xboole_0(X1,X1)) = k2_xboole_0(k2_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_45])).

cnf(c_0_86,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X1),X1))) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_30]),c_0_27]),c_0_31]),c_0_22]),c_0_48])).

cnf(c_0_87,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k2_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_15])).

cnf(c_0_88,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_79]),c_0_80]),c_0_75])).

cnf(c_0_89,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X2))) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_46]),c_0_58])).

cnf(c_0_90,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X2))) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_34]),c_0_82])).

cnf(c_0_91,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X1),k2_xboole_0(X1,X1)) = k2_xboole_0(k2_xboole_0(X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_56]),c_0_83])).

cnf(c_0_92,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),k2_xboole_0(k4_xboole_0(X1,X1),X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_84]),c_0_85]),c_0_12]),c_0_86])).

cnf(c_0_93,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X1,X2))) = k3_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_78]),c_0_16]),c_0_15]),c_0_15])).

cnf(c_0_94,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X1))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_73]),c_0_11]),c_0_12])).

cnf(c_0_95,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X2,X1))) = k3_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_87]),c_0_16]),c_0_15]),c_0_15])).

cnf(c_0_96,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X1),X2) = k4_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_88]),c_0_13]),c_0_90]),c_0_79])).

cnf(c_0_97,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X2,X1))) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_77])).

cnf(c_0_98,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_18]),c_0_11])).

cnf(c_0_99,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k4_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_69]),c_0_48]),c_0_64])).

cnf(c_0_100,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(k2_xboole_0(X1,X1),X1)) = k2_xboole_0(k4_xboole_0(X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_91]),c_0_22]),c_0_56]),c_0_22]),c_0_56]),c_0_84])).

cnf(c_0_101,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X1),X1),k2_xboole_0(k4_xboole_0(X1,X1),X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_91]),c_0_22]),c_0_56]),c_0_84]),c_0_22]),c_0_56])).

cnf(c_0_102,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X2))) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_58]),c_0_23]),c_0_15]),c_0_95])).

cnf(c_0_103,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_96]),c_0_97])).

cnf(c_0_104,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k4_xboole_0(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_98])).

cnf(c_0_105,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X1),X1),X1) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_48]),c_0_13]),c_0_91]),c_0_48]),c_0_54]),c_0_22]),c_0_101])).

cnf(c_0_106,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_32])).

cnf(c_0_107,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) = k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_48]),c_0_11])).

cnf(c_0_108,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X1))) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_109,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k4_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_104,c_0_42])).

cnf(c_0_110,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(k4_xboole_0(X1,X1),X1)) = k2_xboole_0(k4_xboole_0(X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_105]),c_0_15]),c_0_106]),c_0_34]),c_0_22]),c_0_11]),c_0_78])).

cnf(c_0_111,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X1),X1),k4_xboole_0(X1,X1)) = k3_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_105]),c_0_15]),c_0_106]),c_0_34]),c_0_22]),c_0_11])).

cnf(c_0_112,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X1),X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_76]),c_0_22])).

cnf(c_0_113,plain,
    ( k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_107]),c_0_44])).

cnf(c_0_114,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_76]),c_0_13])).

cnf(c_0_115,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_22]),c_0_93]),c_0_108])).

cnf(c_0_116,plain,
    ( k3_xboole_0(k2_xboole_0(k4_xboole_0(X1,X1),X1),k2_xboole_0(k4_xboole_0(X1,X1),X1)) = k3_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_110]),c_0_12]),c_0_69]),c_0_13]),c_0_22]),c_0_111])).

cnf(c_0_117,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X1),X2)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_112]),c_0_108]),c_0_113]),c_0_114]),c_0_15]),c_0_106])).

cnf(c_0_118,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_23]),c_0_15]),c_0_23])).

cnf(c_0_119,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X2),X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_115])).

cnf(c_0_120,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X1),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_117]),c_0_115]),c_0_18]),c_0_118]),c_0_15]),c_0_60])).

cnf(c_0_121,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_76]),c_0_12])).

cnf(c_0_122,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X2),X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_119]),c_0_14])).

cnf(c_0_123,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_113]),c_0_107]),c_0_120])).

cnf(c_0_124,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X1),X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_122])).

cnf(c_0_125,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k4_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_123]),c_0_121])).

cnf(c_0_126,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X1),X2),k4_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_124]),c_0_15]),c_0_106]),c_0_120]),c_0_11])).

cnf(c_0_127,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_125]),c_0_17])).

cnf(c_0_128,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3))) = k3_xboole_0(k3_xboole_0(X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_126]),c_0_95])).

cnf(c_0_129,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_13]),c_0_127]),c_0_12])).

cnf(c_0_130,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_128])).

cnf(c_0_131,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3))) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_16,c_0_129])).

cnf(c_0_132,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) = k4_xboole_0(k3_xboole_0(X1,X3),k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_44]),c_0_22])).

cnf(c_0_133,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_130]),c_0_11])).

fof(c_0_134,negated_conjecture,(
    ~ ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(assume_negation,[status(cth)],[t49_xboole_1])).

cnf(c_0_135,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3)) = k3_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_131]),c_0_11])).

cnf(c_0_136,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1)) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_20]),c_0_133]),c_0_12]),c_0_131])).

fof(c_0_137,negated_conjecture,(
    k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_134])])])).

cnf(c_0_138,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k3_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_135]),c_0_14]),c_0_133]),c_0_136])).

cnf(c_0_139,negated_conjecture,
    ( k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_140,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X2,X1),X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_138])).

cnf(c_0_141,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_140]),c_0_15])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:41:07 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 1.33/1.51  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 1.33/1.51  # and selection function SelectNewComplexAHP.
% 1.33/1.51  #
% 1.33/1.51  # Preprocessing time       : 0.026 s
% 1.33/1.51  # Presaturation interreduction done
% 1.33/1.51  
% 1.33/1.51  # Proof found!
% 1.33/1.51  # SZS status Theorem
% 1.33/1.51  # SZS output start CNFRefutation
% 1.33/1.51  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.33/1.51  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.33/1.51  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.33/1.51  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.33/1.51  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.33/1.51  fof(t49_xboole_1, conjecture, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 1.33/1.51  fof(c_0_6, plain, ![X13, X14]:k4_xboole_0(X13,k4_xboole_0(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.33/1.51  fof(c_0_7, plain, ![X8, X9, X10]:k4_xboole_0(k4_xboole_0(X8,X9),X10)=k4_xboole_0(X8,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 1.33/1.51  fof(c_0_8, plain, ![X6, X7]:k2_xboole_0(X6,k4_xboole_0(X7,X6))=k2_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 1.33/1.51  fof(c_0_9, plain, ![X11, X12]:k4_xboole_0(X11,k3_xboole_0(X11,X12))=k4_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 1.33/1.51  fof(c_0_10, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.33/1.51  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.33/1.51  cnf(c_0_12, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.33/1.51  cnf(c_0_13, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.33/1.51  cnf(c_0_14, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.33/1.51  cnf(c_0_15, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.33/1.51  cnf(c_0_16, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_12])).
% 1.33/1.51  cnf(c_0_17, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_13, c_0_12])).
% 1.33/1.51  cnf(c_0_18, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 1.33/1.51  cnf(c_0_19, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k3_xboole_0(X2,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_13]), c_0_15])).
% 1.33/1.51  cnf(c_0_20, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_11]), c_0_14])).
% 1.33/1.51  cnf(c_0_21, plain, (k4_xboole_0(X1,k2_xboole_0(k3_xboole_0(X2,X1),X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_18]), c_0_12])).
% 1.33/1.51  cnf(c_0_22, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_12]), c_0_16]), c_0_15]), c_0_20]), c_0_12])).
% 1.33/1.51  cnf(c_0_23, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_14]), c_0_11])).
% 1.33/1.51  cnf(c_0_24, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_18])).
% 1.33/1.51  cnf(c_0_25, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X1,X2)))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_17, c_0_19])).
% 1.33/1.51  cnf(c_0_26, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k4_xboole_0(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_18, c_0_23])).
% 1.33/1.51  cnf(c_0_27, plain, (k4_xboole_0(X1,k2_xboole_0(X1,k2_xboole_0(X1,X1)))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_13]), c_0_12]), c_0_12]), c_0_22])).
% 1.33/1.51  cnf(c_0_28, plain, (k4_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_14]), c_0_12])).
% 1.33/1.51  cnf(c_0_29, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k4_xboole_0(k3_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_15]), c_0_26])).
% 1.33/1.51  cnf(c_0_30, plain, (k3_xboole_0(X1,k2_xboole_0(X1,k2_xboole_0(X1,X1)))=k3_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_27]), c_0_11])).
% 1.33/1.51  cnf(c_0_31, plain, (k3_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k4_xboole_0(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_14]), c_0_28]), c_0_15])).
% 1.33/1.51  cnf(c_0_32, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_12, c_0_11])).
% 1.33/1.51  cnf(c_0_33, plain, (k4_xboole_0(k3_xboole_0(X1,X1),k2_xboole_0(X1,k2_xboole_0(X1,X1)))=k4_xboole_0(k3_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.33/1.51  cnf(c_0_34, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X1)=k4_xboole_0(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_20]), c_0_11]), c_0_15]), c_0_31]), c_0_32])).
% 1.33/1.51  cnf(c_0_35, plain, (k2_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X2))=k2_xboole_0(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_13, c_0_29])).
% 1.33/1.51  cnf(c_0_36, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k2_xboole_0(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_13, c_0_18])).
% 1.33/1.51  cnf(c_0_37, plain, (k4_xboole_0(k3_xboole_0(X1,X1),k2_xboole_0(X1,k2_xboole_0(X1,X1)))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_22])).
% 1.33/1.51  cnf(c_0_38, plain, (k3_xboole_0(k3_xboole_0(X1,X1),k2_xboole_0(X1,k2_xboole_0(X1,X1)))=k3_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_33]), c_0_11]), c_0_15]), c_0_23])).
% 1.33/1.51  cnf(c_0_39, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k2_xboole_0(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 1.33/1.51  cnf(c_0_40, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_22]), c_0_11])).
% 1.33/1.51  cnf(c_0_41, plain, (k2_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X1)))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_20]), c_0_12]), c_0_13])).
% 1.33/1.51  cnf(c_0_42, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k4_xboole_0(X2,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_34, c_0_15])).
% 1.33/1.51  cnf(c_0_43, plain, (k2_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1))=k2_xboole_0(k3_xboole_0(X1,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_15]), c_0_38]), c_0_39]), c_0_15]), c_0_38])).
% 1.33/1.51  cnf(c_0_44, plain, (k3_xboole_0(k2_xboole_0(X1,X1),X2)=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_40])).
% 1.33/1.51  cnf(c_0_45, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_41]), c_0_13]), c_0_15]), c_0_20])).
% 1.33/1.51  cnf(c_0_46, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(X2,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_34]), c_0_42])).
% 1.33/1.51  cnf(c_0_47, plain, (k2_xboole_0(k3_xboole_0(X1,X1),k2_xboole_0(X1,X1))=k2_xboole_0(k3_xboole_0(X1,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_15]), c_0_40]), c_0_15]), c_0_40]), c_0_43]), c_0_15]), c_0_40])).
% 1.33/1.51  cnf(c_0_48, plain, (k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_12]), c_0_12]), c_0_12])).
% 1.33/1.51  cnf(c_0_49, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_34]), c_0_17])).
% 1.33/1.51  cnf(c_0_50, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X1))=k3_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_45]), c_0_11])).
% 1.33/1.51  cnf(c_0_51, plain, (k4_xboole_0(k2_xboole_0(X1,X1),k2_xboole_0(k3_xboole_0(X1,X1),X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49]), c_0_13]), c_0_33]), c_0_34]), c_0_22])).
% 1.33/1.51  cnf(c_0_52, plain, (k4_xboole_0(k2_xboole_0(X1,X1),k3_xboole_0(X1,X1))=k4_xboole_0(k2_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_18, c_0_50])).
% 1.33/1.51  cnf(c_0_53, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X2)))=k4_xboole_0(X2,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 1.33/1.51  cnf(c_0_54, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X1))=k2_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_51]), c_0_13]), c_0_52]), c_0_13])).
% 1.33/1.51  cnf(c_0_55, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k4_xboole_0(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_19, c_0_46])).
% 1.33/1.51  cnf(c_0_56, plain, (k4_xboole_0(k2_xboole_0(X1,X1),X1)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_22]), c_0_55]), c_0_48]), c_0_54]), c_0_22]), c_0_22])).
% 1.33/1.51  cnf(c_0_57, plain, (k4_xboole_0(k2_xboole_0(X1,X1),k3_xboole_0(X2,X1))=k4_xboole_0(k2_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_18, c_0_40])).
% 1.33/1.51  cnf(c_0_58, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_55]), c_0_11])).
% 1.33/1.51  cnf(c_0_59, plain, (k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_13]), c_0_16])).
% 1.33/1.51  cnf(c_0_60, plain, (k3_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_20, c_0_32])).
% 1.33/1.51  cnf(c_0_61, plain, (k4_xboole_0(k2_xboole_0(X1,X1),k2_xboole_0(X1,X2))=k4_xboole_0(X1,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_56]), c_0_12])).
% 1.33/1.51  cnf(c_0_62, plain, (k4_xboole_0(k2_xboole_0(X1,X1),k3_xboole_0(X1,X2))=k4_xboole_0(k2_xboole_0(X1,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_44]), c_0_22])).
% 1.33/1.51  cnf(c_0_63, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X1)))=k4_xboole_0(k2_xboole_0(X1,X1),k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_58]), c_0_22]), c_0_15])).
% 1.33/1.51  cnf(c_0_64, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X3)))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_22]), c_0_12])).
% 1.33/1.51  cnf(c_0_65, plain, (k4_xboole_0(k3_xboole_0(k4_xboole_0(X1,X2),X3),X2)=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_23])).
% 1.33/1.51  cnf(c_0_66, plain, (k3_xboole_0(X1,k2_xboole_0(k3_xboole_0(X1,X2),X3))=k3_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_28]), c_0_11])).
% 1.33/1.51  cnf(c_0_67, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X1))=k2_xboole_0(k2_xboole_0(X1,X2),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_61]), c_0_13])).
% 1.33/1.51  cnf(c_0_68, plain, (k4_xboole_0(k2_xboole_0(X1,X1),k2_xboole_0(X2,X1))=k4_xboole_0(X1,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_11]), c_0_44]), c_0_64]), c_0_15]), c_0_55])).
% 1.33/1.51  cnf(c_0_69, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X2)))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_20]), c_0_12]), c_0_12]), c_0_48]), c_0_12])).
% 1.33/1.51  cnf(c_0_70, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X2,X3)))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_22]), c_0_12]), c_0_48])).
% 1.33/1.51  cnf(c_0_71, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X2,X1)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_36]), c_0_66]), c_0_40])).
% 1.33/1.51  cnf(c_0_72, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k4_xboole_0(X1,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_67]), c_0_68]), c_0_48]), c_0_69]), c_0_55]), c_0_70]), c_0_68]), c_0_48]), c_0_69])).
% 1.33/1.51  cnf(c_0_73, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_71]), c_0_14])).
% 1.33/1.51  cnf(c_0_74, plain, (k3_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2))=k4_xboole_0(k2_xboole_0(X2,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_72]), c_0_73]), c_0_15])).
% 1.33/1.51  cnf(c_0_75, plain, (k3_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_70]), c_0_16])).
% 1.33/1.51  cnf(c_0_76, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_74]), c_0_13]), c_0_13]), c_0_75]), c_0_15]), c_0_20])).
% 1.33/1.51  cnf(c_0_77, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(X1,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_76]), c_0_55]), c_0_48]), c_0_69])).
% 1.33/1.51  cnf(c_0_78, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_13, c_0_11])).
% 1.33/1.51  cnf(c_0_79, plain, (k4_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X1,X2)))=k3_xboole_0(k4_xboole_0(X1,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_77]), c_0_17])).
% 1.33/1.51  cnf(c_0_80, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(k4_xboole_0(X1,X2),X3)))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_12]), c_0_12])).
% 1.33/1.51  cnf(c_0_81, plain, (k2_xboole_0(X1,k4_xboole_0(k3_xboole_0(X2,X1),X2))=k2_xboole_0(X1,k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_13, c_0_29])).
% 1.33/1.51  cnf(c_0_82, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_49, c_0_15])).
% 1.33/1.51  cnf(c_0_83, plain, (k2_xboole_0(k2_xboole_0(X1,X1),k4_xboole_0(X2,X1))=k2_xboole_0(k2_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_13, c_0_22])).
% 1.33/1.51  cnf(c_0_84, plain, (k2_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(X1,X1))=k2_xboole_0(k4_xboole_0(X1,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_56]), c_0_15]), c_0_40]), c_0_78])).
% 1.33/1.51  cnf(c_0_85, plain, (k2_xboole_0(k2_xboole_0(X1,X1),k4_xboole_0(X1,X1))=k2_xboole_0(k2_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_13, c_0_45])).
% 1.33/1.51  cnf(c_0_86, plain, (k4_xboole_0(X1,k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X1),X1)))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_30]), c_0_27]), c_0_31]), c_0_22]), c_0_48])).
% 1.33/1.51  cnf(c_0_87, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k2_xboole_0(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_78, c_0_15])).
% 1.33/1.51  cnf(c_0_88, plain, (k3_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X2))=k4_xboole_0(X1,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_79]), c_0_80]), c_0_75])).
% 1.33/1.51  cnf(c_0_89, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X2)))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_46]), c_0_58])).
% 1.33/1.51  cnf(c_0_90, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X2)))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_34]), c_0_82])).
% 1.33/1.51  cnf(c_0_91, plain, (k2_xboole_0(k2_xboole_0(X1,X1),k2_xboole_0(X1,X1))=k2_xboole_0(k2_xboole_0(X1,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_56]), c_0_83])).
% 1.33/1.51  cnf(c_0_92, plain, (k4_xboole_0(k2_xboole_0(X1,X1),k2_xboole_0(k4_xboole_0(X1,X1),X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_84]), c_0_85]), c_0_12]), c_0_86])).
% 1.33/1.51  cnf(c_0_93, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X1,X2)))=k3_xboole_0(X1,k4_xboole_0(X3,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_78]), c_0_16]), c_0_15]), c_0_15])).
% 1.33/1.51  cnf(c_0_94, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X1)))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_73]), c_0_11]), c_0_12])).
% 1.33/1.51  cnf(c_0_95, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X3,k4_xboole_0(X2,X1)))=k3_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_87]), c_0_16]), c_0_15]), c_0_15])).
% 1.33/1.51  cnf(c_0_96, plain, (k3_xboole_0(k4_xboole_0(X1,X1),X2)=k4_xboole_0(X1,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_88]), c_0_13]), c_0_90]), c_0_79])).
% 1.33/1.51  cnf(c_0_97, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X2,X1)))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_89, c_0_77])).
% 1.33/1.51  cnf(c_0_98, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_18]), c_0_11])).
% 1.33/1.51  cnf(c_0_99, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k4_xboole_0(X2,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_69]), c_0_48]), c_0_64])).
% 1.33/1.51  cnf(c_0_100, plain, (k2_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(k2_xboole_0(X1,X1),X1))=k2_xboole_0(k4_xboole_0(X1,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_91]), c_0_22]), c_0_56]), c_0_22]), c_0_56]), c_0_84])).
% 1.33/1.51  cnf(c_0_101, plain, (k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X1),X1),k2_xboole_0(k4_xboole_0(X1,X1),X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_91]), c_0_22]), c_0_56]), c_0_84]), c_0_22]), c_0_56])).
% 1.33/1.51  cnf(c_0_102, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X2)))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_58]), c_0_23]), c_0_15]), c_0_95])).
% 1.33/1.51  cnf(c_0_103, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_96]), c_0_97])).
% 1.33/1.51  cnf(c_0_104, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k4_xboole_0(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_18, c_0_98])).
% 1.33/1.51  cnf(c_0_105, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X1),X1),X1)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_48]), c_0_13]), c_0_91]), c_0_48]), c_0_54]), c_0_22]), c_0_101])).
% 1.33/1.51  cnf(c_0_106, plain, (k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_11, c_0_32])).
% 1.33/1.51  cnf(c_0_107, plain, (k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))=k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X4)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_48]), c_0_11])).
% 1.33/1.51  cnf(c_0_108, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X1)))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 1.33/1.51  cnf(c_0_109, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k4_xboole_0(X2,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_104, c_0_42])).
% 1.33/1.51  cnf(c_0_110, plain, (k2_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(k4_xboole_0(X1,X1),X1))=k2_xboole_0(k4_xboole_0(X1,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_105]), c_0_15]), c_0_106]), c_0_34]), c_0_22]), c_0_11]), c_0_78])).
% 1.33/1.51  cnf(c_0_111, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X1),X1),k4_xboole_0(X1,X1))=k3_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_105]), c_0_15]), c_0_106]), c_0_34]), c_0_22]), c_0_11])).
% 1.33/1.51  cnf(c_0_112, plain, (k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X1),X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_76]), c_0_22])).
% 1.33/1.51  cnf(c_0_113, plain, (k3_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k3_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_107]), c_0_44])).
% 1.33/1.51  cnf(c_0_114, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_76]), c_0_13])).
% 1.33/1.51  cnf(c_0_115, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_22]), c_0_93]), c_0_108])).
% 1.33/1.51  cnf(c_0_116, plain, (k3_xboole_0(k2_xboole_0(k4_xboole_0(X1,X1),X1),k2_xboole_0(k4_xboole_0(X1,X1),X1))=k3_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_110]), c_0_12]), c_0_69]), c_0_13]), c_0_22]), c_0_111])).
% 1.33/1.51  cnf(c_0_117, plain, (k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X1),X2))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_112]), c_0_108]), c_0_113]), c_0_114]), c_0_15]), c_0_106])).
% 1.33/1.51  cnf(c_0_118, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_23]), c_0_15]), c_0_23])).
% 1.33/1.51  cnf(c_0_119, plain, (k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X2),X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_115])).
% 1.33/1.51  cnf(c_0_120, plain, (k4_xboole_0(k3_xboole_0(X1,X1),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_117]), c_0_115]), c_0_18]), c_0_118]), c_0_15]), c_0_60])).
% 1.33/1.51  cnf(c_0_121, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k4_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_76]), c_0_12])).
% 1.33/1.51  cnf(c_0_122, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X2),X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_119]), c_0_14])).
% 1.33/1.51  cnf(c_0_123, plain, (k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_113]), c_0_107]), c_0_120])).
% 1.33/1.51  cnf(c_0_124, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X1),X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_122])).
% 1.33/1.51  cnf(c_0_125, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k4_xboole_0(X2,k2_xboole_0(X3,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_123]), c_0_121])).
% 1.33/1.51  cnf(c_0_126, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X1),X2),k4_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_124]), c_0_15]), c_0_106]), c_0_120]), c_0_11])).
% 1.33/1.51  cnf(c_0_127, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_125]), c_0_17])).
% 1.33/1.51  cnf(c_0_128, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))=k3_xboole_0(k3_xboole_0(X3,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_126]), c_0_95])).
% 1.33/1.51  cnf(c_0_129, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_13]), c_0_127]), c_0_12])).
% 1.33/1.51  cnf(c_0_130, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_60, c_0_128])).
% 1.33/1.51  cnf(c_0_131, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X3)))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_16, c_0_129])).
% 1.33/1.51  cnf(c_0_132, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))=k4_xboole_0(k3_xboole_0(X1,X3),k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_44]), c_0_22])).
% 1.33/1.51  cnf(c_0_133, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_130]), c_0_11])).
% 1.33/1.51  fof(c_0_134, negated_conjecture, ~(![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(assume_negation,[status(cth)],[t49_xboole_1])).
% 1.33/1.51  cnf(c_0_135, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X3))=k3_xboole_0(k3_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_131]), c_0_11])).
% 1.33/1.51  cnf(c_0_136, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))=k3_xboole_0(k4_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_20]), c_0_133]), c_0_12]), c_0_131])).
% 1.33/1.51  fof(c_0_137, negated_conjecture, k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_134])])])).
% 1.33/1.51  cnf(c_0_138, plain, (k3_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k3_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_135]), c_0_14]), c_0_133]), c_0_136])).
% 1.33/1.51  cnf(c_0_139, negated_conjecture, (k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_137])).
% 1.33/1.51  cnf(c_0_140, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X2,X1),X3)), inference(spm,[status(thm)],[c_0_15, c_0_138])).
% 1.33/1.51  cnf(c_0_141, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139, c_0_140]), c_0_15])]), ['proof']).
% 1.33/1.51  # SZS output end CNFRefutation
% 1.33/1.51  # Proof object total steps             : 142
% 1.33/1.51  # Proof object clause steps            : 129
% 1.33/1.51  # Proof object formula steps           : 13
% 1.33/1.51  # Proof object conjectures             : 5
% 1.33/1.51  # Proof object clause conjectures      : 2
% 1.33/1.51  # Proof object formula conjectures     : 3
% 1.33/1.51  # Proof object initial clauses used    : 6
% 1.33/1.51  # Proof object initial formulas used   : 6
% 1.33/1.51  # Proof object generating inferences   : 117
% 1.33/1.51  # Proof object simplifying inferences  : 231
% 1.33/1.51  # Training examples: 0 positive, 0 negative
% 1.33/1.51  # Parsed axioms                        : 6
% 1.33/1.51  # Removed by relevancy pruning/SinE    : 0
% 1.33/1.51  # Initial clauses                      : 6
% 1.33/1.51  # Removed in clause preprocessing      : 0
% 1.33/1.51  # Initial clauses in saturation        : 6
% 1.33/1.51  # Processed clauses                    : 3403
% 1.33/1.51  # ...of these trivial                  : 1231
% 1.33/1.51  # ...subsumed                          : 1560
% 1.33/1.51  # ...remaining for further processing  : 612
% 1.33/1.51  # Other redundant clauses eliminated   : 0
% 1.33/1.51  # Clauses deleted for lack of memory   : 0
% 1.33/1.51  # Backward-subsumed                    : 0
% 1.33/1.51  # Backward-rewritten                   : 349
% 1.33/1.51  # Generated clauses                    : 108962
% 1.33/1.51  # ...of the previous two non-trivial   : 78436
% 1.33/1.51  # Contextual simplify-reflections      : 0
% 1.33/1.51  # Paramodulations                      : 108962
% 1.33/1.51  # Factorizations                       : 0
% 1.33/1.51  # Equation resolutions                 : 0
% 1.33/1.51  # Propositional unsat checks           : 0
% 1.33/1.51  #    Propositional check models        : 0
% 1.33/1.51  #    Propositional check unsatisfiable : 0
% 1.33/1.51  #    Propositional clauses             : 0
% 1.33/1.51  #    Propositional clauses after purity: 0
% 1.33/1.51  #    Propositional unsat core size     : 0
% 1.33/1.51  #    Propositional preprocessing time  : 0.000
% 1.33/1.51  #    Propositional encoding time       : 0.000
% 1.33/1.51  #    Propositional solver time         : 0.000
% 1.33/1.51  #    Success case prop preproc time    : 0.000
% 1.33/1.51  #    Success case prop encoding time   : 0.000
% 1.33/1.51  #    Success case prop solver time     : 0.000
% 1.33/1.51  # Current number of processed clauses  : 257
% 1.33/1.51  #    Positive orientable unit clauses  : 246
% 1.33/1.51  #    Positive unorientable unit clauses: 11
% 1.33/1.51  #    Negative unit clauses             : 0
% 1.33/1.51  #    Non-unit-clauses                  : 0
% 1.33/1.51  # Current number of unprocessed clauses: 73657
% 1.33/1.51  # ...number of literals in the above   : 73657
% 1.33/1.51  # Current number of archived formulas  : 0
% 1.33/1.51  # Current number of archived clauses   : 355
% 1.33/1.51  # Clause-clause subsumption calls (NU) : 0
% 1.33/1.51  # Rec. Clause-clause subsumption calls : 0
% 1.33/1.51  # Non-unit clause-clause subsumptions  : 0
% 1.33/1.51  # Unit Clause-clause subsumption calls : 424
% 1.33/1.51  # Rewrite failures with RHS unbound    : 0
% 1.33/1.51  # BW rewrite match attempts            : 2895
% 1.33/1.51  # BW rewrite match successes           : 393
% 1.33/1.51  # Condensation attempts                : 0
% 1.33/1.51  # Condensation successes               : 0
% 1.33/1.51  # Termbank termtop insertions          : 1384785
% 1.33/1.51  
% 1.33/1.51  # -------------------------------------------------
% 1.33/1.51  # User time                : 1.123 s
% 1.33/1.51  # System time              : 0.045 s
% 1.33/1.51  # Total time               : 1.168 s
% 1.33/1.51  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
