%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:01 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  132 (153867 expanded)
%              Number of clauses        :  115 (68886 expanded)
%              Number of leaves         :    8 (42490 expanded)
%              Depth                    :   30
%              Number of atoms          :  132 (153867 expanded)
%              Number of equality atoms :  131 (153866 expanded)
%              Maximal formula depth    :    4 (   1 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t94_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(c_0_8,plain,(
    ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_9,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_10,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k4_xboole_0(X9,X8)) = k2_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_13,plain,(
    ! [X12,X13,X14] : k4_xboole_0(k4_xboole_0(X12,X13),X14) = k4_xboole_0(X12,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_14,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_18,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_14]),c_0_16])).

cnf(c_0_20,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = k4_xboole_0(X1,k5_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,X1)) = k3_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k5_xboole_0(X1,X1),k3_xboole_0(X1,X1)) = k2_xboole_0(X1,k5_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_23]),c_0_11])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X1),k5_xboole_0(X1,X1)) = k3_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_24]),c_0_10]),c_0_23])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k5_xboole_0(X1,X1),X2)) = k4_xboole_0(k3_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_23])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1)) = k3_xboole_0(k3_xboole_0(X1,X1),k5_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_16]),c_0_16])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_19]),c_0_21])).

cnf(c_0_30,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_10])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_15])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,k5_xboole_0(X1,X1))) = k3_xboole_0(k3_xboole_0(X1,X1),k5_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_24]),c_0_27])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,X1))) = k4_xboole_0(k3_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_11])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_19]),c_0_15])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X2)) = k3_xboole_0(X1,k5_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_20])).

cnf(c_0_36,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X1),X1) = k3_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_21])).

cnf(c_0_37,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X1),k5_xboole_0(X1,X1)) = k4_xboole_0(k3_xboole_0(X1,X1),X1) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X1),X1) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_34])).

cnf(c_0_39,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X1),k5_xboole_0(X1,X1)) = k3_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_35]),c_0_20])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1)) = k4_xboole_0(k3_xboole_0(X1,X1),X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_37])).

cnf(c_0_41,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_38]),c_0_16]),c_0_15]),c_0_19]),c_0_16]),c_0_15]),c_0_19]),c_0_39])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X1),X1) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_16]),c_0_15]),c_0_19]),c_0_16]),c_0_33])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[c_0_40,c_0_42])).

cnf(c_0_44,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_21]),c_0_11]),c_0_11])).

fof(c_0_45,plain,(
    ! [X17,X18,X19] : k5_xboole_0(k5_xboole_0(X17,X18),X19) = k5_xboole_0(X17,k5_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_46,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X3,k4_xboole_0(X1,X2))) = k5_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_20]),c_0_20])).

cnf(c_0_48,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1)) = k2_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_43]),c_0_44]),c_0_15])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_14]),c_0_15])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X1),k5_xboole_0(X1,X1)) = k3_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_30]),c_0_36])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X1),k4_xboole_0(k5_xboole_0(X1,X1),X1)) = k5_xboole_0(X1,k5_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_23])).

cnf(c_0_53,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_19]),c_0_15]),c_0_11]),c_0_15]),c_0_47])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_48]),c_0_19])).

cnf(c_0_56,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_15])).

cnf(c_0_57,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X1),k5_xboole_0(X1,X1)) = k5_xboole_0(X1,k5_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_51]),c_0_19]),c_0_52])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1)) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_43]),c_0_27]),c_0_37]),c_0_42]),c_0_20])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1))) = k2_xboole_0(X1,k5_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_25]),c_0_15]),c_0_47]),c_0_53]),c_0_11]),c_0_24])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_10]),c_0_15])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X1),k4_xboole_0(X2,X1)) = k2_xboole_0(k3_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_42]),c_0_56]),c_0_11]),c_0_50])).

cnf(c_0_63,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_10]),c_0_16])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_41]),c_0_16]),c_0_33]),c_0_42])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = k2_xboole_0(X1,k5_xboole_0(X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_48]),c_0_58]),c_0_57]),c_0_58]),c_0_47]),c_0_53]),c_0_59])).

cnf(c_0_66,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_60]),c_0_11]),c_0_60])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_60])).

cnf(c_0_68,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k4_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_50])).

cnf(c_0_69,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X2)) = k2_xboole_0(k3_xboole_0(X2,X2),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_61])).

cnf(c_0_70,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_62])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_14]),c_0_16])).

cnf(c_0_72,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_63]),c_0_15])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k2_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_20]),c_0_16])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,k5_xboole_0(X1,X1))) = k5_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_64]),c_0_64]),c_0_20]),c_0_53]),c_0_65])).

cnf(c_0_75,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_66]),c_0_67]),c_0_68])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k3_xboole_0(X2,X2)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_48]),c_0_19]),c_0_19])).

cnf(c_0_77,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X1),X2) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_14]),c_0_69]),c_0_70])).

cnf(c_0_78,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_71]),c_0_15])).

cnf(c_0_79,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k2_xboole_0(k2_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_72])).

cnf(c_0_80,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X1),X1) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_33]),c_0_42]),c_0_22]),c_0_64]),c_0_33]),c_0_42]),c_0_15]),c_0_19]),c_0_14])).

cnf(c_0_81,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_75])).

cnf(c_0_82,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X1),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_76])).

cnf(c_0_83,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_11]),c_0_79])).

cnf(c_0_84,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X1,X1)) = k2_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_80]),c_0_23]),c_0_11]),c_0_44]),c_0_15]),c_0_53]),c_0_65])).

cnf(c_0_85,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_11])).

cnf(c_0_86,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X1),X2) = k3_xboole_0(k4_xboole_0(X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_41]),c_0_16]),c_0_81])).

cnf(c_0_87,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_56,c_0_11])).

cnf(c_0_88,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_83])).

cnf(c_0_89,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X1),X2) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_82]),c_0_55]),c_0_20])).

cnf(c_0_90,plain,
    ( k2_xboole_0(k5_xboole_0(X1,X1),k3_xboole_0(X1,X1)) = k2_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_84])).

cnf(c_0_91,plain,
    ( k2_xboole_0(X1,k3_xboole_0(k4_xboole_0(X2,X1),X1)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_85])).

cnf(c_0_92,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),X2) = k3_xboole_0(k4_xboole_0(X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_81]),c_0_85])).

cnf(c_0_93,plain,
    ( k2_xboole_0(X1,k3_xboole_0(k4_xboole_0(X1,X2),X2)) = k2_xboole_0(X1,k5_xboole_0(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_86])).

cnf(c_0_94,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88]),c_0_88])).

cnf(c_0_95,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_21])).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X1)) = k2_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[c_0_65,c_0_84])).

cnf(c_0_97,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X1),X2) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_29]),c_0_36]),c_0_89])).

cnf(c_0_98,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k5_xboole_0(X2,X2)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_90]),c_0_19]),c_0_19])).

cnf(c_0_99,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])).

cnf(c_0_100,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_20]),c_0_15]),c_0_60])).

cnf(c_0_101,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(k4_xboole_0(X1,X2),X3))) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_95]),c_0_16])).

cnf(c_0_102,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_92]),c_0_16]),c_0_93]),c_0_33]),c_0_82]),c_0_16]),c_0_19])).

cnf(c_0_103,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2))) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_96]),c_0_53]),c_0_97])).

cnf(c_0_104,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X1),k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_61,c_0_77])).

cnf(c_0_105,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k5_xboole_0(X1,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_82])).

cnf(c_0_106,plain,
    ( k4_xboole_0(k2_xboole_0(k5_xboole_0(X1,X1),X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_90]),c_0_19]),c_0_19])).

cnf(c_0_107,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X1,X2)),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_108,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_100]),c_0_14])).

cnf(c_0_109,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_91]),c_0_19]),c_0_102])).

cnf(c_0_110,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X1),X2) = k5_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_41]),c_0_53])).

cnf(c_0_111,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,X2))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_89]),c_0_89])).

cnf(c_0_112,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),X2) = k2_xboole_0(k5_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_77,c_0_41])).

cnf(c_0_113,plain,
    ( k5_xboole_0(X1,k2_xboole_0(k5_xboole_0(X1,X1),X2)) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_105]),c_0_106]),c_0_20])).

cnf(c_0_114,plain,
    ( k3_xboole_0(k2_xboole_0(X1,k4_xboole_0(X1,X2)),X2) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_107]),c_0_10]),c_0_21])).

fof(c_0_115,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t94_xboole_1])).

cnf(c_0_116,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),X2) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_108]),c_0_73]),c_0_109])).

cnf(c_0_117,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_47])).

cnf(c_0_118,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k2_xboole_0(k5_xboole_0(X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112]),c_0_112]),c_0_110]),c_0_113]),c_0_103])).

cnf(c_0_119,plain,
    ( k3_xboole_0(k2_xboole_0(X1,k5_xboole_0(X2,X2)),X2) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_114,c_0_99])).

fof(c_0_120,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_115])])])).

cnf(c_0_121,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),X1) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_116,c_0_47])).

cnf(c_0_122,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = k2_xboole_0(k5_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_123,plain,
    ( k3_xboole_0(k2_xboole_0(k5_xboole_0(X1,X1),X2),X1) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_119,c_0_11])).

cnf(c_0_124,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_125,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X2)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_69,c_0_77])).

cnf(c_0_126,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_123])).

cnf(c_0_127,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X2)) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_82]),c_0_55]),c_0_20])).

cnf(c_0_128,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_47]),c_0_53])).

cnf(c_0_129,negated_conjecture,
    ( k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0))) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_124,c_0_53])).

cnf(c_0_130,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_127]),c_0_11]),c_0_100]),c_0_128]),c_0_47])).

cnf(c_0_131,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_130]),c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 0.48/0.71  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.48/0.71  # and selection function SelectNewComplexAHP.
% 0.48/0.71  #
% 0.48/0.71  # Preprocessing time       : 0.025 s
% 0.48/0.71  # Presaturation interreduction done
% 0.48/0.71  
% 0.48/0.71  # Proof found!
% 0.48/0.71  # SZS status Theorem
% 0.48/0.71  # SZS output start CNFRefutation
% 0.48/0.71  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.48/0.71  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.48/0.71  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.48/0.71  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.48/0.71  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.48/0.71  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.48/0.71  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.48/0.71  fof(t94_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.48/0.71  fof(c_0_8, plain, ![X10, X11]:k4_xboole_0(k2_xboole_0(X10,X11),X11)=k4_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.48/0.71  fof(c_0_9, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.48/0.71  cnf(c_0_10, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.48/0.71  cnf(c_0_11, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.48/0.71  fof(c_0_12, plain, ![X8, X9]:k2_xboole_0(X8,k4_xboole_0(X9,X8))=k2_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.48/0.71  fof(c_0_13, plain, ![X12, X13, X14]:k4_xboole_0(k4_xboole_0(X12,X13),X14)=k4_xboole_0(X12,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.48/0.71  cnf(c_0_14, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.48/0.71  cnf(c_0_15, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.48/0.71  cnf(c_0_16, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.48/0.71  fof(c_0_17, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.48/0.71  fof(c_0_18, plain, ![X15, X16]:k4_xboole_0(X15,k4_xboole_0(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.48/0.71  cnf(c_0_19, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_14]), c_0_16])).
% 0.48/0.71  cnf(c_0_20, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.71  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.48/0.71  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=k4_xboole_0(X1,k5_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.48/0.71  cnf(c_0_23, plain, (k4_xboole_0(X1,k5_xboole_0(X1,X1))=k3_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.48/0.71  cnf(c_0_24, plain, (k2_xboole_0(k5_xboole_0(X1,X1),k3_xboole_0(X1,X1))=k2_xboole_0(X1,k5_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_23]), c_0_11])).
% 0.48/0.71  cnf(c_0_25, plain, (k4_xboole_0(k3_xboole_0(X1,X1),k5_xboole_0(X1,X1))=k3_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_24]), c_0_10]), c_0_23])).
% 0.48/0.71  cnf(c_0_26, plain, (k4_xboole_0(X1,k2_xboole_0(k5_xboole_0(X1,X1),X2))=k4_xboole_0(k3_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_16, c_0_23])).
% 0.48/0.71  cnf(c_0_27, plain, (k4_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1))=k3_xboole_0(k3_xboole_0(X1,X1),k5_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_21, c_0_25])).
% 0.48/0.71  cnf(c_0_28, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_16]), c_0_16])).
% 0.48/0.71  cnf(c_0_29, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_19]), c_0_21])).
% 0.48/0.71  cnf(c_0_30, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k3_xboole_0(k2_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_21, c_0_10])).
% 0.48/0.71  cnf(c_0_31, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_10, c_0_15])).
% 0.48/0.71  cnf(c_0_32, plain, (k4_xboole_0(X1,k2_xboole_0(X1,k5_xboole_0(X1,X1)))=k3_xboole_0(k3_xboole_0(X1,X1),k5_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_24]), c_0_27])).
% 0.48/0.71  cnf(c_0_33, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,X1)))=k4_xboole_0(k3_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_26, c_0_11])).
% 0.48/0.71  cnf(c_0_34, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k3_xboole_0(k4_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_19]), c_0_15])).
% 0.48/0.71  cnf(c_0_35, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X2))=k3_xboole_0(X1,k5_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_29, c_0_20])).
% 0.48/0.71  cnf(c_0_36, plain, (k3_xboole_0(k2_xboole_0(X1,X1),X1)=k3_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_21])).
% 0.48/0.71  cnf(c_0_37, plain, (k3_xboole_0(k3_xboole_0(X1,X1),k5_xboole_0(X1,X1))=k4_xboole_0(k3_xboole_0(X1,X1),X1)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.48/0.71  cnf(c_0_38, plain, (k3_xboole_0(k4_xboole_0(X1,X1),X1)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_19, c_0_34])).
% 0.48/0.71  cnf(c_0_39, plain, (k3_xboole_0(k4_xboole_0(X1,X1),k5_xboole_0(X1,X1))=k3_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_35]), c_0_20])).
% 0.48/0.71  cnf(c_0_40, plain, (k4_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1))=k4_xboole_0(k3_xboole_0(X1,X1),X1)), inference(rw,[status(thm)],[c_0_27, c_0_37])).
% 0.48/0.71  cnf(c_0_41, plain, (k3_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_38]), c_0_16]), c_0_15]), c_0_19]), c_0_16]), c_0_15]), c_0_19]), c_0_39])).
% 0.48/0.71  cnf(c_0_42, plain, (k4_xboole_0(k3_xboole_0(X1,X1),X1)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_16]), c_0_15]), c_0_19]), c_0_16]), c_0_33])).
% 0.48/0.71  cnf(c_0_43, plain, (k4_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[c_0_40, c_0_42])).
% 0.48/0.71  cnf(c_0_44, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_21]), c_0_11]), c_0_11])).
% 0.48/0.71  fof(c_0_45, plain, ![X17, X18, X19]:k5_xboole_0(k5_xboole_0(X17,X18),X19)=k5_xboole_0(X17,k5_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.48/0.71  cnf(c_0_46, plain, (k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X3,k4_xboole_0(X1,X2)))=k5_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_20, c_0_16])).
% 0.48/0.71  cnf(c_0_47, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_20]), c_0_20])).
% 0.48/0.71  cnf(c_0_48, plain, (k2_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1))=k2_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_43]), c_0_44]), c_0_15])).
% 0.48/0.71  cnf(c_0_49, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.48/0.71  cnf(c_0_50, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_14]), c_0_15])).
% 0.48/0.71  cnf(c_0_51, plain, (k4_xboole_0(k2_xboole_0(X1,X1),k5_xboole_0(X1,X1))=k3_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_30]), c_0_36])).
% 0.48/0.71  cnf(c_0_52, plain, (k2_xboole_0(k3_xboole_0(X1,X1),k4_xboole_0(k5_xboole_0(X1,X1),X1))=k5_xboole_0(X1,k5_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_20, c_0_23])).
% 0.48/0.71  cnf(c_0_53, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.48/0.71  cnf(c_0_54, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_19]), c_0_15]), c_0_11]), c_0_15]), c_0_47])).
% 0.48/0.71  cnf(c_0_55, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_48]), c_0_19])).
% 0.48/0.71  cnf(c_0_56, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X1))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_15])).
% 0.48/0.71  cnf(c_0_57, plain, (k5_xboole_0(k2_xboole_0(X1,X1),k5_xboole_0(X1,X1))=k5_xboole_0(X1,k5_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_51]), c_0_19]), c_0_52])).
% 0.48/0.71  cnf(c_0_58, plain, (k5_xboole_0(k3_xboole_0(X1,X1),k3_xboole_0(X1,X1))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_43]), c_0_27]), c_0_37]), c_0_42]), c_0_20])).
% 0.48/0.71  cnf(c_0_59, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X1)))=k2_xboole_0(X1,k5_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_25]), c_0_15]), c_0_47]), c_0_53]), c_0_11]), c_0_24])).
% 0.48/0.71  cnf(c_0_60, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_10]), c_0_15])).
% 0.48/0.71  cnf(c_0_61, plain, (k5_xboole_0(k3_xboole_0(X1,X1),k4_xboole_0(X2,X1))=k2_xboole_0(k3_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.48/0.71  cnf(c_0_62, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_42]), c_0_56]), c_0_11]), c_0_50])).
% 0.48/0.71  cnf(c_0_63, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_10]), c_0_16])).
% 0.48/0.71  cnf(c_0_64, plain, (k4_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_41]), c_0_16]), c_0_33]), c_0_42])).
% 0.48/0.71  cnf(c_0_65, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=k2_xboole_0(X1,k5_xboole_0(X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_48]), c_0_58]), c_0_57]), c_0_58]), c_0_47]), c_0_53]), c_0_59])).
% 0.48/0.71  cnf(c_0_66, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_60]), c_0_11]), c_0_60])).
% 0.48/0.71  cnf(c_0_67, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k4_xboole_0(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_10, c_0_60])).
% 0.48/0.71  cnf(c_0_68, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k4_xboole_0(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_10, c_0_50])).
% 0.48/0.71  cnf(c_0_69, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X2))=k2_xboole_0(k3_xboole_0(X2,X2),X1)), inference(spm,[status(thm)],[c_0_47, c_0_61])).
% 0.48/0.71  cnf(c_0_70, plain, (k2_xboole_0(k3_xboole_0(X1,X1),k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_11, c_0_62])).
% 0.48/0.71  cnf(c_0_71, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k4_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_14]), c_0_16])).
% 0.48/0.71  cnf(c_0_72, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_63]), c_0_15])).
% 0.48/0.71  cnf(c_0_73, plain, (k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X2,k2_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_20]), c_0_16])).
% 0.48/0.71  cnf(c_0_74, plain, (k5_xboole_0(X1,k2_xboole_0(X1,k5_xboole_0(X1,X1)))=k5_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_64]), c_0_64]), c_0_20]), c_0_53]), c_0_65])).
% 0.48/0.71  cnf(c_0_75, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k4_xboole_0(X2,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_66]), c_0_67]), c_0_68])).
% 0.48/0.71  cnf(c_0_76, plain, (k4_xboole_0(k2_xboole_0(X1,k3_xboole_0(X2,X2)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_48]), c_0_19]), c_0_19])).
% 0.48/0.71  cnf(c_0_77, plain, (k2_xboole_0(k3_xboole_0(X1,X1),X2)=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_14]), c_0_69]), c_0_70])).
% 0.48/0.71  cnf(c_0_78, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_71]), c_0_15])).
% 0.48/0.71  cnf(c_0_79, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k2_xboole_0(k2_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_11, c_0_72])).
% 0.48/0.71  cnf(c_0_80, plain, (k4_xboole_0(k5_xboole_0(X1,X1),X1)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_33]), c_0_42]), c_0_22]), c_0_64]), c_0_33]), c_0_42]), c_0_15]), c_0_19]), c_0_14])).
% 0.48/0.71  cnf(c_0_81, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k3_xboole_0(k4_xboole_0(X2,X1),X1)), inference(spm,[status(thm)],[c_0_34, c_0_75])).
% 0.48/0.71  cnf(c_0_82, plain, (k4_xboole_0(k3_xboole_0(X1,X1),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_76])).
% 0.48/0.71  cnf(c_0_83, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X3,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_11]), c_0_79])).
% 0.48/0.71  cnf(c_0_84, plain, (k2_xboole_0(X1,k5_xboole_0(X1,X1))=k2_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_80]), c_0_23]), c_0_11]), c_0_44]), c_0_15]), c_0_53]), c_0_65])).
% 0.48/0.71  cnf(c_0_85, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k3_xboole_0(k4_xboole_0(X2,X1),X1)), inference(spm,[status(thm)],[c_0_81, c_0_11])).
% 0.48/0.71  cnf(c_0_86, plain, (k4_xboole_0(k5_xboole_0(X1,X1),X2)=k3_xboole_0(k4_xboole_0(X2,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_41]), c_0_16]), c_0_81])).
% 0.48/0.71  cnf(c_0_87, plain, (k2_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k2_xboole_0(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_56, c_0_11])).
% 0.48/0.71  cnf(c_0_88, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X2,k2_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_11, c_0_83])).
% 0.48/0.71  cnf(c_0_89, plain, (k5_xboole_0(k3_xboole_0(X1,X1),X2)=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_82]), c_0_55]), c_0_20])).
% 0.48/0.71  cnf(c_0_90, plain, (k2_xboole_0(k5_xboole_0(X1,X1),k3_xboole_0(X1,X1))=k2_xboole_0(X1,X1)), inference(rw,[status(thm)],[c_0_24, c_0_84])).
% 0.48/0.71  cnf(c_0_91, plain, (k2_xboole_0(X1,k3_xboole_0(k4_xboole_0(X2,X1),X1))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_49, c_0_85])).
% 0.48/0.71  cnf(c_0_92, plain, (k3_xboole_0(k4_xboole_0(X1,X2),X2)=k3_xboole_0(k4_xboole_0(X2,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_81]), c_0_85])).
% 0.48/0.71  cnf(c_0_93, plain, (k2_xboole_0(X1,k3_xboole_0(k4_xboole_0(X1,X2),X2))=k2_xboole_0(X1,k5_xboole_0(X2,X2))), inference(spm,[status(thm)],[c_0_15, c_0_86])).
% 0.48/0.71  cnf(c_0_94, plain, (k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88]), c_0_88])).
% 0.48/0.71  cnf(c_0_95, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_21, c_0_21])).
% 0.48/0.71  cnf(c_0_96, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X1))=k2_xboole_0(X1,X1)), inference(rw,[status(thm)],[c_0_65, c_0_84])).
% 0.48/0.71  cnf(c_0_97, plain, (k5_xboole_0(k2_xboole_0(X1,X1),X2)=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_29]), c_0_36]), c_0_89])).
% 0.48/0.71  cnf(c_0_98, plain, (k4_xboole_0(k2_xboole_0(X1,k5_xboole_0(X2,X2)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_90]), c_0_19]), c_0_19])).
% 0.48/0.71  cnf(c_0_99, plain, (k2_xboole_0(X1,k5_xboole_0(X2,X2))=k2_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])).
% 0.48/0.71  cnf(c_0_100, plain, (k2_xboole_0(X1,k5_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_20]), c_0_15]), c_0_60])).
% 0.48/0.71  cnf(c_0_101, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(k4_xboole_0(X1,X2),X3)))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_95]), c_0_16])).
% 0.48/0.71  cnf(c_0_102, plain, (k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_92]), c_0_16]), c_0_93]), c_0_33]), c_0_82]), c_0_16]), c_0_19])).
% 0.48/0.71  cnf(c_0_103, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2)))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_96]), c_0_53]), c_0_97])).
% 0.48/0.71  cnf(c_0_104, plain, (k5_xboole_0(k3_xboole_0(X1,X1),k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_61, c_0_77])).
% 0.48/0.71  cnf(c_0_105, plain, (k4_xboole_0(X1,k2_xboole_0(k5_xboole_0(X1,X1),X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_82])).
% 0.48/0.71  cnf(c_0_106, plain, (k4_xboole_0(k2_xboole_0(k5_xboole_0(X1,X1),X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_90]), c_0_19]), c_0_19])).
% 0.48/0.71  cnf(c_0_107, plain, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X1,X2)),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.48/0.71  cnf(c_0_108, plain, (k4_xboole_0(k5_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_100]), c_0_14])).
% 0.48/0.71  cnf(c_0_109, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X2,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_91]), c_0_19]), c_0_102])).
% 0.48/0.71  cnf(c_0_110, plain, (k5_xboole_0(k4_xboole_0(X1,X1),X2)=k5_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_41]), c_0_53])).
% 0.48/0.71  cnf(c_0_111, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k2_xboole_0(X1,X2)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_89]), c_0_89])).
% 0.48/0.71  cnf(c_0_112, plain, (k2_xboole_0(k4_xboole_0(X1,X1),X2)=k2_xboole_0(k5_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_77, c_0_41])).
% 0.48/0.71  cnf(c_0_113, plain, (k5_xboole_0(X1,k2_xboole_0(k5_xboole_0(X1,X1),X2))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_105]), c_0_106]), c_0_20])).
% 0.48/0.71  cnf(c_0_114, plain, (k3_xboole_0(k2_xboole_0(X1,k4_xboole_0(X1,X2)),X2)=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_107]), c_0_10]), c_0_21])).
% 0.48/0.71  fof(c_0_115, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t94_xboole_1])).
% 0.48/0.71  cnf(c_0_116, plain, (k3_xboole_0(k5_xboole_0(X1,X2),X2)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_108]), c_0_73]), c_0_109])).
% 0.48/0.71  cnf(c_0_117, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_53, c_0_47])).
% 0.48/0.71  cnf(c_0_118, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k2_xboole_0(k5_xboole_0(X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112]), c_0_112]), c_0_110]), c_0_113]), c_0_103])).
% 0.48/0.71  cnf(c_0_119, plain, (k3_xboole_0(k2_xboole_0(X1,k5_xboole_0(X2,X2)),X2)=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_114, c_0_99])).
% 0.48/0.71  fof(c_0_120, negated_conjecture, k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_115])])])).
% 0.48/0.71  cnf(c_0_121, plain, (k3_xboole_0(k5_xboole_0(X1,X2),X1)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_116, c_0_47])).
% 0.48/0.71  cnf(c_0_122, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=k2_xboole_0(k5_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 0.48/0.71  cnf(c_0_123, plain, (k3_xboole_0(k2_xboole_0(k5_xboole_0(X1,X1),X2),X1)=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_119, c_0_11])).
% 0.48/0.71  cnf(c_0_124, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_120])).
% 0.48/0.71  cnf(c_0_125, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X2,X2))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_69, c_0_77])).
% 0.48/0.71  cnf(c_0_126, plain, (k4_xboole_0(X1,k5_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_123])).
% 0.48/0.71  cnf(c_0_127, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X2))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_82]), c_0_55]), c_0_20])).
% 0.48/0.71  cnf(c_0_128, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_47]), c_0_53])).
% 0.48/0.71  cnf(c_0_129, negated_conjecture, (k5_xboole_0(esk1_0,k5_xboole_0(esk2_0,k3_xboole_0(esk1_0,esk2_0)))!=k2_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_124, c_0_53])).
% 0.48/0.71  cnf(c_0_130, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_127]), c_0_11]), c_0_100]), c_0_128]), c_0_47])).
% 0.48/0.71  cnf(c_0_131, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_130]), c_0_11])]), ['proof']).
% 0.48/0.71  # SZS output end CNFRefutation
% 0.48/0.71  # Proof object total steps             : 132
% 0.48/0.71  # Proof object clause steps            : 115
% 0.48/0.71  # Proof object formula steps           : 17
% 0.48/0.71  # Proof object conjectures             : 6
% 0.48/0.71  # Proof object clause conjectures      : 3
% 0.48/0.71  # Proof object formula conjectures     : 3
% 0.48/0.71  # Proof object initial clauses used    : 8
% 0.48/0.71  # Proof object initial formulas used   : 8
% 0.48/0.71  # Proof object generating inferences   : 95
% 0.48/0.71  # Proof object simplifying inferences  : 159
% 0.48/0.71  # Training examples: 0 positive, 0 negative
% 0.48/0.71  # Parsed axioms                        : 8
% 0.48/0.71  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.71  # Initial clauses                      : 8
% 0.48/0.71  # Removed in clause preprocessing      : 0
% 0.48/0.71  # Initial clauses in saturation        : 8
% 0.48/0.71  # Processed clauses                    : 2034
% 0.48/0.71  # ...of these trivial                  : 790
% 0.48/0.71  # ...subsumed                          : 711
% 0.48/0.71  # ...remaining for further processing  : 533
% 0.48/0.71  # Other redundant clauses eliminated   : 0
% 0.48/0.71  # Clauses deleted for lack of memory   : 0
% 0.48/0.71  # Backward-subsumed                    : 1
% 0.48/0.71  # Backward-rewritten                   : 338
% 0.48/0.71  # Generated clauses                    : 52706
% 0.48/0.71  # ...of the previous two non-trivial   : 39406
% 0.48/0.71  # Contextual simplify-reflections      : 0
% 0.48/0.71  # Paramodulations                      : 52706
% 0.48/0.71  # Factorizations                       : 0
% 0.48/0.71  # Equation resolutions                 : 0
% 0.48/0.71  # Propositional unsat checks           : 0
% 0.48/0.71  #    Propositional check models        : 0
% 0.48/0.71  #    Propositional check unsatisfiable : 0
% 0.48/0.71  #    Propositional clauses             : 0
% 0.48/0.71  #    Propositional clauses after purity: 0
% 0.48/0.71  #    Propositional unsat core size     : 0
% 0.48/0.71  #    Propositional preprocessing time  : 0.000
% 0.48/0.71  #    Propositional encoding time       : 0.000
% 0.48/0.71  #    Propositional solver time         : 0.000
% 0.48/0.71  #    Success case prop preproc time    : 0.000
% 0.48/0.71  #    Success case prop encoding time   : 0.000
% 0.48/0.71  #    Success case prop solver time     : 0.000
% 0.48/0.71  # Current number of processed clauses  : 186
% 0.48/0.71  #    Positive orientable unit clauses  : 174
% 0.48/0.71  #    Positive unorientable unit clauses: 12
% 0.48/0.71  #    Negative unit clauses             : 0
% 0.48/0.71  #    Non-unit-clauses                  : 0
% 0.48/0.71  # Current number of unprocessed clauses: 36527
% 0.48/0.71  # ...number of literals in the above   : 36527
% 0.48/0.71  # Current number of archived formulas  : 0
% 0.48/0.71  # Current number of archived clauses   : 347
% 0.48/0.71  # Clause-clause subsumption calls (NU) : 0
% 0.48/0.71  # Rec. Clause-clause subsumption calls : 0
% 0.48/0.71  # Non-unit clause-clause subsumptions  : 0
% 0.48/0.71  # Unit Clause-clause subsumption calls : 193
% 0.48/0.71  # Rewrite failures with RHS unbound    : 0
% 0.48/0.71  # BW rewrite match attempts            : 1634
% 0.48/0.71  # BW rewrite match successes           : 587
% 0.48/0.71  # Condensation attempts                : 0
% 0.48/0.71  # Condensation successes               : 0
% 0.48/0.71  # Termbank termtop insertions          : 535427
% 0.54/0.72  
% 0.54/0.72  # -------------------------------------------------
% 0.54/0.72  # User time                : 0.348 s
% 0.54/0.72  # System time              : 0.023 s
% 0.54/0.72  # Total time               : 0.371 s
% 0.54/0.72  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
