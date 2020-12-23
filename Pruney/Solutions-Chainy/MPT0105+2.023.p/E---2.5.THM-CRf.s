%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:11 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   73 (4651 expanded)
%              Number of clauses        :   50 (2048 expanded)
%              Number of leaves         :   11 (1301 expanded)
%              Depth                    :   20
%              Number of atoms          :   73 (4651 expanded)
%              Number of equality atoms :   72 (4650 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(l98_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t98_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(c_0_11,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k2_xboole_0(X15,X16)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_12,plain,(
    ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_13,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X11] : k4_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_18,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k4_xboole_0(k2_xboole_0(X6,X7),k3_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[l98_xboole_1])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k5_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_24,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

fof(c_0_26,plain,(
    ! [X19,X20,X21] : k5_xboole_0(k5_xboole_0(X19,X20),X21) = k5_xboole_0(X19,k5_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_21]),c_0_20])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_21]),c_0_16])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_16]),c_0_20])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_27]),c_0_28]),c_0_21])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_34,plain,(
    ! [X22,X23] : k2_xboole_0(X22,X23) = k5_xboole_0(k5_xboole_0(X22,X23),k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_36,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_35,c_0_29])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X2,X1))) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_31]),c_0_29])).

fof(c_0_40,plain,(
    ! [X12,X13,X14] : k4_xboole_0(k4_xboole_0(X12,X13),X14) = k4_xboole_0(X12,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k5_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_39])).

cnf(c_0_42,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X2,X1))) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_41]),c_0_29]),c_0_31])).

cnf(c_0_44,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_15]),c_0_16])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_42]),c_0_22])).

cnf(c_0_46,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_32]),c_0_30])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_41]),c_0_29]),c_0_31])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_45]),c_0_20])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_42])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_46]),c_0_44]),c_0_29])).

cnf(c_0_51,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_32]),c_0_30])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_45]),c_0_16])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3)))) = k3_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_42]),c_0_42])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_43,c_0_50])).

cnf(c_0_55,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_52])).

cnf(c_0_57,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X2) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_45]),c_0_16])).

cnf(c_0_58,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_28]),c_0_22]),c_0_45])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_19]),c_0_56])).

cnf(c_0_60,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X2) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_57]),c_0_32]),c_0_30])).

fof(c_0_61,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t98_xboole_1])).

cnf(c_0_62,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_19])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_47,c_0_59])).

cnf(c_0_64,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_60]),c_0_57]),c_0_29])).

fof(c_0_65,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_61])])])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_60])).

cnf(c_0_67,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_63]),c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_69,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk1_0) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_63])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_69]),c_0_22]),c_0_30]),c_0_29]),c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:15:07 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.15/0.39  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.15/0.39  # and selection function SelectNewComplexAHP.
% 0.15/0.39  #
% 0.15/0.39  # Preprocessing time       : 0.026 s
% 0.15/0.39  # Presaturation interreduction done
% 0.15/0.39  
% 0.15/0.39  # Proof found!
% 0.15/0.39  # SZS status Theorem
% 0.15/0.39  # SZS output start CNFRefutation
% 0.15/0.39  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.15/0.39  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.15/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.15/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.15/0.39  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.15/0.39  fof(l98_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 0.15/0.39  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.15/0.39  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.15/0.39  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.15/0.39  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.15/0.39  fof(t98_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.15/0.39  fof(c_0_11, plain, ![X15, X16]:k4_xboole_0(X15,k2_xboole_0(X15,X16))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.15/0.39  fof(c_0_12, plain, ![X8]:k2_xboole_0(X8,k1_xboole_0)=X8, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.15/0.39  fof(c_0_13, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.15/0.39  fof(c_0_14, plain, ![X11]:k4_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.15/0.39  cnf(c_0_15, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.39  cnf(c_0_16, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.39  fof(c_0_17, plain, ![X9, X10]:k2_xboole_0(X9,k4_xboole_0(X10,X9))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.15/0.39  fof(c_0_18, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k4_xboole_0(k2_xboole_0(X6,X7),k3_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[l98_xboole_1])).
% 0.15/0.39  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.39  cnf(c_0_20, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  cnf(c_0_21, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.15/0.39  cnf(c_0_22, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.39  fof(c_0_23, plain, ![X4, X5]:k5_xboole_0(X4,X5)=k5_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.15/0.39  cnf(c_0_24, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.39  cnf(c_0_25, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.15/0.39  fof(c_0_26, plain, ![X19, X20, X21]:k5_xboole_0(k5_xboole_0(X19,X20),X21)=k5_xboole_0(X19,k5_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.15/0.39  cnf(c_0_27, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_21]), c_0_20])).
% 0.15/0.39  cnf(c_0_28, plain, (k2_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_21]), c_0_16])).
% 0.15/0.39  cnf(c_0_29, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.15/0.39  cnf(c_0_30, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_16]), c_0_20])).
% 0.15/0.39  cnf(c_0_31, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.15/0.39  cnf(c_0_32, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_27]), c_0_28]), c_0_21])).
% 0.15/0.39  cnf(c_0_33, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.15/0.39  fof(c_0_34, plain, ![X22, X23]:k2_xboole_0(X22,X23)=k5_xboole_0(k5_xboole_0(X22,X23),k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.15/0.39  cnf(c_0_35, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.15/0.39  cnf(c_0_36, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.15/0.39  cnf(c_0_37, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_35, c_0_29])).
% 0.15/0.39  cnf(c_0_38, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_36, c_0_31])).
% 0.15/0.39  cnf(c_0_39, plain, (k5_xboole_0(X1,k5_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X2,X1)))=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_31]), c_0_29])).
% 0.15/0.39  fof(c_0_40, plain, ![X12, X13, X14]:k4_xboole_0(k4_xboole_0(X12,X13),X14)=k4_xboole_0(X12,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.15/0.39  cnf(c_0_41, plain, (k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k5_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_35, c_0_39])).
% 0.15/0.39  cnf(c_0_42, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.39  cnf(c_0_43, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k2_xboole_0(X2,X1)))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_41]), c_0_29]), c_0_31])).
% 0.15/0.39  cnf(c_0_44, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X1)=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_15]), c_0_16])).
% 0.15/0.39  cnf(c_0_45, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_42]), c_0_22])).
% 0.15/0.39  cnf(c_0_46, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_32]), c_0_30])).
% 0.15/0.39  cnf(c_0_47, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_41]), c_0_29]), c_0_31])).
% 0.15/0.39  cnf(c_0_48, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_45]), c_0_20])).
% 0.15/0.39  cnf(c_0_49, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_22, c_0_42])).
% 0.15/0.39  cnf(c_0_50, plain, (k5_xboole_0(X1,k2_xboole_0(X1,X2))=k4_xboole_0(k2_xboole_0(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_46]), c_0_44]), c_0_29])).
% 0.15/0.39  cnf(c_0_51, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_32]), c_0_30])).
% 0.15/0.39  cnf(c_0_52, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_45]), c_0_16])).
% 0.15/0.39  cnf(c_0_53, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,k2_xboole_0(X2,X3))))=k3_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_42]), c_0_42])).
% 0.15/0.39  cnf(c_0_54, plain, (k5_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X2))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_43, c_0_50])).
% 0.15/0.39  cnf(c_0_55, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.15/0.39  cnf(c_0_56, plain, (k3_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_48, c_0_52])).
% 0.15/0.39  cnf(c_0_57, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X2)=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_45]), c_0_16])).
% 0.15/0.39  cnf(c_0_58, plain, (k3_xboole_0(k4_xboole_0(X1,X2),X2)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_28]), c_0_22]), c_0_45])).
% 0.15/0.39  cnf(c_0_59, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_19]), c_0_56])).
% 0.15/0.39  cnf(c_0_60, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X2)=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_57]), c_0_32]), c_0_30])).
% 0.15/0.39  fof(c_0_61, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(assume_negation,[status(cth)],[t98_xboole_1])).
% 0.15/0.39  cnf(c_0_62, plain, (k3_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_19])).
% 0.15/0.39  cnf(c_0_63, plain, (k5_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_47, c_0_59])).
% 0.15/0.39  cnf(c_0_64, plain, (k5_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(k2_xboole_0(X2,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_60]), c_0_57]), c_0_29])).
% 0.15/0.39  fof(c_0_65, negated_conjecture, k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_61])])])).
% 0.15/0.39  cnf(c_0_66, plain, (k3_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_60])).
% 0.15/0.39  cnf(c_0_67, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_63]), c_0_64])).
% 0.15/0.39  cnf(c_0_68, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.15/0.39  cnf(c_0_69, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.15/0.39  cnf(c_0_70, negated_conjecture, (k2_xboole_0(esk2_0,esk1_0)!=k2_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_68, c_0_63])).
% 0.15/0.39  cnf(c_0_71, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_69]), c_0_22]), c_0_30]), c_0_29]), c_0_63])).
% 0.15/0.39  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71])]), ['proof']).
% 0.15/0.39  # SZS output end CNFRefutation
% 0.15/0.39  # Proof object total steps             : 73
% 0.15/0.39  # Proof object clause steps            : 50
% 0.15/0.39  # Proof object formula steps           : 23
% 0.15/0.39  # Proof object conjectures             : 6
% 0.15/0.39  # Proof object clause conjectures      : 3
% 0.15/0.39  # Proof object formula conjectures     : 3
% 0.15/0.39  # Proof object initial clauses used    : 11
% 0.15/0.39  # Proof object initial formulas used   : 11
% 0.15/0.39  # Proof object generating inferences   : 33
% 0.15/0.39  # Proof object simplifying inferences  : 46
% 0.15/0.39  # Training examples: 0 positive, 0 negative
% 0.15/0.39  # Parsed axioms                        : 11
% 0.15/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.39  # Initial clauses                      : 11
% 0.15/0.39  # Removed in clause preprocessing      : 0
% 0.15/0.40  # Initial clauses in saturation        : 11
% 0.15/0.40  # Processed clauses                    : 134
% 0.15/0.40  # ...of these trivial                  : 41
% 0.15/0.40  # ...subsumed                          : 1
% 0.15/0.40  # ...remaining for further processing  : 92
% 0.15/0.40  # Other redundant clauses eliminated   : 0
% 0.15/0.40  # Clauses deleted for lack of memory   : 0
% 0.15/0.40  # Backward-subsumed                    : 0
% 0.15/0.40  # Backward-rewritten                   : 24
% 0.15/0.40  # Generated clauses                    : 1381
% 0.15/0.40  # ...of the previous two non-trivial   : 567
% 0.15/0.40  # Contextual simplify-reflections      : 0
% 0.15/0.40  # Paramodulations                      : 1381
% 0.15/0.40  # Factorizations                       : 0
% 0.15/0.40  # Equation resolutions                 : 0
% 0.15/0.40  # Propositional unsat checks           : 0
% 0.15/0.40  #    Propositional check models        : 0
% 0.15/0.40  #    Propositional check unsatisfiable : 0
% 0.15/0.40  #    Propositional clauses             : 0
% 0.15/0.40  #    Propositional clauses after purity: 0
% 0.15/0.40  #    Propositional unsat core size     : 0
% 0.15/0.40  #    Propositional preprocessing time  : 0.000
% 0.15/0.40  #    Propositional encoding time       : 0.000
% 0.15/0.40  #    Propositional solver time         : 0.000
% 0.15/0.40  #    Success case prop preproc time    : 0.000
% 0.15/0.40  #    Success case prop encoding time   : 0.000
% 0.15/0.40  #    Success case prop solver time     : 0.000
% 0.15/0.40  # Current number of processed clauses  : 57
% 0.15/0.40  #    Positive orientable unit clauses  : 55
% 0.15/0.40  #    Positive unorientable unit clauses: 2
% 0.15/0.40  #    Negative unit clauses             : 0
% 0.15/0.40  #    Non-unit-clauses                  : 0
% 0.15/0.40  # Current number of unprocessed clauses: 443
% 0.15/0.40  # ...number of literals in the above   : 443
% 0.15/0.40  # Current number of archived formulas  : 0
% 0.15/0.40  # Current number of archived clauses   : 35
% 0.15/0.40  # Clause-clause subsumption calls (NU) : 0
% 0.15/0.40  # Rec. Clause-clause subsumption calls : 0
% 0.15/0.40  # Non-unit clause-clause subsumptions  : 0
% 0.15/0.40  # Unit Clause-clause subsumption calls : 7
% 0.15/0.40  # Rewrite failures with RHS unbound    : 0
% 0.15/0.40  # BW rewrite match attempts            : 127
% 0.15/0.40  # BW rewrite match successes           : 70
% 0.15/0.40  # Condensation attempts                : 0
% 0.15/0.40  # Condensation successes               : 0
% 0.15/0.40  # Termbank termtop insertions          : 8409
% 0.15/0.40  
% 0.15/0.40  # -------------------------------------------------
% 0.15/0.40  # User time                : 0.033 s
% 0.15/0.40  # System time              : 0.006 s
% 0.15/0.40  # Total time               : 0.039 s
% 0.15/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
