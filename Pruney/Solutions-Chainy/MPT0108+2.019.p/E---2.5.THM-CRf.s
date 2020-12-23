%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:24 EST 2020

% Result     : Theorem 0.07s
% Output     : CNFRefutation 0.07s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 734 expanded)
%              Number of clauses        :   43 ( 333 expanded)
%              Number of leaves         :   12 ( 200 expanded)
%              Depth                    :   16
%              Number of atoms          :   68 ( 734 expanded)
%              Number of equality atoms :   67 ( 733 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t101_xboole_1,conjecture,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

fof(c_0_12,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k2_xboole_0(X13,X14)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_14,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X11,X12] : k2_xboole_0(X11,k3_xboole_0(X11,X12)) = X11 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_18,plain,(
    ! [X23,X24] : k2_xboole_0(X23,X24) = k2_xboole_0(k5_xboole_0(X23,X24),k3_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X8] : k2_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_16])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_26])).

fof(c_0_29,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_30,plain,(
    ! [X25,X26] : k2_xboole_0(X25,X26) = k5_xboole_0(X25,k4_xboole_0(X26,X25)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_31,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_27]),c_0_28])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_28]),c_0_26])).

fof(c_0_36,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_37,plain,(
    ! [X20,X21,X22] : k5_xboole_0(k5_xboole_0(X20,X21),X22) = k5_xboole_0(X20,k5_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_34]),c_0_35])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_23])).

fof(c_0_41,plain,(
    ! [X17,X18,X19] : k3_xboole_0(X17,k4_xboole_0(X18,X19)) = k4_xboole_0(k3_xboole_0(X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_38])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_39])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_21]),c_0_19])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_15]),c_0_46])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_32])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_20,c_0_38])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_33])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_48]),c_0_35])).

cnf(c_0_53,plain,
    ( k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_32])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_39]),c_0_51])).

cnf(c_0_55,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_52]),c_0_39]),c_0_33])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_39]),c_0_23])).

fof(c_0_57,negated_conjecture,(
    ~ ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t101_xboole_1])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_52])).

cnf(c_0_59,plain,
    ( k2_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_40]),c_0_35]),c_0_56])).

cnf(c_0_60,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_56])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_19])).

fof(c_0_62,negated_conjecture,(
    k5_xboole_0(esk1_0,esk2_0) != k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).

cnf(c_0_63,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2 ),
    inference(spm,[status(thm)],[c_0_58,c_0_56])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_59]),c_0_42]),c_0_60]),c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( k5_xboole_0(esk1_0,esk2_0) != k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_56]),c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.08  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.07/0.27  % Computer   : n009.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 13:56:26 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.27  # Version: 2.5pre002
% 0.07/0.27  # No SInE strategy applied
% 0.07/0.27  # Trying AutoSched0 for 299 seconds
% 0.07/0.30  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.07/0.30  # and selection function SelectNewComplexAHP.
% 0.07/0.30  #
% 0.07/0.30  # Preprocessing time       : 0.015 s
% 0.07/0.30  # Presaturation interreduction done
% 0.07/0.30  
% 0.07/0.30  # Proof found!
% 0.07/0.30  # SZS status Theorem
% 0.07/0.30  # SZS output start CNFRefutation
% 0.07/0.30  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.07/0.30  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.07/0.30  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.07/0.30  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.07/0.30  fof(t93_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 0.07/0.30  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.07/0.30  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.07/0.30  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.07/0.30  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.07/0.30  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.07/0.30  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.07/0.30  fof(t101_xboole_1, conjecture, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_xboole_1)).
% 0.07/0.30  fof(c_0_12, plain, ![X15, X16]:k4_xboole_0(X15,k4_xboole_0(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.07/0.30  fof(c_0_13, plain, ![X13, X14]:k4_xboole_0(X13,k2_xboole_0(X13,X14))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.07/0.30  fof(c_0_14, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.07/0.30  cnf(c_0_15, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.07/0.30  cnf(c_0_16, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.07/0.30  fof(c_0_17, plain, ![X11, X12]:k2_xboole_0(X11,k3_xboole_0(X11,X12))=X11, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.07/0.30  fof(c_0_18, plain, ![X23, X24]:k2_xboole_0(X23,X24)=k2_xboole_0(k5_xboole_0(X23,X24),k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t93_xboole_1])).
% 0.07/0.30  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.07/0.30  cnf(c_0_20, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=k4_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.07/0.30  cnf(c_0_21, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.07/0.30  fof(c_0_22, plain, ![X8]:k2_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.07/0.30  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.07/0.30  cnf(c_0_24, plain, (k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_16])).
% 0.07/0.30  cnf(c_0_25, plain, (k2_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=X1), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 0.07/0.30  cnf(c_0_26, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.07/0.30  cnf(c_0_27, plain, (k2_xboole_0(k1_xboole_0,k3_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.07/0.30  cnf(c_0_28, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_26])).
% 0.07/0.30  fof(c_0_29, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.07/0.30  fof(c_0_30, plain, ![X25, X26]:k2_xboole_0(X25,X26)=k5_xboole_0(X25,k4_xboole_0(X26,X25)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.07/0.30  cnf(c_0_31, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_27]), c_0_28])).
% 0.07/0.30  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.07/0.30  cnf(c_0_33, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.07/0.30  cnf(c_0_34, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.07/0.30  cnf(c_0_35, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_28]), c_0_26])).
% 0.07/0.30  fof(c_0_36, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.07/0.30  fof(c_0_37, plain, ![X20, X21, X22]:k5_xboole_0(k5_xboole_0(X20,X21),X22)=k5_xboole_0(X20,k5_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.07/0.30  cnf(c_0_38, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_34]), c_0_35])).
% 0.07/0.30  cnf(c_0_39, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.07/0.30  cnf(c_0_40, plain, (k4_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_23])).
% 0.07/0.30  fof(c_0_41, plain, ![X17, X18, X19]:k3_xboole_0(X17,k4_xboole_0(X18,X19))=k4_xboole_0(k3_xboole_0(X17,X18),X19), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.07/0.30  cnf(c_0_42, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.07/0.30  cnf(c_0_43, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_38])).
% 0.07/0.30  cnf(c_0_44, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_35, c_0_39])).
% 0.07/0.30  cnf(c_0_45, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_21]), c_0_19])).
% 0.07/0.30  cnf(c_0_46, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.07/0.30  cnf(c_0_47, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.07/0.30  cnf(c_0_48, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_15]), c_0_46])).
% 0.07/0.30  cnf(c_0_49, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_32])).
% 0.07/0.30  cnf(c_0_50, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_20, c_0_38])).
% 0.07/0.30  cnf(c_0_51, plain, (k5_xboole_0(X1,k2_xboole_0(X1,X2))=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_47, c_0_33])).
% 0.07/0.30  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_48]), c_0_35])).
% 0.07/0.30  cnf(c_0_53, plain, (k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_32])).
% 0.07/0.30  cnf(c_0_54, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_39]), c_0_51])).
% 0.07/0.30  cnf(c_0_55, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_52]), c_0_39]), c_0_33])).
% 0.07/0.30  cnf(c_0_56, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_39]), c_0_23])).
% 0.07/0.30  fof(c_0_57, negated_conjecture, ~(![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t101_xboole_1])).
% 0.07/0.30  cnf(c_0_58, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_52])).
% 0.07/0.30  cnf(c_0_59, plain, (k2_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_40]), c_0_35]), c_0_56])).
% 0.07/0.30  cnf(c_0_60, plain, (k5_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_51, c_0_56])).
% 0.07/0.30  cnf(c_0_61, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_19])).
% 0.07/0.30  fof(c_0_62, negated_conjecture, k5_xboole_0(esk1_0,esk2_0)!=k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).
% 0.07/0.30  cnf(c_0_63, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X2), inference(spm,[status(thm)],[c_0_58, c_0_56])).
% 0.07/0.30  cnf(c_0_64, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_59]), c_0_42]), c_0_60]), c_0_61])).
% 0.07/0.30  cnf(c_0_65, negated_conjecture, (k5_xboole_0(esk1_0,esk2_0)!=k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.07/0.30  cnf(c_0_66, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_56]), c_0_59])).
% 0.07/0.30  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])]), ['proof']).
% 0.07/0.30  # SZS output end CNFRefutation
% 0.07/0.30  # Proof object total steps             : 68
% 0.07/0.30  # Proof object clause steps            : 43
% 0.07/0.30  # Proof object formula steps           : 25
% 0.07/0.30  # Proof object conjectures             : 5
% 0.07/0.30  # Proof object clause conjectures      : 2
% 0.07/0.30  # Proof object formula conjectures     : 3
% 0.07/0.30  # Proof object initial clauses used    : 12
% 0.07/0.30  # Proof object initial formulas used   : 12
% 0.07/0.30  # Proof object generating inferences   : 28
% 0.07/0.30  # Proof object simplifying inferences  : 26
% 0.07/0.30  # Training examples: 0 positive, 0 negative
% 0.07/0.30  # Parsed axioms                        : 12
% 0.07/0.30  # Removed by relevancy pruning/SinE    : 0
% 0.07/0.30  # Initial clauses                      : 12
% 0.07/0.30  # Removed in clause preprocessing      : 0
% 0.07/0.30  # Initial clauses in saturation        : 12
% 0.07/0.30  # Processed clauses                    : 396
% 0.07/0.30  # ...of these trivial                  : 190
% 0.07/0.30  # ...subsumed                          : 68
% 0.07/0.30  # ...remaining for further processing  : 138
% 0.07/0.30  # Other redundant clauses eliminated   : 0
% 0.07/0.30  # Clauses deleted for lack of memory   : 0
% 0.07/0.30  # Backward-subsumed                    : 0
% 0.07/0.30  # Backward-rewritten                   : 33
% 0.07/0.30  # Generated clauses                    : 3884
% 0.07/0.30  # ...of the previous two non-trivial   : 1844
% 0.07/0.30  # Contextual simplify-reflections      : 0
% 0.07/0.30  # Paramodulations                      : 3884
% 0.07/0.30  # Factorizations                       : 0
% 0.07/0.30  # Equation resolutions                 : 0
% 0.07/0.30  # Propositional unsat checks           : 0
% 0.07/0.30  #    Propositional check models        : 0
% 0.07/0.30  #    Propositional check unsatisfiable : 0
% 0.07/0.30  #    Propositional clauses             : 0
% 0.07/0.30  #    Propositional clauses after purity: 0
% 0.07/0.30  #    Propositional unsat core size     : 0
% 0.07/0.30  #    Propositional preprocessing time  : 0.000
% 0.07/0.30  #    Propositional encoding time       : 0.000
% 0.07/0.30  #    Propositional solver time         : 0.000
% 0.07/0.30  #    Success case prop preproc time    : 0.000
% 0.07/0.30  #    Success case prop encoding time   : 0.000
% 0.07/0.30  #    Success case prop solver time     : 0.000
% 0.07/0.30  # Current number of processed clauses  : 93
% 0.07/0.30  #    Positive orientable unit clauses  : 89
% 0.07/0.30  #    Positive unorientable unit clauses: 4
% 0.07/0.30  #    Negative unit clauses             : 0
% 0.07/0.30  #    Non-unit-clauses                  : 0
% 0.07/0.30  # Current number of unprocessed clauses: 1441
% 0.07/0.30  # ...number of literals in the above   : 1441
% 0.07/0.30  # Current number of archived formulas  : 0
% 0.07/0.30  # Current number of archived clauses   : 45
% 0.07/0.30  # Clause-clause subsumption calls (NU) : 0
% 0.07/0.30  # Rec. Clause-clause subsumption calls : 0
% 0.07/0.30  # Non-unit clause-clause subsumptions  : 0
% 0.07/0.30  # Unit Clause-clause subsumption calls : 10
% 0.07/0.30  # Rewrite failures with RHS unbound    : 0
% 0.07/0.30  # BW rewrite match attempts            : 232
% 0.07/0.30  # BW rewrite match successes           : 136
% 0.07/0.30  # Condensation attempts                : 0
% 0.07/0.30  # Condensation successes               : 0
% 0.07/0.30  # Termbank termtop insertions          : 23729
% 0.07/0.30  
% 0.07/0.30  # -------------------------------------------------
% 0.07/0.30  # User time                : 0.030 s
% 0.07/0.30  # System time              : 0.003 s
% 0.07/0.30  # Total time               : 0.032 s
% 0.07/0.30  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
