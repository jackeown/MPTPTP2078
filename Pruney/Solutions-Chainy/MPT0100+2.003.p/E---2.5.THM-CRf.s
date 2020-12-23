%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:56 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 808 expanded)
%              Number of clauses        :   46 ( 357 expanded)
%              Number of leaves         :   14 ( 225 expanded)
%              Depth                    :   19
%              Number of atoms          :   75 ( 808 expanded)
%              Number of equality atoms :   74 ( 807 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t24_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t93_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(c_0_14,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k3_xboole_0(X22,X23) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_16,plain,(
    ! [X10] : k2_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_17,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_18,plain,(
    ! [X30] : k5_xboole_0(X30,X30) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X11,X12] : k2_xboole_0(X11,k3_xboole_0(X11,X12)) = X11 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X1) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])).

fof(c_0_28,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_31,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k3_xboole_0(X20,X21)) = k4_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_33,plain,(
    ! [X17,X18,X19] : k4_xboole_0(k4_xboole_0(X17,X18),X19) = k4_xboole_0(X17,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_32])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_25,c_0_27])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_20])).

fof(c_0_39,plain,(
    ! [X13,X14,X15] : k2_xboole_0(X13,k3_xboole_0(X14,X15)) = k3_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(X13,X15)) ),
    inference(variable_rename,[status(thm)],[t24_xboole_1])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_42,plain,(
    ! [X24,X25,X26] : k3_xboole_0(X24,k4_xboole_0(X25,X26)) = k4_xboole_0(k3_xboole_0(X24,X25),X26) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_44,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_29]),c_0_27]),c_0_29])).

fof(c_0_45,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_46,plain,(
    ! [X27,X28,X29] : k2_xboole_0(k2_xboole_0(X27,X28),X29) = k2_xboole_0(X27,k2_xboole_0(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_43]),c_0_20])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_22]),c_0_44])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_19]),c_0_34])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k3_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_19]),c_0_47])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_51])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_22])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_23]),c_0_36])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,X2)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_23]),c_0_19]),c_0_54])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_50])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_55])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_56]),c_0_41])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_57]),c_0_20])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_58]),c_0_59])).

cnf(c_0_64,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_23])).

fof(c_0_65,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t93_xboole_1])).

cnf(c_0_66,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64])).

fof(c_0_67,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k2_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_65])])])).

cnf(c_0_68,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_64,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k2_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_70,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_58]),c_0_30]),c_0_30]),c_0_66])).

cnf(c_0_71,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_30]),c_0_23])).

cnf(c_0_72,negated_conjecture,
    ( k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k5_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_69,c_0_30])).

cnf(c_0_73,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:40:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.45  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.18/0.45  # and selection function SelectNewComplexAHP.
% 0.18/0.45  #
% 0.18/0.45  # Preprocessing time       : 0.026 s
% 0.18/0.45  # Presaturation interreduction done
% 0.18/0.45  
% 0.18/0.45  # Proof found!
% 0.18/0.45  # SZS status Theorem
% 0.18/0.45  # SZS output start CNFRefutation
% 0.18/0.45  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.18/0.45  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.18/0.45  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.18/0.45  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.18/0.45  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.18/0.45  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.18/0.45  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.18/0.45  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.18/0.45  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.18/0.45  fof(t24_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 0.18/0.45  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.18/0.45  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.18/0.45  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.18/0.45  fof(t93_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 0.18/0.45  fof(c_0_14, plain, ![X22, X23]:k4_xboole_0(X22,k4_xboole_0(X22,X23))=k3_xboole_0(X22,X23), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.18/0.45  fof(c_0_15, plain, ![X16]:k4_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.18/0.45  fof(c_0_16, plain, ![X10]:k2_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.18/0.45  fof(c_0_17, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.18/0.45  fof(c_0_18, plain, ![X30]:k5_xboole_0(X30,X30)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.18/0.45  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.45  cnf(c_0_20, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.45  fof(c_0_21, plain, ![X11, X12]:k2_xboole_0(X11,k3_xboole_0(X11,X12))=X11, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.18/0.45  cnf(c_0_22, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.45  cnf(c_0_23, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.45  cnf(c_0_24, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.45  cnf(c_0_25, plain, (k4_xboole_0(X1,X1)=k3_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.45  cnf(c_0_26, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.45  cnf(c_0_27, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])).
% 0.18/0.45  fof(c_0_28, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.18/0.45  cnf(c_0_29, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.18/0.45  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.45  fof(c_0_31, plain, ![X20, X21]:k4_xboole_0(X20,k3_xboole_0(X20,X21))=k4_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.18/0.45  cnf(c_0_32, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.45  fof(c_0_33, plain, ![X17, X18, X19]:k4_xboole_0(k4_xboole_0(X17,X18),X19)=k4_xboole_0(X17,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.18/0.45  cnf(c_0_34, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.45  cnf(c_0_35, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_32])).
% 0.18/0.45  cnf(c_0_36, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.45  cnf(c_0_37, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_25, c_0_27])).
% 0.18/0.45  cnf(c_0_38, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_20])).
% 0.18/0.45  fof(c_0_39, plain, ![X13, X14, X15]:k2_xboole_0(X13,k3_xboole_0(X14,X15))=k3_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(X13,X15)), inference(variable_rename,[status(thm)],[t24_xboole_1])).
% 0.18/0.45  cnf(c_0_40, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.18/0.45  cnf(c_0_41, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.45  fof(c_0_42, plain, ![X24, X25, X26]:k3_xboole_0(X24,k4_xboole_0(X25,X26))=k4_xboole_0(k3_xboole_0(X24,X25),X26), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.18/0.45  cnf(c_0_43, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_30])).
% 0.18/0.45  cnf(c_0_44, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_29]), c_0_27]), c_0_29])).
% 0.18/0.45  fof(c_0_45, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.18/0.45  fof(c_0_46, plain, ![X27, X28, X29]:k2_xboole_0(k2_xboole_0(X27,X28),X29)=k2_xboole_0(X27,k2_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.18/0.45  cnf(c_0_47, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.45  cnf(c_0_48, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_43]), c_0_20])).
% 0.18/0.45  cnf(c_0_49, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_22]), c_0_44])).
% 0.18/0.45  cnf(c_0_50, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.45  cnf(c_0_51, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_19]), c_0_34])).
% 0.18/0.45  cnf(c_0_52, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.45  cnf(c_0_53, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k3_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_19]), c_0_47])).
% 0.18/0.45  cnf(c_0_54, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.18/0.45  cnf(c_0_55, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(spm,[status(thm)],[c_0_26, c_0_51])).
% 0.18/0.45  cnf(c_0_56, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_52, c_0_22])).
% 0.18/0.45  cnf(c_0_57, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_23]), c_0_36])).
% 0.18/0.45  cnf(c_0_58, plain, (k4_xboole_0(X1,k5_xboole_0(X1,X2))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_23]), c_0_19]), c_0_54])).
% 0.18/0.45  cnf(c_0_59, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_34, c_0_50])).
% 0.18/0.45  cnf(c_0_60, plain, (k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k2_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_52, c_0_55])).
% 0.18/0.45  cnf(c_0_61, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_56]), c_0_41])).
% 0.18/0.45  cnf(c_0_62, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k5_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_57]), c_0_20])).
% 0.18/0.45  cnf(c_0_63, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_58]), c_0_59])).
% 0.18/0.45  cnf(c_0_64, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,k5_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_60, c_0_23])).
% 0.18/0.45  fof(c_0_65, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t93_xboole_1])).
% 0.18/0.45  cnf(c_0_66, plain, (k2_xboole_0(X1,k5_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64])).
% 0.18/0.45  fof(c_0_67, negated_conjecture, k2_xboole_0(esk1_0,esk2_0)!=k2_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_65])])])).
% 0.18/0.45  cnf(c_0_68, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_64, c_0_66])).
% 0.18/0.45  cnf(c_0_69, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k2_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.18/0.45  cnf(c_0_70, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_58]), c_0_30]), c_0_30]), c_0_66])).
% 0.18/0.45  cnf(c_0_71, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_30]), c_0_23])).
% 0.18/0.45  cnf(c_0_72, negated_conjecture, (k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k5_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_69, c_0_30])).
% 0.18/0.45  cnf(c_0_73, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.18/0.45  cnf(c_0_74, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73]), c_0_30])]), ['proof']).
% 0.18/0.45  # SZS output end CNFRefutation
% 0.18/0.45  # Proof object total steps             : 75
% 0.18/0.45  # Proof object clause steps            : 46
% 0.18/0.45  # Proof object formula steps           : 29
% 0.18/0.45  # Proof object conjectures             : 6
% 0.18/0.45  # Proof object clause conjectures      : 3
% 0.18/0.45  # Proof object formula conjectures     : 3
% 0.18/0.45  # Proof object initial clauses used    : 14
% 0.18/0.45  # Proof object initial formulas used   : 14
% 0.18/0.45  # Proof object generating inferences   : 28
% 0.18/0.45  # Proof object simplifying inferences  : 29
% 0.18/0.45  # Training examples: 0 positive, 0 negative
% 0.18/0.45  # Parsed axioms                        : 14
% 0.18/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.45  # Initial clauses                      : 14
% 0.18/0.45  # Removed in clause preprocessing      : 0
% 0.18/0.45  # Initial clauses in saturation        : 14
% 0.18/0.45  # Processed clauses                    : 722
% 0.18/0.45  # ...of these trivial                  : 299
% 0.18/0.45  # ...subsumed                          : 199
% 0.18/0.45  # ...remaining for further processing  : 224
% 0.18/0.45  # Other redundant clauses eliminated   : 0
% 0.18/0.45  # Clauses deleted for lack of memory   : 0
% 0.18/0.45  # Backward-subsumed                    : 0
% 0.18/0.45  # Backward-rewritten                   : 71
% 0.18/0.45  # Generated clauses                    : 12798
% 0.18/0.45  # ...of the previous two non-trivial   : 6938
% 0.18/0.45  # Contextual simplify-reflections      : 0
% 0.18/0.45  # Paramodulations                      : 12798
% 0.18/0.45  # Factorizations                       : 0
% 0.18/0.45  # Equation resolutions                 : 0
% 0.18/0.45  # Propositional unsat checks           : 0
% 0.18/0.45  #    Propositional check models        : 0
% 0.18/0.45  #    Propositional check unsatisfiable : 0
% 0.18/0.45  #    Propositional clauses             : 0
% 0.18/0.45  #    Propositional clauses after purity: 0
% 0.18/0.45  #    Propositional unsat core size     : 0
% 0.18/0.45  #    Propositional preprocessing time  : 0.000
% 0.18/0.45  #    Propositional encoding time       : 0.000
% 0.18/0.45  #    Propositional solver time         : 0.000
% 0.18/0.45  #    Success case prop preproc time    : 0.000
% 0.18/0.45  #    Success case prop encoding time   : 0.000
% 0.18/0.45  #    Success case prop solver time     : 0.000
% 0.18/0.45  # Current number of processed clauses  : 139
% 0.18/0.45  #    Positive orientable unit clauses  : 133
% 0.18/0.45  #    Positive unorientable unit clauses: 6
% 0.18/0.45  #    Negative unit clauses             : 0
% 0.18/0.45  #    Non-unit-clauses                  : 0
% 0.18/0.45  # Current number of unprocessed clauses: 6152
% 0.18/0.45  # ...number of literals in the above   : 6152
% 0.18/0.45  # Current number of archived formulas  : 0
% 0.18/0.45  # Current number of archived clauses   : 85
% 0.18/0.45  # Clause-clause subsumption calls (NU) : 0
% 0.18/0.45  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.45  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.45  # Unit Clause-clause subsumption calls : 17
% 0.18/0.45  # Rewrite failures with RHS unbound    : 0
% 0.18/0.45  # BW rewrite match attempts            : 370
% 0.18/0.45  # BW rewrite match successes           : 195
% 0.18/0.45  # Condensation attempts                : 0
% 0.18/0.45  # Condensation successes               : 0
% 0.18/0.45  # Termbank termtop insertions          : 95156
% 0.18/0.46  
% 0.18/0.46  # -------------------------------------------------
% 0.18/0.46  # User time                : 0.116 s
% 0.18/0.46  # System time              : 0.006 s
% 0.18/0.46  # Total time               : 0.122 s
% 0.18/0.46  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
