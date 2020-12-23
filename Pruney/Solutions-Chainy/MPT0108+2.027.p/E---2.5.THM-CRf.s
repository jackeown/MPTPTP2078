%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:25 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   76 (1270 expanded)
%              Number of clauses        :   53 ( 581 expanded)
%              Number of leaves         :   11 ( 344 expanded)
%              Depth                    :   16
%              Number of atoms          :   76 (1270 expanded)
%              Number of equality atoms :   75 (1269 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t101_xboole_1,conjecture,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

fof(c_0_11,plain,(
    ! [X16] : k5_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_12,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_13,plain,(
    ! [X17,X18,X19] : k5_xboole_0(k5_xboole_0(X17,X18),X19) = k5_xboole_0(X17,k5_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_14,plain,(
    ! [X20] : k5_xboole_0(X20,X20) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_15,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,plain,(
    ! [X21,X22] : k2_xboole_0(X21,X22) = k5_xboole_0(X21,k4_xboole_0(X22,X21)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_22,plain,(
    ! [X10,X11] : k3_xboole_0(X10,k2_xboole_0(X10,X11)) = X10 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_23,plain,(
    ! [X15] : k4_xboole_0(k1_xboole_0,X15) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_24,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_25,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(spm,[status(thm)],[c_0_25,c_0_16])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_27])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_28]),c_0_18])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_29]),c_0_15])).

fof(c_0_36,plain,(
    ! [X12,X13,X14] : k3_xboole_0(X12,k4_xboole_0(X13,X14)) = k4_xboole_0(k3_xboole_0(X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_30])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),X3)) = k5_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_31])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_16])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X1),X3)) = k5_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_37])).

cnf(c_0_43,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X2,X1)) = k5_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_28,c_0_35])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_32])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_44])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_28])).

cnf(c_0_49,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k5_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_28]),c_0_16])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3))) = k4_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_51,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,k5_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_17])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_46]),c_0_16]),c_0_27])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_47])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_33])).

cnf(c_0_55,plain,
    ( k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_37])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2))) = k2_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_31]),c_0_52])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_52])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_19]),c_0_29])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_31])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_54]),c_0_15])).

cnf(c_0_61,plain,
    ( k3_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_28])).

cnf(c_0_62,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k5_xboole_0(X2,X1)),k3_xboole_0(X1,k5_xboole_0(X2,X1))) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_41]),c_0_57]),c_0_58]),c_0_15])).

cnf(c_0_63,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_59]),c_0_47])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_49,c_0_33])).

cnf(c_0_65,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X2) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_60]),c_0_16]),c_0_27])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

fof(c_0_67,negated_conjecture,(
    ~ ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t101_xboole_1])).

cnf(c_0_68,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_60])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_16])).

fof(c_0_70,negated_conjecture,(
    k5_xboole_0(esk1_0,esk2_0) != k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_67])])])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2 ),
    inference(spm,[status(thm)],[c_0_68,c_0_52])).

cnf(c_0_72,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_69]),c_0_17]),c_0_37]),c_0_27]),c_0_52])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(esk1_0,esk2_0) != k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k5_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:39:31 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.19/0.41  # and selection function SelectNewComplexAHP.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.026 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.19/0.41  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.41  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.41  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.41  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.41  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.19/0.41  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.19/0.41  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.41  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.19/0.41  fof(t101_xboole_1, conjecture, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_xboole_1)).
% 0.19/0.41  fof(c_0_11, plain, ![X16]:k5_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.19/0.41  fof(c_0_12, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.41  fof(c_0_13, plain, ![X17, X18, X19]:k5_xboole_0(k5_xboole_0(X17,X18),X19)=k5_xboole_0(X17,k5_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.41  fof(c_0_14, plain, ![X20]:k5_xboole_0(X20,X20)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.41  cnf(c_0_15, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_16, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_17, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_18, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_19, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.41  fof(c_0_20, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.41  fof(c_0_21, plain, ![X21, X22]:k2_xboole_0(X21,X22)=k5_xboole_0(X21,k4_xboole_0(X22,X21)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.41  fof(c_0_22, plain, ![X10, X11]:k3_xboole_0(X10,k2_xboole_0(X10,X11))=X10, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.19/0.41  fof(c_0_23, plain, ![X15]:k4_xboole_0(k1_xboole_0,X15)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.19/0.41  fof(c_0_24, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.41  cnf(c_0_25, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.19/0.41  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_27, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_28, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_29, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.41  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  cnf(c_0_31, plain, (k5_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.41  cnf(c_0_32, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(spm,[status(thm)],[c_0_25, c_0_16])).
% 0.19/0.41  cnf(c_0_33, plain, (k5_xboole_0(X1,k2_xboole_0(X1,X2))=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_25, c_0_27])).
% 0.19/0.41  cnf(c_0_34, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_28]), c_0_18])).
% 0.19/0.41  cnf(c_0_35, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_29]), c_0_15])).
% 0.19/0.41  fof(c_0_36, plain, ![X12, X13, X14]:k3_xboole_0(X12,k4_xboole_0(X13,X14))=k4_xboole_0(k3_xboole_0(X12,X13),X14), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.19/0.41  cnf(c_0_37, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_30])).
% 0.19/0.41  cnf(c_0_38, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X1,X2),X3))=k5_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_17, c_0_31])).
% 0.19/0.41  cnf(c_0_39, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_16])).
% 0.19/0.41  cnf(c_0_40, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.41  cnf(c_0_41, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_42, plain, (k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X2,X1),X3))=k5_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_17, c_0_37])).
% 0.19/0.41  cnf(c_0_43, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k2_xboole_0(X2,X1))=k5_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.41  cnf(c_0_44, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_28, c_0_35])).
% 0.19/0.41  cnf(c_0_45, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.41  cnf(c_0_46, plain, (k5_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_32])).
% 0.19/0.41  cnf(c_0_47, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_41, c_0_44])).
% 0.19/0.41  cnf(c_0_48, plain, (k3_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_28])).
% 0.19/0.41  cnf(c_0_49, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k5_xboole_0(X1,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_28]), c_0_16])).
% 0.19/0.41  cnf(c_0_50, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X3)))=k4_xboole_0(k5_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_26, c_0_17])).
% 0.19/0.41  cnf(c_0_51, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(X3,k5_xboole_0(X1,X2))))=k2_xboole_0(k5_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_27, c_0_17])).
% 0.19/0.41  cnf(c_0_52, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_46]), c_0_16]), c_0_27])).
% 0.19/0.41  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k5_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_26, c_0_47])).
% 0.19/0.41  cnf(c_0_54, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_33])).
% 0.19/0.41  cnf(c_0_55, plain, (k5_xboole_0(X1,k4_xboole_0(X2,k5_xboole_0(X1,X2)))=k4_xboole_0(k5_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_50, c_0_37])).
% 0.19/0.41  cnf(c_0_56, plain, (k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X1,X2)))=k2_xboole_0(X2,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_31]), c_0_52])).
% 0.19/0.41  cnf(c_0_57, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_52])).
% 0.19/0.41  cnf(c_0_58, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_19]), c_0_29])).
% 0.19/0.41  cnf(c_0_59, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_31])).
% 0.19/0.41  cnf(c_0_60, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_54]), c_0_15])).
% 0.19/0.41  cnf(c_0_61, plain, (k3_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3))=k4_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_41, c_0_28])).
% 0.19/0.41  cnf(c_0_62, plain, (k4_xboole_0(k2_xboole_0(X1,k5_xboole_0(X2,X1)),k3_xboole_0(X1,k5_xboole_0(X2,X1)))=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_41]), c_0_57]), c_0_58]), c_0_15])).
% 0.19/0.41  cnf(c_0_63, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_59]), c_0_47])).
% 0.19/0.41  cnf(c_0_64, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[c_0_49, c_0_33])).
% 0.19/0.41  cnf(c_0_65, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X2)=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_60]), c_0_16]), c_0_27])).
% 0.19/0.41  cnf(c_0_66, plain, (k4_xboole_0(X1,k5_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.19/0.41  fof(c_0_67, negated_conjecture, ~(![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t101_xboole_1])).
% 0.19/0.41  cnf(c_0_68, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_60])).
% 0.19/0.41  cnf(c_0_69, plain, (k4_xboole_0(X1,k5_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_66, c_0_16])).
% 0.19/0.41  fof(c_0_70, negated_conjecture, k5_xboole_0(esk1_0,esk2_0)!=k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_67])])])).
% 0.19/0.41  cnf(c_0_71, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X2), inference(spm,[status(thm)],[c_0_68, c_0_52])).
% 0.19/0.41  cnf(c_0_72, plain, (k2_xboole_0(X1,k5_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_69]), c_0_17]), c_0_37]), c_0_27]), c_0_52])).
% 0.19/0.41  cnf(c_0_73, negated_conjecture, (k5_xboole_0(esk1_0,esk2_0)!=k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.41  cnf(c_0_74, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k5_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_69])).
% 0.19/0.41  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 76
% 0.19/0.41  # Proof object clause steps            : 53
% 0.19/0.41  # Proof object formula steps           : 23
% 0.19/0.41  # Proof object conjectures             : 5
% 0.19/0.41  # Proof object clause conjectures      : 2
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 11
% 0.19/0.41  # Proof object initial formulas used   : 11
% 0.19/0.41  # Proof object generating inferences   : 38
% 0.19/0.41  # Proof object simplifying inferences  : 31
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 11
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 11
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 11
% 0.19/0.41  # Processed clauses                    : 612
% 0.19/0.41  # ...of these trivial                  : 279
% 0.19/0.41  # ...subsumed                          : 164
% 0.19/0.41  # ...remaining for further processing  : 169
% 0.19/0.41  # Other redundant clauses eliminated   : 0
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 0
% 0.19/0.41  # Backward-rewritten                   : 27
% 0.19/0.41  # Generated clauses                    : 7752
% 0.19/0.41  # ...of the previous two non-trivial   : 3953
% 0.19/0.41  # Contextual simplify-reflections      : 0
% 0.19/0.41  # Paramodulations                      : 7752
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 0
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 131
% 0.19/0.41  #    Positive orientable unit clauses  : 125
% 0.19/0.41  #    Positive unorientable unit clauses: 6
% 0.19/0.41  #    Negative unit clauses             : 0
% 0.19/0.41  #    Non-unit-clauses                  : 0
% 0.19/0.41  # Current number of unprocessed clauses: 3266
% 0.19/0.41  # ...number of literals in the above   : 3266
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 38
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.41  # Unit Clause-clause subsumption calls : 18
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 298
% 0.19/0.41  # BW rewrite match successes           : 186
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 51620
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.073 s
% 0.19/0.41  # System time              : 0.007 s
% 0.19/0.41  # Total time               : 0.080 s
% 0.19/0.41  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
