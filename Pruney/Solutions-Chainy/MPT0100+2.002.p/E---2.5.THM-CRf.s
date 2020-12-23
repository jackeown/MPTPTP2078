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
% DateTime   : Thu Dec  3 10:33:55 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 (1753 expanded)
%              Number of clauses        :   44 ( 770 expanded)
%              Number of leaves         :   11 ( 491 expanded)
%              Depth                    :   17
%              Number of atoms          :   67 (1753 expanded)
%              Number of equality atoms :   66 (1752 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t93_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(c_0_11,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_12,plain,(
    ! [X15] : k4_xboole_0(X15,k1_xboole_0) = X15 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_13,plain,(
    ! [X14] : k3_xboole_0(X14,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X18,X19,X20] : k4_xboole_0(k4_xboole_0(X18,X19),X20) = k4_xboole_0(X18,k2_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_18,plain,(
    ! [X16,X17] : k4_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_19,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_20,plain,(
    ! [X23] : k4_xboole_0(k1_xboole_0,X23) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X11,X12,X13] : k4_xboole_0(X11,k3_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X13)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_14])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_24]),c_0_15])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_21]),c_0_27])).

fof(c_0_33,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_28]),c_0_15])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_21]),c_0_30]),c_0_31])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_32]),c_0_15])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_29]),c_0_35])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X1,X3))) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_14])).

cnf(c_0_40,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k3_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_24]),c_0_26])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_37])).

cnf(c_0_43,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_24])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_37])).

fof(c_0_46,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_45]),c_0_40]),c_0_41])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_31,c_0_35])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_22,c_0_14])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k5_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_37])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_15]),c_0_16]),c_0_15]),c_0_37])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_52]),c_0_25]),c_0_35])).

cnf(c_0_56,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_50]),c_0_22]),c_0_54])).

fof(c_0_57,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t93_xboole_1])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_55]),c_0_56])).

fof(c_0_59,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k2_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).

cnf(c_0_60,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X1,X2)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_58]),c_0_45]),c_0_37])).

cnf(c_0_61,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k2_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_62,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X2,X1)) = k5_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_60]),c_0_26])).

cnf(c_0_63,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_60]),c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k5_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_37])).

cnf(c_0_65,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_62]),c_0_63]),c_0_37])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:24:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.20/0.42  # and selection function SelectNewComplexAHP.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.014 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.42  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.42  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.42  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.20/0.42  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.20/0.42  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.42  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.20/0.42  fof(l36_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l36_xboole_1)).
% 0.20/0.42  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.42  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.20/0.42  fof(t93_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 0.20/0.42  fof(c_0_11, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.42  fof(c_0_12, plain, ![X15]:k4_xboole_0(X15,k1_xboole_0)=X15, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.42  fof(c_0_13, plain, ![X14]:k3_xboole_0(X14,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.42  cnf(c_0_14, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.42  cnf(c_0_15, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_16, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  fof(c_0_17, plain, ![X18, X19, X20]:k4_xboole_0(k4_xboole_0(X18,X19),X20)=k4_xboole_0(X18,k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.20/0.42  fof(c_0_18, plain, ![X16, X17]:k4_xboole_0(k2_xboole_0(X16,X17),X17)=k4_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.20/0.42  fof(c_0_19, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.42  fof(c_0_20, plain, ![X23]:k4_xboole_0(k1_xboole_0,X23)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.20/0.42  cnf(c_0_21, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.20/0.42  cnf(c_0_22, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.42  fof(c_0_23, plain, ![X11, X12, X13]:k4_xboole_0(X11,k3_xboole_0(X12,X13))=k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X13)), inference(variable_rename,[status(thm)],[l36_xboole_1])).
% 0.20/0.42  cnf(c_0_24, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.42  cnf(c_0_25, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_14, c_0_14])).
% 0.20/0.42  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_27, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_28, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.42  cnf(c_0_29, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_30, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_24]), c_0_15])).
% 0.20/0.42  cnf(c_0_31, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.42  cnf(c_0_32, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_21]), c_0_27])).
% 0.20/0.42  fof(c_0_33, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.42  cnf(c_0_34, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_28]), c_0_15])).
% 0.20/0.42  cnf(c_0_35, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_21]), c_0_30]), c_0_31])).
% 0.20/0.42  cnf(c_0_36, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_32]), c_0_15])).
% 0.20/0.42  cnf(c_0_37, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.42  cnf(c_0_38, plain, (k4_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_29]), c_0_35])).
% 0.20/0.42  cnf(c_0_39, plain, (k4_xboole_0(X1,k3_xboole_0(X2,k4_xboole_0(X1,X3)))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_29, c_0_14])).
% 0.20/0.42  cnf(c_0_40, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k3_xboole_0(X2,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_24]), c_0_26])).
% 0.20/0.42  cnf(c_0_41, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.42  cnf(c_0_42, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_37])).
% 0.20/0.42  cnf(c_0_43, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.42  cnf(c_0_44, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_24])).
% 0.20/0.42  cnf(c_0_45, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_37])).
% 0.20/0.42  fof(c_0_46, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.20/0.42  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_45]), c_0_40]), c_0_41])).
% 0.20/0.42  cnf(c_0_48, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X1))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_31, c_0_35])).
% 0.20/0.42  cnf(c_0_49, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_22, c_0_14])).
% 0.20/0.42  cnf(c_0_50, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.42  cnf(c_0_51, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.42  cnf(c_0_52, plain, (k4_xboole_0(X1,k5_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.20/0.42  cnf(c_0_53, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_37])).
% 0.20/0.42  cnf(c_0_54, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_15]), c_0_16]), c_0_15]), c_0_37])).
% 0.20/0.42  cnf(c_0_55, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_52]), c_0_25]), c_0_35])).
% 0.20/0.42  cnf(c_0_56, plain, (k4_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_50]), c_0_22]), c_0_54])).
% 0.20/0.42  fof(c_0_57, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t93_xboole_1])).
% 0.20/0.42  cnf(c_0_58, plain, (k4_xboole_0(k5_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_55]), c_0_56])).
% 0.20/0.42  fof(c_0_59, negated_conjecture, k2_xboole_0(esk1_0,esk2_0)!=k2_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_57])])])).
% 0.20/0.42  cnf(c_0_60, plain, (k2_xboole_0(X1,k5_xboole_0(X1,X2))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_58]), c_0_45]), c_0_37])).
% 0.20/0.42  cnf(c_0_61, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k2_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.42  cnf(c_0_62, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X2,X1))=k5_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_60]), c_0_26])).
% 0.20/0.42  cnf(c_0_63, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k5_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_60]), c_0_52])).
% 0.20/0.42  cnf(c_0_64, negated_conjecture, (k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k5_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_61, c_0_37])).
% 0.20/0.42  cnf(c_0_65, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_62]), c_0_63]), c_0_37])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_37])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 67
% 0.20/0.42  # Proof object clause steps            : 44
% 0.20/0.42  # Proof object formula steps           : 23
% 0.20/0.42  # Proof object conjectures             : 6
% 0.20/0.42  # Proof object clause conjectures      : 3
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 11
% 0.20/0.42  # Proof object initial formulas used   : 11
% 0.20/0.42  # Proof object generating inferences   : 28
% 0.20/0.42  # Proof object simplifying inferences  : 36
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 12
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 12
% 0.20/0.42  # Removed in clause preprocessing      : 0
% 0.20/0.42  # Initial clauses in saturation        : 12
% 0.20/0.42  # Processed clauses                    : 900
% 0.20/0.42  # ...of these trivial                  : 500
% 0.20/0.42  # ...subsumed                          : 197
% 0.20/0.42  # ...remaining for further processing  : 203
% 0.20/0.42  # Other redundant clauses eliminated   : 0
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 0
% 0.20/0.42  # Backward-rewritten                   : 30
% 0.20/0.42  # Generated clauses                    : 12431
% 0.20/0.42  # ...of the previous two non-trivial   : 6899
% 0.20/0.42  # Contextual simplify-reflections      : 0
% 0.20/0.42  # Paramodulations                      : 12431
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 0
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 161
% 0.20/0.42  #    Positive orientable unit clauses  : 158
% 0.20/0.42  #    Positive unorientable unit clauses: 3
% 0.20/0.42  #    Negative unit clauses             : 0
% 0.20/0.42  #    Non-unit-clauses                  : 0
% 0.20/0.42  # Current number of unprocessed clauses: 5907
% 0.20/0.42  # ...number of literals in the above   : 5907
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 42
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.42  # Unit Clause-clause subsumption calls : 0
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 204
% 0.20/0.42  # BW rewrite match successes           : 54
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 94864
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.064 s
% 0.20/0.42  # System time              : 0.003 s
% 0.20/0.42  # Total time               : 0.067 s
% 0.20/0.42  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
