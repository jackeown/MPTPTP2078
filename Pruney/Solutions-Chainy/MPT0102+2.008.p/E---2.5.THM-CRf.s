%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 471 expanded)
%              Number of clauses        :   33 ( 212 expanded)
%              Number of leaves         :   13 ( 129 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 ( 481 expanded)
%              Number of equality atoms :   65 ( 480 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t95_xboole_1,conjecture,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(c_0_13,plain,(
    ! [X23,X24] : k4_xboole_0(X23,k2_xboole_0(X23,X24)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_14,plain,(
    ! [X17,X18,X19] : k4_xboole_0(k4_xboole_0(X17,X18),X19) = k4_xboole_0(X17,k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t95_xboole_1])).

fof(c_0_16,plain,(
    ! [X14] : k4_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,negated_conjecture,(
    k3_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_20,plain,(
    ! [X25,X26] : k4_xboole_0(X25,k4_xboole_0(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_21,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_22,plain,(
    ! [X15,X16] : k4_xboole_0(k2_xboole_0(X15,X16),X16) = k4_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_23,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X1),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_26,plain,(
    ! [X11] : k2_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_27,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X12,X13] :
      ( k4_xboole_0(X12,X13) != k4_xboole_0(X13,X12)
      | X12 = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).

cnf(c_0_31,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_34,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k2_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_29])).

cnf(c_0_37,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k4_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_25,c_0_33])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X2),X3) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_18]),c_0_18])).

cnf(c_0_42,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk1_0),esk2_0)) != k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_32]),c_0_18]),c_0_18])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,X2) = X1
    | k4_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_18]),c_0_33]),c_0_39])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_28]),c_0_28])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk1_0),esk2_0),k4_xboole_0(k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk2_0,esk1_0))) != k1_xboole_0
    | k4_xboole_0(k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk2_0,esk1_0)) != k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_31]),c_0_18]),c_0_46]),c_0_24])).

fof(c_0_49,plain,(
    ! [X20,X21,X22] : k4_xboole_0(k2_xboole_0(X20,X21),X22) = k2_xboole_0(k4_xboole_0(X20,X22),k4_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

fof(c_0_50,plain,(
    ! [X10] : k2_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk1_0),esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_45]),c_0_48]),c_0_45])])).

cnf(c_0_52,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X2)
    | k4_xboole_0(X3,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_44])).

cnf(c_0_53,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_32]),c_0_18])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk1_0),esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_33])])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X1) = k4_xboole_0(X3,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_46]),c_0_42])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:12:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.42  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.026 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.20/0.42  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.20/0.42  fof(t95_xboole_1, conjecture, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.20/0.42  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.42  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.42  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.20/0.42  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.20/0.42  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.42  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.42  fof(t32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 0.20/0.42  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.42  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.20/0.42  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.20/0.42  fof(c_0_13, plain, ![X23, X24]:k4_xboole_0(X23,k2_xboole_0(X23,X24))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.20/0.42  fof(c_0_14, plain, ![X17, X18, X19]:k4_xboole_0(k4_xboole_0(X17,X18),X19)=k4_xboole_0(X17,k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.20/0.42  fof(c_0_15, negated_conjecture, ~(![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t95_xboole_1])).
% 0.20/0.42  fof(c_0_16, plain, ![X14]:k4_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.42  cnf(c_0_17, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_18, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  fof(c_0_19, negated_conjecture, k3_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.42  fof(c_0_20, plain, ![X25, X26]:k4_xboole_0(X25,k4_xboole_0(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.42  fof(c_0_21, plain, ![X8, X9]:k5_xboole_0(X8,X9)=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.20/0.42  fof(c_0_22, plain, ![X15, X16]:k4_xboole_0(k2_xboole_0(X15,X16),X16)=k4_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.20/0.42  fof(c_0_23, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.42  cnf(c_0_24, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_25, plain, (k4_xboole_0(k4_xboole_0(X1,X1),X2)=k1_xboole_0), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.42  fof(c_0_26, plain, ![X11]:k2_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.42  cnf(c_0_27, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_28, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.42  cnf(c_0_29, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  fof(c_0_30, plain, ![X12, X13]:(k4_xboole_0(X12,X13)!=k4_xboole_0(X13,X12)|X12=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).
% 0.20/0.42  cnf(c_0_31, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_32, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_33, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.42  fof(c_0_34, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.42  cnf(c_0_35, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.42  cnf(c_0_36, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k2_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_29])).
% 0.20/0.42  cnf(c_0_37, plain, (X1=X2|k4_xboole_0(X1,X2)!=k4_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  cnf(c_0_38, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.42  cnf(c_0_39, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_25, c_0_33])).
% 0.20/0.42  cnf(c_0_40, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.42  cnf(c_0_41, plain, (k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X3)),X2),X3)=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_18]), c_0_18])).
% 0.20/0.42  cnf(c_0_42, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_35, c_0_32])).
% 0.20/0.42  cnf(c_0_43, negated_conjecture, (k2_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk1_0),esk2_0))!=k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_32]), c_0_18]), c_0_18])).
% 0.20/0.42  cnf(c_0_44, plain, (k2_xboole_0(X1,X2)=X1|k4_xboole_0(X2,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_18]), c_0_33]), c_0_39])).
% 0.20/0.42  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_28]), c_0_28])).
% 0.20/0.42  cnf(c_0_46, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_38]), c_0_39]), c_0_39])).
% 0.20/0.42  cnf(c_0_47, negated_conjecture, (k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk1_0),esk2_0),k4_xboole_0(k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk2_0,esk1_0)))!=k1_xboole_0|k4_xboole_0(k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk2_0,esk1_0))!=k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.42  cnf(c_0_48, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_31]), c_0_18]), c_0_46]), c_0_24])).
% 0.20/0.42  fof(c_0_49, plain, ![X20, X21, X22]:k4_xboole_0(k2_xboole_0(X20,X21),X22)=k2_xboole_0(k4_xboole_0(X20,X22),k4_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 0.20/0.42  fof(c_0_50, plain, ![X10]:k2_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk1_0),esk2_0),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_45]), c_0_48]), c_0_45])])).
% 0.20/0.42  cnf(c_0_52, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,X2)|k4_xboole_0(X3,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_44])).
% 0.20/0.42  cnf(c_0_53, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k4_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_32]), c_0_18])).
% 0.20/0.42  cnf(c_0_54, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.42  cnf(c_0_55, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.42  cnf(c_0_56, negated_conjecture, (k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),esk1_0),esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_33])])).
% 0.20/0.42  cnf(c_0_57, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X1)=k4_xboole_0(X3,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_46]), c_0_42])).
% 0.20/0.42  cnf(c_0_58, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_55])).
% 0.20/0.42  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_46])]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 60
% 0.20/0.42  # Proof object clause steps            : 33
% 0.20/0.42  # Proof object formula steps           : 27
% 0.20/0.42  # Proof object conjectures             : 10
% 0.20/0.42  # Proof object clause conjectures      : 7
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 13
% 0.20/0.42  # Proof object initial formulas used   : 13
% 0.20/0.42  # Proof object generating inferences   : 13
% 0.20/0.42  # Proof object simplifying inferences  : 34
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 13
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 13
% 0.20/0.42  # Removed in clause preprocessing      : 2
% 0.20/0.42  # Initial clauses in saturation        : 11
% 0.20/0.42  # Processed clauses                    : 457
% 0.20/0.42  # ...of these trivial                  : 42
% 0.20/0.42  # ...subsumed                          : 273
% 0.20/0.42  # ...remaining for further processing  : 142
% 0.20/0.42  # Other redundant clauses eliminated   : 59
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 2
% 0.20/0.42  # Backward-rewritten                   : 59
% 0.20/0.42  # Generated clauses                    : 3071
% 0.20/0.42  # ...of the previous two non-trivial   : 2153
% 0.20/0.42  # Contextual simplify-reflections      : 0
% 0.20/0.42  # Paramodulations                      : 3011
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 60
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
% 0.20/0.42  # Current number of processed clauses  : 70
% 0.20/0.42  #    Positive orientable unit clauses  : 35
% 0.20/0.42  #    Positive unorientable unit clauses: 4
% 0.20/0.42  #    Negative unit clauses             : 8
% 0.20/0.42  #    Non-unit-clauses                  : 23
% 0.20/0.42  # Current number of unprocessed clauses: 1679
% 0.20/0.42  # ...number of literals in the above   : 2727
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 74
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 1303
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 754
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 138
% 0.20/0.42  # Unit Clause-clause subsumption calls : 228
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 217
% 0.20/0.42  # BW rewrite match successes           : 78
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 28810
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.067 s
% 0.20/0.42  # System time              : 0.003 s
% 0.20/0.42  # Total time               : 0.070 s
% 0.20/0.42  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
