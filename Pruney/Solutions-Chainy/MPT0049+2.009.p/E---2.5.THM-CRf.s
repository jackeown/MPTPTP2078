%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:06 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :   51 (1185 expanded)
%              Number of clauses        :   34 ( 530 expanded)
%              Number of leaves         :    8 ( 327 expanded)
%              Depth                    :   13
%              Number of atoms          :   56 (1220 expanded)
%              Number of equality atoms :   55 (1219 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t42_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(c_0_8,plain,(
    ! [X11,X12] : k4_xboole_0(k2_xboole_0(X11,X12),X12) = k4_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_9,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_10,plain,(
    ! [X13,X14,X15] : k4_xboole_0(k4_xboole_0(X13,X14),X15) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_11,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X7,X8] :
      ( k4_xboole_0(X7,X8) != k4_xboole_0(X8,X7)
      | X7 = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).

cnf(c_0_14,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X1) = k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_16,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_17,plain,(
    ! [X16,X17,X18] : k2_xboole_0(k2_xboole_0(X16,X17),X18) = k2_xboole_0(X16,k2_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_18,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k4_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k4_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X6] : k2_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = X1
    | k4_xboole_0(X1,k2_xboole_0(X1,X2)) != k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X2,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_19]),c_0_19])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_14])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_21])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = X1
    | k4_xboole_0(X2,k2_xboole_0(X1,X2)) != k4_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_25])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X2,X1))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_20])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_14]),c_0_30]),c_0_14])])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_29,c_0_31])).

cnf(c_0_33,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_20])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_12])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_12,c_0_32])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t42_xboole_1])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_12])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_25]),c_0_21]),c_0_15])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_20]),c_0_34])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_35]),c_0_14])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_31]),c_0_14])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_21])).

fof(c_0_43,negated_conjecture,(
    k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3))) = k4_xboole_0(k2_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_14]),c_0_39]),c_0_40]),c_0_32])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X2) = k4_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_26]),c_0_15])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_19]),c_0_19]),c_0_41])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_35]),c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_14]),c_0_20]),c_0_46]),c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:45:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 4.62/4.84  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 4.62/4.84  # and selection function PSelectComplexExceptUniqMaxHorn.
% 4.62/4.84  #
% 4.62/4.84  # Preprocessing time       : 0.026 s
% 4.62/4.84  # Presaturation interreduction done
% 4.62/4.84  
% 4.62/4.84  # Proof found!
% 4.62/4.84  # SZS status Theorem
% 4.62/4.84  # SZS output start CNFRefutation
% 4.62/4.84  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 4.62/4.84  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.62/4.84  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.62/4.84  fof(t32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 4.62/4.84  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.62/4.84  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.62/4.84  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.62/4.84  fof(t42_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_xboole_1)).
% 4.62/4.84  fof(c_0_8, plain, ![X11, X12]:k4_xboole_0(k2_xboole_0(X11,X12),X12)=k4_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 4.62/4.84  fof(c_0_9, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 4.62/4.84  fof(c_0_10, plain, ![X13, X14, X15]:k4_xboole_0(k4_xboole_0(X13,X14),X15)=k4_xboole_0(X13,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 4.62/4.84  cnf(c_0_11, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 4.62/4.84  cnf(c_0_12, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 4.62/4.84  fof(c_0_13, plain, ![X7, X8]:(k4_xboole_0(X7,X8)!=k4_xboole_0(X8,X7)|X7=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).
% 4.62/4.84  cnf(c_0_14, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 4.62/4.84  cnf(c_0_15, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X1)=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 4.62/4.84  fof(c_0_16, plain, ![X9, X10]:k2_xboole_0(X9,k4_xboole_0(X10,X9))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 4.62/4.84  fof(c_0_17, plain, ![X16, X17, X18]:k2_xboole_0(k2_xboole_0(X16,X17),X18)=k2_xboole_0(X16,k2_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 4.62/4.84  cnf(c_0_18, plain, (X1=X2|k4_xboole_0(X1,X2)!=k4_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.62/4.84  cnf(c_0_19, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k4_xboole_0(X2,k2_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_14])).
% 4.62/4.84  cnf(c_0_20, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.62/4.84  cnf(c_0_21, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.62/4.84  fof(c_0_22, plain, ![X6]:k2_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 4.62/4.84  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=X1|k4_xboole_0(X1,k2_xboole_0(X1,X2))!=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_18, c_0_15])).
% 4.62/4.84  cnf(c_0_24, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(X2,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_19]), c_0_19])).
% 4.62/4.84  cnf(c_0_25, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_20, c_0_14])).
% 4.62/4.84  cnf(c_0_26, plain, (k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X1),X3))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_21])).
% 4.62/4.84  cnf(c_0_27, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.62/4.84  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=X1|k4_xboole_0(X2,k2_xboole_0(X1,X2))!=k4_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 4.62/4.84  cnf(c_0_29, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=k2_xboole_0(X1,k4_xboole_0(X2,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_24]), c_0_25])).
% 4.62/4.84  cnf(c_0_30, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X2,X1)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_20])).
% 4.62/4.84  cnf(c_0_31, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_14]), c_0_30]), c_0_14])])).
% 4.62/4.84  cnf(c_0_32, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[c_0_29, c_0_31])).
% 4.62/4.84  cnf(c_0_33, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X2,X1))=k4_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_11, c_0_20])).
% 4.62/4.84  cnf(c_0_34, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_25, c_0_12])).
% 4.62/4.84  cnf(c_0_35, plain, (k2_xboole_0(k4_xboole_0(X1,X1),X2)=X2), inference(spm,[status(thm)],[c_0_12, c_0_32])).
% 4.62/4.84  fof(c_0_36, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(assume_negation,[status(cth)],[t42_xboole_1])).
% 4.62/4.84  cnf(c_0_37, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_33, c_0_12])).
% 4.62/4.84  cnf(c_0_38, plain, (k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_15]), c_0_25]), c_0_21]), c_0_15])).
% 4.62/4.84  cnf(c_0_39, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_20]), c_0_34])).
% 4.62/4.84  cnf(c_0_40, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_35]), c_0_14])).
% 4.62/4.84  cnf(c_0_41, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_31]), c_0_14])).
% 4.62/4.84  cnf(c_0_42, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X3,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_12, c_0_21])).
% 4.62/4.84  fof(c_0_43, negated_conjecture, k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 4.62/4.84  cnf(c_0_44, plain, (k4_xboole_0(k2_xboole_0(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X1,k4_xboole_0(k2_xboole_0(X1,X2),X3)))=k4_xboole_0(k2_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_14]), c_0_39]), c_0_40]), c_0_32])).
% 4.62/4.84  cnf(c_0_45, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),X3),X2)=k4_xboole_0(k2_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_26]), c_0_15])).
% 4.62/4.84  cnf(c_0_46, plain, (k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_19]), c_0_19]), c_0_41])).
% 4.62/4.84  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_35]), c_0_35])).
% 4.62/4.84  cnf(c_0_48, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk3_0),k4_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 4.62/4.84  cnf(c_0_49, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k4_xboole_0(k2_xboole_0(X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_14]), c_0_20]), c_0_46]), c_0_47])).
% 4.62/4.84  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49])]), ['proof']).
% 4.62/4.84  # SZS output end CNFRefutation
% 4.62/4.84  # Proof object total steps             : 51
% 4.62/4.84  # Proof object clause steps            : 34
% 4.62/4.84  # Proof object formula steps           : 17
% 4.62/4.84  # Proof object conjectures             : 5
% 4.62/4.84  # Proof object clause conjectures      : 2
% 4.62/4.84  # Proof object formula conjectures     : 3
% 4.62/4.84  # Proof object initial clauses used    : 8
% 4.62/4.84  # Proof object initial formulas used   : 8
% 4.62/4.84  # Proof object generating inferences   : 24
% 4.62/4.84  # Proof object simplifying inferences  : 31
% 4.62/4.84  # Training examples: 0 positive, 0 negative
% 4.62/4.84  # Parsed axioms                        : 8
% 4.62/4.84  # Removed by relevancy pruning/SinE    : 0
% 4.62/4.84  # Initial clauses                      : 8
% 4.62/4.84  # Removed in clause preprocessing      : 0
% 4.62/4.84  # Initial clauses in saturation        : 8
% 4.62/4.84  # Processed clauses                    : 20483
% 4.62/4.84  # ...of these trivial                  : 1121
% 4.62/4.84  # ...subsumed                          : 18195
% 4.62/4.84  # ...remaining for further processing  : 1167
% 4.62/4.84  # Other redundant clauses eliminated   : 2111
% 4.62/4.84  # Clauses deleted for lack of memory   : 0
% 4.62/4.84  # Backward-subsumed                    : 74
% 4.62/4.84  # Backward-rewritten                   : 171
% 4.62/4.84  # Generated clauses                    : 521647
% 4.62/4.84  # ...of the previous two non-trivial   : 459259
% 4.62/4.84  # Contextual simplify-reflections      : 2
% 4.62/4.84  # Paramodulations                      : 519358
% 4.62/4.84  # Factorizations                       : 0
% 4.62/4.84  # Equation resolutions                 : 2289
% 4.62/4.84  # Propositional unsat checks           : 0
% 4.62/4.84  #    Propositional check models        : 0
% 4.62/4.84  #    Propositional check unsatisfiable : 0
% 4.62/4.84  #    Propositional clauses             : 0
% 4.62/4.84  #    Propositional clauses after purity: 0
% 4.62/4.84  #    Propositional unsat core size     : 0
% 4.62/4.84  #    Propositional preprocessing time  : 0.000
% 4.62/4.84  #    Propositional encoding time       : 0.000
% 4.62/4.84  #    Propositional solver time         : 0.000
% 4.62/4.84  #    Success case prop preproc time    : 0.000
% 4.62/4.84  #    Success case prop encoding time   : 0.000
% 4.62/4.84  #    Success case prop solver time     : 0.000
% 4.62/4.84  # Current number of processed clauses  : 907
% 4.62/4.84  #    Positive orientable unit clauses  : 330
% 4.62/4.84  #    Positive unorientable unit clauses: 7
% 4.62/4.84  #    Negative unit clauses             : 2
% 4.62/4.84  #    Non-unit-clauses                  : 568
% 4.62/4.84  # Current number of unprocessed clauses: 436182
% 4.62/4.84  # ...number of literals in the above   : 773348
% 4.62/4.84  # Current number of archived formulas  : 0
% 4.62/4.84  # Current number of archived clauses   : 253
% 4.62/4.84  # Clause-clause subsumption calls (NU) : 314293
% 4.62/4.84  # Rec. Clause-clause subsumption calls : 313225
% 4.62/4.84  # Non-unit clause-clause subsumptions  : 13755
% 4.62/4.84  # Unit Clause-clause subsumption calls : 144
% 4.62/4.84  # Rewrite failures with RHS unbound    : 36
% 4.62/4.84  # BW rewrite match attempts            : 6395
% 4.62/4.84  # BW rewrite match successes           : 207
% 4.62/4.84  # Condensation attempts                : 0
% 4.62/4.84  # Condensation successes               : 0
% 4.62/4.84  # Termbank termtop insertions          : 8808949
% 4.68/4.86  
% 4.68/4.86  # -------------------------------------------------
% 4.68/4.86  # User time                : 4.309 s
% 4.68/4.86  # System time              : 0.218 s
% 4.68/4.86  # Total time               : 4.527 s
% 4.68/4.86  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
