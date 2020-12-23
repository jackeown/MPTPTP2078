%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:54 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 424 expanded)
%              Number of clauses        :   26 ( 197 expanded)
%              Number of leaves         :    6 ( 113 expanded)
%              Depth                    :   12
%              Number of atoms          :   39 ( 424 expanded)
%              Number of equality atoms :   38 ( 423 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t24_xboole_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(c_0_6,plain,(
    ! [X12,X13,X14] : k3_xboole_0(X12,k2_xboole_0(X13,X14)) = k2_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X12,X14)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

fof(c_0_7,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_8,plain,(
    ! [X8,X9] : k3_xboole_0(X8,k2_xboole_0(X8,X9)) = X8 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_9,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_10,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k3_xboole_0(X10,X11)) = X10 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_15,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1)) = k3_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_12]),c_0_13])).

cnf(c_0_20,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k3_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X1,X3),X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_19]),c_0_20])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_12]),c_0_18])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_13])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,X1),X3)) = k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_11])).

cnf(c_0_26,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) = k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_12])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(k2_xboole_0(X2,X1),X3))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_13])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t24_xboole_1])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,k2_xboole_0(X2,X3)))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_32,negated_conjecture,(
    k2_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) != k3_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,k2_xboole_0(X3,X2)))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( k2_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) != k3_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_18]),c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( k2_xboole_0(esk1_0,k3_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk2_0))) != k2_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_26]),c_0_11])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_35]),c_0_29]),c_0_24]),c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 18:41:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.20/0.44  # and selection function SelectNewComplexAHP.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.026 s
% 0.20/0.44  # Presaturation interreduction done
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.20/0.44  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.44  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.20/0.44  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.44  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.20/0.44  fof(t24_xboole_1, conjecture, ![X1, X2, X3]:k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 0.20/0.44  fof(c_0_6, plain, ![X12, X13, X14]:k3_xboole_0(X12,k2_xboole_0(X13,X14))=k2_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X12,X14)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.20/0.44  fof(c_0_7, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.44  fof(c_0_8, plain, ![X8, X9]:k3_xboole_0(X8,k2_xboole_0(X8,X9))=X8, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.20/0.44  fof(c_0_9, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.44  cnf(c_0_10, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.44  cnf(c_0_11, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.44  cnf(c_0_12, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.44  fof(c_0_14, plain, ![X10, X11]:k2_xboole_0(X10,k3_xboole_0(X10,X11))=X10, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.20/0.44  cnf(c_0_15, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))=k3_xboole_0(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.44  cnf(c_0_16, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(X2,k2_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.44  cnf(c_0_17, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.44  cnf(c_0_18, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.44  cnf(c_0_19, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_12]), c_0_13])).
% 0.20/0.44  cnf(c_0_20, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k2_xboole_0(X2,k3_xboole_0(k2_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.44  cnf(c_0_21, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_18, c_0_11])).
% 0.20/0.44  cnf(c_0_22, plain, (k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,X1),X3))=k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X1,X3),X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_19]), c_0_20])).
% 0.20/0.44  cnf(c_0_23, plain, (k3_xboole_0(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_12]), c_0_18])).
% 0.20/0.44  cnf(c_0_24, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_13])).
% 0.20/0.44  cnf(c_0_25, plain, (k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X2,X1),X3))=k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_22, c_0_11])).
% 0.20/0.44  cnf(c_0_26, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))=k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_16, c_0_12])).
% 0.20/0.44  cnf(c_0_27, plain, (k3_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))=X1), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.44  cnf(c_0_28, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(k2_xboole_0(X2,X1),X3)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.20/0.44  cnf(c_0_29, plain, (k2_xboole_0(X1,k3_xboole_0(k2_xboole_0(X1,X2),X3))=k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_25, c_0_13])).
% 0.20/0.44  fof(c_0_30, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t24_xboole_1])).
% 0.20/0.44  cnf(c_0_31, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,k2_xboole_0(X2,X3))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.44  fof(c_0_32, negated_conjecture, k2_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))!=k3_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).
% 0.20/0.44  cnf(c_0_33, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X1,k2_xboole_0(X3,X2))))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_24])).
% 0.20/0.44  cnf(c_0_34, negated_conjecture, (k2_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))!=k3_xboole_0(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.44  cnf(c_0_35, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_18]), c_0_15])).
% 0.20/0.44  cnf(c_0_36, negated_conjecture, (k2_xboole_0(esk1_0,k3_xboole_0(esk3_0,k2_xboole_0(esk1_0,esk2_0)))!=k2_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_26]), c_0_11])).
% 0.20/0.44  cnf(c_0_37, plain, (k2_xboole_0(X1,k3_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_35]), c_0_29]), c_0_24]), c_0_35])).
% 0.20/0.44  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_11])]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 39
% 0.20/0.44  # Proof object clause steps            : 26
% 0.20/0.44  # Proof object formula steps           : 13
% 0.20/0.44  # Proof object conjectures             : 6
% 0.20/0.44  # Proof object clause conjectures      : 3
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 6
% 0.20/0.44  # Proof object initial formulas used   : 6
% 0.20/0.44  # Proof object generating inferences   : 17
% 0.20/0.44  # Proof object simplifying inferences  : 15
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 6
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 6
% 0.20/0.44  # Removed in clause preprocessing      : 0
% 0.20/0.44  # Initial clauses in saturation        : 6
% 0.20/0.44  # Processed clauses                    : 775
% 0.20/0.44  # ...of these trivial                  : 358
% 0.20/0.44  # ...subsumed                          : 291
% 0.20/0.44  # ...remaining for further processing  : 126
% 0.20/0.44  # Other redundant clauses eliminated   : 0
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 0
% 0.20/0.44  # Backward-rewritten                   : 44
% 0.20/0.44  # Generated clauses                    : 11445
% 0.20/0.44  # ...of the previous two non-trivial   : 6755
% 0.20/0.44  # Contextual simplify-reflections      : 0
% 0.20/0.44  # Paramodulations                      : 11445
% 0.20/0.44  # Factorizations                       : 0
% 0.20/0.44  # Equation resolutions                 : 0
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 76
% 0.20/0.44  #    Positive orientable unit clauses  : 71
% 0.20/0.44  #    Positive unorientable unit clauses: 5
% 0.20/0.44  #    Negative unit clauses             : 0
% 0.20/0.44  #    Non-unit-clauses                  : 0
% 0.20/0.44  # Current number of unprocessed clauses: 5832
% 0.20/0.44  # ...number of literals in the above   : 5832
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 50
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.44  # Unit Clause-clause subsumption calls : 30
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 377
% 0.20/0.44  # BW rewrite match successes           : 193
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 84055
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.098 s
% 0.20/0.44  # System time              : 0.009 s
% 0.20/0.44  # Total time               : 0.108 s
% 0.20/0.44  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
