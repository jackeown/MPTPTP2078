%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:24 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 100 expanded)
%              Number of clauses        :   23 (  45 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :   44 ( 100 expanded)
%              Number of equality atoms :   43 (  99 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t53_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(c_0_10,plain,(
    ! [X6] : k2_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_11,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_12,plain,(
    ! [X20,X21] : k2_xboole_0(k3_xboole_0(X20,X21),k4_xboole_0(X20,X21)) = X20 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_13,plain,(
    ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_19,plain,(
    ! [X7,X8] : k2_xboole_0(X7,k4_xboole_0(X8,X7)) = k2_xboole_0(X7,X8) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,plain,(
    ! [X12,X13,X14] : k4_xboole_0(k4_xboole_0(X12,X13),X14) = k4_xboole_0(X12,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_17]),c_0_22])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_23])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t53_xboole_1])).

fof(c_0_28,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_29,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_14]),c_0_23])).

fof(c_0_31,plain,(
    ! [X9] : k4_xboole_0(X9,k1_xboole_0) = X9 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_32,negated_conjecture,(
    k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) != k3_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_33,plain,(
    ! [X17,X18,X19] : k3_xboole_0(X17,k4_xboole_0(X18,X19)) = k4_xboole_0(k3_xboole_0(X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_22])).

cnf(c_0_36,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) != k3_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_34]),c_0_20]),c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k3_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk1_0),esk3_0) != k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( k3_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:35:35 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.12/0.37  # and selection function SelectNewComplexAHP.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.025 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.12/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.12/0.37  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.12/0.37  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.12/0.37  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.12/0.37  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.12/0.37  fof(t53_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 0.12/0.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.37  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.12/0.37  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.12/0.37  fof(c_0_10, plain, ![X6]:k2_xboole_0(X6,k1_xboole_0)=X6, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.12/0.37  fof(c_0_11, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.12/0.37  fof(c_0_12, plain, ![X20, X21]:k2_xboole_0(k3_xboole_0(X20,X21),k4_xboole_0(X20,X21))=X20, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.12/0.37  fof(c_0_13, plain, ![X10, X11]:k4_xboole_0(k2_xboole_0(X10,X11),X11)=k4_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.12/0.37  cnf(c_0_14, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_16, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_17, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_18, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.37  fof(c_0_19, plain, ![X7, X8]:k2_xboole_0(X7,k4_xboole_0(X8,X7))=k2_xboole_0(X7,X8), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.12/0.37  cnf(c_0_20, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 0.12/0.37  cnf(c_0_21, plain, (k4_xboole_0(X1,X1)=k4_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.37  cnf(c_0_22, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_23, plain, (k2_xboole_0(k4_xboole_0(X1,X1),k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.37  fof(c_0_24, plain, ![X12, X13, X14]:k4_xboole_0(k4_xboole_0(X12,X13),X14)=k4_xboole_0(X12,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.12/0.37  cnf(c_0_25, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_17]), c_0_22])).
% 0.12/0.37  cnf(c_0_26, plain, (k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k4_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_23])).
% 0.12/0.37  fof(c_0_27, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t53_xboole_1])).
% 0.12/0.37  fof(c_0_28, plain, ![X15, X16]:k4_xboole_0(X15,k4_xboole_0(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.37  cnf(c_0_29, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_30, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_14]), c_0_23])).
% 0.12/0.37  fof(c_0_31, plain, ![X9]:k4_xboole_0(X9,k1_xboole_0)=X9, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.12/0.37  fof(c_0_32, negated_conjecture, k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))!=k3_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.12/0.37  fof(c_0_33, plain, ![X17, X18, X19]:k3_xboole_0(X17,k4_xboole_0(X18,X19))=k4_xboole_0(k3_xboole_0(X17,X18),X19), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.12/0.37  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_35, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X1))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_22])).
% 0.12/0.37  cnf(c_0_36, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))!=k3_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_38, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.37  cnf(c_0_39, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.12/0.37  cnf(c_0_40, plain, (k2_xboole_0(X1,k4_xboole_0(X1,X2))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_34]), c_0_20]), c_0_15])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k3_xboole_0(k4_xboole_0(esk1_0,esk2_0),esk1_0),esk3_0)!=k4_xboole_0(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.37  cnf(c_0_42, plain, (k3_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_29])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 44
% 0.12/0.37  # Proof object clause steps            : 23
% 0.12/0.37  # Proof object formula steps           : 21
% 0.12/0.37  # Proof object conjectures             : 6
% 0.12/0.37  # Proof object clause conjectures      : 3
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 10
% 0.12/0.37  # Proof object initial formulas used   : 10
% 0.12/0.37  # Proof object generating inferences   : 10
% 0.12/0.37  # Proof object simplifying inferences  : 12
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 10
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 10
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 10
% 0.12/0.37  # Processed clauses                    : 84
% 0.12/0.37  # ...of these trivial                  : 25
% 0.12/0.37  # ...subsumed                          : 3
% 0.12/0.37  # ...remaining for further processing  : 56
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 14
% 0.12/0.37  # Generated clauses                    : 415
% 0.12/0.37  # ...of the previous two non-trivial   : 222
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 415
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 32
% 0.12/0.37  #    Positive orientable unit clauses  : 31
% 0.12/0.37  #    Positive unorientable unit clauses: 1
% 0.12/0.37  #    Negative unit clauses             : 0
% 0.12/0.37  #    Non-unit-clauses                  : 0
% 0.12/0.37  # Current number of unprocessed clauses: 131
% 0.12/0.37  # ...number of literals in the above   : 131
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 24
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 91
% 0.12/0.37  # BW rewrite match successes           : 16
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3103
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.028 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.033 s
% 0.12/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
