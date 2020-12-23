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
% DateTime   : Thu Dec  3 10:32:24 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  83 expanded)
%              Number of clauses        :   18 (  36 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  83 expanded)
%              Number of equality atoms :   32 (  82 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t50_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(t52_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(c_0_7,plain,(
    ! [X7,X8,X9] : k4_xboole_0(k4_xboole_0(X7,X8),X9) = k4_xboole_0(X7,k2_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_8,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k3_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_9,plain,(
    ! [X10,X11] : k4_xboole_0(X10,k3_xboole_0(X10,X11)) = k4_xboole_0(X10,X11) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_10,plain,(
    ! [X14,X15,X16] : k3_xboole_0(X14,k4_xboole_0(X15,X16)) = k4_xboole_0(k3_xboole_0(X14,X15),X16) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_11,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X17,X18,X19] : k3_xboole_0(X17,k4_xboole_0(X18,X19)) = k4_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X17,X19)) ),
    inference(variable_rename,[status(thm)],[t50_xboole_1])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,plain,(
    ! [X4,X5,X6] : k4_xboole_0(X4,k3_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X6)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_12]),c_0_13])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_16]),c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X1),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_20,c_0_14])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t52_xboole_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3))) = k4_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_14]),c_0_23])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,X3))) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_24]),c_0_17])).

fof(c_0_28,negated_conjecture,(
    k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X2,X1),X3)) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_12]),c_0_27]),c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_31,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) = k4_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_12]),c_0_14]),c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:04:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.19/0.37  # and selection function SelectNewComplexAHP.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.025 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.19/0.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.37  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.19/0.37  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.19/0.37  fof(t50_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_xboole_1)).
% 0.19/0.37  fof(l36_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 0.19/0.37  fof(t52_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.19/0.37  fof(c_0_7, plain, ![X7, X8, X9]:k4_xboole_0(k4_xboole_0(X7,X8),X9)=k4_xboole_0(X7,k2_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.19/0.37  fof(c_0_8, plain, ![X12, X13]:k4_xboole_0(X12,k4_xboole_0(X12,X13))=k3_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.37  fof(c_0_9, plain, ![X10, X11]:k4_xboole_0(X10,k3_xboole_0(X10,X11))=k4_xboole_0(X10,X11), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.19/0.37  fof(c_0_10, plain, ![X14, X15, X16]:k3_xboole_0(X14,k4_xboole_0(X15,X16))=k4_xboole_0(k3_xboole_0(X14,X15),X16), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.19/0.37  cnf(c_0_11, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_12, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_13, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_14, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  fof(c_0_15, plain, ![X17, X18, X19]:k3_xboole_0(X17,k4_xboole_0(X18,X19))=k4_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X17,X19)), inference(variable_rename,[status(thm)],[t50_xboole_1])).
% 0.19/0.37  cnf(c_0_16, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.37  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.37  fof(c_0_18, plain, ![X4, X5, X6]:k4_xboole_0(X4,k3_xboole_0(X5,X6))=k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X6)), inference(variable_rename,[status(thm)],[l36_xboole_1])).
% 0.19/0.37  cnf(c_0_19, plain, (k3_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_12]), c_0_13])).
% 0.19/0.37  cnf(c_0_20, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_21, plain, (k3_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_16]), c_0_17])).
% 0.19/0.37  cnf(c_0_22, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_23, plain, (k4_xboole_0(k3_xboole_0(X1,X1),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_14])).
% 0.19/0.37  cnf(c_0_24, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_20, c_0_14])).
% 0.19/0.37  fof(c_0_25, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t52_xboole_1])).
% 0.19/0.37  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X1,X3)))=k4_xboole_0(X1,k3_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_14]), c_0_23])).
% 0.19/0.37  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,X3)))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_24]), c_0_17])).
% 0.19/0.37  fof(c_0_28, negated_conjecture, k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.19/0.37  cnf(c_0_29, plain, (k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X2,X1),X3))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_12]), c_0_27]), c_0_14])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_31, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))=k4_xboole_0(X1,k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_12]), c_0_14]), c_0_29])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 33
% 0.19/0.37  # Proof object clause steps            : 18
% 0.19/0.37  # Proof object formula steps           : 15
% 0.19/0.37  # Proof object conjectures             : 5
% 0.19/0.37  # Proof object clause conjectures      : 2
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 7
% 0.19/0.37  # Proof object initial formulas used   : 7
% 0.19/0.37  # Proof object generating inferences   : 8
% 0.19/0.37  # Proof object simplifying inferences  : 13
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 7
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 7
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 7
% 0.19/0.37  # Processed clauses                    : 48
% 0.19/0.37  # ...of these trivial                  : 10
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 38
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 5
% 0.19/0.37  # Generated clauses                    : 525
% 0.19/0.37  # ...of the previous two non-trivial   : 351
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 525
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 26
% 0.19/0.37  #    Positive orientable unit clauses  : 26
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 0
% 0.19/0.37  #    Non-unit-clauses                  : 0
% 0.19/0.37  # Current number of unprocessed clauses: 317
% 0.19/0.37  # ...number of literals in the above   : 317
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 12
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 12
% 0.19/0.37  # BW rewrite match successes           : 5
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 5711
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.030 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.034 s
% 0.19/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
