%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:02 EST 2020

% Result     : Theorem 1.19s
% Output     : CNFRefutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  46 expanded)
%              Number of clauses        :   17 (  20 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  58 expanded)
%              Number of equality atoms :   29 (  41 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t117_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X3,X2)
     => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t45_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X3,X2)
       => k4_xboole_0(X1,X3) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t117_xboole_1])).

fof(c_0_9,plain,(
    ! [X18,X19,X20] : k4_xboole_0(X18,k4_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X18,X19),k3_xboole_0(X18,X20)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

fof(c_0_10,plain,(
    ! [X7,X8] : k3_xboole_0(X7,k2_xboole_0(X7,X8)) = X7 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

fof(c_0_11,plain,(
    ! [X4] : k2_xboole_0(X4,X4) = X4 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_12,plain,(
    ! [X5,X6] :
      ( ~ r1_tarski(X5,X6)
      | k2_xboole_0(X5,X6) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_13,plain,(
    ! [X9,X10] : r1_tarski(k4_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_14,plain,(
    ! [X11,X12] : k4_xboole_0(k2_xboole_0(X11,X12),X12) = k4_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_15,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | X14 = k2_xboole_0(X13,k4_xboole_0(X14,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0)
    & k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( X2 = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X4))) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_17])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(X1,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_22]),c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk3_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X3,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(X1,esk2_0),k3_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0))) = k4_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.19/1.44  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 1.19/1.44  # and selection function SelectNewComplexAHP.
% 1.19/1.44  #
% 1.19/1.44  # Preprocessing time       : 0.026 s
% 1.19/1.44  
% 1.19/1.44  # Proof found!
% 1.19/1.44  # SZS status Theorem
% 1.19/1.44  # SZS output start CNFRefutation
% 1.19/1.44  fof(t117_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_xboole_1)).
% 1.19/1.44  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 1.19/1.44  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.19/1.44  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.19/1.44  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.19/1.44  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.19/1.44  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.19/1.44  fof(t45_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 1.19/1.44  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X3,X2)=>k4_xboole_0(X1,X3)=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t117_xboole_1])).
% 1.19/1.44  fof(c_0_9, plain, ![X18, X19, X20]:k4_xboole_0(X18,k4_xboole_0(X19,X20))=k2_xboole_0(k4_xboole_0(X18,X19),k3_xboole_0(X18,X20)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 1.19/1.44  fof(c_0_10, plain, ![X7, X8]:k3_xboole_0(X7,k2_xboole_0(X7,X8))=X7, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 1.19/1.44  fof(c_0_11, plain, ![X4]:k2_xboole_0(X4,X4)=X4, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 1.19/1.44  fof(c_0_12, plain, ![X5, X6]:(~r1_tarski(X5,X6)|k2_xboole_0(X5,X6)=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.19/1.44  fof(c_0_13, plain, ![X9, X10]:r1_tarski(k4_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 1.19/1.44  fof(c_0_14, plain, ![X11, X12]:k4_xboole_0(k2_xboole_0(X11,X12),X12)=k4_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 1.19/1.44  fof(c_0_15, plain, ![X13, X14]:(~r1_tarski(X13,X14)|X14=k2_xboole_0(X13,k4_xboole_0(X14,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_xboole_1])])).
% 1.19/1.44  fof(c_0_16, negated_conjecture, (r1_tarski(esk3_0,esk2_0)&k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 1.19/1.44  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.19/1.44  cnf(c_0_18, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.19/1.44  cnf(c_0_19, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.19/1.44  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.19/1.44  cnf(c_0_21, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.19/1.44  cnf(c_0_22, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.19/1.44  cnf(c_0_23, plain, (X2=k2_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.19/1.44  cnf(c_0_24, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.19/1.44  cnf(c_0_25, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X4)))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X3,X4)))), inference(spm,[status(thm)],[c_0_17, c_0_17])).
% 1.19/1.44  cnf(c_0_26, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.19/1.44  cnf(c_0_27, plain, (k2_xboole_0(k4_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 1.19/1.44  cnf(c_0_28, plain, (k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k3_xboole_0(X1,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_22]), c_0_17])).
% 1.19/1.44  cnf(c_0_29, negated_conjecture, (k2_xboole_0(esk3_0,k4_xboole_0(esk2_0,esk3_0))=esk2_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.19/1.44  cnf(c_0_30, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X3,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 1.19/1.44  cnf(c_0_31, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,k4_xboole_0(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.19/1.44  cnf(c_0_32, negated_conjecture, (k2_xboole_0(k4_xboole_0(X1,esk2_0),k3_xboole_0(X1,k4_xboole_0(esk2_0,esk3_0)))=k4_xboole_0(X1,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 1.19/1.44  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])]), ['proof']).
% 1.19/1.44  # SZS output end CNFRefutation
% 1.19/1.44  # Proof object total steps             : 34
% 1.19/1.44  # Proof object clause steps            : 17
% 1.19/1.44  # Proof object formula steps           : 17
% 1.19/1.44  # Proof object conjectures             : 8
% 1.19/1.44  # Proof object clause conjectures      : 5
% 1.19/1.44  # Proof object formula conjectures     : 3
% 1.19/1.44  # Proof object initial clauses used    : 9
% 1.19/1.44  # Proof object initial formulas used   : 8
% 1.19/1.44  # Proof object generating inferences   : 7
% 1.19/1.44  # Proof object simplifying inferences  : 5
% 1.19/1.44  # Training examples: 0 positive, 0 negative
% 1.19/1.44  # Parsed axioms                        : 9
% 1.19/1.44  # Removed by relevancy pruning/SinE    : 0
% 1.19/1.44  # Initial clauses                      : 10
% 1.19/1.44  # Removed in clause preprocessing      : 0
% 1.19/1.44  # Initial clauses in saturation        : 10
% 1.19/1.44  # Processed clauses                    : 1581
% 1.19/1.44  # ...of these trivial                  : 792
% 1.19/1.44  # ...subsumed                          : 0
% 1.19/1.44  # ...remaining for further processing  : 789
% 1.19/1.44  # Other redundant clauses eliminated   : 0
% 1.19/1.44  # Clauses deleted for lack of memory   : 0
% 1.19/1.44  # Backward-subsumed                    : 0
% 1.19/1.44  # Backward-rewritten                   : 190
% 1.19/1.44  # Generated clauses                    : 101284
% 1.19/1.44  # ...of the previous two non-trivial   : 46919
% 1.19/1.44  # Contextual simplify-reflections      : 0
% 1.19/1.44  # Paramodulations                      : 101284
% 1.19/1.44  # Factorizations                       : 0
% 1.19/1.44  # Equation resolutions                 : 0
% 1.19/1.44  # Propositional unsat checks           : 0
% 1.19/1.44  #    Propositional check models        : 0
% 1.19/1.44  #    Propositional check unsatisfiable : 0
% 1.19/1.44  #    Propositional clauses             : 0
% 1.19/1.44  #    Propositional clauses after purity: 0
% 1.19/1.44  #    Propositional unsat core size     : 0
% 1.19/1.44  #    Propositional preprocessing time  : 0.000
% 1.19/1.44  #    Propositional encoding time       : 0.000
% 1.19/1.44  #    Propositional solver time         : 0.000
% 1.19/1.44  #    Success case prop preproc time    : 0.000
% 1.19/1.44  #    Success case prop encoding time   : 0.000
% 1.19/1.44  #    Success case prop solver time     : 0.000
% 1.19/1.44  # Current number of processed clauses  : 599
% 1.19/1.44  #    Positive orientable unit clauses  : 595
% 1.19/1.44  #    Positive unorientable unit clauses: 2
% 1.19/1.44  #    Negative unit clauses             : 0
% 1.19/1.44  #    Non-unit-clauses                  : 2
% 1.19/1.44  # Current number of unprocessed clauses: 45019
% 1.19/1.44  # ...number of literals in the above   : 45019
% 1.19/1.44  # Current number of archived formulas  : 0
% 1.19/1.44  # Current number of archived clauses   : 190
% 1.19/1.44  # Clause-clause subsumption calls (NU) : 1
% 1.19/1.44  # Rec. Clause-clause subsumption calls : 1
% 1.19/1.44  # Non-unit clause-clause subsumptions  : 0
% 1.19/1.44  # Unit Clause-clause subsumption calls : 5
% 1.19/1.44  # Rewrite failures with RHS unbound    : 0
% 1.19/1.44  # BW rewrite match attempts            : 2371
% 1.19/1.44  # BW rewrite match successes           : 133
% 1.19/1.44  # Condensation attempts                : 0
% 1.19/1.44  # Condensation successes               : 0
% 1.19/1.44  # Termbank termtop insertions          : 1460716
% 1.19/1.44  
% 1.19/1.44  # -------------------------------------------------
% 1.19/1.44  # User time                : 1.036 s
% 1.19/1.44  # System time              : 0.051 s
% 1.19/1.44  # Total time               : 1.088 s
% 1.19/1.44  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
