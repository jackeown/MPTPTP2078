%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:37 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   25 (  41 expanded)
%              Number of clauses        :   12 (  18 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  47 expanded)
%              Number of equality atoms :   28 (  46 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t146_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(t45_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

fof(t93_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t132_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_tarski(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3))
      & k2_zfmisc_1(X3,k2_tarski(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X3,k1_tarski(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(assume_negation,[status(cth)],[t146_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X7,X8,X9,X10] : k2_enumset1(X7,X8,X9,X10) = k2_xboole_0(k2_tarski(X7,X8),k2_tarski(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t45_enumset1])).

fof(c_0_8,plain,(
    ! [X18,X19] : k3_tarski(k2_tarski(X18,X19)) = k2_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[t93_zfmisc_1])).

fof(c_0_9,negated_conjecture,(
    k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0),k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_10,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X15,X16,X17] :
      ( k2_zfmisc_1(k1_tarski(X15),k2_tarski(X16,X17)) = k2_tarski(k4_tarski(X15,X16),k4_tarski(X15,X17))
      & k2_zfmisc_1(k2_tarski(X15,X16),k1_tarski(X17)) = k2_tarski(k4_tarski(X15,X17),k4_tarski(X16,X17)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X11] : k2_tarski(X11,X11) = k1_tarski(X11) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_14,negated_conjecture,
    ( k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0),k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X12,X13,X14] :
      ( k2_zfmisc_1(k2_tarski(X12,X13),X14) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X12),X14),k2_zfmisc_1(k1_tarski(X13),X14))
      & k2_zfmisc_1(X14,k2_tarski(X12,X13)) = k2_xboole_0(k2_zfmisc_1(X14,k1_tarski(X12)),k2_zfmisc_1(X14,k1_tarski(X13))) ) ),
    inference(variable_rename,[status(thm)],[t132_zfmisc_1])).

cnf(c_0_19,negated_conjecture,
    ( k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) != k3_tarski(k2_tarski(k2_tarski(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0)),k2_tarski(k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(esk1_0,esk1_0),k2_tarski(esk3_0,esk4_0)),k2_zfmisc_1(k2_tarski(esk2_0,esk2_0),k2_tarski(esk3_0,esk4_0)))) != k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),X3) = k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(X1,X1),X3),k2_zfmisc_1(k2_tarski(X2,X2),X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_17]),c_0_17]),c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:51:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.12/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.049 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t146_zfmisc_1, conjecture, ![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 0.12/0.38  fof(t45_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 0.12/0.38  fof(t93_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 0.12/0.38  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.12/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.38  fof(t132_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_tarski(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3))&k2_zfmisc_1(X3,k2_tarski(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X3,k1_tarski(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_zfmisc_1)).
% 0.12/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(assume_negation,[status(cth)],[t146_zfmisc_1])).
% 0.12/0.38  fof(c_0_7, plain, ![X7, X8, X9, X10]:k2_enumset1(X7,X8,X9,X10)=k2_xboole_0(k2_tarski(X7,X8),k2_tarski(X9,X10)), inference(variable_rename,[status(thm)],[t45_enumset1])).
% 0.12/0.38  fof(c_0_8, plain, ![X18, X19]:k3_tarski(k2_tarski(X18,X19))=k2_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[t93_zfmisc_1])).
% 0.12/0.38  fof(c_0_9, negated_conjecture, k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0))!=k2_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0),k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.12/0.38  cnf(c_0_10, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_11, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  fof(c_0_12, plain, ![X15, X16, X17]:(k2_zfmisc_1(k1_tarski(X15),k2_tarski(X16,X17))=k2_tarski(k4_tarski(X15,X16),k4_tarski(X15,X17))&k2_zfmisc_1(k2_tarski(X15,X16),k1_tarski(X17))=k2_tarski(k4_tarski(X15,X17),k4_tarski(X16,X17))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.12/0.38  fof(c_0_13, plain, ![X11]:k2_tarski(X11,X11)=k1_tarski(X11), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.38  cnf(c_0_14, negated_conjecture, (k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0))!=k2_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0),k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_15, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4)))), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.38  cnf(c_0_16, plain, (k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  fof(c_0_18, plain, ![X12, X13, X14]:(k2_zfmisc_1(k2_tarski(X12,X13),X14)=k2_xboole_0(k2_zfmisc_1(k1_tarski(X12),X14),k2_zfmisc_1(k1_tarski(X13),X14))&k2_zfmisc_1(X14,k2_tarski(X12,X13))=k2_xboole_0(k2_zfmisc_1(X14,k1_tarski(X12)),k2_zfmisc_1(X14,k1_tarski(X13)))), inference(variable_rename,[status(thm)],[t132_zfmisc_1])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0))!=k3_tarski(k2_tarski(k2_tarski(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0)),k2_tarski(k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0))))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.38  cnf(c_0_20, plain, (k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.38  cnf(c_0_21, plain, (k2_zfmisc_1(k2_tarski(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(esk1_0,esk1_0),k2_tarski(esk3_0,esk4_0)),k2_zfmisc_1(k2_tarski(esk2_0,esk2_0),k2_tarski(esk3_0,esk4_0))))!=k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_20])).
% 0.12/0.38  cnf(c_0_23, plain, (k2_zfmisc_1(k2_tarski(X1,X2),X3)=k3_tarski(k2_tarski(k2_zfmisc_1(k2_tarski(X1,X1),X3),k2_zfmisc_1(k2_tarski(X2,X2),X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_17]), c_0_17]), c_0_11])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 25
% 0.12/0.38  # Proof object clause steps            : 12
% 0.12/0.38  # Proof object formula steps           : 13
% 0.12/0.38  # Proof object conjectures             : 7
% 0.12/0.38  # Proof object clause conjectures      : 4
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 6
% 0.12/0.38  # Proof object initial formulas used   : 6
% 0.12/0.38  # Proof object generating inferences   : 0
% 0.12/0.38  # Proof object simplifying inferences  : 10
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 7
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 9
% 0.12/0.38  # Removed in clause preprocessing      : 3
% 0.12/0.38  # Initial clauses in saturation        : 6
% 0.12/0.38  # Processed clauses                    : 7
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 0
% 0.12/0.38  # ...remaining for further processing  : 7
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 2
% 0.12/0.38  # Generated clauses                    : 0
% 0.12/0.38  # ...of the previous two non-trivial   : 1
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 0
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 5
% 0.12/0.38  #    Positive orientable unit clauses  : 4
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 0
% 0.12/0.38  #    Non-unit-clauses                  : 1
% 0.12/0.38  # Current number of unprocessed clauses: 0
% 0.12/0.38  # ...number of literals in the above   : 0
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 5
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.38  # Unit Clause-clause subsumption calls : 0
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 8
% 0.12/0.38  # BW rewrite match successes           : 3
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 582
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.050 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.053 s
% 0.12/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
