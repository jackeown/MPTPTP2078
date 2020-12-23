%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:27 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t42_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t55_xboole_1,conjecture,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(c_0_6,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k4_xboole_0(X5,X4)) = k2_xboole_0(X4,X5) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_7,plain,(
    ! [X6,X7,X8] : k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_8,plain,(
    ! [X9,X10,X11] : k4_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(k4_xboole_0(X9,X11),k4_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t42_xboole_1])).

fof(c_0_9,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k3_xboole_0(X12,X13)) = k4_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(assume_negation,[status(cth)],[t55_xboole_1])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X16,X17] : k2_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(X16,X17)) = X16 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_14,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,negated_conjecture,(
    k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1))) = k2_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k3_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X1,X3),k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) != k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X1)) = k4_xboole_0(k2_xboole_0(X1,X3),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.20/0.43  # and selection function SelectNewComplexAHP.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.025 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.43  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.20/0.43  fof(t42_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 0.20/0.43  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.20/0.43  fof(t55_xboole_1, conjecture, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_xboole_1)).
% 0.20/0.43  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.20/0.43  fof(c_0_6, plain, ![X4, X5]:k2_xboole_0(X4,k4_xboole_0(X5,X4))=k2_xboole_0(X4,X5), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.43  fof(c_0_7, plain, ![X6, X7, X8]:k4_xboole_0(k4_xboole_0(X6,X7),X8)=k4_xboole_0(X6,k2_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.20/0.43  fof(c_0_8, plain, ![X9, X10, X11]:k4_xboole_0(k2_xboole_0(X9,X10),X11)=k2_xboole_0(k4_xboole_0(X9,X11),k4_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t42_xboole_1])).
% 0.20/0.43  fof(c_0_9, plain, ![X12, X13]:k4_xboole_0(X12,k3_xboole_0(X12,X13))=k4_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.20/0.43  fof(c_0_10, negated_conjecture, ~(![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(assume_negation,[status(cth)],[t55_xboole_1])).
% 0.20/0.43  cnf(c_0_11, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.43  cnf(c_0_12, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.43  fof(c_0_13, plain, ![X16, X17]:k2_xboole_0(k3_xboole_0(X16,X17),k4_xboole_0(X16,X17))=X16, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.20/0.43  cnf(c_0_14, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.43  cnf(c_0_15, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.43  fof(c_0_16, negated_conjecture, k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.20/0.43  cnf(c_0_17, plain, (k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X1)))=k2_xboole_0(X1,k4_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.43  cnf(c_0_18, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.43  cnf(c_0_19, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,k3_xboole_0(X1,X2)))=k4_xboole_0(k2_xboole_0(X1,X3),k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.43  cnf(c_0_20, negated_conjecture, (k4_xboole_0(k2_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))!=k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.43  cnf(c_0_21, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X1))=k4_xboole_0(k2_xboole_0(X1,X3),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.20/0.43  cnf(c_0_22, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21])]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 23
% 0.20/0.43  # Proof object clause steps            : 10
% 0.20/0.43  # Proof object formula steps           : 13
% 0.20/0.43  # Proof object conjectures             : 5
% 0.20/0.43  # Proof object clause conjectures      : 2
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 6
% 0.20/0.43  # Proof object initial formulas used   : 6
% 0.20/0.43  # Proof object generating inferences   : 3
% 0.20/0.43  # Proof object simplifying inferences  : 3
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 7
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 7
% 0.20/0.43  # Removed in clause preprocessing      : 0
% 0.20/0.43  # Initial clauses in saturation        : 7
% 0.20/0.43  # Processed clauses                    : 390
% 0.20/0.43  # ...of these trivial                  : 201
% 0.20/0.43  # ...subsumed                          : 38
% 0.20/0.43  # ...remaining for further processing  : 151
% 0.20/0.43  # Other redundant clauses eliminated   : 0
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 0
% 0.20/0.43  # Backward-rewritten                   : 30
% 0.20/0.43  # Generated clauses                    : 8050
% 0.20/0.43  # ...of the previous two non-trivial   : 3732
% 0.20/0.43  # Contextual simplify-reflections      : 0
% 0.20/0.43  # Paramodulations                      : 8050
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 0
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 114
% 0.20/0.43  #    Positive orientable unit clauses  : 113
% 0.20/0.43  #    Positive unorientable unit clauses: 1
% 0.20/0.43  #    Negative unit clauses             : 0
% 0.20/0.43  #    Non-unit-clauses                  : 0
% 0.20/0.43  # Current number of unprocessed clauses: 3249
% 0.20/0.43  # ...number of literals in the above   : 3249
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 37
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.43  # Unit Clause-clause subsumption calls : 10
% 0.20/0.43  # Rewrite failures with RHS unbound    : 6
% 0.20/0.43  # BW rewrite match attempts            : 225
% 0.20/0.43  # BW rewrite match successes           : 22
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 70473
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.087 s
% 0.20/0.43  # System time              : 0.005 s
% 0.20/0.43  # Total time               : 0.092 s
% 0.20/0.43  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
