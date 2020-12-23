%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:59 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   13 (  47 expanded)
%              Number of clauses        :    6 (  18 expanded)
%              Number of leaves         :    3 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  47 expanded)
%              Number of equality atoms :   12 (  46 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t116_xboole_1,conjecture,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t50_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] : k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(assume_negation,[status(cth)],[t116_xboole_1])).

fof(c_0_4,negated_conjecture,(
    k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) != k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,X5) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_6,plain,(
    ! [X6,X7,X8] : k3_xboole_0(X6,k4_xboole_0(X7,X8)) = k4_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X8)) ),
    inference(variable_rename,[status(thm)],[t50_xboole_1])).

cnf(c_0_7,negated_conjecture,
    ( k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) != k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))) != k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8]),c_0_8]),c_0_8]),c_0_8]),c_0_8])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_8]),c_0_8]),c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:48:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_____X1495__C12_02_nc_F1_AE_CS_SP_S2S
% 0.12/0.36  # and selection function SelectNewComplexAHP.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.026 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t116_xboole_1, conjecture, ![X1, X2, X3]:k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_xboole_1)).
% 0.12/0.36  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.36  fof(t50_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 0.12/0.36  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3]:k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t116_xboole_1])).
% 0.12/0.36  fof(c_0_4, negated_conjecture, k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))!=k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.12/0.36  fof(c_0_5, plain, ![X4, X5]:k4_xboole_0(X4,k4_xboole_0(X4,X5))=k3_xboole_0(X4,X5), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.36  fof(c_0_6, plain, ![X6, X7, X8]:k3_xboole_0(X6,k4_xboole_0(X7,X8))=k4_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X8)), inference(variable_rename,[status(thm)],[t50_xboole_1])).
% 0.12/0.36  cnf(c_0_7, negated_conjecture, (k3_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))!=k3_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_8, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_9, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_10, negated_conjecture, (k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))))!=k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_8]), c_0_8]), c_0_8]), c_0_8]), c_0_8])).
% 0.12/0.36  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_8]), c_0_8]), c_0_8])).
% 0.12/0.36  cnf(c_0_12, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11]), c_0_11])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 13
% 0.12/0.36  # Proof object clause steps            : 6
% 0.12/0.36  # Proof object formula steps           : 7
% 0.12/0.36  # Proof object conjectures             : 6
% 0.12/0.36  # Proof object clause conjectures      : 3
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 3
% 0.12/0.36  # Proof object initial formulas used   : 3
% 0.12/0.36  # Proof object generating inferences   : 0
% 0.12/0.36  # Proof object simplifying inferences  : 11
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 3
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 3
% 0.12/0.36  # Removed in clause preprocessing      : 1
% 0.12/0.36  # Initial clauses in saturation        : 2
% 0.12/0.36  # Processed clauses                    : 2
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 1
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 0
% 0.12/0.36  # Generated clauses                    : 0
% 0.12/0.36  # ...of the previous two non-trivial   : 0
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 0
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 1
% 0.12/0.36  #    Positive orientable unit clauses  : 1
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 0
% 0.12/0.36  #    Non-unit-clauses                  : 0
% 0.12/0.36  # Current number of unprocessed clauses: 0
% 0.12/0.36  # ...number of literals in the above   : 0
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 1
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 0
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 0
% 0.12/0.36  # BW rewrite match successes           : 0
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 227
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.024 s
% 0.12/0.36  # System time              : 0.005 s
% 0.12/0.36  # Total time               : 0.029 s
% 0.12/0.36  # Maximum resident set size: 1552 pages
%------------------------------------------------------------------------------
