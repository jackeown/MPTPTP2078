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
% DateTime   : Thu Dec  3 10:36:25 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   18 (  33 expanded)
%              Number of clauses        :    9 (  14 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  33 expanded)
%              Number of equality atoms :   17 (  32 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

fof(t45_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

fof(t112_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X3,X1) ),
    inference(assume_negation,[status(cth)],[t113_enumset1])).

fof(c_0_5,negated_conjecture,(
    k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk2_0,esk4_0,esk3_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X14] : k2_enumset1(X11,X12,X13,X14) = k2_xboole_0(k2_tarski(X11,X12),k2_tarski(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t45_enumset1])).

fof(c_0_7,plain,(
    ! [X7,X8,X9,X10] : k2_enumset1(X7,X8,X9,X10) = k2_enumset1(X8,X10,X7,X9) ),
    inference(variable_rename,[status(thm)],[t112_enumset1])).

cnf(c_0_8,negated_conjecture,
    ( k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk2_0,esk4_0,esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X5,X6] : k2_tarski(X5,X6) = k2_tarski(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_11,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X2,X4,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk4_0),k2_tarski(esk3_0,esk1_0)) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8,c_0_9]),c_0_9])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_xboole_0(k2_tarski(X2,X4),k2_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_9]),c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk4_0,esk3_0)) != k2_xboole_0(k2_tarski(esk2_0,esk4_0),k2_tarski(esk3_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13]),c_0_13])).

cnf(c_0_16,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_xboole_0(k2_tarski(X1,X4),k2_tarski(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:08:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.038 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t113_enumset1, conjecture, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X3,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 0.14/0.39  fof(t45_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_enumset1)).
% 0.14/0.39  fof(t112_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X1,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_enumset1)).
% 0.14/0.39  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.14/0.39  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X3,X1)), inference(assume_negation,[status(cth)],[t113_enumset1])).
% 0.14/0.39  fof(c_0_5, negated_conjecture, k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk2_0,esk4_0,esk3_0,esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.14/0.39  fof(c_0_6, plain, ![X11, X12, X13, X14]:k2_enumset1(X11,X12,X13,X14)=k2_xboole_0(k2_tarski(X11,X12),k2_tarski(X13,X14)), inference(variable_rename,[status(thm)],[t45_enumset1])).
% 0.14/0.39  fof(c_0_7, plain, ![X7, X8, X9, X10]:k2_enumset1(X7,X8,X9,X10)=k2_enumset1(X8,X10,X7,X9), inference(variable_rename,[status(thm)],[t112_enumset1])).
% 0.14/0.39  cnf(c_0_8, negated_conjecture, (k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk2_0,esk4_0,esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.39  cnf(c_0_9, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.39  fof(c_0_10, plain, ![X5, X6]:k2_tarski(X5,X6)=k2_tarski(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.14/0.39  cnf(c_0_11, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X2,X4,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.39  cnf(c_0_12, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk4_0),k2_tarski(esk3_0,esk1_0))!=k2_xboole_0(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8, c_0_9]), c_0_9])).
% 0.14/0.39  cnf(c_0_13, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_14, plain, (k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_xboole_0(k2_tarski(X2,X4),k2_tarski(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_9]), c_0_9])).
% 0.14/0.39  cnf(c_0_15, negated_conjecture, (k2_xboole_0(k2_tarski(esk2_0,esk1_0),k2_tarski(esk4_0,esk3_0))!=k2_xboole_0(k2_tarski(esk2_0,esk4_0),k2_tarski(esk3_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13]), c_0_13])).
% 0.14/0.39  cnf(c_0_16, plain, (k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_xboole_0(k2_tarski(X1,X4),k2_tarski(X2,X3))), inference(spm,[status(thm)],[c_0_14, c_0_13])).
% 0.14/0.39  cnf(c_0_17, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 18
% 0.14/0.39  # Proof object clause steps            : 9
% 0.14/0.39  # Proof object formula steps           : 9
% 0.14/0.39  # Proof object conjectures             : 7
% 0.14/0.39  # Proof object clause conjectures      : 4
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 4
% 0.14/0.39  # Proof object initial formulas used   : 4
% 0.14/0.39  # Proof object generating inferences   : 1
% 0.14/0.39  # Proof object simplifying inferences  : 8
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 4
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 4
% 0.14/0.39  # Removed in clause preprocessing      : 1
% 0.14/0.39  # Initial clauses in saturation        : 3
% 0.14/0.39  # Processed clauses                    : 15
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 4
% 0.14/0.39  # ...remaining for further processing  : 11
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 1
% 0.14/0.39  # Generated clauses                    : 118
% 0.14/0.39  # ...of the previous two non-trivial   : 88
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 118
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 0
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 7
% 0.14/0.39  #    Positive orientable unit clauses  : 0
% 0.14/0.39  #    Positive unorientable unit clauses: 7
% 0.14/0.39  #    Negative unit clauses             : 0
% 0.14/0.39  #    Non-unit-clauses                  : 0
% 0.14/0.39  # Current number of unprocessed clauses: 79
% 0.14/0.39  # ...number of literals in the above   : 79
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 5
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.39  # Unit Clause-clause subsumption calls : 15
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 76
% 0.14/0.39  # BW rewrite match successes           : 76
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 1115
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.039 s
% 0.14/0.39  # System time              : 0.005 s
% 0.14/0.39  # Total time               : 0.044 s
% 0.14/0.39  # Maximum resident set size: 1552 pages
%------------------------------------------------------------------------------
