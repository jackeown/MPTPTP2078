%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  35 expanded)
%              Number of clauses        :    8 (  14 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  39 expanded)
%              Number of equality atoms :   20 (  38 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k1_tarski(X4)) = k2_tarski(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k1_tarski(X4)) = k2_tarski(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4)) ),
    inference(assume_negation,[status(cth)],[t40_mcart_1])).

fof(c_0_6,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k1_tarski(esk4_0)) != k2_tarski(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X5] : k2_tarski(X5,X5) = k1_tarski(X5) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_8,plain,(
    ! [X9,X10,X11] : k3_mcart_1(X9,X10,X11) = k4_tarski(k4_tarski(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_9,plain,(
    ! [X12,X13,X14] : k3_zfmisc_1(X12,X13,X14) = k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X6,X7,X8] :
      ( k2_zfmisc_1(k1_tarski(X6),k2_tarski(X7,X8)) = k2_tarski(k4_tarski(X6,X7),k4_tarski(X6,X8))
      & k2_zfmisc_1(k2_tarski(X6,X7),k1_tarski(X8)) = k2_tarski(k4_tarski(X6,X8),k4_tarski(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_11,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k1_tarski(esk4_0)) != k2_tarski(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk3_0)),k2_tarski(esk4_0,esk4_0)) != k2_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12]),c_0_13]),c_0_13]),c_0_14])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:13:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.36  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.20/0.36  # and selection function SelectNewComplexAHP.
% 0.20/0.36  #
% 0.20/0.36  # Preprocessing time       : 0.026 s
% 0.20/0.36  # Presaturation interreduction done
% 0.20/0.36  
% 0.20/0.36  # Proof found!
% 0.20/0.36  # SZS status Theorem
% 0.20/0.36  # SZS output start CNFRefutation
% 0.20/0.36  fof(t40_mcart_1, conjecture, ![X1, X2, X3, X4]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k1_tarski(X4))=k2_tarski(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_mcart_1)).
% 0.20/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.36  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.20/0.36  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.20/0.36  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.20/0.36  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k1_tarski(X4))=k2_tarski(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4))), inference(assume_negation,[status(cth)],[t40_mcart_1])).
% 0.20/0.36  fof(c_0_6, negated_conjecture, k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k1_tarski(esk4_0))!=k2_tarski(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.36  fof(c_0_7, plain, ![X5]:k2_tarski(X5,X5)=k1_tarski(X5), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.36  fof(c_0_8, plain, ![X9, X10, X11]:k3_mcart_1(X9,X10,X11)=k4_tarski(k4_tarski(X9,X10),X11), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.20/0.36  fof(c_0_9, plain, ![X12, X13, X14]:k3_zfmisc_1(X12,X13,X14)=k2_zfmisc_1(k2_zfmisc_1(X12,X13),X14), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.20/0.36  fof(c_0_10, plain, ![X6, X7, X8]:(k2_zfmisc_1(k1_tarski(X6),k2_tarski(X7,X8))=k2_tarski(k4_tarski(X6,X7),k4_tarski(X6,X8))&k2_zfmisc_1(k2_tarski(X6,X7),k1_tarski(X8))=k2_tarski(k4_tarski(X6,X8),k4_tarski(X7,X8))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.20/0.36  cnf(c_0_11, negated_conjecture, (k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k1_tarski(esk4_0))!=k2_tarski(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.36  cnf(c_0_12, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.36  cnf(c_0_13, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.36  cnf(c_0_14, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.36  cnf(c_0_15, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.36  cnf(c_0_16, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk3_0)),k2_tarski(esk4_0,esk4_0))!=k2_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_12]), c_0_13]), c_0_13]), c_0_14])).
% 0.20/0.36  cnf(c_0_17, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[c_0_15, c_0_12])).
% 0.20/0.36  cnf(c_0_18, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17])]), ['proof']).
% 0.20/0.36  # SZS output end CNFRefutation
% 0.20/0.36  # Proof object total steps             : 19
% 0.20/0.36  # Proof object clause steps            : 8
% 0.20/0.36  # Proof object formula steps           : 11
% 0.20/0.36  # Proof object conjectures             : 6
% 0.20/0.36  # Proof object clause conjectures      : 3
% 0.20/0.36  # Proof object formula conjectures     : 3
% 0.20/0.36  # Proof object initial clauses used    : 5
% 0.20/0.36  # Proof object initial formulas used   : 5
% 0.20/0.36  # Proof object generating inferences   : 0
% 0.20/0.36  # Proof object simplifying inferences  : 9
% 0.20/0.36  # Training examples: 0 positive, 0 negative
% 0.20/0.36  # Parsed axioms                        : 5
% 0.20/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.36  # Initial clauses                      : 6
% 0.20/0.36  # Removed in clause preprocessing      : 3
% 0.20/0.36  # Initial clauses in saturation        : 3
% 0.20/0.36  # Processed clauses                    : 2
% 0.20/0.36  # ...of these trivial                  : 0
% 0.20/0.36  # ...subsumed                          : 0
% 0.20/0.36  # ...remaining for further processing  : 2
% 0.20/0.36  # Other redundant clauses eliminated   : 0
% 0.20/0.36  # Clauses deleted for lack of memory   : 0
% 0.20/0.36  # Backward-subsumed                    : 0
% 0.20/0.36  # Backward-rewritten                   : 1
% 0.20/0.36  # Generated clauses                    : 0
% 0.20/0.36  # ...of the previous two non-trivial   : 0
% 0.20/0.36  # Contextual simplify-reflections      : 0
% 0.20/0.36  # Paramodulations                      : 0
% 0.20/0.36  # Factorizations                       : 0
% 0.20/0.36  # Equation resolutions                 : 0
% 0.20/0.36  # Propositional unsat checks           : 0
% 0.20/0.36  #    Propositional check models        : 0
% 0.20/0.36  #    Propositional check unsatisfiable : 0
% 0.20/0.36  #    Propositional clauses             : 0
% 0.20/0.36  #    Propositional clauses after purity: 0
% 0.20/0.36  #    Propositional unsat core size     : 0
% 0.20/0.36  #    Propositional preprocessing time  : 0.000
% 0.20/0.36  #    Propositional encoding time       : 0.000
% 0.20/0.36  #    Propositional solver time         : 0.000
% 0.20/0.36  #    Success case prop preproc time    : 0.000
% 0.20/0.36  #    Success case prop encoding time   : 0.000
% 0.20/0.36  #    Success case prop solver time     : 0.000
% 0.20/0.36  # Current number of processed clauses  : 1
% 0.20/0.36  #    Positive orientable unit clauses  : 1
% 0.20/0.36  #    Positive unorientable unit clauses: 0
% 0.20/0.36  #    Negative unit clauses             : 0
% 0.20/0.36  #    Non-unit-clauses                  : 0
% 0.20/0.36  # Current number of unprocessed clauses: 1
% 0.20/0.36  # ...number of literals in the above   : 1
% 0.20/0.36  # Current number of archived formulas  : 0
% 0.20/0.36  # Current number of archived clauses   : 4
% 0.20/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.36  # Unit Clause-clause subsumption calls : 0
% 0.20/0.36  # Rewrite failures with RHS unbound    : 0
% 0.20/0.36  # BW rewrite match attempts            : 1
% 0.20/0.36  # BW rewrite match successes           : 1
% 0.20/0.36  # Condensation attempts                : 0
% 0.20/0.36  # Condensation successes               : 0
% 0.20/0.36  # Termbank termtop insertions          : 348
% 0.20/0.36  
% 0.20/0.36  # -------------------------------------------------
% 0.20/0.36  # User time                : 0.025 s
% 0.20/0.36  # System time              : 0.004 s
% 0.20/0.36  # Total time               : 0.029 s
% 0.20/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
