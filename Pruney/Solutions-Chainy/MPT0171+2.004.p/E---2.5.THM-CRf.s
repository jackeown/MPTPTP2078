%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:56 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   11 (  11 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t87_enumset1,conjecture,(
    ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] : k3_enumset1(X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t87_enumset1])).

fof(c_0_4,negated_conjecture,(
    k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X17] : k2_enumset1(X17,X17,X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

fof(c_0_6,plain,(
    ! [X13,X14,X15,X16] : k3_enumset1(X13,X13,X14,X15,X16) = k2_enumset1(X13,X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_7,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:38:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.36  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.20/0.36  # and selection function SelectNewComplexAHP.
% 0.20/0.36  #
% 0.20/0.36  # Preprocessing time       : 0.026 s
% 0.20/0.36  # Presaturation interreduction done
% 0.20/0.36  
% 0.20/0.36  # Proof found!
% 0.20/0.36  # SZS status Theorem
% 0.20/0.36  # SZS output start CNFRefutation
% 0.20/0.36  fof(t87_enumset1, conjecture, ![X1]:k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_enumset1)).
% 0.20/0.36  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 0.20/0.36  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.36  fof(c_0_3, negated_conjecture, ~(![X1]:k3_enumset1(X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(assume_negation,[status(cth)],[t87_enumset1])).
% 0.20/0.36  fof(c_0_4, negated_conjecture, k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)!=k1_tarski(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.20/0.36  fof(c_0_5, plain, ![X17]:k2_enumset1(X17,X17,X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 0.20/0.36  fof(c_0_6, plain, ![X13, X14, X15, X16]:k3_enumset1(X13,X13,X14,X15,X16)=k2_enumset1(X13,X14,X15,X16), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.36  cnf(c_0_7, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.36  cnf(c_0_8, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.36  cnf(c_0_9, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.36  cnf(c_0_10, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7, c_0_8]), c_0_9])]), ['proof']).
% 0.20/0.36  # SZS output end CNFRefutation
% 0.20/0.36  # Proof object total steps             : 11
% 0.20/0.36  # Proof object clause steps            : 4
% 0.20/0.36  # Proof object formula steps           : 7
% 0.20/0.36  # Proof object conjectures             : 5
% 0.20/0.36  # Proof object clause conjectures      : 2
% 0.20/0.36  # Proof object formula conjectures     : 3
% 0.20/0.36  # Proof object initial clauses used    : 3
% 0.20/0.36  # Proof object initial formulas used   : 3
% 0.20/0.36  # Proof object generating inferences   : 0
% 0.20/0.36  # Proof object simplifying inferences  : 3
% 0.20/0.36  # Training examples: 0 positive, 0 negative
% 0.20/0.36  # Parsed axioms                        : 5
% 0.20/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.36  # Initial clauses                      : 5
% 0.20/0.36  # Removed in clause preprocessing      : 3
% 0.20/0.36  # Initial clauses in saturation        : 2
% 0.20/0.36  # Processed clauses                    : 1
% 0.20/0.36  # ...of these trivial                  : 0
% 0.20/0.36  # ...subsumed                          : 0
% 0.20/0.36  # ...remaining for further processing  : 0
% 0.20/0.36  # Other redundant clauses eliminated   : 0
% 0.20/0.36  # Clauses deleted for lack of memory   : 0
% 0.20/0.36  # Backward-subsumed                    : 0
% 0.20/0.36  # Backward-rewritten                   : 0
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
% 0.20/0.36  # Current number of processed clauses  : 0
% 0.20/0.36  #    Positive orientable unit clauses  : 0
% 0.20/0.36  #    Positive unorientable unit clauses: 0
% 0.20/0.36  #    Negative unit clauses             : 0
% 0.20/0.36  #    Non-unit-clauses                  : 0
% 0.20/0.36  # Current number of unprocessed clauses: 1
% 0.20/0.36  # ...number of literals in the above   : 1
% 0.20/0.36  # Current number of archived formulas  : 0
% 0.20/0.36  # Current number of archived clauses   : 3
% 0.20/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.36  # Unit Clause-clause subsumption calls : 0
% 0.20/0.36  # Rewrite failures with RHS unbound    : 0
% 0.20/0.36  # BW rewrite match attempts            : 0
% 0.20/0.36  # BW rewrite match successes           : 0
% 0.20/0.36  # Condensation attempts                : 0
% 0.20/0.36  # Condensation successes               : 0
% 0.20/0.36  # Termbank termtop insertions          : 206
% 0.20/0.36  
% 0.20/0.36  # -------------------------------------------------
% 0.20/0.36  # User time                : 0.022 s
% 0.20/0.36  # System time              : 0.006 s
% 0.20/0.36  # Total time               : 0.029 s
% 0.20/0.36  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
