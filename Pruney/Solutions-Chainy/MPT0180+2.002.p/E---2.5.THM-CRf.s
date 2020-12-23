%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:06 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    4
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t96_enumset1,conjecture,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_enumset1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t90_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_enumset1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t96_enumset1])).

fof(c_0_5,negated_conjecture,(
    k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X20] : k1_enumset1(X20,X20,X20) = k1_tarski(X20) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

fof(c_0_7,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_8,plain,(
    ! [X21,X22,X23,X24] : k6_enumset1(X21,X21,X21,X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t90_enumset1])).

cnf(c_0_9,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.32  % Computer   : n013.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 18:30:54 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.33  # Version: 2.5pre002
% 0.10/0.33  # No SInE strategy applied
% 0.10/0.33  # Trying AutoSched0 for 299 seconds
% 0.10/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.10/0.34  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.10/0.34  #
% 0.10/0.34  # Preprocessing time       : 0.014 s
% 0.10/0.34  # Presaturation interreduction done
% 0.10/0.34  
% 0.10/0.34  # Proof found!
% 0.10/0.34  # SZS status Theorem
% 0.10/0.34  # SZS output start CNFRefutation
% 0.10/0.34  fof(t96_enumset1, conjecture, ![X1]:k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_enumset1)).
% 0.10/0.34  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 0.10/0.34  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.10/0.34  fof(t90_enumset1, axiom, ![X1, X2, X3, X4]:k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_enumset1)).
% 0.10/0.34  fof(c_0_4, negated_conjecture, ~(![X1]:k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(assume_negation,[status(cth)],[t96_enumset1])).
% 0.10/0.34  fof(c_0_5, negated_conjecture, k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)!=k1_tarski(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.10/0.34  fof(c_0_6, plain, ![X20]:k1_enumset1(X20,X20,X20)=k1_tarski(X20), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.10/0.34  fof(c_0_7, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.10/0.34  fof(c_0_8, plain, ![X21, X22, X23, X24]:k6_enumset1(X21,X21,X21,X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t90_enumset1])).
% 0.10/0.34  cnf(c_0_9, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.10/0.34  cnf(c_0_10, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.10/0.34  cnf(c_0_11, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.10/0.34  cnf(c_0_12, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.10/0.34  cnf(c_0_13, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])]), ['proof']).
% 0.10/0.34  # SZS output end CNFRefutation
% 0.10/0.34  # Proof object total steps             : 14
% 0.10/0.34  # Proof object clause steps            : 5
% 0.10/0.34  # Proof object formula steps           : 9
% 0.10/0.34  # Proof object conjectures             : 5
% 0.10/0.34  # Proof object clause conjectures      : 2
% 0.10/0.34  # Proof object formula conjectures     : 3
% 0.10/0.34  # Proof object initial clauses used    : 4
% 0.10/0.34  # Proof object initial formulas used   : 4
% 0.10/0.34  # Proof object generating inferences   : 0
% 0.10/0.34  # Proof object simplifying inferences  : 4
% 0.10/0.34  # Training examples: 0 positive, 0 negative
% 0.10/0.34  # Parsed axioms                        : 5
% 0.10/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.34  # Initial clauses                      : 5
% 0.10/0.34  # Removed in clause preprocessing      : 3
% 0.10/0.34  # Initial clauses in saturation        : 2
% 0.10/0.34  # Processed clauses                    : 1
% 0.10/0.34  # ...of these trivial                  : 0
% 0.10/0.34  # ...subsumed                          : 0
% 0.10/0.34  # ...remaining for further processing  : 0
% 0.10/0.34  # Other redundant clauses eliminated   : 0
% 0.10/0.34  # Clauses deleted for lack of memory   : 0
% 0.10/0.34  # Backward-subsumed                    : 0
% 0.10/0.34  # Backward-rewritten                   : 0
% 0.10/0.34  # Generated clauses                    : 0
% 0.10/0.34  # ...of the previous two non-trivial   : 0
% 0.10/0.34  # Contextual simplify-reflections      : 0
% 0.10/0.34  # Paramodulations                      : 0
% 0.10/0.34  # Factorizations                       : 0
% 0.10/0.34  # Equation resolutions                 : 0
% 0.10/0.34  # Propositional unsat checks           : 0
% 0.10/0.34  #    Propositional check models        : 0
% 0.10/0.34  #    Propositional check unsatisfiable : 0
% 0.10/0.34  #    Propositional clauses             : 0
% 0.10/0.34  #    Propositional clauses after purity: 0
% 0.10/0.34  #    Propositional unsat core size     : 0
% 0.10/0.34  #    Propositional preprocessing time  : 0.000
% 0.10/0.34  #    Propositional encoding time       : 0.000
% 0.10/0.34  #    Propositional solver time         : 0.000
% 0.10/0.34  #    Success case prop preproc time    : 0.000
% 0.10/0.34  #    Success case prop encoding time   : 0.000
% 0.10/0.34  #    Success case prop solver time     : 0.000
% 0.10/0.34  # Current number of processed clauses  : 0
% 0.10/0.34  #    Positive orientable unit clauses  : 0
% 0.10/0.34  #    Positive unorientable unit clauses: 0
% 0.10/0.34  #    Negative unit clauses             : 0
% 0.10/0.34  #    Non-unit-clauses                  : 0
% 0.10/0.34  # Current number of unprocessed clauses: 1
% 0.10/0.34  # ...number of literals in the above   : 1
% 0.10/0.34  # Current number of archived formulas  : 0
% 0.10/0.34  # Current number of archived clauses   : 3
% 0.10/0.34  # Clause-clause subsumption calls (NU) : 0
% 0.10/0.34  # Rec. Clause-clause subsumption calls : 0
% 0.10/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.10/0.34  # Unit Clause-clause subsumption calls : 0
% 0.10/0.34  # Rewrite failures with RHS unbound    : 0
% 0.10/0.34  # BW rewrite match attempts            : 0
% 0.10/0.34  # BW rewrite match successes           : 0
% 0.10/0.34  # Condensation attempts                : 0
% 0.10/0.34  # Condensation successes               : 0
% 0.16/0.34  # Termbank termtop insertions          : 221
% 0.16/0.34  
% 0.16/0.34  # -------------------------------------------------
% 0.16/0.34  # User time                : 0.015 s
% 0.16/0.34  # System time              : 0.002 s
% 0.16/0.34  # Total time               : 0.017 s
% 0.16/0.34  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
