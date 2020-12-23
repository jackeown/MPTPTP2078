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
% DateTime   : Thu Dec  3 10:59:57 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   13 (  19 expanded)
%              Number of clauses        :    6 (   8 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  19 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t54_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_mcart_1)).

fof(c_0_3,plain,(
    ! [X8,X9,X10,X11] : k4_zfmisc_1(X8,X9,X10,X11) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10),X11) ),
    inference(variable_rename,[status(thm)],[t53_mcart_1])).

fof(c_0_4,plain,(
    ! [X5,X6,X7] : k3_zfmisc_1(X5,X6,X7) = k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(assume_negation,[status(cth)],[t54_mcart_1])).

cnf(c_0_6,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,(
    k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0) != k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0) != k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_7]),c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:20:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic U_____100_C02_04_F1_SE_CS_SP_PS_S5PRR_RG_ND_S04AN
% 0.13/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.026 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t53_mcart_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_mcart_1)).
% 0.13/0.36  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.13/0.36  fof(t54_mcart_1, conjecture, ![X1, X2, X3, X4]:k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)=k4_zfmisc_1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_mcart_1)).
% 0.13/0.36  fof(c_0_3, plain, ![X8, X9, X10, X11]:k4_zfmisc_1(X8,X9,X10,X11)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X9),X10),X11), inference(variable_rename,[status(thm)],[t53_mcart_1])).
% 0.13/0.36  fof(c_0_4, plain, ![X5, X6, X7]:k3_zfmisc_1(X5,X6,X7)=k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.13/0.36  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4]:k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)=k4_zfmisc_1(X1,X2,X3,X4)), inference(assume_negation,[status(cth)],[t54_mcart_1])).
% 0.13/0.36  cnf(c_0_6, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.13/0.36  cnf(c_0_7, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  fof(c_0_8, negated_conjecture, k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0)!=k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.13/0.36  cnf(c_0_9, plain, (k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)=k4_zfmisc_1(X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_6, c_0_7])).
% 0.13/0.36  cnf(c_0_10, negated_conjecture, (k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0)!=k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.36  cnf(c_0_11, plain, (k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4)=k4_zfmisc_1(X1,X2,X3,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_7]), c_0_9])).
% 0.13/0.36  cnf(c_0_12, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11])]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 13
% 0.13/0.36  # Proof object clause steps            : 6
% 0.13/0.36  # Proof object formula steps           : 7
% 0.13/0.36  # Proof object conjectures             : 5
% 0.13/0.36  # Proof object clause conjectures      : 2
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 3
% 0.13/0.36  # Proof object initial formulas used   : 3
% 0.13/0.36  # Proof object generating inferences   : 1
% 0.13/0.36  # Proof object simplifying inferences  : 4
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 3
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 3
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 3
% 0.13/0.36  # Processed clauses                    : 7
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 0
% 0.13/0.36  # ...remaining for further processing  : 7
% 0.13/0.36  # Other redundant clauses eliminated   : 0
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 1
% 0.13/0.36  # Generated clauses                    : 5
% 0.13/0.36  # ...of the previous two non-trivial   : 2
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 5
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 0
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 3
% 0.13/0.36  #    Positive orientable unit clauses  : 3
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 0
% 0.13/0.36  #    Non-unit-clauses                  : 0
% 0.13/0.36  # Current number of unprocessed clauses: 1
% 0.13/0.36  # ...number of literals in the above   : 1
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 4
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.36  # Unit Clause-clause subsumption calls : 0
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 1
% 0.13/0.36  # BW rewrite match successes           : 1
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 236
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.024 s
% 0.13/0.36  # System time              : 0.005 s
% 0.13/0.36  # Total time               : 0.029 s
% 0.13/0.36  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
