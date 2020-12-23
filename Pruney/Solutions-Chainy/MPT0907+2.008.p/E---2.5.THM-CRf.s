%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:07 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   18 (  31 expanded)
%              Number of clauses        :   11 (  14 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  68 expanded)
%              Number of equality atoms :   27 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t67_mcart_1])).

fof(c_0_4,plain,(
    ! [X11,X12,X13] :
      ( ( X11 != k1_mcart_1(X11)
        | X11 != k4_tarski(X12,X13) )
      & ( X11 != k2_mcart_1(X11)
        | X11 != k4_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

fof(c_0_5,plain,(
    ! [X6,X7,X8] :
      ( ~ r2_hidden(X6,k2_zfmisc_1(X7,X8))
      | k4_tarski(esk1_1(X6),esk2_1(X6)) = X6 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

fof(c_0_6,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))
    & ( esk3_0 = k1_mcart_1(esk3_0)
      | esk3_0 = k2_mcart_1(esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( X1 != k1_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k4_tarski(esk1_1(X1),esk2_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( k4_tarski(esk1_1(esk3_0),esk2_1(esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( esk3_0 = k1_mcart_1(esk3_0)
    | esk3_0 = k2_mcart_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( k1_mcart_1(esk3_0) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k2_mcart_1(esk3_0) = esk3_0 ),
    inference(sr,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_11]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:35:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.14/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.026 s
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t67_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_mcart_1)).
% 0.14/0.37  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.14/0.37  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.14/0.37  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t67_mcart_1])).
% 0.14/0.37  fof(c_0_4, plain, ![X11, X12, X13]:((X11!=k1_mcart_1(X11)|X11!=k4_tarski(X12,X13))&(X11!=k2_mcart_1(X11)|X11!=k4_tarski(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 0.14/0.37  fof(c_0_5, plain, ![X6, X7, X8]:(~r2_hidden(X6,k2_zfmisc_1(X7,X8))|k4_tarski(esk1_1(X6),esk2_1(X6))=X6), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.14/0.37  fof(c_0_6, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))&(esk3_0=k1_mcart_1(esk3_0)|esk3_0=k2_mcart_1(esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.14/0.37  cnf(c_0_7, plain, (X1!=k1_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.37  cnf(c_0_8, plain, (k4_tarski(esk1_1(X1),esk2_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.37  cnf(c_0_9, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  cnf(c_0_10, plain, (k1_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_11, negated_conjecture, (k4_tarski(esk1_1(esk3_0),esk2_1(esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.14/0.37  cnf(c_0_12, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.37  cnf(c_0_13, negated_conjecture, (esk3_0=k1_mcart_1(esk3_0)|esk3_0=k2_mcart_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  cnf(c_0_14, negated_conjecture, (k1_mcart_1(esk3_0)!=esk3_0), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.14/0.37  cnf(c_0_15, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_16, negated_conjecture, (k2_mcart_1(esk3_0)=esk3_0), inference(sr,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.37  cnf(c_0_17, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_11]), c_0_16])]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 18
% 0.14/0.37  # Proof object clause steps            : 11
% 0.14/0.37  # Proof object formula steps           : 7
% 0.14/0.37  # Proof object conjectures             : 9
% 0.14/0.37  # Proof object clause conjectures      : 6
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 5
% 0.14/0.37  # Proof object initial formulas used   : 3
% 0.14/0.37  # Proof object generating inferences   : 3
% 0.14/0.37  # Proof object simplifying inferences  : 5
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 3
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 5
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 5
% 0.14/0.37  # Processed clauses                    : 10
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 10
% 0.14/0.37  # Other redundant clauses eliminated   : 2
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 0
% 0.14/0.37  # Generated clauses                    : 6
% 0.14/0.37  # ...of the previous two non-trivial   : 5
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 3
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 2
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 7
% 0.14/0.37  #    Positive orientable unit clauses  : 3
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 3
% 0.14/0.37  #    Non-unit-clauses                  : 1
% 0.14/0.37  # Current number of unprocessed clauses: 0
% 0.14/0.37  # ...number of literals in the above   : 0
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 1
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 1
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 0
% 0.14/0.37  # BW rewrite match successes           : 0
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 338
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.025 s
% 0.14/0.37  # System time              : 0.005 s
% 0.14/0.37  # Total time               : 0.030 s
% 0.14/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
