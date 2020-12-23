%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:24 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   15 (  47 expanded)
%              Number of clauses        :   10 (  18 expanded)
%              Number of leaves         :    2 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 ( 169 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t106_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X2,X4) ) ) ),
    inference(assume_negation,[status(cth)],[t106_zfmisc_1])).

fof(c_0_3,negated_conjecture,
    ( ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
      | ~ r2_hidden(esk1_0,esk3_0)
      | ~ r2_hidden(esk2_0,esk4_0) )
    & ( r2_hidden(esk1_0,esk3_0)
      | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) )
    & ( r2_hidden(esk2_0,esk4_0)
      | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])])).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8] :
      ( ( r2_hidden(X5,X7)
        | ~ r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) )
      & ( r2_hidden(X6,X8)
        | ~ r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) )
      & ( ~ r2_hidden(X5,X7)
        | ~ r2_hidden(X6,X8)
        | r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_5,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r2_hidden(esk1_0,esk3_0)
    | ~ r2_hidden(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_9,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_5,c_0_6]),c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_10,c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_11]),c_0_12]),c_0_13])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:25:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___092_C01_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.026 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t106_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 0.12/0.37  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.12/0.37  fof(c_0_2, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4)))), inference(assume_negation,[status(cth)],[t106_zfmisc_1])).
% 0.12/0.37  fof(c_0_3, negated_conjecture, ((~r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))|(~r2_hidden(esk1_0,esk3_0)|~r2_hidden(esk2_0,esk4_0)))&((r2_hidden(esk1_0,esk3_0)|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)))&(r2_hidden(esk2_0,esk4_0)|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])])).
% 0.12/0.37  fof(c_0_4, plain, ![X5, X6, X7, X8]:(((r2_hidden(X5,X7)|~r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)))&(r2_hidden(X6,X8)|~r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8))))&(~r2_hidden(X5,X7)|~r2_hidden(X6,X8)|r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.12/0.37  cnf(c_0_5, negated_conjecture, (~r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))|~r2_hidden(esk1_0,esk3_0)|~r2_hidden(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.37  cnf(c_0_6, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_7, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_8, negated_conjecture, (r2_hidden(esk2_0,esk4_0)|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.37  cnf(c_0_9, negated_conjecture, (~r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_5, c_0_6]), c_0_7])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (r2_hidden(esk1_0,esk3_0)|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.37  cnf(c_0_11, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (r2_hidden(esk2_0,esk4_0)), inference(sr,[status(thm)],[c_0_8, c_0_9])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (r2_hidden(esk1_0,esk3_0)), inference(sr,[status(thm)],[c_0_10, c_0_9])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_11]), c_0_12]), c_0_13])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 15
% 0.12/0.37  # Proof object clause steps            : 10
% 0.12/0.37  # Proof object formula steps           : 5
% 0.12/0.37  # Proof object conjectures             : 10
% 0.12/0.37  # Proof object clause conjectures      : 7
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 6
% 0.12/0.37  # Proof object initial formulas used   : 2
% 0.12/0.37  # Proof object generating inferences   : 1
% 0.12/0.37  # Proof object simplifying inferences  : 7
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 2
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 6
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 6
% 0.12/0.37  # Processed clauses                    : 14
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 14
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 5
% 0.12/0.37  # ...of the previous two non-trivial   : 2
% 0.12/0.37  # Contextual simplify-reflections      : 2
% 0.12/0.37  # Paramodulations                      : 3
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 6
% 0.12/0.37  #    Positive orientable unit clauses  : 2
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 3
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 8
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 7
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 7
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 0
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 506
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.027 s
% 0.12/0.37  # System time              : 0.002 s
% 0.12/0.37  # Total time               : 0.029 s
% 0.12/0.37  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
