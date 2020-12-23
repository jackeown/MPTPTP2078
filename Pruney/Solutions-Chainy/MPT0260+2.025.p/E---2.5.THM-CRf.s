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
% DateTime   : Thu Dec  3 10:41:54 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  28 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  45 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_zfmisc_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t55_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(c_0_5,plain,(
    ! [X10,X11] : r1_tarski(k1_tarski(X10),k2_tarski(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_7,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_8,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
          & r2_hidden(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t55_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(k1_tarski(X8),X9)
      | ~ r2_hidden(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_14,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)
    & r2_hidden(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_xboole_0(k2_tarski(X1,X1),X2)
    | ~ r1_xboole_0(k2_tarski(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_tarski(X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk1_0,esk1_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:12:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.35  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.20/0.35  # and selection function SelectNewComplexAHPNS.
% 0.20/0.35  #
% 0.20/0.35  # Preprocessing time       : 0.015 s
% 0.20/0.35  
% 0.20/0.35  # Proof found!
% 0.20/0.35  # SZS status Theorem
% 0.20/0.35  # SZS output start CNFRefutation
% 0.20/0.35  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 0.20/0.35  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.35  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.35  fof(t55_zfmisc_1, conjecture, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.20/0.35  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.20/0.35  fof(c_0_5, plain, ![X10, X11]:r1_tarski(k1_tarski(X10),k2_tarski(X10,X11)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 0.20/0.35  fof(c_0_6, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.35  fof(c_0_7, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|~r1_xboole_0(X5,X6)|r1_xboole_0(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.35  cnf(c_0_8, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.35  cnf(c_0_9, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.35  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3)))), inference(assume_negation,[status(cth)],[t55_zfmisc_1])).
% 0.20/0.35  fof(c_0_11, plain, ![X8, X9]:(~r1_xboole_0(k1_tarski(X8),X9)|~r2_hidden(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.20/0.35  cnf(c_0_12, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.35  cnf(c_0_13, plain, (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.20/0.35  fof(c_0_14, negated_conjecture, (r1_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)&r2_hidden(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.20/0.35  cnf(c_0_15, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.35  cnf(c_0_16, plain, (r1_xboole_0(k2_tarski(X1,X1),X2)|~r1_xboole_0(k2_tarski(X1,X3),X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.35  cnf(c_0_17, negated_conjecture, (r1_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.35  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_tarski(X1,X1),X2)), inference(rw,[status(thm)],[c_0_15, c_0_9])).
% 0.20/0.35  cnf(c_0_19, negated_conjecture, (r1_xboole_0(k2_tarski(esk1_0,esk1_0),esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.35  cnf(c_0_20, negated_conjecture, (r2_hidden(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.35  cnf(c_0_21, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])]), ['proof']).
% 0.20/0.35  # SZS output end CNFRefutation
% 0.20/0.35  # Proof object total steps             : 22
% 0.20/0.35  # Proof object clause steps            : 11
% 0.20/0.35  # Proof object formula steps           : 11
% 0.20/0.35  # Proof object conjectures             : 7
% 0.20/0.35  # Proof object clause conjectures      : 4
% 0.20/0.35  # Proof object formula conjectures     : 3
% 0.20/0.35  # Proof object initial clauses used    : 6
% 0.20/0.35  # Proof object initial formulas used   : 5
% 0.20/0.35  # Proof object generating inferences   : 3
% 0.20/0.35  # Proof object simplifying inferences  : 4
% 0.20/0.35  # Training examples: 0 positive, 0 negative
% 0.20/0.35  # Parsed axioms                        : 5
% 0.20/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.35  # Initial clauses                      : 6
% 0.20/0.35  # Removed in clause preprocessing      : 1
% 0.20/0.35  # Initial clauses in saturation        : 5
% 0.20/0.35  # Processed clauses                    : 7
% 0.20/0.35  # ...of these trivial                  : 0
% 0.20/0.35  # ...subsumed                          : 0
% 0.20/0.35  # ...remaining for further processing  : 7
% 0.20/0.35  # Other redundant clauses eliminated   : 0
% 0.20/0.35  # Clauses deleted for lack of memory   : 0
% 0.20/0.35  # Backward-subsumed                    : 0
% 0.20/0.35  # Backward-rewritten                   : 0
% 0.20/0.35  # Generated clauses                    : 4
% 0.20/0.35  # ...of the previous two non-trivial   : 2
% 0.20/0.35  # Contextual simplify-reflections      : 0
% 0.20/0.35  # Paramodulations                      : 4
% 0.20/0.35  # Factorizations                       : 0
% 0.20/0.35  # Equation resolutions                 : 0
% 0.20/0.35  # Propositional unsat checks           : 0
% 0.20/0.35  #    Propositional check models        : 0
% 0.20/0.35  #    Propositional check unsatisfiable : 0
% 0.20/0.35  #    Propositional clauses             : 0
% 0.20/0.35  #    Propositional clauses after purity: 0
% 0.20/0.35  #    Propositional unsat core size     : 0
% 0.20/0.35  #    Propositional preprocessing time  : 0.000
% 0.20/0.35  #    Propositional encoding time       : 0.000
% 0.20/0.35  #    Propositional solver time         : 0.000
% 0.20/0.35  #    Success case prop preproc time    : 0.000
% 0.20/0.35  #    Success case prop encoding time   : 0.000
% 0.20/0.35  #    Success case prop solver time     : 0.000
% 0.20/0.35  # Current number of processed clauses  : 7
% 0.20/0.35  #    Positive orientable unit clauses  : 4
% 0.20/0.35  #    Positive unorientable unit clauses: 0
% 0.20/0.35  #    Negative unit clauses             : 0
% 0.20/0.35  #    Non-unit-clauses                  : 3
% 0.20/0.35  # Current number of unprocessed clauses: 0
% 0.20/0.35  # ...number of literals in the above   : 0
% 0.20/0.35  # Current number of archived formulas  : 0
% 0.20/0.35  # Current number of archived clauses   : 1
% 0.20/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.35  # Unit Clause-clause subsumption calls : 0
% 0.20/0.35  # Rewrite failures with RHS unbound    : 0
% 0.20/0.35  # BW rewrite match attempts            : 0
% 0.20/0.35  # BW rewrite match successes           : 0
% 0.20/0.35  # Condensation attempts                : 0
% 0.20/0.35  # Condensation successes               : 0
% 0.20/0.35  # Termbank termtop insertions          : 361
% 0.20/0.35  
% 0.20/0.35  # -------------------------------------------------
% 0.20/0.35  # User time                : 0.015 s
% 0.20/0.35  # System time              : 0.003 s
% 0.20/0.35  # Total time               : 0.018 s
% 0.20/0.35  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
