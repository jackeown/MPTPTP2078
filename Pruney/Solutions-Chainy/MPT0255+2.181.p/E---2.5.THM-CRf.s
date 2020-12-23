%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:42 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  49 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_zfmisc_1,conjecture,(
    ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t47_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)
     => r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] : k2_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t50_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X10,X11] :
      ( ~ r1_xboole_0(k1_tarski(X10),X11)
      | ~ r2_hidden(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_9,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X6,X7,X8] :
      ( ( r1_xboole_0(X6,k2_xboole_0(X7,X8))
        | ~ r1_xboole_0(X6,X7)
        | ~ r1_xboole_0(X6,X8) )
      & ( r1_xboole_0(X6,X7)
        | ~ r1_xboole_0(X6,k2_xboole_0(X7,X8)) )
      & ( r1_xboole_0(X6,X8)
        | ~ r1_xboole_0(X6,k2_xboole_0(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

fof(c_0_11,negated_conjecture,(
    k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_12,plain,(
    ! [X5] : r1_xboole_0(X5,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_13,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(k2_xboole_0(k2_tarski(X12,X13),X14),X14)
      | r2_hidden(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_zfmisc_1])])).

fof(c_0_19,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_tarski(X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_23])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:48:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.14/0.37  # and selection function SelectNewComplexAHPNS.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.027 s
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t50_zfmisc_1, conjecture, ![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 0.14/0.37  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.14/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.37  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.14/0.37  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.14/0.37  fof(t47_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)=>r2_hidden(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 0.14/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:k2_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t50_zfmisc_1])).
% 0.14/0.37  fof(c_0_8, plain, ![X10, X11]:(~r1_xboole_0(k1_tarski(X10),X11)|~r2_hidden(X10,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.14/0.37  fof(c_0_9, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.37  fof(c_0_10, plain, ![X6, X7, X8]:((r1_xboole_0(X6,k2_xboole_0(X7,X8))|~r1_xboole_0(X6,X7)|~r1_xboole_0(X6,X8))&((r1_xboole_0(X6,X7)|~r1_xboole_0(X6,k2_xboole_0(X7,X8)))&(r1_xboole_0(X6,X8)|~r1_xboole_0(X6,k2_xboole_0(X7,X8))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.14/0.37  fof(c_0_11, negated_conjecture, k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.14/0.37  fof(c_0_12, plain, ![X5]:r1_xboole_0(X5,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.14/0.37  cnf(c_0_13, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_15, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_16, negated_conjecture, (k2_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  cnf(c_0_17, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  fof(c_0_18, plain, ![X12, X13, X14]:(~r1_tarski(k2_xboole_0(k2_tarski(X12,X13),X14),X14)|r2_hidden(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_zfmisc_1])])).
% 0.14/0.37  fof(c_0_19, plain, ![X4]:r1_tarski(k1_xboole_0,X4), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.37  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_tarski(X1,X1),X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.37  cnf(c_0_21, negated_conjecture, (r1_xboole_0(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.14/0.37  cnf(c_0_22, plain, (r2_hidden(X1,X3)|~r1_tarski(k2_xboole_0(k2_tarski(X1,X2),X3),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.37  cnf(c_0_23, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.37  cnf(c_0_25, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_16]), c_0_23])]), c_0_24]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 26
% 0.14/0.37  # Proof object clause steps            : 11
% 0.14/0.37  # Proof object formula steps           : 15
% 0.14/0.37  # Proof object conjectures             : 7
% 0.14/0.37  # Proof object clause conjectures      : 4
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 7
% 0.14/0.37  # Proof object initial formulas used   : 7
% 0.14/0.37  # Proof object generating inferences   : 3
% 0.14/0.37  # Proof object simplifying inferences  : 6
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 7
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 9
% 0.14/0.37  # Removed in clause preprocessing      : 1
% 0.14/0.37  # Initial clauses in saturation        : 8
% 0.14/0.37  # Processed clauses                    : 12
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 12
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 0
% 0.14/0.37  # Generated clauses                    : 6
% 0.14/0.37  # ...of the previous two non-trivial   : 5
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 6
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 0
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
% 0.14/0.37  # Current number of processed clauses  : 12
% 0.14/0.37  #    Positive orientable unit clauses  : 5
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 3
% 0.14/0.37  #    Non-unit-clauses                  : 4
% 0.14/0.37  # Current number of unprocessed clauses: 1
% 0.14/0.37  # ...number of literals in the above   : 3
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 1
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 2
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 2
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 4
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 0
% 0.14/0.37  # BW rewrite match successes           : 0
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 571
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.028 s
% 0.14/0.37  # System time              : 0.002 s
% 0.14/0.37  # Total time               : 0.030 s
% 0.14/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
