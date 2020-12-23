%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:19 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   23 (  38 expanded)
%              Number of clauses        :   12 (  16 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  49 expanded)
%              Number of equality atoms :   21 (  36 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t140_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t46_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1)) = X2 ) ),
    inference(assume_negation,[status(cth)],[t140_zfmisc_1])).

fof(c_0_6,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    & k2_xboole_0(k4_xboole_0(esk2_0,k1_tarski(esk1_0)),k1_tarski(esk1_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_8,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,k1_tarski(esk1_0)),k1_tarski(esk1_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X3,X4] : k2_xboole_0(X3,X4) = k2_xboole_0(X4,X3) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_11,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | k2_xboole_0(k1_tarski(X12),X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).

cnf(c_0_12,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk2_0,k2_tarski(esk1_0,esk1_0)),k2_tarski(esk1_0,esk1_0)) != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8,c_0_9]),c_0_9])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X5,X6] : k2_xboole_0(X5,k4_xboole_0(X6,X5)) = k2_xboole_0(X5,X6) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_15,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk1_0,esk1_0),k4_xboole_0(esk2_0,k2_tarski(esk1_0,esk1_0))) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tarski(esk1_0,esk1_0)) != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_13])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,k2_tarski(X2,X2)) = X1
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:51:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S059A
% 0.14/0.35  # and selection function SelectComplexExceptUniqMaxPosHorn.
% 0.14/0.35  #
% 0.14/0.35  # Preprocessing time       : 0.015 s
% 0.14/0.35  # Presaturation interreduction done
% 0.14/0.35  
% 0.14/0.35  # Proof found!
% 0.14/0.35  # SZS status Theorem
% 0.14/0.35  # SZS output start CNFRefutation
% 0.14/0.35  fof(t140_zfmisc_1, conjecture, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 0.14/0.35  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.35  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.14/0.35  fof(t46_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 0.14/0.35  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.14/0.35  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X1))=X2)), inference(assume_negation,[status(cth)],[t140_zfmisc_1])).
% 0.14/0.35  fof(c_0_6, negated_conjecture, (r2_hidden(esk1_0,esk2_0)&k2_xboole_0(k4_xboole_0(esk2_0,k1_tarski(esk1_0)),k1_tarski(esk1_0))!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.14/0.35  fof(c_0_7, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.35  cnf(c_0_8, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,k1_tarski(esk1_0)),k1_tarski(esk1_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.35  cnf(c_0_9, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.35  fof(c_0_10, plain, ![X3, X4]:k2_xboole_0(X3,X4)=k2_xboole_0(X4,X3), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.14/0.35  fof(c_0_11, plain, ![X12, X13]:(~r2_hidden(X12,X13)|k2_xboole_0(k1_tarski(X12),X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_zfmisc_1])])).
% 0.14/0.35  cnf(c_0_12, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk2_0,k2_tarski(esk1_0,esk1_0)),k2_tarski(esk1_0,esk1_0))!=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8, c_0_9]), c_0_9])).
% 0.14/0.35  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.35  fof(c_0_14, plain, ![X5, X6]:k2_xboole_0(X5,k4_xboole_0(X6,X5))=k2_xboole_0(X5,X6), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.14/0.35  cnf(c_0_15, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.35  cnf(c_0_16, negated_conjecture, (k2_xboole_0(k2_tarski(esk1_0,esk1_0),k4_xboole_0(esk2_0,k2_tarski(esk1_0,esk1_0)))!=esk2_0), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.35  cnf(c_0_17, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.35  cnf(c_0_18, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_9])).
% 0.14/0.35  cnf(c_0_19, negated_conjecture, (k2_xboole_0(esk2_0,k2_tarski(esk1_0,esk1_0))!=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_13])).
% 0.14/0.35  cnf(c_0_20, plain, (k2_xboole_0(X1,k2_tarski(X2,X2))=X1|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_13, c_0_18])).
% 0.14/0.35  cnf(c_0_21, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.35  cnf(c_0_22, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])]), ['proof']).
% 0.14/0.35  # SZS output end CNFRefutation
% 0.14/0.35  # Proof object total steps             : 23
% 0.14/0.35  # Proof object clause steps            : 12
% 0.14/0.35  # Proof object formula steps           : 11
% 0.14/0.35  # Proof object conjectures             : 9
% 0.14/0.35  # Proof object clause conjectures      : 6
% 0.14/0.35  # Proof object formula conjectures     : 3
% 0.14/0.36  # Proof object initial clauses used    : 6
% 0.14/0.36  # Proof object initial formulas used   : 5
% 0.14/0.36  # Proof object generating inferences   : 2
% 0.14/0.36  # Proof object simplifying inferences  : 8
% 0.14/0.36  # Training examples: 0 positive, 0 negative
% 0.14/0.36  # Parsed axioms                        : 7
% 0.14/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.36  # Initial clauses                      : 9
% 0.14/0.36  # Removed in clause preprocessing      : 1
% 0.14/0.36  # Initial clauses in saturation        : 8
% 0.14/0.36  # Processed clauses                    : 18
% 0.14/0.36  # ...of these trivial                  : 0
% 0.14/0.36  # ...subsumed                          : 0
% 0.14/0.36  # ...remaining for further processing  : 18
% 0.14/0.36  # Other redundant clauses eliminated   : 1
% 0.14/0.36  # Clauses deleted for lack of memory   : 0
% 0.14/0.36  # Backward-subsumed                    : 0
% 0.14/0.36  # Backward-rewritten                   : 2
% 0.14/0.36  # Generated clauses                    : 8
% 0.14/0.36  # ...of the previous two non-trivial   : 6
% 0.14/0.36  # Contextual simplify-reflections      : 0
% 0.14/0.36  # Paramodulations                      : 7
% 0.14/0.36  # Factorizations                       : 0
% 0.14/0.36  # Equation resolutions                 : 1
% 0.14/0.36  # Propositional unsat checks           : 0
% 0.14/0.36  #    Propositional check models        : 0
% 0.14/0.36  #    Propositional check unsatisfiable : 0
% 0.14/0.36  #    Propositional clauses             : 0
% 0.14/0.36  #    Propositional clauses after purity: 0
% 0.14/0.36  #    Propositional unsat core size     : 0
% 0.14/0.36  #    Propositional preprocessing time  : 0.000
% 0.14/0.36  #    Propositional encoding time       : 0.000
% 0.14/0.36  #    Propositional solver time         : 0.000
% 0.14/0.36  #    Success case prop preproc time    : 0.000
% 0.14/0.36  #    Success case prop encoding time   : 0.000
% 0.14/0.36  #    Success case prop solver time     : 0.000
% 0.14/0.36  # Current number of processed clauses  : 7
% 0.14/0.36  #    Positive orientable unit clauses  : 2
% 0.14/0.36  #    Positive unorientable unit clauses: 1
% 0.14/0.36  #    Negative unit clauses             : 2
% 0.14/0.36  #    Non-unit-clauses                  : 2
% 0.14/0.36  # Current number of unprocessed clauses: 4
% 0.14/0.36  # ...number of literals in the above   : 8
% 0.14/0.36  # Current number of archived formulas  : 0
% 0.14/0.36  # Current number of archived clauses   : 11
% 0.14/0.36  # Clause-clause subsumption calls (NU) : 4
% 0.14/0.36  # Rec. Clause-clause subsumption calls : 4
% 0.14/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.36  # Unit Clause-clause subsumption calls : 0
% 0.14/0.36  # Rewrite failures with RHS unbound    : 0
% 0.14/0.36  # BW rewrite match attempts            : 5
% 0.14/0.36  # BW rewrite match successes           : 5
% 0.14/0.36  # Condensation attempts                : 0
% 0.14/0.36  # Condensation successes               : 0
% 0.14/0.36  # Termbank termtop insertions          : 514
% 0.14/0.36  
% 0.14/0.36  # -------------------------------------------------
% 0.14/0.36  # User time                : 0.017 s
% 0.14/0.36  # System time              : 0.001 s
% 0.14/0.36  # Total time               : 0.018 s
% 0.14/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
