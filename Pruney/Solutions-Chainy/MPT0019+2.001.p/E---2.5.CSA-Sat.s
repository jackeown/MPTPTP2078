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
% DateTime   : Thu Dec  3 10:31:48 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  55 expanded)
%              Number of clauses        :   14 (  23 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   36 (  75 expanded)
%              Number of equality atoms :   11 (  32 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t12_xboole_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_5,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | r1_tarski(k2_xboole_0(X9,X11),k2_xboole_0(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).

fof(c_0_6,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_7,plain,(
    ! [X6] : k2_xboole_0(X6,X6) = X6 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => k2_xboole_0(X1,X2) = X2 ) ),
    inference(assume_negation,[status(cth)],[t12_xboole_1])).

cnf(c_0_9,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_10,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

fof(c_0_12,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & k2_xboole_0(esk1_0,esk2_0) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_13,plain,(
    ! [X7,X8] : r1_tarski(X7,k2_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_14,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10]),
    [final]).

cnf(c_0_15,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_11]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_18,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_10]),
    [final]).

cnf(c_0_19,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10]),
    [final]).

cnf(c_0_20,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_10]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk1_0) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_10]),
    [final]).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_10]),
    [final]).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_11]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:31:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S061I
% 0.21/0.38  # and selection function SelectMaxLComplexAPPNTNp.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.026 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # No proof found!
% 0.21/0.38  # SZS status CounterSatisfiable
% 0.21/0.38  # SZS output start Saturation
% 0.21/0.38  fof(t9_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 0.21/0.38  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.21/0.38  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.21/0.38  fof(t12_xboole_1, conjecture, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.38  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.21/0.38  fof(c_0_5, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|r1_tarski(k2_xboole_0(X9,X11),k2_xboole_0(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_xboole_1])])).
% 0.21/0.38  fof(c_0_6, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.21/0.38  fof(c_0_7, plain, ![X6]:k2_xboole_0(X6,X6)=X6, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.21/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2)), inference(assume_negation,[status(cth)],[t12_xboole_1])).
% 0.21/0.38  cnf(c_0_9, plain, (r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.21/0.38  cnf(c_0_10, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.21/0.38  cnf(c_0_11, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.21/0.38  fof(c_0_12, negated_conjecture, (r1_tarski(esk1_0,esk2_0)&k2_xboole_0(esk1_0,esk2_0)!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.21/0.38  fof(c_0_13, plain, ![X7, X8]:r1_tarski(X7,k2_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.21/0.38  cnf(c_0_14, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_9, c_0_10]), ['final']).
% 0.21/0.38  cnf(c_0_15, plain, (r1_tarski(k2_xboole_0(X1,X2),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_9, c_0_11]), ['final']).
% 0.21/0.38  cnf(c_0_16, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.38  cnf(c_0_17, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.21/0.38  cnf(c_0_18, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_14, c_0_10]), ['final']).
% 0.21/0.38  cnf(c_0_19, plain, (r1_tarski(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_9, c_0_10]), ['final']).
% 0.21/0.38  cnf(c_0_20, plain, (r1_tarski(k2_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_10]), ['final']).
% 0.21/0.38  cnf(c_0_21, negated_conjecture, (k2_xboole_0(esk2_0,esk1_0)!=esk2_0), inference(rw,[status(thm)],[c_0_16, c_0_10]), ['final']).
% 0.21/0.38  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_17, c_0_10]), ['final']).
% 0.21/0.38  cnf(c_0_23, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_17, c_0_11]), ['final']).
% 0.21/0.38  cnf(c_0_24, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.21/0.38  # SZS output end Saturation
% 0.21/0.38  # Proof object total steps             : 25
% 0.21/0.38  # Proof object clause steps            : 14
% 0.21/0.38  # Proof object formula steps           : 11
% 0.21/0.38  # Proof object conjectures             : 6
% 0.21/0.38  # Proof object clause conjectures      : 3
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 6
% 0.21/0.38  # Proof object initial formulas used   : 5
% 0.21/0.38  # Proof object generating inferences   : 7
% 0.21/0.38  # Proof object simplifying inferences  : 1
% 0.21/0.38  # Parsed axioms                        : 5
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 6
% 0.21/0.38  # Removed in clause preprocessing      : 0
% 0.21/0.38  # Initial clauses in saturation        : 6
% 0.21/0.38  # Processed clauses                    : 40
% 0.21/0.38  # ...of these trivial                  : 1
% 0.21/0.38  # ...subsumed                          : 19
% 0.21/0.38  # ...remaining for further processing  : 20
% 0.21/0.38  # Other redundant clauses eliminated   : 0
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 1
% 0.21/0.38  # Generated clauses                    : 38
% 0.21/0.38  # ...of the previous two non-trivial   : 28
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 38
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 0
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 13
% 0.21/0.38  #    Positive orientable unit clauses  : 5
% 0.21/0.38  #    Positive unorientable unit clauses: 1
% 0.21/0.38  #    Negative unit clauses             : 1
% 0.21/0.38  #    Non-unit-clauses                  : 6
% 0.21/0.38  # Current number of unprocessed clauses: 0
% 0.21/0.38  # ...number of literals in the above   : 0
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 7
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 83
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 83
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 19
% 0.21/0.38  # Unit Clause-clause subsumption calls : 0
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 17
% 0.21/0.38  # BW rewrite match successes           : 12
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 517
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.025 s
% 0.21/0.38  # System time              : 0.004 s
% 0.21/0.38  # Total time               : 0.030 s
% 0.21/0.38  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
