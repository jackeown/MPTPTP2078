%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:51 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   22 (  36 expanded)
%              Number of clauses        :   12 (  14 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :   50 (  88 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_xboole_1,conjecture,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t67_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ~ ( r1_tarski(X2,X1)
            & r1_xboole_0(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t69_xboole_1])).

fof(c_0_6,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X9,X11)
      | ~ r1_xboole_0(X10,X11)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).

fof(c_0_7,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & r1_tarski(esk2_0,esk1_0)
    & r1_xboole_0(esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_9,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_12,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_13,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r1_tarski(esk2_0,X1)
    | ~ r1_xboole_0(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( r1_xboole_0(esk2_0,X1)
    | ~ r1_xboole_0(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_11]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r1_xboole_0(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_11]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17]),
    [final]).

cnf(c_0_21,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:04:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_____0021_10gd3
% 0.14/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.026 s
% 0.14/0.37  
% 0.14/0.37  # No proof found!
% 0.14/0.37  # SZS status CounterSatisfiable
% 0.14/0.37  # SZS output start Saturation
% 0.14/0.37  fof(t69_xboole_1, conjecture, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.14/0.37  fof(t67_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 0.14/0.37  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.14/0.37  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.14/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1))))), inference(assume_negation,[status(cth)],[t69_xboole_1])).
% 0.14/0.37  fof(c_0_6, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X9,X11)|~r1_xboole_0(X10,X11)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).
% 0.14/0.37  fof(c_0_7, negated_conjecture, (~v1_xboole_0(esk2_0)&(r1_tarski(esk2_0,esk1_0)&r1_xboole_0(esk2_0,esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.14/0.37  fof(c_0_8, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_xboole_0(X7,X8)|r1_xboole_0(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.14/0.37  fof(c_0_9, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.14/0.37  cnf(c_0_10, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.14/0.37  cnf(c_0_11, negated_conjecture, (r1_tarski(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.37  cnf(c_0_12, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.37  cnf(c_0_13, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.37  cnf(c_0_14, negated_conjecture, (r1_xboole_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.37  cnf(c_0_15, negated_conjecture, (esk2_0=k1_xboole_0|~r1_tarski(esk2_0,X1)|~r1_xboole_0(X1,esk1_0)), inference(spm,[status(thm)],[c_0_10, c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_16, negated_conjecture, (r1_xboole_0(esk2_0,X1)|~r1_xboole_0(esk1_0,X1)), inference(spm,[status(thm)],[c_0_12, c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_17, negated_conjecture, (r1_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_13, c_0_14]), ['final']).
% 0.14/0.37  cnf(c_0_18, negated_conjecture, (esk2_0=k1_xboole_0|~r1_xboole_0(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_15, c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_19, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, (r1_xboole_0(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_17]), ['final']).
% 0.14/0.37  cnf(c_0_21, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0]), ['final']).
% 0.14/0.37  # SZS output end Saturation
% 0.14/0.37  # Proof object total steps             : 22
% 0.14/0.37  # Proof object clause steps            : 12
% 0.14/0.37  # Proof object formula steps           : 10
% 0.14/0.37  # Proof object conjectures             : 11
% 0.14/0.37  # Proof object clause conjectures      : 8
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 7
% 0.14/0.37  # Proof object initial formulas used   : 5
% 0.14/0.37  # Proof object generating inferences   : 5
% 0.14/0.37  # Proof object simplifying inferences  : 0
% 0.14/0.37  # Parsed axioms                        : 5
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 7
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 7
% 0.14/0.37  # Processed clauses                    : 12
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 12
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 0
% 0.14/0.37  # Generated clauses                    : 7
% 0.14/0.37  # ...of the previous two non-trivial   : 5
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 7
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
% 0.14/0.37  #    Negative unit clauses             : 1
% 0.14/0.37  #    Non-unit-clauses                  : 6
% 0.14/0.37  # Current number of unprocessed clauses: 0
% 0.14/0.37  # ...number of literals in the above   : 0
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 0
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 4
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 4
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 0
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 0
% 0.14/0.37  # BW rewrite match successes           : 0
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 471
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.023 s
% 0.14/0.37  # System time              : 0.007 s
% 0.14/0.37  # Total time               : 0.030 s
% 0.14/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
