%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:02 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   16 (  22 expanded)
%              Number of clauses        :    7 (   9 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    4
%              Number of atoms          :   25 (  37 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_xboole_1,conjecture,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t35_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k4_xboole_0(X1,X4),k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(assume_negation,[status(cth)],[t36_xboole_1])).

fof(c_0_5,plain,(
    ! [X6,X7,X8,X9] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(k4_xboole_0(X6,X9),k4_xboole_0(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_xboole_1])])).

fof(c_0_6,plain,(
    ! [X10] : k4_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_7,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_8,negated_conjecture,(
    ~ r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_9,plain,
    ( r1_tarski(k4_xboole_0(X1,X4),k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_11,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_13,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])]),
    [final]).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:59:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S061I
% 0.14/0.37  # and selection function SelectMaxLComplexAPPNTNp.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.027 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # No proof found!
% 0.14/0.37  # SZS status CounterSatisfiable
% 0.14/0.37  # SZS output start Saturation
% 0.14/0.37  fof(t36_xboole_1, conjecture, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.14/0.37  fof(t35_xboole_1, axiom, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k4_xboole_0(X1,X4),k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_xboole_1)).
% 0.14/0.37  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.14/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1)), inference(assume_negation,[status(cth)],[t36_xboole_1])).
% 0.14/0.37  fof(c_0_5, plain, ![X6, X7, X8, X9]:(~r1_tarski(X6,X7)|~r1_tarski(X8,X9)|r1_tarski(k4_xboole_0(X6,X9),k4_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_xboole_1])])).
% 0.14/0.37  fof(c_0_6, plain, ![X10]:k4_xboole_0(X10,k1_xboole_0)=X10, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.14/0.37  fof(c_0_7, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.37  fof(c_0_8, negated_conjecture, ~r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.14/0.37  cnf(c_0_9, plain, (r1_tarski(k4_xboole_0(X1,X4),k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.14/0.37  cnf(c_0_10, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.14/0.37  cnf(c_0_11, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.37  cnf(c_0_12, negated_conjecture, (~r1_tarski(k4_xboole_0(esk1_0,esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.37  cnf(c_0_13, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])]), ['final']).
% 0.14/0.37  cnf(c_0_14, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X3,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_9, c_0_10]), ['final']).
% 0.14/0.37  cnf(c_0_15, negated_conjecture, (~r1_tarski(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.14/0.37  # SZS output end Saturation
% 0.14/0.37  # Proof object total steps             : 16
% 0.14/0.37  # Proof object clause steps            : 7
% 0.14/0.37  # Proof object formula steps           : 9
% 0.14/0.37  # Proof object conjectures             : 5
% 0.14/0.37  # Proof object clause conjectures      : 2
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 4
% 0.14/0.37  # Proof object initial formulas used   : 4
% 0.14/0.37  # Proof object generating inferences   : 3
% 0.14/0.37  # Proof object simplifying inferences  : 2
% 0.14/0.37  # Parsed axioms                        : 4
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 4
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 4
% 0.14/0.37  # Processed clauses                    : 11
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 11
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 0
% 0.14/0.37  # Generated clauses                    : 5
% 0.14/0.37  # ...of the previous two non-trivial   : 3
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 5
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
% 0.14/0.37  # Current number of processed clauses  : 7
% 0.14/0.37  #    Positive orientable unit clauses  : 2
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 2
% 0.14/0.37  #    Non-unit-clauses                  : 3
% 0.14/0.37  # Current number of unprocessed clauses: 0
% 0.14/0.37  # ...number of literals in the above   : 0
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 4
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 5
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 5
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 1
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 0
% 0.14/0.37  # BW rewrite match successes           : 0
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 294
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.026 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.030 s
% 0.14/0.38  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
