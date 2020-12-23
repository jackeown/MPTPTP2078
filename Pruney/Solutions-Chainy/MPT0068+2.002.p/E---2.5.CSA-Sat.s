%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:34 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   25 (  71 expanded)
%              Number of clauses        :   16 (  31 expanded)
%              Number of leaves         :    4 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 ( 142 expanded)
%              Number of equality atoms :   19 (  55 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t61_xboole_1,conjecture,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

fof(c_0_4,plain,(
    ! [X5,X6] :
      ( ( k4_xboole_0(X5,X6) != k1_xboole_0
        | r1_tarski(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | k4_xboole_0(X5,X6) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_5,plain,(
    ! [X7,X8] : r1_tarski(k4_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_6,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_7,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

fof(c_0_8,plain,(
    ! [X3,X4] :
      ( ( r1_tarski(X3,X4)
        | ~ r2_xboole_0(X3,X4) )
      & ( X3 != X4
        | ~ r2_xboole_0(X3,X4) )
      & ( ~ r1_tarski(X3,X4)
        | X3 = X4
        | r2_xboole_0(X3,X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_9,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_6,c_0_7]),
    [final]).

cnf(c_0_10,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( X1 != k1_xboole_0
       => r2_xboole_0(k1_xboole_0,X1) ) ),
    inference(assume_negation,[status(cth)],[t61_xboole_1])).

cnf(c_0_12,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_9]),
    [final]).

cnf(c_0_13,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_7]),
    [final]).

cnf(c_0_14,plain,
    ( X1 != X2
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & ~ r2_xboole_0(k1_xboole_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_16,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_9]),
    [final]).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_9]),
    [final]).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_20,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(er,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_xboole_0(k1_xboole_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_23,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_9]),
    [final]).

cnf(c_0_24,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_6,c_0_16]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:26:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___008_C45_F1_PI_S5PRR_SE_Q4_CS_SP_S4S
% 0.13/0.38  # and selection function SelectNewComplexAHPNS.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.13/0.38  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.13/0.38  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.13/0.38  fof(t61_xboole_1, conjecture, ![X1]:(X1!=k1_xboole_0=>r2_xboole_0(k1_xboole_0,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_xboole_1)).
% 0.13/0.38  fof(c_0_4, plain, ![X5, X6]:((k4_xboole_0(X5,X6)!=k1_xboole_0|r1_tarski(X5,X6))&(~r1_tarski(X5,X6)|k4_xboole_0(X5,X6)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.13/0.38  fof(c_0_5, plain, ![X7, X8]:r1_tarski(k4_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.13/0.38  cnf(c_0_6, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.38  cnf(c_0_7, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.38  fof(c_0_8, plain, ![X3, X4]:(((r1_tarski(X3,X4)|~r2_xboole_0(X3,X4))&(X3!=X4|~r2_xboole_0(X3,X4)))&(~r1_tarski(X3,X4)|X3=X4|r2_xboole_0(X3,X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.13/0.38  cnf(c_0_9, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_6, c_0_7]), ['final']).
% 0.13/0.38  cnf(c_0_10, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(X1!=k1_xboole_0=>r2_xboole_0(k1_xboole_0,X1))), inference(assume_negation,[status(cth)],[t61_xboole_1])).
% 0.13/0.38  cnf(c_0_12, plain, (r1_tarski(k1_xboole_0,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_7, c_0_9]), ['final']).
% 0.13/0.38  cnf(c_0_13, plain, (k4_xboole_0(X1,X2)=X1|r2_xboole_0(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_10, c_0_7]), ['final']).
% 0.13/0.38  cnf(c_0_14, plain, (X1!=X2|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  fof(c_0_15, negated_conjecture, (esk1_0!=k1_xboole_0&~r2_xboole_0(k1_xboole_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.13/0.38  cnf(c_0_16, plain, (r1_tarski(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_9]), ['final']).
% 0.13/0.38  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_13, c_0_9]), ['final']).
% 0.13/0.38  cnf(c_0_18, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.38  cnf(c_0_19, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.38  cnf(c_0_20, plain, (~r2_xboole_0(X1,X1)), inference(er,[status(thm)],[c_0_14]), ['final']).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (~r2_xboole_0(k1_xboole_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.38  cnf(c_0_23, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_9, c_0_9]), ['final']).
% 0.13/0.38  cnf(c_0_24, plain, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_6, c_0_16]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 25
% 0.13/0.38  # Proof object clause steps            : 16
% 0.13/0.38  # Proof object formula steps           : 9
% 0.13/0.38  # Proof object conjectures             : 5
% 0.13/0.38  # Proof object clause conjectures      : 2
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 8
% 0.13/0.38  # Proof object initial formulas used   : 4
% 0.13/0.38  # Proof object generating inferences   : 7
% 0.13/0.38  # Proof object simplifying inferences  : 1
% 0.13/0.38  # Parsed axioms                        : 4
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 8
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 8
% 0.13/0.38  # Processed clauses                    : 18
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 1
% 0.13/0.38  # ...remaining for further processing  : 16
% 0.13/0.38  # Other redundant clauses eliminated   : 1
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 24
% 0.13/0.38  # ...of the previous two non-trivial   : 10
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 23
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 1
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 15
% 0.13/0.38  #    Positive orientable unit clauses  : 6
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 6
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 0
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 3
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 3
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.38  # Unit Clause-clause subsumption calls : 2
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 509
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.027 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.030 s
% 0.13/0.38  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
