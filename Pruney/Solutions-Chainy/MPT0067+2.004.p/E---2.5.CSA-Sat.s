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
% DateTime   : Thu Dec  3 10:32:33 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   14 (  25 expanded)
%              Number of clauses        :    9 (  10 expanded)
%              Number of leaves         :    2 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  63 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_xboole_1,conjecture,(
    ! [X1,X2] :
      ~ ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( r1_tarski(X1,X2)
          & r2_xboole_0(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t60_xboole_1])).

fof(c_0_3,plain,(
    ! [X3,X4] :
      ( ( r1_tarski(X3,X4)
        | ~ r2_xboole_0(X3,X4) )
      & ( X3 != X4
        | ~ r2_xboole_0(X3,X4) )
      & ( ~ r1_tarski(X3,X4)
        | X3 = X4
        | r2_xboole_0(X3,X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

fof(c_0_4,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r2_xboole_0(esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_6,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_7,plain,
    ( X1 != X2
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,negated_conjecture,
    ( r2_xboole_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_9,negated_conjecture,
    ( esk2_0 = esk1_0
    | r2_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_10,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(er,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( r2_xboole_0(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_8]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:14:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S057A
% 0.20/0.37  # and selection function SelectMin2Infpos.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.026 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # No proof found!
% 0.20/0.37  # SZS status CounterSatisfiable
% 0.20/0.37  # SZS output start Saturation
% 0.20/0.37  fof(t60_xboole_1, conjecture, ![X1, X2]:~((r1_tarski(X1,X2)&r2_xboole_0(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 0.20/0.37  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.20/0.37  fof(c_0_2, negated_conjecture, ~(![X1, X2]:~((r1_tarski(X1,X2)&r2_xboole_0(X2,X1)))), inference(assume_negation,[status(cth)],[t60_xboole_1])).
% 0.20/0.37  fof(c_0_3, plain, ![X3, X4]:(((r1_tarski(X3,X4)|~r2_xboole_0(X3,X4))&(X3!=X4|~r2_xboole_0(X3,X4)))&(~r1_tarski(X3,X4)|X3=X4|r2_xboole_0(X3,X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.20/0.37  fof(c_0_4, negated_conjecture, (r1_tarski(esk1_0,esk2_0)&r2_xboole_0(esk2_0,esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).
% 0.20/0.37  cnf(c_0_5, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.20/0.37  cnf(c_0_6, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.37  cnf(c_0_7, plain, (X1!=X2|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.37  cnf(c_0_8, negated_conjecture, (r2_xboole_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.37  cnf(c_0_9, negated_conjecture, (esk2_0=esk1_0|r2_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_5, c_0_6])).
% 0.20/0.37  cnf(c_0_10, plain, (~r2_xboole_0(X1,X1)), inference(er,[status(thm)],[c_0_7]), ['final']).
% 0.20/0.37  cnf(c_0_11, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.20/0.37  cnf(c_0_12, negated_conjecture, (r2_xboole_0(esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), ['final']).
% 0.20/0.37  cnf(c_0_13, negated_conjecture, (r1_tarski(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_11, c_0_8]), ['final']).
% 0.20/0.37  # SZS output end Saturation
% 0.20/0.37  # Proof object total steps             : 14
% 0.20/0.37  # Proof object clause steps            : 9
% 0.20/0.37  # Proof object formula steps           : 5
% 0.20/0.37  # Proof object conjectures             : 8
% 0.20/0.37  # Proof object clause conjectures      : 5
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 5
% 0.20/0.37  # Proof object initial formulas used   : 2
% 0.20/0.37  # Proof object generating inferences   : 3
% 0.20/0.37  # Proof object simplifying inferences  : 2
% 0.20/0.37  # Parsed axioms                        : 2
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 5
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 5
% 0.20/0.37  # Processed clauses                    : 14
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 14
% 0.20/0.38  # Other redundant clauses eliminated   : 1
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 1
% 0.20/0.38  # Generated clauses                    : 8
% 0.20/0.38  # ...of the previous two non-trivial   : 6
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 7
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 1
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 7
% 0.20/0.38  #    Positive orientable unit clauses  : 4
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 2
% 0.20/0.38  # Current number of unprocessed clauses: 0
% 0.20/0.38  # ...number of literals in the above   : 0
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 6
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.38  # Unit Clause-clause subsumption calls : 0
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 255
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.025 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.029 s
% 0.20/0.38  # Maximum resident set size: 1548 pages
%------------------------------------------------------------------------------
