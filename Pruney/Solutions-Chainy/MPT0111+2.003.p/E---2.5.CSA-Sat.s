%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:32 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   14 (  27 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    2 (   7 expanded)
%              Depth                    :    4
%              Number of atoms          :   50 ( 124 expanded)
%              Number of equality atoms :   11 (  29 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t104_xboole_1,conjecture,(
    ! [X1,X2] :
      ( ~ ( ~ r2_xboole_0(X1,X2)
          & X1 != X2
          & ~ r2_xboole_0(X2,X1) )
    <=> r3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ~ ( ~ r2_xboole_0(X1,X2)
            & X1 != X2
            & ~ r2_xboole_0(X2,X1) )
      <=> r3_xboole_0(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t104_xboole_1])).

fof(c_0_3,negated_conjecture,
    ( ( ~ r2_xboole_0(esk1_0,esk2_0)
      | ~ r3_xboole_0(esk1_0,esk2_0) )
    & ( esk1_0 != esk2_0
      | ~ r3_xboole_0(esk1_0,esk2_0) )
    & ( ~ r2_xboole_0(esk2_0,esk1_0)
      | ~ r3_xboole_0(esk1_0,esk2_0) )
    & ( r2_xboole_0(esk1_0,esk2_0)
      | esk1_0 = esk2_0
      | r2_xboole_0(esk2_0,esk1_0)
      | r3_xboole_0(esk1_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])).

fof(c_0_4,plain,(
    ! [X3,X4] :
      ( ( r1_tarski(X3,X4)
        | ~ r2_xboole_0(X3,X4) )
      & ( X3 != X4
        | ~ r2_xboole_0(X3,X4) )
      & ( ~ r1_tarski(X3,X4)
        | X3 = X4
        | r2_xboole_0(X3,X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_5,negated_conjecture,
    ( esk1_0 != esk2_0
    | ~ r3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_6,negated_conjecture,
    ( r2_xboole_0(esk1_0,esk2_0)
    | esk1_0 = esk2_0
    | r2_xboole_0(esk2_0,esk1_0)
    | r3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_7,plain,
    ( X1 != X2
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( r3_xboole_0(esk1_0,esk2_0)
    | r2_xboole_0(esk2_0,esk1_0)
    | r2_xboole_0(esk1_0,esk2_0)
    | ~ r3_xboole_0(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( ~ r2_xboole_0(esk2_0,esk1_0)
    | ~ r3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_xboole_0(esk1_0,esk2_0)
    | ~ r3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_13,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(er,[status(thm)],[c_0_7]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S057A
% 0.13/0.37  # and selection function SelectMin2Infpos.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # No proof found!
% 0.13/0.37  # SZS status CounterSatisfiable
% 0.13/0.37  # SZS output start Saturation
% 0.13/0.37  fof(t104_xboole_1, conjecture, ![X1, X2]:(~(((~(r2_xboole_0(X1,X2))&X1!=X2)&~(r2_xboole_0(X2,X1))))<=>r3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_xboole_1)).
% 0.13/0.37  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.13/0.37  fof(c_0_2, negated_conjecture, ~(![X1, X2]:(~(((~(r2_xboole_0(X1,X2))&X1!=X2)&~(r2_xboole_0(X2,X1))))<=>r3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t104_xboole_1])).
% 0.13/0.37  fof(c_0_3, negated_conjecture, ((((~r2_xboole_0(esk1_0,esk2_0)|~r3_xboole_0(esk1_0,esk2_0))&(esk1_0!=esk2_0|~r3_xboole_0(esk1_0,esk2_0)))&(~r2_xboole_0(esk2_0,esk1_0)|~r3_xboole_0(esk1_0,esk2_0)))&(r2_xboole_0(esk1_0,esk2_0)|esk1_0=esk2_0|r2_xboole_0(esk2_0,esk1_0)|r3_xboole_0(esk1_0,esk2_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])).
% 0.13/0.37  fof(c_0_4, plain, ![X3, X4]:(((r1_tarski(X3,X4)|~r2_xboole_0(X3,X4))&(X3!=X4|~r2_xboole_0(X3,X4)))&(~r1_tarski(X3,X4)|X3=X4|r2_xboole_0(X3,X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.13/0.37  cnf(c_0_5, negated_conjecture, (esk1_0!=esk2_0|~r3_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.13/0.37  cnf(c_0_6, negated_conjecture, (r2_xboole_0(esk1_0,esk2_0)|esk1_0=esk2_0|r2_xboole_0(esk2_0,esk1_0)|r3_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.13/0.37  cnf(c_0_7, plain, (X1!=X2|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_8, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_9, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (r3_xboole_0(esk1_0,esk2_0)|r2_xboole_0(esk2_0,esk1_0)|r2_xboole_0(esk1_0,esk2_0)|~r3_xboole_0(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_5, c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (~r2_xboole_0(esk2_0,esk1_0)|~r3_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (~r2_xboole_0(esk1_0,esk2_0)|~r3_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.13/0.37  cnf(c_0_13, plain, (~r2_xboole_0(X1,X1)), inference(er,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  # SZS output end Saturation
% 0.13/0.37  # Proof object total steps             : 14
% 0.13/0.37  # Proof object clause steps            : 9
% 0.13/0.37  # Proof object formula steps           : 5
% 0.13/0.37  # Proof object conjectures             : 8
% 0.13/0.37  # Proof object clause conjectures      : 5
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 7
% 0.13/0.37  # Proof object initial formulas used   : 2
% 0.13/0.37  # Proof object generating inferences   : 1
% 0.13/0.37  # Proof object simplifying inferences  : 1
% 0.13/0.37  # Parsed axioms                        : 2
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 7
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 7
% 0.13/0.37  # Processed clauses                    : 18
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 2
% 0.13/0.37  # ...remaining for further processing  : 16
% 0.13/0.37  # Other redundant clauses eliminated   : 1
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 4
% 0.13/0.37  # ...of the previous two non-trivial   : 4
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 3
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 1
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 8
% 0.13/0.37  #    Positive orientable unit clauses  : 0
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 7
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 7
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 8
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 8
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 2
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 441
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.025 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.029 s
% 0.13/0.37  # Maximum resident set size: 1552 pages
%------------------------------------------------------------------------------
