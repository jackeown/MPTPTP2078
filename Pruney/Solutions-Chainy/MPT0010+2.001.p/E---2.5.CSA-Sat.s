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
% DateTime   : Thu Dec  3 10:31:45 EST 2020

% Result     : CounterSatisfiable 0.18s
% Output     : Saturation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   27 (  58 expanded)
%              Number of clauses        :   19 (  27 expanded)
%              Number of leaves         :    4 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 ( 157 expanded)
%              Number of equality atoms :    4 (   7 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_xboole_1,conjecture,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( r1_tarski(X1,k1_xboole_0)
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t3_xboole_1])).

fof(c_0_5,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_6,negated_conjecture,
    ( r1_tarski(esk3_0,k1_xboole_0)
    & esk3_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( r1_tarski(esk3_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_12,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | r2_hidden(esk2_2(esk3_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_15]),
    [final]).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_11]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),X1)
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_14]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_19])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_20]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_14]),
    [final]).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_11]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:25:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.18/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.026 s
% 0.18/0.36  
% 0.18/0.36  # No proof found!
% 0.18/0.36  # SZS status CounterSatisfiable
% 0.18/0.36  # SZS output start Saturation
% 0.18/0.36  fof(t3_xboole_1, conjecture, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.18/0.36  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.36  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.18/0.36  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.36  fof(c_0_4, negated_conjecture, ~(![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t3_xboole_1])).
% 0.18/0.36  fof(c_0_5, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.37  fof(c_0_6, negated_conjecture, (r1_tarski(esk3_0,k1_xboole_0)&esk3_0!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.18/0.37  cnf(c_0_7, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.18/0.37  cnf(c_0_8, negated_conjecture, (r1_tarski(esk3_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.37  fof(c_0_9, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.18/0.37  cnf(c_0_10, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.18/0.37  cnf(c_0_11, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.18/0.37  cnf(c_0_12, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.37  cnf(c_0_13, negated_conjecture, (r1_tarski(esk3_0,X1)|r2_hidden(esk2_2(esk3_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.18/0.37  cnf(c_0_14, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0]), ['final']).
% 0.18/0.37  cnf(c_0_15, negated_conjecture, (r1_tarski(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])]), ['final']).
% 0.18/0.37  cnf(c_0_16, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_7, c_0_15]), ['final']).
% 0.18/0.37  cnf(c_0_17, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.18/0.37  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_12, c_0_11]), ['final']).
% 0.18/0.37  cnf(c_0_19, negated_conjecture, (r2_hidden(esk1_1(esk3_0),X1)|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.37  cnf(c_0_20, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_21, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_12, c_0_19])).
% 0.18/0.37  cnf(c_0_22, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.18/0.37  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_7, c_0_20]), ['final']).
% 0.18/0.37  cnf(c_0_24, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.18/0.37  cnf(c_0_25, negated_conjecture, (v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_14]), ['final']).
% 0.18/0.37  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_22, c_0_11]), ['final']).
% 0.18/0.37  # SZS output end Saturation
% 0.18/0.37  # Proof object total steps             : 27
% 0.18/0.37  # Proof object clause steps            : 19
% 0.18/0.37  # Proof object formula steps           : 8
% 0.18/0.37  # Proof object conjectures             : 12
% 0.18/0.37  # Proof object clause conjectures      : 9
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 8
% 0.18/0.37  # Proof object initial formulas used   : 4
% 0.18/0.37  # Proof object generating inferences   : 11
% 0.18/0.37  # Proof object simplifying inferences  : 2
% 0.18/0.37  # Parsed axioms                        : 4
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 8
% 0.18/0.37  # Removed in clause preprocessing      : 0
% 0.18/0.37  # Initial clauses in saturation        : 8
% 0.18/0.37  # Processed clauses                    : 21
% 0.18/0.37  # ...of these trivial                  : 0
% 0.18/0.37  # ...subsumed                          : 2
% 0.18/0.37  # ...remaining for further processing  : 19
% 0.18/0.37  # Other redundant clauses eliminated   : 0
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 1
% 0.18/0.37  # Backward-rewritten                   : 4
% 0.18/0.37  # Generated clauses                    : 22
% 0.18/0.37  # ...of the previous two non-trivial   : 15
% 0.18/0.37  # Contextual simplify-reflections      : 0
% 0.18/0.37  # Paramodulations                      : 22
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 0
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 14
% 0.18/0.37  #    Positive orientable unit clauses  : 5
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 1
% 0.18/0.37  #    Non-unit-clauses                  : 8
% 0.18/0.37  # Current number of unprocessed clauses: 0
% 0.18/0.37  # ...number of literals in the above   : 0
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 5
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 9
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 9
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.18/0.37  # Unit Clause-clause subsumption calls : 3
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 6
% 0.18/0.37  # BW rewrite match successes           : 3
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 605
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.027 s
% 0.18/0.37  # System time              : 0.003 s
% 0.18/0.37  # Total time               : 0.030 s
% 0.18/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
