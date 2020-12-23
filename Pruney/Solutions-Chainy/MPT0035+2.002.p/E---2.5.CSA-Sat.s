%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:57 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   15 (  45 expanded)
%              Number of clauses        :   10 (  19 expanded)
%              Number of leaves         :    2 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   55 ( 257 expanded)
%              Number of equality atoms :   17 (  65 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & ! [X4] :
            ( ( r1_tarski(X4,X2)
              & r1_tarski(X4,X3) )
           => r1_tarski(X4,X1) ) )
     => X1 = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

fof(t28_xboole_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_2,plain,(
    ! [X5,X6,X7] :
      ( ( r1_tarski(esk1_3(X5,X6,X7),X6)
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X5,X7)
        | X5 = k3_xboole_0(X6,X7) )
      & ( r1_tarski(esk1_3(X5,X6,X7),X7)
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X5,X7)
        | X5 = k3_xboole_0(X6,X7) )
      & ( ~ r1_tarski(esk1_3(X5,X6,X7),X5)
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X5,X7)
        | X5 = k3_xboole_0(X6,X7) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => k3_xboole_0(X1,X2) = X1 ) ),
    inference(assume_negation,[status(cth)],[t28_xboole_1])).

cnf(c_0_4,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(esk1_3(X1,X2,X3),X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_5,plain,
    ( r1_tarski(esk1_3(X1,X2,X3),X2)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

fof(c_0_6,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    & k3_xboole_0(esk2_0,esk3_0) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_4,c_0_5]),
    [final]).

cnf(c_0_8,plain,
    ( r1_tarski(esk1_3(X1,X2,X3),X3)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_9,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_11,plain,
    ( k3_xboole_0(esk1_3(X1,X2,X3),X2) = esk1_3(X1,X2,X3)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(esk1_3(X1,X2,X3),esk1_3(X1,X2,X3))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_5]),
    [final]).

cnf(c_0_12,plain,
    ( k3_xboole_0(esk1_3(X1,X2,X3),X3) = esk1_3(X1,X2,X3)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(esk1_3(X1,X2,X3),esk1_3(X1,X2,X3))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8]),
    [final]).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_4,c_0_8]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_9]),c_0_10]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:29:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.12/0.35  # and selection function SelectVGNonCR.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.021 s
% 0.12/0.35  # Presaturation interreduction done
% 0.12/0.35  
% 0.12/0.35  # No proof found!
% 0.12/0.35  # SZS status CounterSatisfiable
% 0.12/0.35  # SZS output start Saturation
% 0.12/0.35  fof(t20_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&![X4]:((r1_tarski(X4,X2)&r1_tarski(X4,X3))=>r1_tarski(X4,X1)))=>X1=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_xboole_1)).
% 0.12/0.35  fof(t28_xboole_1, conjecture, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.12/0.35  fof(c_0_2, plain, ![X5, X6, X7]:(((r1_tarski(esk1_3(X5,X6,X7),X6)|(~r1_tarski(X5,X6)|~r1_tarski(X5,X7))|X5=k3_xboole_0(X6,X7))&(r1_tarski(esk1_3(X5,X6,X7),X7)|(~r1_tarski(X5,X6)|~r1_tarski(X5,X7))|X5=k3_xboole_0(X6,X7)))&(~r1_tarski(esk1_3(X5,X6,X7),X5)|(~r1_tarski(X5,X6)|~r1_tarski(X5,X7))|X5=k3_xboole_0(X6,X7))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).
% 0.12/0.35  fof(c_0_3, negated_conjecture, ~(![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1)), inference(assume_negation,[status(cth)],[t28_xboole_1])).
% 0.12/0.35  cnf(c_0_4, plain, (X1=k3_xboole_0(X2,X3)|~r1_tarski(esk1_3(X1,X2,X3),X1)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.12/0.35  cnf(c_0_5, plain, (r1_tarski(esk1_3(X1,X2,X3),X2)|X1=k3_xboole_0(X2,X3)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.12/0.35  fof(c_0_6, negated_conjecture, (r1_tarski(esk2_0,esk3_0)&k3_xboole_0(esk2_0,esk3_0)!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.12/0.35  cnf(c_0_7, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)|~r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_4, c_0_5]), ['final']).
% 0.12/0.35  cnf(c_0_8, plain, (r1_tarski(esk1_3(X1,X2,X3),X3)|X1=k3_xboole_0(X2,X3)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.12/0.35  cnf(c_0_9, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.12/0.35  cnf(c_0_10, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.12/0.35  cnf(c_0_11, plain, (k3_xboole_0(esk1_3(X1,X2,X3),X2)=esk1_3(X1,X2,X3)|X1=k3_xboole_0(X2,X3)|~r1_tarski(esk1_3(X1,X2,X3),esk1_3(X1,X2,X3))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_7, c_0_5]), ['final']).
% 0.12/0.35  cnf(c_0_12, plain, (k3_xboole_0(esk1_3(X1,X2,X3),X3)=esk1_3(X1,X2,X3)|X1=k3_xboole_0(X2,X3)|~r1_tarski(esk1_3(X1,X2,X3),esk1_3(X1,X2,X3))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_7, c_0_8]), ['final']).
% 0.12/0.35  cnf(c_0_13, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_4, c_0_8]), ['final']).
% 0.12/0.35  cnf(c_0_14, negated_conjecture, (~r1_tarski(esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_9]), c_0_10]), ['final']).
% 0.12/0.35  # SZS output end Saturation
% 0.12/0.35  # Proof object total steps             : 15
% 0.12/0.35  # Proof object clause steps            : 10
% 0.12/0.35  # Proof object formula steps           : 5
% 0.12/0.35  # Proof object conjectures             : 6
% 0.12/0.35  # Proof object clause conjectures      : 3
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 5
% 0.12/0.35  # Proof object initial formulas used   : 2
% 0.12/0.35  # Proof object generating inferences   : 5
% 0.12/0.35  # Proof object simplifying inferences  : 1
% 0.12/0.35  # Parsed axioms                        : 2
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 5
% 0.12/0.35  # Removed in clause preprocessing      : 0
% 0.12/0.35  # Initial clauses in saturation        : 5
% 0.12/0.35  # Processed clauses                    : 15
% 0.12/0.35  # ...of these trivial                  : 0
% 0.12/0.35  # ...subsumed                          : 0
% 0.12/0.35  # ...remaining for further processing  : 15
% 0.12/0.35  # Other redundant clauses eliminated   : 0
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 0
% 0.12/0.35  # Backward-rewritten                   : 0
% 0.12/0.35  # Generated clauses                    : 5
% 0.12/0.35  # ...of the previous two non-trivial   : 5
% 0.12/0.35  # Contextual simplify-reflections      : 0
% 0.12/0.35  # Paramodulations                      : 5
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 0
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 10
% 0.12/0.35  #    Positive orientable unit clauses  : 1
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 2
% 0.12/0.35  #    Non-unit-clauses                  : 7
% 0.12/0.35  # Current number of unprocessed clauses: 0
% 0.12/0.35  # ...number of literals in the above   : 0
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 5
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 60
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 22
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.35  # Unit Clause-clause subsumption calls : 0
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 0
% 0.12/0.35  # BW rewrite match successes           : 0
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 486
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.020 s
% 0.12/0.35  # System time              : 0.004 s
% 0.12/0.35  # Total time               : 0.025 s
% 0.12/0.35  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
