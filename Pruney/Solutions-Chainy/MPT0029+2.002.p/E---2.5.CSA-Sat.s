%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:53 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   17 (  44 expanded)
%              Number of clauses        :   10 (  19 expanded)
%              Number of leaves         :    3 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   55 ( 251 expanded)
%              Number of equality atoms :   18 (  63 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t22_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(c_0_3,plain,(
    ! [X5,X6,X7] :
      ( ( r1_tarski(X5,esk1_3(X5,X6,X7))
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X7,X6)
        | X6 = k2_xboole_0(X5,X7) )
      & ( r1_tarski(X7,esk1_3(X5,X6,X7))
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X7,X6)
        | X6 = k2_xboole_0(X5,X7) )
      & ( ~ r1_tarski(X6,esk1_3(X5,X6,X7))
        | ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X7,X6)
        | X6 = k2_xboole_0(X5,X7) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).

cnf(c_0_4,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk1_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_5,plain,
    ( r1_tarski(X1,esk1_3(X1,X2,X3))
    | X2 = k2_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

fof(c_0_6,plain,(
    ! [X9,X10] : r1_tarski(k3_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(assume_negation,[status(cth)],[t22_xboole_1])).

cnf(c_0_8,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_4,c_0_5]),
    [final]).

cnf(c_0_9,plain,
    ( r1_tarski(X1,esk1_3(X2,X3,X1))
    | X3 = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_10,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

fof(c_0_11,negated_conjecture,(
    k2_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( k2_xboole_0(esk1_3(X1,X2,X3),X3) = esk1_3(X1,X2,X3)
    | X2 = k2_xboole_0(X1,X3)
    | ~ r1_tarski(esk1_3(X1,X2,X3),esk1_3(X1,X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9]),
    [final]).

cnf(c_0_13,plain,
    ( k2_xboole_0(esk1_3(X1,X2,X3),X1) = esk1_3(X1,X2,X3)
    | X2 = k2_xboole_0(X1,X3)
    | ~ r1_tarski(esk1_3(X1,X2,X3),esk1_3(X1,X2,X3))
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_5]),
    [final]).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_4,c_0_9]),
    [final]).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_10]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.19/0.37  # and selection function SelectVGNonCR.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.026 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # No proof found!
% 0.19/0.37  # SZS status CounterSatisfiable
% 0.19/0.37  # SZS output start Saturation
% 0.19/0.37  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_xboole_1)).
% 0.19/0.37  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.19/0.37  fof(t22_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.19/0.37  fof(c_0_3, plain, ![X5, X6, X7]:(((r1_tarski(X5,esk1_3(X5,X6,X7))|(~r1_tarski(X5,X6)|~r1_tarski(X7,X6))|X6=k2_xboole_0(X5,X7))&(r1_tarski(X7,esk1_3(X5,X6,X7))|(~r1_tarski(X5,X6)|~r1_tarski(X7,X6))|X6=k2_xboole_0(X5,X7)))&(~r1_tarski(X6,esk1_3(X5,X6,X7))|(~r1_tarski(X5,X6)|~r1_tarski(X7,X6))|X6=k2_xboole_0(X5,X7))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 0.19/0.37  cnf(c_0_4, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk1_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.19/0.37  cnf(c_0_5, plain, (r1_tarski(X1,esk1_3(X1,X2,X3))|X2=k2_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.19/0.37  fof(c_0_6, plain, ![X9, X10]:r1_tarski(k3_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.19/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(assume_negation,[status(cth)],[t22_xboole_1])).
% 0.19/0.37  cnf(c_0_8, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)|~r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_4, c_0_5]), ['final']).
% 0.19/0.37  cnf(c_0_9, plain, (r1_tarski(X1,esk1_3(X2,X3,X1))|X3=k2_xboole_0(X2,X1)|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.19/0.37  cnf(c_0_10, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.37  fof(c_0_11, negated_conjecture, k2_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))!=esk2_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.37  cnf(c_0_12, plain, (k2_xboole_0(esk1_3(X1,X2,X3),X3)=esk1_3(X1,X2,X3)|X2=k2_xboole_0(X1,X3)|~r1_tarski(esk1_3(X1,X2,X3),esk1_3(X1,X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_8, c_0_9]), ['final']).
% 0.19/0.37  cnf(c_0_13, plain, (k2_xboole_0(esk1_3(X1,X2,X3),X1)=esk1_3(X1,X2,X3)|X2=k2_xboole_0(X1,X3)|~r1_tarski(esk1_3(X1,X2,X3),esk1_3(X1,X2,X3))|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_8, c_0_5]), ['final']).
% 0.19/0.37  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X2,X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_4, c_0_9]), ['final']).
% 0.19/0.37  cnf(c_0_15, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_8, c_0_10]), ['final']).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (k2_xboole_0(esk2_0,k3_xboole_0(esk2_0,esk3_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.19/0.37  # SZS output end Saturation
% 0.19/0.37  # Proof object total steps             : 17
% 0.19/0.37  # Proof object clause steps            : 10
% 0.19/0.37  # Proof object formula steps           : 7
% 0.19/0.37  # Proof object conjectures             : 4
% 0.19/0.37  # Proof object clause conjectures      : 1
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 5
% 0.19/0.37  # Proof object initial formulas used   : 3
% 0.19/0.37  # Proof object generating inferences   : 5
% 0.19/0.37  # Proof object simplifying inferences  : 0
% 0.19/0.37  # Parsed axioms                        : 3
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 5
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 5
% 0.19/0.37  # Processed clauses                    : 15
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 15
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 5
% 0.19/0.37  # ...of the previous two non-trivial   : 5
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 5
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 10
% 0.19/0.37  #    Positive orientable unit clauses  : 1
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 8
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 5
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 60
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 22
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 505
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.026 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.030 s
% 0.19/0.37  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
