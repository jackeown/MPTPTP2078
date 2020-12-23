%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:47 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   23 (  38 expanded)
%              Number of clauses        :   14 (  16 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 ( 101 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X1,X3)
          & r1_xboole_0(X2,X3) )
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t67_xboole_1])).

fof(c_0_5,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_6,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r1_tarski(esk1_0,esk3_0)
    & r1_xboole_0(esk2_0,esk3_0)
    & esk1_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_8,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r1_tarski(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_16,plain,(
    ! [X9] :
      ( ( r1_xboole_0(X9,X9)
        | X9 != k1_xboole_0 )
      & ( X9 = k1_xboole_0
        | ~ r1_xboole_0(X9,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(esk1_0,X1)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_15])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:28:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_____0021_10gd3
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.026 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t67_xboole_1, conjecture, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 0.12/0.37  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.12/0.37  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.12/0.37  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.12/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t67_xboole_1])).
% 0.12/0.37  fof(c_0_5, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_xboole_0(X7,X8)|r1_xboole_0(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.12/0.37  fof(c_0_6, negated_conjecture, (((r1_tarski(esk1_0,esk2_0)&r1_tarski(esk1_0,esk3_0))&r1_xboole_0(esk2_0,esk3_0))&esk1_0!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.12/0.37  fof(c_0_7, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.12/0.37  cnf(c_0_8, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_9, negated_conjecture, (r1_tarski(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_10, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (r1_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (r1_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.37  fof(c_0_16, plain, ![X9]:((r1_xboole_0(X9,X9)|X9!=k1_xboole_0)&(X9=k1_xboole_0|~r1_xboole_0(X9,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (r1_xboole_0(esk1_0,X1)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_8, c_0_14])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (r1_xboole_0(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_10, c_0_15])).
% 0.12/0.37  cnf(c_0_19, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (r1_xboole_0(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 23
% 0.12/0.37  # Proof object clause steps            : 14
% 0.12/0.37  # Proof object formula steps           : 9
% 0.12/0.37  # Proof object conjectures             : 14
% 0.12/0.37  # Proof object clause conjectures      : 11
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 7
% 0.12/0.37  # Proof object initial formulas used   : 4
% 0.12/0.37  # Proof object generating inferences   : 7
% 0.12/0.37  # Proof object simplifying inferences  : 1
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 4
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 8
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 8
% 0.12/0.37  # Processed clauses                    : 16
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 16
% 0.12/0.37  # Other redundant clauses eliminated   : 1
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 14
% 0.12/0.37  # ...of the previous two non-trivial   : 9
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 13
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 1
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 15
% 0.12/0.37  #    Positive orientable unit clauses  : 9
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 5
% 0.12/0.37  # Current number of unprocessed clauses: 1
% 0.12/0.37  # ...number of literals in the above   : 1
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 0
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 6
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 6
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 0
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 502
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.025 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.030 s
% 0.12/0.37  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
