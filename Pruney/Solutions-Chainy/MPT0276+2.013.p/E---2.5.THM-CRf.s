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
% DateTime   : Thu Dec  3 10:43:05 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   21 (  39 expanded)
%              Number of clauses        :   12 (  15 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :   57 ( 102 expanded)
%              Number of equality atoms :   45 (  90 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t74_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k4_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X2)
        & k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(t42_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k4_xboole_0(k2_tarski(X1,X2),X3) != k1_xboole_0
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X1)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k1_tarski(X2)
          & k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t74_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X7,X8,X9] :
      ( ( ~ r1_tarski(X7,k2_tarski(X8,X9))
        | X7 = k1_xboole_0
        | X7 = k1_tarski(X8)
        | X7 = k1_tarski(X9)
        | X7 = k2_tarski(X8,X9) )
      & ( X7 != k1_xboole_0
        | r1_tarski(X7,k2_tarski(X8,X9)) )
      & ( X7 != k1_tarski(X8)
        | r1_tarski(X7,k2_tarski(X8,X9)) )
      & ( X7 != k1_tarski(X9)
        | r1_tarski(X7,k2_tarski(X8,X9)) )
      & ( X7 != k2_tarski(X8,X9)
        | r1_tarski(X7,k2_tarski(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t42_zfmisc_1])])])).

fof(c_0_6,plain,(
    ! [X6] : k2_tarski(X6,X6) = k1_tarski(X6) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_7,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_xboole_0
    & k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0)
    & k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk2_0)
    & k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X4,X5),X4) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_11,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_tarski(X3,X3)
    | X1 = k2_tarski(X2,X3)
    | X1 = k2_tarski(X2,X2)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8,c_0_9]),c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_11,c_0_9])).

cnf(c_0_16,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X1)
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X2,X2)
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:10:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.14/0.37  # and selection function SelectDiffNegLit.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.026 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t74_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X1))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X2))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_zfmisc_1)).
% 0.14/0.37  fof(t42_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_zfmisc_1)).
% 0.14/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.37  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.14/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:~((((k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_xboole_0&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X1))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k1_tarski(X2))&k4_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t74_zfmisc_1])).
% 0.14/0.37  fof(c_0_5, plain, ![X7, X8, X9]:((~r1_tarski(X7,k2_tarski(X8,X9))|(X7=k1_xboole_0|X7=k1_tarski(X8)|X7=k1_tarski(X9)|X7=k2_tarski(X8,X9)))&((((X7!=k1_xboole_0|r1_tarski(X7,k2_tarski(X8,X9)))&(X7!=k1_tarski(X8)|r1_tarski(X7,k2_tarski(X8,X9))))&(X7!=k1_tarski(X9)|r1_tarski(X7,k2_tarski(X8,X9))))&(X7!=k2_tarski(X8,X9)|r1_tarski(X7,k2_tarski(X8,X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t42_zfmisc_1])])])).
% 0.14/0.37  fof(c_0_6, plain, ![X6]:k2_tarski(X6,X6)=k1_tarski(X6), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.37  fof(c_0_7, negated_conjecture, (((k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)!=k1_xboole_0&k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)!=k1_tarski(esk1_0))&k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)!=k1_tarski(esk2_0))&k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)!=k2_tarski(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.14/0.37  cnf(c_0_8, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k2_tarski(X2,X3)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.37  cnf(c_0_9, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  fof(c_0_10, plain, ![X4, X5]:r1_tarski(k4_xboole_0(X4,X5),X4), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.14/0.37  cnf(c_0_11, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)!=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_12, plain, (X1=k1_xboole_0|X1=k2_tarski(X3,X3)|X1=k2_tarski(X2,X3)|X1=k2_tarski(X2,X2)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8, c_0_9]), c_0_9])).
% 0.14/0.37  cnf(c_0_13, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_14, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_15, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)!=k2_tarski(esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_11, c_0_9])).
% 0.14/0.37  cnf(c_0_16, plain, (k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X1)|k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)|k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X2,X2)|k4_xboole_0(k2_tarski(X1,X2),X3)=k1_xboole_0), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.37  cnf(c_0_17, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)!=k2_tarski(esk1_0,esk1_0)), inference(rw,[status(thm)],[c_0_14, c_0_9])).
% 0.14/0.37  cnf(c_0_18, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)!=k2_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_19, negated_conjecture, (k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 21
% 0.14/0.37  # Proof object clause steps            : 12
% 0.14/0.37  # Proof object formula steps           : 9
% 0.14/0.37  # Proof object conjectures             : 10
% 0.14/0.37  # Proof object clause conjectures      : 7
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 7
% 0.14/0.37  # Proof object initial formulas used   : 4
% 0.14/0.37  # Proof object generating inferences   : 2
% 0.14/0.37  # Proof object simplifying inferences  : 7
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 4
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 11
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 10
% 0.14/0.38  # Processed clauses                    : 25
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 25
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 45
% 0.14/0.38  # ...of the previous two non-trivial   : 29
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 32
% 0.14/0.38  # Factorizations                       : 9
% 0.14/0.38  # Equation resolutions                 : 4
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 15
% 0.14/0.38  #    Positive orientable unit clauses  : 5
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 4
% 0.14/0.38  #    Non-unit-clauses                  : 6
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 11
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 12
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 12
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.38  # Unit Clause-clause subsumption calls : 0
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 3
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1220
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.027 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.030 s
% 0.14/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
