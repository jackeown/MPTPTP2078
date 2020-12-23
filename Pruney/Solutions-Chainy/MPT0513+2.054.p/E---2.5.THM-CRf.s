%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:00 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  51 expanded)
%              Number of clauses        :   13 (  25 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  68 expanded)
%              Number of equality atoms :   21 (  39 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t102_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(t111_relat_1,conjecture,(
    ! [X1] : k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(c_0_7,plain,(
    ! [X5] : v1_relat_1(k6_relat_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_8,plain,(
    ! [X9] :
      ( k1_relat_1(k6_relat_1(X9)) = X9
      & k2_relat_1(k6_relat_1(X9)) = X9 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_9,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_relat_1(X8)
      | ~ r1_tarski(X6,X7)
      | k7_relat_1(k7_relat_1(X8,X6),X7) = k7_relat_1(X8,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t102_relat_1])])).

fof(c_0_10,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_11,plain,(
    ! [X10] :
      ( ~ v1_relat_1(X10)
      | k7_relat_1(X10,k1_relat_1(X10)) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_12,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_14,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] : k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t111_relat_1])).

cnf(c_0_16,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

fof(c_0_21,negated_conjecture,(
    k7_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_22,plain,
    ( k7_relat_1(k7_relat_1(X1,k1_xboole_0),X2) = k7_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_23]),c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:29:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.22/0.38  # and selection function SelectDiffNegLit.
% 0.22/0.38  #
% 0.22/0.38  # Preprocessing time       : 0.026 s
% 0.22/0.38  # Presaturation interreduction done
% 0.22/0.38  
% 0.22/0.38  # Proof found!
% 0.22/0.38  # SZS status Theorem
% 0.22/0.38  # SZS output start CNFRefutation
% 0.22/0.38  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.22/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.22/0.38  fof(t102_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_relat_1)).
% 0.22/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.22/0.38  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.22/0.38  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.22/0.38  fof(t111_relat_1, conjecture, ![X1]:k7_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 0.22/0.38  fof(c_0_7, plain, ![X5]:v1_relat_1(k6_relat_1(X5)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.22/0.38  fof(c_0_8, plain, ![X9]:(k1_relat_1(k6_relat_1(X9))=X9&k2_relat_1(k6_relat_1(X9))=X9), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.22/0.38  fof(c_0_9, plain, ![X6, X7, X8]:(~v1_relat_1(X8)|(~r1_tarski(X6,X7)|k7_relat_1(k7_relat_1(X8,X6),X7)=k7_relat_1(X8,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t102_relat_1])])).
% 0.22/0.38  fof(c_0_10, plain, ![X4]:r1_tarski(k1_xboole_0,X4), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.22/0.38  fof(c_0_11, plain, ![X10]:(~v1_relat_1(X10)|k7_relat_1(X10,k1_relat_1(X10))=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.22/0.38  cnf(c_0_12, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.22/0.38  cnf(c_0_13, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.22/0.38  cnf(c_0_14, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.22/0.38  fof(c_0_15, negated_conjecture, ~(![X1]:k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t111_relat_1])).
% 0.22/0.38  cnf(c_0_16, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.38  cnf(c_0_17, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.22/0.38  cnf(c_0_18, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.22/0.38  cnf(c_0_19, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.22/0.38  cnf(c_0_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_14, c_0_13])).
% 0.22/0.38  fof(c_0_21, negated_conjecture, k7_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.22/0.38  cnf(c_0_22, plain, (k7_relat_1(k7_relat_1(X1,k1_xboole_0),X2)=k7_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.22/0.38  cnf(c_0_23, plain, (k7_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.22/0.38  cnf(c_0_24, negated_conjecture, (k7_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.22/0.38  cnf(c_0_25, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_23]), c_0_23])).
% 0.22/0.38  cnf(c_0_26, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25])]), ['proof']).
% 0.22/0.38  # SZS output end CNFRefutation
% 0.22/0.38  # Proof object total steps             : 27
% 0.22/0.38  # Proof object clause steps            : 13
% 0.22/0.38  # Proof object formula steps           : 14
% 0.22/0.38  # Proof object conjectures             : 5
% 0.22/0.38  # Proof object clause conjectures      : 2
% 0.22/0.38  # Proof object formula conjectures     : 3
% 0.22/0.38  # Proof object initial clauses used    : 7
% 0.22/0.38  # Proof object initial formulas used   : 7
% 0.22/0.38  # Proof object generating inferences   : 5
% 0.22/0.38  # Proof object simplifying inferences  : 5
% 0.22/0.38  # Training examples: 0 positive, 0 negative
% 0.22/0.38  # Parsed axioms                        : 7
% 0.22/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.38  # Initial clauses                      : 8
% 0.22/0.38  # Removed in clause preprocessing      : 0
% 0.22/0.38  # Initial clauses in saturation        : 8
% 0.22/0.38  # Processed clauses                    : 23
% 0.22/0.38  # ...of these trivial                  : 0
% 0.22/0.38  # ...subsumed                          : 0
% 0.22/0.38  # ...remaining for further processing  : 23
% 0.22/0.38  # Other redundant clauses eliminated   : 0
% 0.22/0.38  # Clauses deleted for lack of memory   : 0
% 0.22/0.38  # Backward-subsumed                    : 0
% 0.22/0.38  # Backward-rewritten                   : 2
% 0.22/0.38  # Generated clauses                    : 9
% 0.22/0.38  # ...of the previous two non-trivial   : 8
% 0.22/0.38  # Contextual simplify-reflections      : 0
% 0.22/0.38  # Paramodulations                      : 9
% 0.22/0.38  # Factorizations                       : 0
% 0.22/0.38  # Equation resolutions                 : 0
% 0.22/0.38  # Propositional unsat checks           : 0
% 0.22/0.38  #    Propositional check models        : 0
% 0.22/0.38  #    Propositional check unsatisfiable : 0
% 0.22/0.38  #    Propositional clauses             : 0
% 0.22/0.38  #    Propositional clauses after purity: 0
% 0.22/0.38  #    Propositional unsat core size     : 0
% 0.22/0.38  #    Propositional preprocessing time  : 0.000
% 0.22/0.38  #    Propositional encoding time       : 0.000
% 0.22/0.38  #    Propositional solver time         : 0.000
% 0.22/0.38  #    Success case prop preproc time    : 0.000
% 0.22/0.38  #    Success case prop encoding time   : 0.000
% 0.22/0.38  #    Success case prop solver time     : 0.000
% 0.22/0.38  # Current number of processed clauses  : 13
% 0.22/0.38  #    Positive orientable unit clauses  : 10
% 0.22/0.38  #    Positive unorientable unit clauses: 0
% 0.22/0.38  #    Negative unit clauses             : 0
% 0.22/0.38  #    Non-unit-clauses                  : 3
% 0.22/0.38  # Current number of unprocessed clauses: 1
% 0.22/0.38  # ...number of literals in the above   : 1
% 0.22/0.38  # Current number of archived formulas  : 0
% 0.22/0.38  # Current number of archived clauses   : 10
% 0.22/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.22/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.22/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.22/0.38  # Unit Clause-clause subsumption calls : 1
% 0.22/0.38  # Rewrite failures with RHS unbound    : 0
% 0.22/0.38  # BW rewrite match attempts            : 2
% 0.22/0.38  # BW rewrite match successes           : 2
% 0.22/0.38  # Condensation attempts                : 0
% 0.22/0.38  # Condensation successes               : 0
% 0.22/0.38  # Termbank termtop insertions          : 449
% 0.22/0.38  
% 0.22/0.38  # -------------------------------------------------
% 0.22/0.38  # User time                : 0.024 s
% 0.22/0.38  # System time              : 0.005 s
% 0.22/0.38  # Total time               : 0.029 s
% 0.22/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
