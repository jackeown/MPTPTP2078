%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:00 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t111_relat_1,conjecture,(
    ! [X1] : k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(c_0_5,plain,(
    ! [X4] : v1_relat_1(k6_relat_1(X4)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] : k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t111_relat_1])).

fof(c_0_7,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | X3 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_8,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X6)
      | r1_tarski(k7_relat_1(X6,X5),X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_9,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

fof(c_0_11,negated_conjecture,(
    k7_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_12,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:15:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.042 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.39  fof(t111_relat_1, conjecture, ![X1]:k7_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 0.13/0.39  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.13/0.39  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.13/0.39  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.13/0.39  fof(c_0_5, plain, ![X4]:v1_relat_1(k6_relat_1(X4)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.39  fof(c_0_6, negated_conjecture, ~(![X1]:k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t111_relat_1])).
% 0.13/0.39  fof(c_0_7, plain, ![X3]:(~r1_tarski(X3,k1_xboole_0)|X3=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.13/0.39  fof(c_0_8, plain, ![X5, X6]:(~v1_relat_1(X6)|r1_tarski(k7_relat_1(X6,X5),X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.13/0.39  cnf(c_0_9, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_10, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.13/0.39  fof(c_0_11, negated_conjecture, k7_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.39  cnf(c_0_12, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_13, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_14, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.39  cnf(c_0_15, negated_conjecture, (k7_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_16, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.13/0.39  cnf(c_0_17, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 18
% 0.13/0.39  # Proof object clause steps            : 8
% 0.13/0.39  # Proof object formula steps           : 10
% 0.13/0.39  # Proof object conjectures             : 5
% 0.13/0.39  # Proof object clause conjectures      : 2
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 5
% 0.13/0.39  # Proof object initial formulas used   : 5
% 0.13/0.39  # Proof object generating inferences   : 2
% 0.13/0.39  # Proof object simplifying inferences  : 4
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 5
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 5
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 5
% 0.13/0.39  # Processed clauses                    : 12
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 0
% 0.13/0.39  # ...remaining for further processing  : 12
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 1
% 0.13/0.39  # Generated clauses                    : 3
% 0.13/0.39  # ...of the previous two non-trivial   : 2
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 3
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 6
% 0.13/0.39  #    Positive orientable unit clauses  : 4
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 2
% 0.13/0.39  # Current number of unprocessed clauses: 0
% 0.13/0.39  # ...number of literals in the above   : 0
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 6
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.39  # Unit Clause-clause subsumption calls : 0
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 1
% 0.13/0.39  # BW rewrite match successes           : 1
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 248
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.043 s
% 0.13/0.39  # System time              : 0.002 s
% 0.13/0.39  # Total time               : 0.045 s
% 0.13/0.39  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
