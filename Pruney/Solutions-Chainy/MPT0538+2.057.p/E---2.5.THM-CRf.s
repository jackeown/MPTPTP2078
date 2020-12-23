%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:25 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   22 (  25 expanded)
%              Number of clauses        :   10 (  11 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  29 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t124_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t138_relat_1,conjecture,(
    ! [X1] : k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(c_0_6,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | k8_relat_1(X7,X8) = k3_xboole_0(X8,k2_zfmisc_1(k1_relat_1(X8),X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).

fof(c_0_7,plain,(
    ! [X3,X4] : k4_xboole_0(X3,k4_xboole_0(X3,X4)) = k3_xboole_0(X3,X4) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_8,plain,(
    ! [X6] : v1_relat_1(k6_relat_1(X6)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] : k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t138_relat_1])).

cnf(c_0_10,plain,
    ( k8_relat_1(X2,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

fof(c_0_14,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_15,negated_conjecture,(
    k8_relat_1(esk1_0,k1_xboole_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_16,plain,
    ( k8_relat_1(X2,X1) = k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k8_relat_1(esk1_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.09/0.30  % Computer   : n022.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % WCLimit    : 600
% 0.09/0.30  % DateTime   : Tue Dec  1 19:09:55 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.30  # Version: 2.5pre002
% 0.09/0.30  # No SInE strategy applied
% 0.09/0.30  # Trying AutoSched0 for 299 seconds
% 0.14/0.32  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S070I
% 0.14/0.32  # and selection function SelectVGNonCR.
% 0.14/0.32  #
% 0.14/0.32  # Preprocessing time       : 0.021 s
% 0.14/0.32  # Presaturation interreduction done
% 0.14/0.32  
% 0.14/0.32  # Proof found!
% 0.14/0.32  # SZS status Theorem
% 0.14/0.32  # SZS output start CNFRefutation
% 0.14/0.32  fof(t124_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k3_xboole_0(X2,k2_zfmisc_1(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 0.14/0.32  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.14/0.32  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.14/0.32  fof(t138_relat_1, conjecture, ![X1]:k8_relat_1(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 0.14/0.32  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.14/0.32  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.14/0.32  fof(c_0_6, plain, ![X7, X8]:(~v1_relat_1(X8)|k8_relat_1(X7,X8)=k3_xboole_0(X8,k2_zfmisc_1(k1_relat_1(X8),X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t124_relat_1])])).
% 0.14/0.32  fof(c_0_7, plain, ![X3, X4]:k4_xboole_0(X3,k4_xboole_0(X3,X4))=k3_xboole_0(X3,X4), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.14/0.32  fof(c_0_8, plain, ![X6]:v1_relat_1(k6_relat_1(X6)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.14/0.32  fof(c_0_9, negated_conjecture, ~(![X1]:k8_relat_1(X1,k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t138_relat_1])).
% 0.14/0.32  cnf(c_0_10, plain, (k8_relat_1(X2,X1)=k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.32  cnf(c_0_11, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.32  cnf(c_0_12, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.32  cnf(c_0_13, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.14/0.32  fof(c_0_14, plain, ![X5]:k4_xboole_0(k1_xboole_0,X5)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.14/0.32  fof(c_0_15, negated_conjecture, k8_relat_1(esk1_0,k1_xboole_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.14/0.32  cnf(c_0_16, plain, (k8_relat_1(X2,X1)=k4_xboole_0(X1,k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.14/0.32  cnf(c_0_17, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.32  cnf(c_0_18, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.32  cnf(c_0_19, negated_conjecture, (k8_relat_1(esk1_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.32  cnf(c_0_20, plain, (k8_relat_1(X1,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_18])).
% 0.14/0.32  cnf(c_0_21, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20])]), ['proof']).
% 0.14/0.32  # SZS output end CNFRefutation
% 0.14/0.32  # Proof object total steps             : 22
% 0.14/0.32  # Proof object clause steps            : 10
% 0.14/0.32  # Proof object formula steps           : 12
% 0.14/0.32  # Proof object conjectures             : 5
% 0.14/0.32  # Proof object clause conjectures      : 2
% 0.14/0.32  # Proof object formula conjectures     : 3
% 0.14/0.32  # Proof object initial clauses used    : 6
% 0.14/0.32  # Proof object initial formulas used   : 6
% 0.14/0.32  # Proof object generating inferences   : 2
% 0.14/0.32  # Proof object simplifying inferences  : 5
% 0.14/0.32  # Training examples: 0 positive, 0 negative
% 0.14/0.32  # Parsed axioms                        : 6
% 0.14/0.32  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.32  # Initial clauses                      : 6
% 0.14/0.32  # Removed in clause preprocessing      : 1
% 0.14/0.32  # Initial clauses in saturation        : 5
% 0.14/0.32  # Processed clauses                    : 12
% 0.14/0.32  # ...of these trivial                  : 0
% 0.14/0.32  # ...subsumed                          : 0
% 0.14/0.32  # ...remaining for further processing  : 12
% 0.14/0.32  # Other redundant clauses eliminated   : 0
% 0.14/0.32  # Clauses deleted for lack of memory   : 0
% 0.14/0.32  # Backward-subsumed                    : 0
% 0.14/0.32  # Backward-rewritten                   : 1
% 0.14/0.32  # Generated clauses                    : 3
% 0.14/0.32  # ...of the previous two non-trivial   : 3
% 0.14/0.32  # Contextual simplify-reflections      : 0
% 0.14/0.32  # Paramodulations                      : 3
% 0.14/0.32  # Factorizations                       : 0
% 0.14/0.32  # Equation resolutions                 : 0
% 0.14/0.32  # Propositional unsat checks           : 0
% 0.14/0.32  #    Propositional check models        : 0
% 0.14/0.32  #    Propositional check unsatisfiable : 0
% 0.14/0.32  #    Propositional clauses             : 0
% 0.14/0.32  #    Propositional clauses after purity: 0
% 0.14/0.32  #    Propositional unsat core size     : 0
% 0.14/0.32  #    Propositional preprocessing time  : 0.000
% 0.14/0.32  #    Propositional encoding time       : 0.000
% 0.14/0.32  #    Propositional solver time         : 0.000
% 0.14/0.32  #    Success case prop preproc time    : 0.000
% 0.14/0.32  #    Success case prop encoding time   : 0.000
% 0.14/0.32  #    Success case prop solver time     : 0.000
% 0.14/0.32  # Current number of processed clauses  : 6
% 0.14/0.32  #    Positive orientable unit clauses  : 5
% 0.14/0.32  #    Positive unorientable unit clauses: 0
% 0.14/0.32  #    Negative unit clauses             : 0
% 0.14/0.32  #    Non-unit-clauses                  : 1
% 0.14/0.32  # Current number of unprocessed clauses: 1
% 0.14/0.32  # ...number of literals in the above   : 1
% 0.14/0.32  # Current number of archived formulas  : 0
% 0.14/0.32  # Current number of archived clauses   : 7
% 0.14/0.32  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.32  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.32  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.32  # Unit Clause-clause subsumption calls : 0
% 0.14/0.32  # Rewrite failures with RHS unbound    : 0
% 0.14/0.32  # BW rewrite match attempts            : 1
% 0.14/0.32  # BW rewrite match successes           : 1
% 0.14/0.32  # Condensation attempts                : 0
% 0.14/0.32  # Condensation successes               : 0
% 0.14/0.32  # Termbank termtop insertions          : 291
% 0.14/0.32  
% 0.14/0.32  # -------------------------------------------------
% 0.14/0.32  # User time                : 0.020 s
% 0.14/0.32  # System time              : 0.004 s
% 0.14/0.32  # Total time               : 0.024 s
% 0.14/0.32  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
