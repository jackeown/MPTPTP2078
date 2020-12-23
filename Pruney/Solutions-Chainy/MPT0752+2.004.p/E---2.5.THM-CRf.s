%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  41 expanded)
%              Number of clauses        :   12 (  18 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  67 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_ordinal1,conjecture,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X1)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

fof(t206_relat_1,axiom,(
    ! [X1,X2] :
      ( v4_relat_1(k1_xboole_0,X1)
      & v5_relat_1(k1_xboole_0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t206_relat_1)).

fof(fc13_subset_1,axiom,(
    ! [X1] : v1_xboole_0(k1_subset_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(cc4_ordinal1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v5_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_ordinal1)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X1)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    inference(assume_negation,[status(cth)],[t45_ordinal1])).

fof(c_0_8,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,esk1_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X6,X7] :
      ( v4_relat_1(k1_xboole_0,X6)
      & v5_relat_1(k1_xboole_0,X7) ) ),
    inference(variable_rename,[status(thm)],[t206_relat_1])).

fof(c_0_10,plain,(
    ! [X4] : v1_xboole_0(k1_subset_1(X4)) ),
    inference(variable_rename,[status(thm)],[fc13_subset_1])).

fof(c_0_11,plain,(
    ! [X3] : k1_subset_1(X3) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_12,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,esk1_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | v5_ordinal1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_ordinal1])])).

cnf(c_0_15,plain,
    ( v1_xboole_0(k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_13])])).

cnf(c_0_18,plain,
    ( v5_ordinal1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | v1_funct_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_22,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | v1_relat_1(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_19])])).

cnf(c_0_25,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t45_ordinal1, conjecture, ![X1]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X1))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_ordinal1)).
% 0.20/0.38  fof(t206_relat_1, axiom, ![X1, X2]:(v4_relat_1(k1_xboole_0,X1)&v5_relat_1(k1_xboole_0,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t206_relat_1)).
% 0.20/0.38  fof(fc13_subset_1, axiom, ![X1]:v1_xboole_0(k1_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 0.20/0.38  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 0.20/0.38  fof(cc4_ordinal1, axiom, ![X1]:(v1_xboole_0(X1)=>v5_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_ordinal1)).
% 0.20/0.38  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.20/0.38  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.20/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:(((v1_relat_1(k1_xboole_0)&v5_relat_1(k1_xboole_0,X1))&v1_funct_1(k1_xboole_0))&v5_ordinal1(k1_xboole_0))), inference(assume_negation,[status(cth)],[t45_ordinal1])).
% 0.20/0.38  fof(c_0_8, negated_conjecture, (~v1_relat_1(k1_xboole_0)|~v5_relat_1(k1_xboole_0,esk1_0)|~v1_funct_1(k1_xboole_0)|~v5_ordinal1(k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.20/0.38  fof(c_0_9, plain, ![X6, X7]:(v4_relat_1(k1_xboole_0,X6)&v5_relat_1(k1_xboole_0,X7)), inference(variable_rename,[status(thm)],[t206_relat_1])).
% 0.20/0.38  fof(c_0_10, plain, ![X4]:v1_xboole_0(k1_subset_1(X4)), inference(variable_rename,[status(thm)],[fc13_subset_1])).
% 0.20/0.38  fof(c_0_11, plain, ![X3]:k1_subset_1(X3)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.20/0.38  cnf(c_0_12, negated_conjecture, (~v1_relat_1(k1_xboole_0)|~v5_relat_1(k1_xboole_0,esk1_0)|~v1_funct_1(k1_xboole_0)|~v5_ordinal1(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_13, plain, (v5_relat_1(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  fof(c_0_14, plain, ![X9]:(~v1_xboole_0(X9)|v5_ordinal1(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_ordinal1])])).
% 0.20/0.38  cnf(c_0_15, plain, (v1_xboole_0(k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_16, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (~v5_ordinal1(k1_xboole_0)|~v1_funct_1(k1_xboole_0)|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_13])])).
% 0.20/0.38  cnf(c_0_18, plain, (v5_ordinal1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_19, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.38  fof(c_0_20, plain, ![X8]:(~v1_xboole_0(X8)|v1_funct_1(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (~v1_funct_1(k1_xboole_0)|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.20/0.38  cnf(c_0_22, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  fof(c_0_23, plain, ![X5]:(~v1_xboole_0(X5)|v1_relat_1(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_19])])).
% 0.20/0.38  cnf(c_0_25, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_19])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 27
% 0.20/0.38  # Proof object clause steps            : 12
% 0.20/0.38  # Proof object formula steps           : 15
% 0.20/0.38  # Proof object conjectures             : 8
% 0.20/0.38  # Proof object clause conjectures      : 5
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 7
% 0.20/0.38  # Proof object initial formulas used   : 7
% 0.20/0.38  # Proof object generating inferences   : 3
% 0.20/0.38  # Proof object simplifying inferences  : 9
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 7
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 8
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 7
% 0.20/0.38  # Processed clauses                    : 16
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 16
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 1
% 0.20/0.38  # Generated clauses                    : 3
% 0.20/0.38  # ...of the previous two non-trivial   : 3
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 3
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
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
% 0.20/0.38  #    Positive orientable unit clauses  : 2
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 4
% 0.20/0.38  # Current number of unprocessed clauses: 1
% 0.20/0.38  # ...number of literals in the above   : 1
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 10
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 1
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 1
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.38  # Unit Clause-clause subsumption calls : 1
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 426
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.026 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.030 s
% 0.20/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
