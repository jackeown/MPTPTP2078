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
% DateTime   : Thu Dec  3 10:54:09 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   18 (  20 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    4
%              Number of atoms          :   31 (  35 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_funct_1,conjecture,(
    ! [X1] : k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(t72_relat_1,axiom,(
    ! [X1] : k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] : k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(assume_negation,[status(cth)],[t67_funct_1])).

fof(c_0_6,negated_conjecture,(
    k2_funct_1(k6_relat_1(esk1_0)) != k6_relat_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v2_funct_1(X3)
      | k2_funct_1(X3) = k4_relat_1(X3) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

fof(c_0_8,plain,(
    ! [X2] : k4_relat_1(k6_relat_1(X2)) = k6_relat_1(X2) ),
    inference(variable_rename,[status(thm)],[t72_relat_1])).

fof(c_0_9,plain,(
    ! [X5] :
      ( v1_relat_1(k6_relat_1(X5))
      & v2_funct_1(k6_relat_1(X5)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_10,plain,(
    ! [X4] :
      ( v1_relat_1(k6_relat_1(X4))
      & v1_funct_1(k6_relat_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_11,negated_conjecture,
    ( k2_funct_1(k6_relat_1(esk1_0)) != k6_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k4_relat_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:02:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.36  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.36  #
% 0.20/0.36  # Preprocessing time       : 0.025 s
% 0.20/0.36  # Presaturation interreduction done
% 0.20/0.36  
% 0.20/0.36  # Proof found!
% 0.20/0.36  # SZS status Theorem
% 0.20/0.36  # SZS output start CNFRefutation
% 0.20/0.36  fof(t67_funct_1, conjecture, ![X1]:k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 0.20/0.36  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 0.20/0.36  fof(t72_relat_1, axiom, ![X1]:k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 0.20/0.36  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.20/0.36  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.20/0.36  fof(c_0_5, negated_conjecture, ~(![X1]:k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(assume_negation,[status(cth)],[t67_funct_1])).
% 0.20/0.36  fof(c_0_6, negated_conjecture, k2_funct_1(k6_relat_1(esk1_0))!=k6_relat_1(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.36  fof(c_0_7, plain, ![X3]:(~v1_relat_1(X3)|~v1_funct_1(X3)|(~v2_funct_1(X3)|k2_funct_1(X3)=k4_relat_1(X3))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.20/0.36  fof(c_0_8, plain, ![X2]:k4_relat_1(k6_relat_1(X2))=k6_relat_1(X2), inference(variable_rename,[status(thm)],[t72_relat_1])).
% 0.20/0.36  fof(c_0_9, plain, ![X5]:(v1_relat_1(k6_relat_1(X5))&v2_funct_1(k6_relat_1(X5))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.20/0.36  fof(c_0_10, plain, ![X4]:(v1_relat_1(k6_relat_1(X4))&v1_funct_1(k6_relat_1(X4))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.20/0.36  cnf(c_0_11, negated_conjecture, (k2_funct_1(k6_relat_1(esk1_0))!=k6_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.36  cnf(c_0_12, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.36  cnf(c_0_13, plain, (k4_relat_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.36  cnf(c_0_14, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.36  cnf(c_0_15, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.36  cnf(c_0_16, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.36  cnf(c_0_17, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), ['proof']).
% 0.20/0.36  # SZS output end CNFRefutation
% 0.20/0.36  # Proof object total steps             : 18
% 0.20/0.36  # Proof object clause steps            : 7
% 0.20/0.36  # Proof object formula steps           : 11
% 0.20/0.36  # Proof object conjectures             : 5
% 0.20/0.36  # Proof object clause conjectures      : 2
% 0.20/0.36  # Proof object formula conjectures     : 3
% 0.20/0.36  # Proof object initial clauses used    : 6
% 0.20/0.36  # Proof object initial formulas used   : 5
% 0.20/0.36  # Proof object generating inferences   : 1
% 0.20/0.36  # Proof object simplifying inferences  : 5
% 0.20/0.36  # Training examples: 0 positive, 0 negative
% 0.20/0.36  # Parsed axioms                        : 5
% 0.20/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.36  # Initial clauses                      : 7
% 0.20/0.36  # Removed in clause preprocessing      : 0
% 0.20/0.36  # Initial clauses in saturation        : 7
% 0.20/0.36  # Processed clauses                    : 13
% 0.20/0.36  # ...of these trivial                  : 1
% 0.20/0.36  # ...subsumed                          : 0
% 0.20/0.36  # ...remaining for further processing  : 12
% 0.20/0.36  # Other redundant clauses eliminated   : 0
% 0.20/0.36  # Clauses deleted for lack of memory   : 0
% 0.20/0.36  # Backward-subsumed                    : 0
% 0.20/0.36  # Backward-rewritten                   : 0
% 0.20/0.36  # Generated clauses                    : 1
% 0.20/0.36  # ...of the previous two non-trivial   : 0
% 0.20/0.36  # Contextual simplify-reflections      : 0
% 0.20/0.36  # Paramodulations                      : 1
% 0.20/0.36  # Factorizations                       : 0
% 0.20/0.36  # Equation resolutions                 : 0
% 0.20/0.36  # Propositional unsat checks           : 0
% 0.20/0.36  #    Propositional check models        : 0
% 0.20/0.36  #    Propositional check unsatisfiable : 0
% 0.20/0.36  #    Propositional clauses             : 0
% 0.20/0.36  #    Propositional clauses after purity: 0
% 0.20/0.36  #    Propositional unsat core size     : 0
% 0.20/0.36  #    Propositional preprocessing time  : 0.000
% 0.20/0.36  #    Propositional encoding time       : 0.000
% 0.20/0.36  #    Propositional solver time         : 0.000
% 0.20/0.36  #    Success case prop preproc time    : 0.000
% 0.20/0.36  #    Success case prop encoding time   : 0.000
% 0.20/0.36  #    Success case prop solver time     : 0.000
% 0.20/0.36  # Current number of processed clauses  : 6
% 0.20/0.36  #    Positive orientable unit clauses  : 4
% 0.20/0.36  #    Positive unorientable unit clauses: 0
% 0.20/0.36  #    Negative unit clauses             : 1
% 0.20/0.36  #    Non-unit-clauses                  : 1
% 0.20/0.36  # Current number of unprocessed clauses: 0
% 0.20/0.36  # ...number of literals in the above   : 0
% 0.20/0.36  # Current number of archived formulas  : 0
% 0.20/0.36  # Current number of archived clauses   : 6
% 0.20/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.36  # Unit Clause-clause subsumption calls : 0
% 0.20/0.36  # Rewrite failures with RHS unbound    : 0
% 0.20/0.36  # BW rewrite match attempts            : 0
% 0.20/0.36  # BW rewrite match successes           : 0
% 0.20/0.36  # Condensation attempts                : 0
% 0.20/0.36  # Condensation successes               : 0
% 0.20/0.36  # Termbank termtop insertions          : 354
% 0.20/0.36  
% 0.20/0.36  # -------------------------------------------------
% 0.20/0.36  # User time                : 0.025 s
% 0.20/0.36  # System time              : 0.003 s
% 0.20/0.36  # Total time               : 0.029 s
% 0.20/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
