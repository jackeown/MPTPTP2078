%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:23 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   22 (  33 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    4
%              Number of atoms          :   65 ( 105 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t99_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => v2_funct_1(k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_funct_1)).

fof(fc7_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2)
        & v2_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v2_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(t52_funct_1,axiom,(
    ! [X1] : v2_funct_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => v2_funct_1(k8_relat_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t99_funct_1])).

fof(c_0_6,plain,(
    ! [X6,X7] :
      ( ( v1_relat_1(k5_relat_1(X6,X7))
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X7) )
      & ( v2_funct_1(k5_relat_1(X6,X7))
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_funct_1])])])).

fof(c_0_7,plain,(
    ! [X3,X4] :
      ( ~ v1_relat_1(X4)
      | k8_relat_1(X3,X4) = k5_relat_1(X4,k6_relat_1(X3)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_8,plain,(
    ! [X8] : v2_funct_1(k6_relat_1(X8)) ),
    inference(variable_rename,[status(thm)],[t52_funct_1])).

fof(c_0_9,plain,(
    ! [X5] :
      ( v1_relat_1(k6_relat_1(X5))
      & v1_funct_1(k6_relat_1(X5)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(esk2_0)
    & ~ v2_funct_1(k8_relat_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_11,plain,
    ( v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_funct_1(k8_relat_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v2_funct_1(k8_relat_1(X1,X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_18,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n023.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 18:00:20 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.16/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4c
% 0.16/0.34  # and selection function SelectCQPrecWNTNp.
% 0.16/0.34  #
% 0.16/0.34  # Preprocessing time       : 0.021 s
% 0.16/0.34  # Presaturation interreduction done
% 0.16/0.34  
% 0.16/0.34  # Proof found!
% 0.16/0.34  # SZS status Theorem
% 0.16/0.34  # SZS output start CNFRefutation
% 0.16/0.34  fof(t99_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>v2_funct_1(k8_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_funct_1)).
% 0.16/0.34  fof(fc7_funct_1, axiom, ![X1, X2]:((((((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))&v2_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v2_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_funct_1)).
% 0.16/0.34  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 0.16/0.34  fof(t52_funct_1, axiom, ![X1]:v2_funct_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 0.16/0.34  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.16/0.34  fof(c_0_5, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>v2_funct_1(k8_relat_1(X1,X2))))), inference(assume_negation,[status(cth)],[t99_funct_1])).
% 0.16/0.34  fof(c_0_6, plain, ![X6, X7]:((v1_relat_1(k5_relat_1(X6,X7))|(~v1_relat_1(X6)|~v1_funct_1(X6)|~v2_funct_1(X6)|~v1_relat_1(X7)|~v1_funct_1(X7)|~v2_funct_1(X7)))&(v2_funct_1(k5_relat_1(X6,X7))|(~v1_relat_1(X6)|~v1_funct_1(X6)|~v2_funct_1(X6)|~v1_relat_1(X7)|~v1_funct_1(X7)|~v2_funct_1(X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_funct_1])])])).
% 0.16/0.34  fof(c_0_7, plain, ![X3, X4]:(~v1_relat_1(X4)|k8_relat_1(X3,X4)=k5_relat_1(X4,k6_relat_1(X3))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.16/0.34  fof(c_0_8, plain, ![X8]:v2_funct_1(k6_relat_1(X8)), inference(variable_rename,[status(thm)],[t52_funct_1])).
% 0.16/0.34  fof(c_0_9, plain, ![X5]:(v1_relat_1(k6_relat_1(X5))&v1_funct_1(k6_relat_1(X5))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.16/0.34  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(v2_funct_1(esk2_0)&~v2_funct_1(k8_relat_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.16/0.34  cnf(c_0_11, plain, (v2_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.16/0.34  cnf(c_0_12, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.16/0.34  cnf(c_0_13, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.16/0.34  cnf(c_0_14, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.34  cnf(c_0_15, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.34  cnf(c_0_16, negated_conjecture, (~v2_funct_1(k8_relat_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.34  cnf(c_0_17, plain, (v2_funct_1(k8_relat_1(X1,X2))|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14]), c_0_15])])).
% 0.16/0.34  cnf(c_0_18, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.34  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.34  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.34  cnf(c_0_21, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20])]), ['proof']).
% 0.16/0.34  # SZS output end CNFRefutation
% 0.16/0.34  # Proof object total steps             : 22
% 0.16/0.34  # Proof object clause steps            : 11
% 0.16/0.34  # Proof object formula steps           : 11
% 0.16/0.34  # Proof object conjectures             : 8
% 0.16/0.34  # Proof object clause conjectures      : 5
% 0.16/0.34  # Proof object formula conjectures     : 3
% 0.16/0.34  # Proof object initial clauses used    : 9
% 0.16/0.34  # Proof object initial formulas used   : 5
% 0.16/0.34  # Proof object generating inferences   : 2
% 0.16/0.34  # Proof object simplifying inferences  : 8
% 0.16/0.34  # Training examples: 0 positive, 0 negative
% 0.16/0.34  # Parsed axioms                        : 5
% 0.16/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.34  # Initial clauses                      : 10
% 0.16/0.34  # Removed in clause preprocessing      : 0
% 0.16/0.34  # Initial clauses in saturation        : 10
% 0.16/0.34  # Processed clauses                    : 22
% 0.16/0.34  # ...of these trivial                  : 0
% 0.16/0.34  # ...subsumed                          : 0
% 0.16/0.34  # ...remaining for further processing  : 22
% 0.16/0.34  # Other redundant clauses eliminated   : 0
% 0.16/0.34  # Clauses deleted for lack of memory   : 0
% 0.16/0.34  # Backward-subsumed                    : 0
% 0.16/0.34  # Backward-rewritten                   : 0
% 0.16/0.34  # Generated clauses                    : 3
% 0.16/0.34  # ...of the previous two non-trivial   : 2
% 0.16/0.34  # Contextual simplify-reflections      : 0
% 0.16/0.34  # Paramodulations                      : 3
% 0.16/0.34  # Factorizations                       : 0
% 0.16/0.34  # Equation resolutions                 : 0
% 0.16/0.34  # Propositional unsat checks           : 0
% 0.16/0.34  #    Propositional check models        : 0
% 0.16/0.34  #    Propositional check unsatisfiable : 0
% 0.16/0.34  #    Propositional clauses             : 0
% 0.16/0.34  #    Propositional clauses after purity: 0
% 0.16/0.34  #    Propositional unsat core size     : 0
% 0.16/0.34  #    Propositional preprocessing time  : 0.000
% 0.16/0.34  #    Propositional encoding time       : 0.000
% 0.16/0.34  #    Propositional solver time         : 0.000
% 0.16/0.34  #    Success case prop preproc time    : 0.000
% 0.16/0.34  #    Success case prop encoding time   : 0.000
% 0.16/0.34  #    Success case prop solver time     : 0.000
% 0.16/0.34  # Current number of processed clauses  : 12
% 0.16/0.34  #    Positive orientable unit clauses  : 6
% 0.16/0.34  #    Positive unorientable unit clauses: 0
% 0.16/0.34  #    Negative unit clauses             : 1
% 0.16/0.34  #    Non-unit-clauses                  : 5
% 0.16/0.34  # Current number of unprocessed clauses: 0
% 0.16/0.34  # ...number of literals in the above   : 0
% 0.16/0.34  # Current number of archived formulas  : 0
% 0.16/0.34  # Current number of archived clauses   : 10
% 0.16/0.34  # Clause-clause subsumption calls (NU) : 0
% 0.16/0.34  # Rec. Clause-clause subsumption calls : 0
% 0.16/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.16/0.34  # Unit Clause-clause subsumption calls : 0
% 0.16/0.34  # Rewrite failures with RHS unbound    : 0
% 0.16/0.34  # BW rewrite match attempts            : 0
% 0.16/0.34  # BW rewrite match successes           : 0
% 0.16/0.34  # Condensation attempts                : 0
% 0.16/0.34  # Condensation successes               : 0
% 0.16/0.34  # Termbank termtop insertions          : 732
% 0.16/0.34  
% 0.16/0.34  # -------------------------------------------------
% 0.16/0.34  # User time                : 0.019 s
% 0.16/0.34  # System time              : 0.005 s
% 0.16/0.34  # Total time               : 0.024 s
% 0.16/0.34  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
