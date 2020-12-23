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
% DateTime   : Thu Dec  3 10:50:06 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   24 (  27 expanded)
%              Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    5
%              Number of atoms          :   49 (  55 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(t116_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t128_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_relat_1)).

fof(c_0_6,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ r1_tarski(k2_relat_1(X11),X10)
      | k8_relat_1(X10,X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

fof(c_0_7,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X7)
      | r1_tarski(k2_relat_1(k8_relat_1(X6,X7)),X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).

fof(c_0_8,plain,(
    ! [X3,X4] :
      ( ~ v1_relat_1(X3)
      | ~ v1_relat_1(X4)
      | v1_relat_1(k5_relat_1(X3,X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_9,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X9)
      | k8_relat_1(X8,X9) = k5_relat_1(X9,k6_relat_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_10,plain,(
    ! [X5] : v1_relat_1(k6_relat_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k8_relat_1(X1,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t128_relat_1])).

cnf(c_0_12,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & k8_relat_1(esk1_0,k8_relat_1(esk1_0,esk2_0)) != k8_relat_1(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_18,plain,
    ( k8_relat_1(X1,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2)
    | ~ v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( v1_relat_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_20,negated_conjecture,
    ( k8_relat_1(esk1_0,k8_relat_1(esk1_0,esk2_0)) != k8_relat_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k8_relat_1(X1,k8_relat_1(X1,X2)) = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.37  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 0.13/0.37  fof(t116_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k8_relat_1(X1,X2)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 0.13/0.37  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.13/0.37  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.13/0.37  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.37  fof(t128_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,k8_relat_1(X1,X2))=k8_relat_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_relat_1)).
% 0.13/0.37  fof(c_0_6, plain, ![X10, X11]:(~v1_relat_1(X11)|(~r1_tarski(k2_relat_1(X11),X10)|k8_relat_1(X10,X11)=X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.13/0.37  fof(c_0_7, plain, ![X6, X7]:(~v1_relat_1(X7)|r1_tarski(k2_relat_1(k8_relat_1(X6,X7)),X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t116_relat_1])])).
% 0.13/0.37  fof(c_0_8, plain, ![X3, X4]:(~v1_relat_1(X3)|~v1_relat_1(X4)|v1_relat_1(k5_relat_1(X3,X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.13/0.37  fof(c_0_9, plain, ![X8, X9]:(~v1_relat_1(X9)|k8_relat_1(X8,X9)=k5_relat_1(X9,k6_relat_1(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.13/0.38  fof(c_0_10, plain, ![X5]:v1_relat_1(k6_relat_1(X5)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.38  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,k8_relat_1(X1,X2))=k8_relat_1(X1,X2))), inference(assume_negation,[status(cth)],[t128_relat_1])).
% 0.13/0.38  cnf(c_0_12, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_13, plain, (r1_tarski(k2_relat_1(k8_relat_1(X2,X1)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_14, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_15, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_16, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  fof(c_0_17, negated_conjecture, (v1_relat_1(esk2_0)&k8_relat_1(esk1_0,k8_relat_1(esk1_0,esk2_0))!=k8_relat_1(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.13/0.38  cnf(c_0_18, plain, (k8_relat_1(X1,k8_relat_1(X1,X2))=k8_relat_1(X1,X2)|~v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.38  cnf(c_0_19, plain, (v1_relat_1(k8_relat_1(X1,X2))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (k8_relat_1(esk1_0,k8_relat_1(esk1_0,esk2_0))!=k8_relat_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_21, plain, (k8_relat_1(X1,k8_relat_1(X1,X2))=k8_relat_1(X1,X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 24
% 0.13/0.38  # Proof object clause steps            : 11
% 0.13/0.38  # Proof object formula steps           : 13
% 0.13/0.38  # Proof object conjectures             : 6
% 0.13/0.38  # Proof object clause conjectures      : 3
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 7
% 0.13/0.38  # Proof object initial formulas used   : 6
% 0.13/0.38  # Proof object generating inferences   : 4
% 0.13/0.38  # Proof object simplifying inferences  : 4
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 6
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 7
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 7
% 0.13/0.38  # Processed clauses                    : 17
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 17
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 1
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 7
% 0.13/0.38  # ...of the previous two non-trivial   : 3
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 7
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 9
% 0.13/0.38  #    Positive orientable unit clauses  : 2
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 6
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 8
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 1
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 583
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.028 s
% 0.13/0.38  # System time              : 0.002 s
% 0.13/0.38  # Total time               : 0.030 s
% 0.13/0.38  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
