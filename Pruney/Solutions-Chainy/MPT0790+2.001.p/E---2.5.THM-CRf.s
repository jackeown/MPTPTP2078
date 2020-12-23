%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   14 (  20 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    4
%              Number of atoms          :   34 (  52 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1))) = k1_wellord1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).

fof(t39_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ( v2_wellord1(X2)
          & r1_tarski(X1,k3_relat_1(X2)) )
       => k3_relat_1(k2_wellord1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_wellord1)).

fof(t13_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_wellord1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( v2_wellord1(X2)
         => k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1))) = k1_wellord1(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t40_wellord1])).

fof(c_0_4,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X6)
      | ~ v2_wellord1(X6)
      | ~ r1_tarski(X5,k3_relat_1(X6))
      | k3_relat_1(k2_wellord1(X6,X5)) = X5 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_wellord1])])).

fof(c_0_5,plain,(
    ! [X3,X4] :
      ( ~ v1_relat_1(X4)
      | r1_tarski(k1_wellord1(X4,X3),k3_relat_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v2_wellord1(esk2_0)
    & k3_relat_1(k2_wellord1(esk2_0,k1_wellord1(esk2_0,esk1_0))) != k1_wellord1(esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( k3_relat_1(k2_wellord1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v2_wellord1(X1)
    | ~ r1_tarski(X2,k3_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( k3_relat_1(k2_wellord1(esk2_0,k1_wellord1(esk2_0,esk1_0))) != k1_wellord1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2))) = k1_wellord1(X1,X2)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:04:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_TT_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.026 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t40_wellord1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(v2_wellord1(X2)=>k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1)))=k1_wellord1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_wellord1)).
% 0.20/0.38  fof(t39_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>((v2_wellord1(X2)&r1_tarski(X1,k3_relat_1(X2)))=>k3_relat_1(k2_wellord1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_wellord1)).
% 0.20/0.38  fof(t13_wellord1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_wellord1(X2,X1),k3_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_wellord1)).
% 0.20/0.38  fof(c_0_3, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(v2_wellord1(X2)=>k3_relat_1(k2_wellord1(X2,k1_wellord1(X2,X1)))=k1_wellord1(X2,X1)))), inference(assume_negation,[status(cth)],[t40_wellord1])).
% 0.20/0.38  fof(c_0_4, plain, ![X5, X6]:(~v1_relat_1(X6)|(~v2_wellord1(X6)|~r1_tarski(X5,k3_relat_1(X6))|k3_relat_1(k2_wellord1(X6,X5))=X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_wellord1])])).
% 0.20/0.38  fof(c_0_5, plain, ![X3, X4]:(~v1_relat_1(X4)|r1_tarski(k1_wellord1(X4,X3),k3_relat_1(X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_wellord1])])).
% 0.20/0.38  fof(c_0_6, negated_conjecture, (v1_relat_1(esk2_0)&(v2_wellord1(esk2_0)&k3_relat_1(k2_wellord1(esk2_0,k1_wellord1(esk2_0,esk1_0)))!=k1_wellord1(esk2_0,esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.20/0.38  cnf(c_0_7, plain, (k3_relat_1(k2_wellord1(X1,X2))=X2|~v1_relat_1(X1)|~v2_wellord1(X1)|~r1_tarski(X2,k3_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  cnf(c_0_8, plain, (r1_tarski(k1_wellord1(X1,X2),k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_9, negated_conjecture, (k3_relat_1(k2_wellord1(esk2_0,k1_wellord1(esk2_0,esk1_0)))!=k1_wellord1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_10, plain, (k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X2)))=k1_wellord1(X1,X2)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.20/0.38  cnf(c_0_11, negated_conjecture, (v2_wellord1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_13, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 14
% 0.20/0.38  # Proof object clause steps            : 7
% 0.20/0.38  # Proof object formula steps           : 7
% 0.20/0.38  # Proof object conjectures             : 7
% 0.20/0.38  # Proof object clause conjectures      : 4
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 5
% 0.20/0.38  # Proof object initial formulas used   : 3
% 0.20/0.38  # Proof object generating inferences   : 2
% 0.20/0.38  # Proof object simplifying inferences  : 3
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 3
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 5
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 5
% 0.20/0.38  # Processed clauses                    : 11
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 11
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 4
% 0.20/0.38  # ...of the previous two non-trivial   : 3
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 4
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
% 0.20/0.38  # Current number of processed clauses  : 6
% 0.20/0.38  #    Positive orientable unit clauses  : 2
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 3
% 0.20/0.38  # Current number of unprocessed clauses: 0
% 0.20/0.38  # ...number of literals in the above   : 0
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 5
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.38  # Unit Clause-clause subsumption calls : 0
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 0
% 0.20/0.38  # BW rewrite match successes           : 0
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 418
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.025 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.029 s
% 0.20/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
