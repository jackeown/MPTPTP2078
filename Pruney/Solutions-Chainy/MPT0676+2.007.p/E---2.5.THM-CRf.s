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
% DateTime   : Thu Dec  3 10:54:26 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   17 (  28 expanded)
%              Number of clauses        :    8 (  10 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  68 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t120_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => r1_tarski(k9_relat_1(k8_relat_1(X1,X3),X2),k9_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_funct_1)).

fof(t157_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(t117_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k8_relat_1(X1,X2),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => r1_tarski(k9_relat_1(k8_relat_1(X1,X3),X2),k9_relat_1(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t120_funct_1])).

fof(c_0_5,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & ~ r1_tarski(k9_relat_1(k8_relat_1(esk1_0,esk3_0),esk2_0),k9_relat_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X8,X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(k9_relat_1(X9,X8),k9_relat_1(X10,X8)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).

cnf(c_0_7,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(k8_relat_1(esk1_0,esk3_0),esk2_0),k9_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_10,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X7)
      | r1_tarski(k8_relat_1(X6,X7),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(esk1_0,esk3_0),esk3_0)
    | ~ v1_relat_1(k8_relat_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])])).

cnf(c_0_12,plain,
    ( r1_tarski(k8_relat_1(X2,X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | v1_relat_1(k8_relat_1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_14,negated_conjecture,
    ( ~ v1_relat_1(k8_relat_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_9])])).

cnf(c_0_15,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_9])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___103_C18_F1_PI_AE_Q4_CS_SP_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t120_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>r1_tarski(k9_relat_1(k8_relat_1(X1,X3),X2),k9_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_funct_1)).
% 0.13/0.38  fof(t157_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 0.13/0.38  fof(t117_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k8_relat_1(X1,X2),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 0.13/0.38  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.13/0.38  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>r1_tarski(k9_relat_1(k8_relat_1(X1,X3),X2),k9_relat_1(X3,X2)))), inference(assume_negation,[status(cth)],[t120_funct_1])).
% 0.13/0.38  fof(c_0_5, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&~r1_tarski(k9_relat_1(k8_relat_1(esk1_0,esk3_0),esk2_0),k9_relat_1(esk3_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.13/0.38  fof(c_0_6, plain, ![X8, X9, X10]:(~v1_relat_1(X9)|(~v1_relat_1(X10)|(~r1_tarski(X9,X10)|r1_tarski(k9_relat_1(X9,X8),k9_relat_1(X10,X8))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).
% 0.13/0.38  cnf(c_0_7, negated_conjecture, (~r1_tarski(k9_relat_1(k8_relat_1(esk1_0,esk3_0),esk2_0),k9_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_8, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_9, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  fof(c_0_10, plain, ![X6, X7]:(~v1_relat_1(X7)|r1_tarski(k8_relat_1(X6,X7),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t117_relat_1])])).
% 0.13/0.38  cnf(c_0_11, negated_conjecture, (~r1_tarski(k8_relat_1(esk1_0,esk3_0),esk3_0)|~v1_relat_1(k8_relat_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])])).
% 0.13/0.38  cnf(c_0_12, plain, (r1_tarski(k8_relat_1(X2,X1),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  fof(c_0_13, plain, ![X4, X5]:(~v1_relat_1(X5)|v1_relat_1(k8_relat_1(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (~v1_relat_1(k8_relat_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_9])])).
% 0.13/0.38  cnf(c_0_15, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_9])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 17
% 0.13/0.38  # Proof object clause steps            : 8
% 0.13/0.38  # Proof object formula steps           : 9
% 0.13/0.38  # Proof object conjectures             : 8
% 0.13/0.38  # Proof object clause conjectures      : 5
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 5
% 0.13/0.38  # Proof object initial formulas used   : 4
% 0.13/0.38  # Proof object generating inferences   : 3
% 0.13/0.38  # Proof object simplifying inferences  : 6
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 4
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 6
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 6
% 0.13/0.38  # Processed clauses                    : 8
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 8
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 3
% 0.13/0.38  # ...of the previous two non-trivial   : 2
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 3
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
% 0.13/0.38  # Current number of processed clauses  : 8
% 0.13/0.38  #    Positive orientable unit clauses  : 2
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 4
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 0
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 6
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 6
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 1
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 426
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.001 s
% 0.13/0.38  # Total time               : 0.030 s
% 0.13/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
