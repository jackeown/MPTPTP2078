%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:12 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   21 (  41 expanded)
%              Number of clauses        :   12 (  15 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 ( 115 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t132_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(t49_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( r1_tarski(X1,X2)
               => r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( r1_tarski(X2,X3)
             => r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t132_relat_1])).

fof(c_0_5,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X6)
      | k8_relat_1(X5,X6) = k5_relat_1(X6,k6_relat_1(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & r1_tarski(esk2_0,esk3_0)
    & ~ r1_tarski(k8_relat_1(esk1_0,esk2_0),k8_relat_1(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X7,X8,X9] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(k5_relat_1(X7,X9),k5_relat_1(X8,X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_relat_1])])])).

cnf(c_0_8,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X4] : v1_relat_1(k6_relat_1(X4)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_11,plain,
    ( r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( k5_relat_1(esk3_0,k6_relat_1(X1)) = k8_relat_1(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),k8_relat_1(X2,esk3_0))
    | ~ r1_tarski(X1,esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_9])])).

cnf(c_0_16,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(X1)) = k8_relat_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(esk1_0,esk2_0),k8_relat_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk2_0),k8_relat_1(X1,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_14]),c_0_16]),c_0_17])])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:04:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.35  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.13/0.35  # and selection function PSelectSmallestOrientable.
% 0.13/0.35  #
% 0.13/0.35  # Preprocessing time       : 0.015 s
% 0.13/0.35  # Presaturation interreduction done
% 0.13/0.35  
% 0.13/0.35  # Proof found!
% 0.13/0.35  # SZS status Theorem
% 0.13/0.35  # SZS output start CNFRefutation
% 0.13/0.35  fof(t132_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_relat_1)).
% 0.13/0.35  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 0.13/0.35  fof(t49_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relat_1)).
% 0.13/0.35  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.36  fof(c_0_4, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X1,X3)))))), inference(assume_negation,[status(cth)],[t132_relat_1])).
% 0.13/0.36  fof(c_0_5, plain, ![X5, X6]:(~v1_relat_1(X6)|k8_relat_1(X5,X6)=k5_relat_1(X6,k6_relat_1(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.13/0.36  fof(c_0_6, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&(r1_tarski(esk2_0,esk3_0)&~r1_tarski(k8_relat_1(esk1_0,esk2_0),k8_relat_1(esk1_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.13/0.36  fof(c_0_7, plain, ![X7, X8, X9]:(~v1_relat_1(X7)|(~v1_relat_1(X8)|(~v1_relat_1(X9)|(~r1_tarski(X7,X8)|r1_tarski(k5_relat_1(X7,X9),k5_relat_1(X8,X9)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_relat_1])])])).
% 0.13/0.36  cnf(c_0_8, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.36  cnf(c_0_9, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.36  fof(c_0_10, plain, ![X4]:v1_relat_1(k6_relat_1(X4)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.36  cnf(c_0_11, plain, (r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.36  cnf(c_0_12, negated_conjecture, (k5_relat_1(esk3_0,k6_relat_1(X1))=k8_relat_1(X1,esk3_0)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.13/0.36  cnf(c_0_13, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.36  cnf(c_0_15, negated_conjecture, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),k8_relat_1(X2,esk3_0))|~r1_tarski(X1,esk3_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_9])])).
% 0.13/0.36  cnf(c_0_16, negated_conjecture, (k5_relat_1(esk2_0,k6_relat_1(X1))=k8_relat_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_8, c_0_14])).
% 0.13/0.36  cnf(c_0_17, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.36  cnf(c_0_18, negated_conjecture, (~r1_tarski(k8_relat_1(esk1_0,esk2_0),k8_relat_1(esk1_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.36  cnf(c_0_19, negated_conjecture, (r1_tarski(k8_relat_1(X1,esk2_0),k8_relat_1(X1,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_14]), c_0_16]), c_0_17])])).
% 0.13/0.36  cnf(c_0_20, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19])]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 21
% 0.13/0.36  # Proof object clause steps            : 12
% 0.13/0.36  # Proof object formula steps           : 9
% 0.13/0.36  # Proof object conjectures             : 12
% 0.13/0.36  # Proof object clause conjectures      : 9
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 7
% 0.13/0.36  # Proof object initial formulas used   : 4
% 0.13/0.36  # Proof object generating inferences   : 4
% 0.13/0.36  # Proof object simplifying inferences  : 8
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 4
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 7
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 7
% 0.13/0.36  # Processed clauses                    : 41
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 3
% 0.13/0.36  # ...remaining for further processing  : 38
% 0.13/0.36  # Other redundant clauses eliminated   : 0
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 1
% 0.13/0.36  # Generated clauses                    : 51
% 0.13/0.36  # ...of the previous two non-trivial   : 51
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 51
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 0
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 30
% 0.13/0.36  #    Positive orientable unit clauses  : 10
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 0
% 0.13/0.36  #    Non-unit-clauses                  : 20
% 0.13/0.36  # Current number of unprocessed clauses: 24
% 0.13/0.36  # ...number of literals in the above   : 62
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 8
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 9
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 9
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.36  # Unit Clause-clause subsumption calls : 1
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 1
% 0.13/0.36  # BW rewrite match successes           : 1
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 1446
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.016 s
% 0.13/0.36  # System time              : 0.004 s
% 0.13/0.36  # Total time               : 0.019 s
% 0.13/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
