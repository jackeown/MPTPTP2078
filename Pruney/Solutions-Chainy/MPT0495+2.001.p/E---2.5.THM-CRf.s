%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:32 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   23 (  40 expanded)
%              Number of clauses        :   12 (  15 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 ( 103 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t93_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => r1_tarski(k5_relat_1(X2,k7_relat_1(X3,X1)),k5_relat_1(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_relat_1)).

fof(t48_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( r1_tarski(X1,X2)
               => r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => r1_tarski(k5_relat_1(X2,k7_relat_1(X3,X1)),k5_relat_1(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t93_relat_1])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k5_relat_1(esk2_0,k7_relat_1(esk3_0,esk1_0)),k5_relat_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X8,X9,X10] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(k5_relat_1(X10,X8),k5_relat_1(X10,X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).

fof(c_0_8,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_relat_1(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_9,plain,(
    ! [X4,X5] :
      ( ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
        | r1_tarski(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | m1_subset_1(X4,k1_zfmisc_1(X5)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk2_0,k7_relat_1(esk3_0,esk1_0)),k5_relat_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_14,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | r1_tarski(k7_relat_1(X12,X11),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_15,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk3_0,esk1_0))
    | ~ r1_tarski(k7_relat_1(esk3_0,esk1_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_18,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk3_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_13])])).

cnf(c_0_21,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_13])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n011.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 13:27:42 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  # Version: 2.5pre002
% 0.11/0.31  # No SInE strategy applied
% 0.11/0.31  # Trying AutoSched0 for 299 seconds
% 0.16/0.34  # AutoSched0-Mode selected heuristic G_E___107_C48_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.16/0.34  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.16/0.34  #
% 0.16/0.34  # Preprocessing time       : 0.026 s
% 0.16/0.34  # Presaturation interreduction done
% 0.16/0.34  
% 0.16/0.34  # Proof found!
% 0.16/0.34  # SZS status Theorem
% 0.16/0.34  # SZS output start CNFRefutation
% 0.16/0.34  fof(t93_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X2,k7_relat_1(X3,X1)),k5_relat_1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_relat_1)).
% 0.16/0.34  fof(t48_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 0.16/0.34  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.16/0.34  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.16/0.34  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 0.16/0.34  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X2,k7_relat_1(X3,X1)),k5_relat_1(X2,X3))))), inference(assume_negation,[status(cth)],[t93_relat_1])).
% 0.16/0.34  fof(c_0_6, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k5_relat_1(esk2_0,k7_relat_1(esk3_0,esk1_0)),k5_relat_1(esk2_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.16/0.34  fof(c_0_7, plain, ![X8, X9, X10]:(~v1_relat_1(X8)|(~v1_relat_1(X9)|(~v1_relat_1(X10)|(~r1_tarski(X8,X9)|r1_tarski(k5_relat_1(X10,X8),k5_relat_1(X10,X9)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_relat_1])])])).
% 0.16/0.34  fof(c_0_8, plain, ![X6, X7]:(~v1_relat_1(X6)|(~m1_subset_1(X7,k1_zfmisc_1(X6))|v1_relat_1(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.16/0.34  fof(c_0_9, plain, ![X4, X5]:((~m1_subset_1(X4,k1_zfmisc_1(X5))|r1_tarski(X4,X5))&(~r1_tarski(X4,X5)|m1_subset_1(X4,k1_zfmisc_1(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.16/0.34  cnf(c_0_10, negated_conjecture, (~r1_tarski(k5_relat_1(esk2_0,k7_relat_1(esk3_0,esk1_0)),k5_relat_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.16/0.34  cnf(c_0_11, plain, (r1_tarski(k5_relat_1(X3,X1),k5_relat_1(X3,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.16/0.34  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.16/0.34  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.16/0.34  fof(c_0_14, plain, ![X11, X12]:(~v1_relat_1(X12)|r1_tarski(k7_relat_1(X12,X11),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.16/0.34  cnf(c_0_15, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.16/0.34  cnf(c_0_16, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.34  cnf(c_0_17, negated_conjecture, (~v1_relat_1(k7_relat_1(esk3_0,esk1_0))|~r1_tarski(k7_relat_1(esk3_0,esk1_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13])])).
% 0.16/0.34  cnf(c_0_18, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.16/0.34  cnf(c_0_19, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.16/0.34  cnf(c_0_20, negated_conjecture, (~v1_relat_1(k7_relat_1(esk3_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_13])])).
% 0.16/0.34  cnf(c_0_21, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.16/0.34  cnf(c_0_22, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_13])]), ['proof']).
% 0.16/0.34  # SZS output end CNFRefutation
% 0.16/0.34  # Proof object total steps             : 23
% 0.16/0.34  # Proof object clause steps            : 12
% 0.16/0.34  # Proof object formula steps           : 11
% 0.16/0.34  # Proof object conjectures             : 9
% 0.16/0.34  # Proof object clause conjectures      : 6
% 0.16/0.34  # Proof object formula conjectures     : 3
% 0.16/0.34  # Proof object initial clauses used    : 7
% 0.16/0.34  # Proof object initial formulas used   : 5
% 0.16/0.34  # Proof object generating inferences   : 5
% 0.16/0.34  # Proof object simplifying inferences  : 7
% 0.16/0.34  # Training examples: 0 positive, 0 negative
% 0.16/0.34  # Parsed axioms                        : 5
% 0.16/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.34  # Initial clauses                      : 8
% 0.16/0.34  # Removed in clause preprocessing      : 0
% 0.16/0.34  # Initial clauses in saturation        : 8
% 0.16/0.34  # Processed clauses                    : 20
% 0.16/0.34  # ...of these trivial                  : 0
% 0.16/0.34  # ...subsumed                          : 0
% 0.16/0.34  # ...remaining for further processing  : 20
% 0.16/0.34  # Other redundant clauses eliminated   : 0
% 0.16/0.34  # Clauses deleted for lack of memory   : 0
% 0.16/0.34  # Backward-subsumed                    : 0
% 0.16/0.34  # Backward-rewritten                   : 0
% 0.16/0.34  # Generated clauses                    : 7
% 0.16/0.34  # ...of the previous two non-trivial   : 5
% 0.16/0.34  # Contextual simplify-reflections      : 0
% 0.16/0.34  # Paramodulations                      : 7
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
% 0.16/0.34  #    Positive orientable unit clauses  : 2
% 0.16/0.34  #    Positive unorientable unit clauses: 0
% 0.16/0.34  #    Negative unit clauses             : 2
% 0.16/0.34  #    Non-unit-clauses                  : 8
% 0.16/0.34  # Current number of unprocessed clauses: 1
% 0.16/0.34  # ...number of literals in the above   : 6
% 0.16/0.34  # Current number of archived formulas  : 0
% 0.16/0.34  # Current number of archived clauses   : 8
% 0.16/0.34  # Clause-clause subsumption calls (NU) : 1
% 0.16/0.34  # Rec. Clause-clause subsumption calls : 1
% 0.16/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.16/0.34  # Unit Clause-clause subsumption calls : 1
% 0.16/0.34  # Rewrite failures with RHS unbound    : 0
% 0.16/0.34  # BW rewrite match attempts            : 0
% 0.16/0.34  # BW rewrite match successes           : 0
% 0.16/0.34  # Condensation attempts                : 0
% 0.16/0.34  # Condensation successes               : 0
% 0.16/0.34  # Termbank termtop insertions          : 692
% 0.16/0.34  
% 0.16/0.34  # -------------------------------------------------
% 0.16/0.34  # User time                : 0.027 s
% 0.16/0.34  # System time              : 0.003 s
% 0.16/0.34  # Total time               : 0.030 s
% 0.16/0.34  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
