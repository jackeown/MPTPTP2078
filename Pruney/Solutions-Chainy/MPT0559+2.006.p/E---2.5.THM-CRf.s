%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:06 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   20 (  23 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   46 (  52 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t76_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(t161_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k9_relat_1(k7_relat_1(X3,X1),X2),k9_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_relat_1)).

fof(t157_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(c_0_5,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(k5_relat_1(X10,k6_relat_1(X9)),X10)
        | ~ v1_relat_1(X10) )
      & ( r1_tarski(k5_relat_1(k6_relat_1(X9),X10),X10)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).

fof(c_0_6,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | k7_relat_1(X12,X11) = k5_relat_1(k6_relat_1(X11),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k9_relat_1(k7_relat_1(X3,X1),X2),k9_relat_1(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t161_relat_1])).

fof(c_0_8,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(k9_relat_1(X7,X6),k9_relat_1(X8,X6)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).

cnf(c_0_9,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | v1_relat_1(k7_relat_1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k9_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0),k9_relat_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_13,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0),k9_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(X1,X2),X3),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:48:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  # Version: 2.5pre002
% 0.21/0.35  # No SInE strategy applied
% 0.21/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.21/0.40  # and selection function SelectCQIPrecWNTNp.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.043 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t76_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 0.21/0.40  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.21/0.40  fof(t161_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(k7_relat_1(X3,X1),X2),k9_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t161_relat_1)).
% 0.21/0.40  fof(t157_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 0.21/0.40  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.21/0.40  fof(c_0_5, plain, ![X9, X10]:((r1_tarski(k5_relat_1(X10,k6_relat_1(X9)),X10)|~v1_relat_1(X10))&(r1_tarski(k5_relat_1(k6_relat_1(X9),X10),X10)|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_relat_1])])])).
% 0.21/0.40  fof(c_0_6, plain, ![X11, X12]:(~v1_relat_1(X12)|k7_relat_1(X12,X11)=k5_relat_1(k6_relat_1(X11),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.21/0.40  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k9_relat_1(k7_relat_1(X3,X1),X2),k9_relat_1(X3,X2)))), inference(assume_negation,[status(cth)],[t161_relat_1])).
% 0.21/0.40  fof(c_0_8, plain, ![X6, X7, X8]:(~v1_relat_1(X7)|(~v1_relat_1(X8)|(~r1_tarski(X7,X8)|r1_tarski(k9_relat_1(X7,X6),k9_relat_1(X8,X6))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).
% 0.21/0.40  cnf(c_0_9, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.40  cnf(c_0_10, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.40  fof(c_0_11, plain, ![X4, X5]:(~v1_relat_1(X4)|v1_relat_1(k7_relat_1(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.21/0.40  fof(c_0_12, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k9_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0),k9_relat_1(esk3_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.21/0.40  cnf(c_0_13, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.40  cnf(c_0_14, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.21/0.40  cnf(c_0_15, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  cnf(c_0_16, negated_conjecture, (~r1_tarski(k9_relat_1(k7_relat_1(esk3_0,esk1_0),esk2_0),k9_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_17, plain, (r1_tarski(k9_relat_1(k7_relat_1(X1,X2),X3),k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.21/0.40  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_19, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 20
% 0.21/0.40  # Proof object clause steps            : 9
% 0.21/0.40  # Proof object formula steps           : 11
% 0.21/0.40  # Proof object conjectures             : 6
% 0.21/0.40  # Proof object clause conjectures      : 3
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 6
% 0.21/0.40  # Proof object initial formulas used   : 5
% 0.21/0.40  # Proof object generating inferences   : 3
% 0.21/0.40  # Proof object simplifying inferences  : 3
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 5
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 7
% 0.21/0.40  # Removed in clause preprocessing      : 0
% 0.21/0.40  # Initial clauses in saturation        : 7
% 0.21/0.40  # Processed clauses                    : 18
% 0.21/0.40  # ...of these trivial                  : 0
% 0.21/0.40  # ...subsumed                          : 0
% 0.21/0.40  # ...remaining for further processing  : 18
% 0.21/0.40  # Other redundant clauses eliminated   : 0
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 0
% 0.21/0.40  # Backward-rewritten                   : 0
% 0.21/0.40  # Generated clauses                    : 8
% 0.21/0.40  # ...of the previous two non-trivial   : 7
% 0.21/0.40  # Contextual simplify-reflections      : 1
% 0.21/0.40  # Paramodulations                      : 8
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 0
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 11
% 0.21/0.40  #    Positive orientable unit clauses  : 1
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 1
% 0.21/0.40  #    Non-unit-clauses                  : 9
% 0.21/0.40  # Current number of unprocessed clauses: 2
% 0.21/0.40  # ...number of literals in the above   : 6
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 7
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 38
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 38
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 1
% 0.21/0.40  # Unit Clause-clause subsumption calls : 0
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 0
% 0.21/0.40  # BW rewrite match successes           : 0
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 709
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.044 s
% 0.21/0.40  # System time              : 0.004 s
% 0.21/0.40  # Total time               : 0.048 s
% 0.21/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
