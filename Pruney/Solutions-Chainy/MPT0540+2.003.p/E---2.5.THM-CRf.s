%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:26 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   25 (  42 expanded)
%              Number of clauses        :   12 (  16 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  78 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t140_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k8_relat_1(X1,X3),X2) = k8_relat_1(X1,k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => k7_relat_1(k8_relat_1(X1,X3),X2) = k8_relat_1(X1,k7_relat_1(X3,X2)) ) ),
    inference(assume_negation,[status(cth)],[t140_relat_1])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & k7_relat_1(k8_relat_1(esk1_0,esk3_0),esk2_0) != k8_relat_1(esk1_0,k7_relat_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | k8_relat_1(X10,X11) = k5_relat_1(X11,k6_relat_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

cnf(c_0_9,negated_conjecture,
    ( k7_relat_1(k8_relat_1(esk1_0,esk3_0),esk2_0) != k8_relat_1(esk1_0,k7_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( k7_relat_1(k8_relat_1(esk1_0,esk3_0),esk2_0) != k5_relat_1(k7_relat_1(esk3_0,esk2_0),k6_relat_1(esk1_0))
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | k7_relat_1(k5_relat_1(X8,X9),X7) = k5_relat_1(k7_relat_1(X8,X7),X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

fof(c_0_14,plain,(
    ! [X6] : v1_relat_1(k6_relat_1(X6)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_15,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | v1_relat_1(k5_relat_1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_16,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | k7_relat_1(X13,X12) = k5_relat_1(k6_relat_1(X12),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

cnf(c_0_17,negated_conjecture,
    ( k7_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk1_0)),esk2_0) != k5_relat_1(k7_relat_1(esk3_0,esk2_0),k6_relat_1(esk1_0))
    | ~ v1_relat_1(k7_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_10]),c_0_12])])).

cnf(c_0_18,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_12])])).

cnf(c_0_23,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_19])])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_12])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:20:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.36  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.027 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t140_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k8_relat_1(X1,X3),X2)=k8_relat_1(X1,k7_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 0.13/0.36  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.13/0.36  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 0.13/0.36  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.36  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.13/0.37  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.13/0.37  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k8_relat_1(X1,X3),X2)=k8_relat_1(X1,k7_relat_1(X3,X2)))), inference(assume_negation,[status(cth)],[t140_relat_1])).
% 0.13/0.37  fof(c_0_7, negated_conjecture, (v1_relat_1(esk3_0)&k7_relat_1(k8_relat_1(esk1_0,esk3_0),esk2_0)!=k8_relat_1(esk1_0,k7_relat_1(esk3_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.37  fof(c_0_8, plain, ![X10, X11]:(~v1_relat_1(X11)|k8_relat_1(X10,X11)=k5_relat_1(X11,k6_relat_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.13/0.37  cnf(c_0_9, negated_conjecture, (k7_relat_1(k8_relat_1(esk1_0,esk3_0),esk2_0)!=k8_relat_1(esk1_0,k7_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_10, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (k7_relat_1(k8_relat_1(esk1_0,esk3_0),esk2_0)!=k5_relat_1(k7_relat_1(esk3_0,esk2_0),k6_relat_1(esk1_0))|~v1_relat_1(k7_relat_1(esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  fof(c_0_13, plain, ![X7, X8, X9]:(~v1_relat_1(X8)|(~v1_relat_1(X9)|k7_relat_1(k5_relat_1(X8,X9),X7)=k5_relat_1(k7_relat_1(X8,X7),X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.13/0.37  fof(c_0_14, plain, ![X6]:v1_relat_1(k6_relat_1(X6)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.37  fof(c_0_15, plain, ![X4, X5]:(~v1_relat_1(X4)|~v1_relat_1(X5)|v1_relat_1(k5_relat_1(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.13/0.37  fof(c_0_16, plain, ![X12, X13]:(~v1_relat_1(X13)|k7_relat_1(X13,X12)=k5_relat_1(k6_relat_1(X12),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (k7_relat_1(k5_relat_1(esk3_0,k6_relat_1(esk1_0)),esk2_0)!=k5_relat_1(k7_relat_1(esk3_0,esk2_0),k6_relat_1(esk1_0))|~v1_relat_1(k7_relat_1(esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_10]), c_0_12])])).
% 0.13/0.37  cnf(c_0_18, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_19, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_20, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_21, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (~v1_relat_1(k7_relat_1(esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_12])])).
% 0.13/0.37  cnf(c_0_23, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_19])])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_12])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 25
% 0.13/0.37  # Proof object clause steps            : 12
% 0.13/0.37  # Proof object formula steps           : 13
% 0.13/0.37  # Proof object conjectures             : 9
% 0.13/0.37  # Proof object clause conjectures      : 6
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 7
% 0.13/0.37  # Proof object initial formulas used   : 6
% 0.13/0.37  # Proof object generating inferences   : 5
% 0.13/0.37  # Proof object simplifying inferences  : 9
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 6
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 7
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 7
% 0.13/0.37  # Processed clauses                    : 19
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 19
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 10
% 0.13/0.37  # ...of the previous two non-trivial   : 9
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 10
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 12
% 0.13/0.37  #    Positive orientable unit clauses  : 2
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 8
% 0.13/0.37  # Current number of unprocessed clauses: 4
% 0.13/0.37  # ...number of literals in the above   : 12
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 7
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 3
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 3
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 2
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 674
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.027 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
