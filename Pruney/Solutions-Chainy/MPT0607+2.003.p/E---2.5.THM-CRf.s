%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:27 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  29 expanded)
%              Number of clauses        :   10 (  11 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  66 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t211_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(k1_relat_1(X3),X1)
       => k6_subset_1(X3,k7_relat_1(X3,X2)) = k7_relat_1(X3,k6_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

fof(t102_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(t109_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(X3,k6_subset_1(X1,X2)) = k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(k1_relat_1(X3),X1)
         => k6_subset_1(X3,k7_relat_1(X3,X2)) = k7_relat_1(X3,k6_subset_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t211_relat_1])).

fof(c_0_5,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_relat_1(X8)
      | ~ r1_tarski(X6,X7)
      | k7_relat_1(k7_relat_1(X8,X6),X7) = k7_relat_1(X8,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t102_relat_1])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(k1_relat_1(esk3_0),esk1_0)
    & k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)) != k7_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | k7_relat_1(X12,k1_relat_1(X12)) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

fof(c_0_10,plain,(
    ! [X9,X10,X11] :
      ( ~ v1_relat_1(X11)
      | k7_relat_1(X11,k6_subset_1(X9,X10)) = k6_subset_1(k7_relat_1(X11,X9),k7_relat_1(X11,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).

cnf(c_0_11,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,k1_relat_1(esk3_0)),esk1_0) = k7_relat_1(X1,k1_relat_1(esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( k7_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k7_relat_1(esk3_0,esk1_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_16,negated_conjecture,
    ( k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0)) != k7_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( k7_relat_1(esk3_0,k6_subset_1(esk1_0,X1)) = k6_subset_1(esk3_0,k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_13])])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:01:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.20/0.37  # and selection function SelectCQIPrecWNTNp.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t211_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(k1_relat_1(X3),X1)=>k6_subset_1(X3,k7_relat_1(X3,X2))=k7_relat_1(X3,k6_subset_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 0.20/0.37  fof(t102_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 0.20/0.37  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.20/0.37  fof(t109_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(X3,k6_subset_1(X1,X2))=k6_subset_1(k7_relat_1(X3,X1),k7_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 0.20/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(k1_relat_1(X3),X1)=>k6_subset_1(X3,k7_relat_1(X3,X2))=k7_relat_1(X3,k6_subset_1(X1,X2))))), inference(assume_negation,[status(cth)],[t211_relat_1])).
% 0.20/0.37  fof(c_0_5, plain, ![X6, X7, X8]:(~v1_relat_1(X8)|(~r1_tarski(X6,X7)|k7_relat_1(k7_relat_1(X8,X6),X7)=k7_relat_1(X8,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t102_relat_1])])).
% 0.20/0.37  fof(c_0_6, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(k1_relat_1(esk3_0),esk1_0)&k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0))!=k7_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.20/0.37  cnf(c_0_7, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.37  cnf(c_0_8, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  fof(c_0_9, plain, ![X12]:(~v1_relat_1(X12)|k7_relat_1(X12,k1_relat_1(X12))=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.20/0.37  fof(c_0_10, plain, ![X9, X10, X11]:(~v1_relat_1(X11)|k7_relat_1(X11,k6_subset_1(X9,X10))=k6_subset_1(k7_relat_1(X11,X9),k7_relat_1(X11,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_relat_1])])).
% 0.20/0.37  cnf(c_0_11, negated_conjecture, (k7_relat_1(k7_relat_1(X1,k1_relat_1(esk3_0)),esk1_0)=k7_relat_1(X1,k1_relat_1(esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.20/0.37  cnf(c_0_12, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_14, plain, (k7_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k7_relat_1(X1,X2),k7_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_15, negated_conjecture, (k7_relat_1(esk3_0,esk1_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.20/0.37  cnf(c_0_16, negated_conjecture, (k6_subset_1(esk3_0,k7_relat_1(esk3_0,esk2_0))!=k7_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.37  cnf(c_0_17, negated_conjecture, (k7_relat_1(esk3_0,k6_subset_1(esk1_0,X1))=k6_subset_1(esk3_0,k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_13])])).
% 0.20/0.37  cnf(c_0_18, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 19
% 0.20/0.37  # Proof object clause steps            : 10
% 0.20/0.37  # Proof object formula steps           : 9
% 0.20/0.37  # Proof object conjectures             : 10
% 0.20/0.37  # Proof object clause conjectures      : 7
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 6
% 0.20/0.37  # Proof object initial formulas used   : 4
% 0.20/0.37  # Proof object generating inferences   : 3
% 0.20/0.37  # Proof object simplifying inferences  : 6
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 5
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 7
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 7
% 0.20/0.37  # Processed clauses                    : 19
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 19
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 2
% 0.20/0.37  # Generated clauses                    : 19
% 0.20/0.37  # ...of the previous two non-trivial   : 15
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 18
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 1
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 10
% 0.20/0.37  #    Positive orientable unit clauses  : 4
% 0.20/0.37  #    Positive unorientable unit clauses: 1
% 0.20/0.37  #    Negative unit clauses             : 0
% 0.20/0.37  #    Non-unit-clauses                  : 5
% 0.20/0.37  # Current number of unprocessed clauses: 10
% 0.20/0.37  # ...number of literals in the above   : 16
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 9
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 1
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 1
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 1
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 2
% 0.20/0.37  # BW rewrite match successes           : 2
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 799
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.026 s
% 0.20/0.37  # System time              : 0.005 s
% 0.20/0.37  # Total time               : 0.031 s
% 0.20/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
