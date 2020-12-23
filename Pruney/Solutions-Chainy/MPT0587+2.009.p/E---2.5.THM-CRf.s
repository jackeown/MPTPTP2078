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
% DateTime   : Thu Dec  3 10:52:01 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   18 (  24 expanded)
%              Number of clauses        :    9 (  10 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  37 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t191_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,k6_subset_1(k1_relat_1(X2),X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => k1_relat_1(k7_relat_1(X2,k6_subset_1(k1_relat_1(X2),X1))) = k6_subset_1(k1_relat_1(X2),X1) ) ),
    inference(assume_negation,[status(cth)],[t191_relat_1])).

fof(c_0_5,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | ~ r1_tarski(X7,k1_relat_1(X8))
      | k1_relat_1(k7_relat_1(X8,X7)) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_6,plain,(
    ! [X3,X4] : r1_tarski(k4_xboole_0(X3,X4),X3) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & k1_relat_1(k7_relat_1(esk2_0,k6_subset_1(k1_relat_1(esk2_0),esk1_0))) != k6_subset_1(k1_relat_1(esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_8,plain,(
    ! [X5,X6] : k6_subset_1(X5,X6) = k4_xboole_0(X5,X6) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_9,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k6_subset_1(k1_relat_1(esk2_0),esk1_0))) != k6_subset_1(k1_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k1_relat_1(k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X2))) = k4_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k4_xboole_0(k1_relat_1(esk2_0),esk1_0))) != k4_xboole_0(k1_relat_1(esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k4_xboole_0(k1_relat_1(esk2_0),X1))) = k4_xboole_0(k1_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:47:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S070I
% 0.21/0.39  # and selection function SelectVGNonCR.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.039 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t191_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,k6_subset_1(k1_relat_1(X2),X1)))=k6_subset_1(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_relat_1)).
% 0.21/0.39  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.21/0.39  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.21/0.39  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.21/0.39  fof(c_0_4, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,k6_subset_1(k1_relat_1(X2),X1)))=k6_subset_1(k1_relat_1(X2),X1))), inference(assume_negation,[status(cth)],[t191_relat_1])).
% 0.21/0.39  fof(c_0_5, plain, ![X7, X8]:(~v1_relat_1(X8)|(~r1_tarski(X7,k1_relat_1(X8))|k1_relat_1(k7_relat_1(X8,X7))=X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.21/0.39  fof(c_0_6, plain, ![X3, X4]:r1_tarski(k4_xboole_0(X3,X4),X3), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.21/0.39  fof(c_0_7, negated_conjecture, (v1_relat_1(esk2_0)&k1_relat_1(k7_relat_1(esk2_0,k6_subset_1(k1_relat_1(esk2_0),esk1_0)))!=k6_subset_1(k1_relat_1(esk2_0),esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.21/0.39  fof(c_0_8, plain, ![X5, X6]:k6_subset_1(X5,X6)=k4_xboole_0(X5,X6), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.21/0.39  cnf(c_0_9, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.39  cnf(c_0_10, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_11, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k6_subset_1(k1_relat_1(esk2_0),esk1_0)))!=k6_subset_1(k1_relat_1(esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.39  cnf(c_0_12, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  cnf(c_0_13, plain, (k1_relat_1(k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X2)))=k4_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.21/0.39  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.39  cnf(c_0_15, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k4_xboole_0(k1_relat_1(esk2_0),esk1_0)))!=k4_xboole_0(k1_relat_1(esk2_0),esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_12])).
% 0.21/0.39  cnf(c_0_16, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k4_xboole_0(k1_relat_1(esk2_0),X1)))=k4_xboole_0(k1_relat_1(esk2_0),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.39  cnf(c_0_17, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 18
% 0.21/0.39  # Proof object clause steps            : 9
% 0.21/0.39  # Proof object formula steps           : 9
% 0.21/0.39  # Proof object conjectures             : 8
% 0.21/0.39  # Proof object clause conjectures      : 5
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 5
% 0.21/0.39  # Proof object initial formulas used   : 4
% 0.21/0.39  # Proof object generating inferences   : 2
% 0.21/0.39  # Proof object simplifying inferences  : 4
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 4
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 5
% 0.21/0.39  # Removed in clause preprocessing      : 1
% 0.21/0.39  # Initial clauses in saturation        : 4
% 0.21/0.39  # Processed clauses                    : 10
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 0
% 0.21/0.39  # ...remaining for further processing  : 10
% 0.21/0.39  # Other redundant clauses eliminated   : 0
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 1
% 0.21/0.39  # Generated clauses                    : 3
% 0.21/0.39  # ...of the previous two non-trivial   : 2
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 3
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 0
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 5
% 0.21/0.39  #    Positive orientable unit clauses  : 3
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 0
% 0.21/0.39  #    Non-unit-clauses                  : 2
% 0.21/0.39  # Current number of unprocessed clauses: 0
% 0.21/0.39  # ...number of literals in the above   : 0
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 6
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 0
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.39  # Unit Clause-clause subsumption calls : 0
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 1
% 0.21/0.39  # BW rewrite match successes           : 1
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 364
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.037 s
% 0.21/0.39  # System time              : 0.006 s
% 0.21/0.39  # Total time               : 0.043 s
% 0.21/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
