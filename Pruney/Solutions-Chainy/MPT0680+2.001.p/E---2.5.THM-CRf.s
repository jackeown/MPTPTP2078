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
% DateTime   : Thu Dec  3 10:54:26 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   19 (  45 expanded)
%              Number of clauses        :   10 (  16 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :    5
%              Number of atoms          :   40 ( 102 expanded)
%              Number of equality atoms :   15 (  41 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t124_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ! [X2,X3] : k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_funct_1)).

fof(t122_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ! [X2,X3] : k9_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_funct_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( ! [X2,X3] : k9_relat_1(X1,k6_subset_1(X2,X3)) = k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
         => v2_funct_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t124_funct_1])).

fof(c_0_5,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | k9_relat_1(X8,k3_xboole_0(esk1_1(X8),esk2_1(X8))) != k3_xboole_0(k9_relat_1(X8,esk1_1(X8)),k9_relat_1(X8,esk2_1(X8)))
      | v2_funct_1(X8) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t122_funct_1])])])).

fof(c_0_6,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,X5) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_7,negated_conjecture,(
    ! [X12,X13] :
      ( v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & k9_relat_1(esk3_0,k6_subset_1(X12,X13)) = k6_subset_1(k9_relat_1(esk3_0,X12),k9_relat_1(esk3_0,X13))
      & ~ v2_funct_1(esk3_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_8,plain,(
    ! [X6,X7] : k6_subset_1(X6,X7) = k4_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_9,plain,
    ( v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k9_relat_1(X1,k3_xboole_0(esk1_1(X1),esk2_1(X1))) != k3_xboole_0(k9_relat_1(X1,esk1_1(X1)),k9_relat_1(X1,esk2_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( k9_relat_1(esk3_0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( v2_funct_1(X1)
    | k9_relat_1(X1,k4_xboole_0(esk1_1(X1),k4_xboole_0(esk1_1(X1),esk2_1(X1)))) != k4_xboole_0(k9_relat_1(X1,esk1_1(X1)),k4_xboole_0(k9_relat_1(X1,esk1_1(X1)),k9_relat_1(X1,esk2_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( k9_relat_1(esk3_0,k4_xboole_0(X1,X2)) = k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])]),c_0_17]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 12:18:27 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.36  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S070I
% 0.14/0.36  # and selection function SelectVGNonCR.
% 0.14/0.36  #
% 0.14/0.36  # Preprocessing time       : 0.026 s
% 0.14/0.36  # Presaturation interreduction done
% 0.14/0.36  
% 0.14/0.36  # Proof found!
% 0.14/0.36  # SZS status Theorem
% 0.14/0.36  # SZS output start CNFRefutation
% 0.14/0.36  fof(t124_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(![X2, X3]:k9_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))=>v2_funct_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_funct_1)).
% 0.14/0.36  fof(t122_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(![X2, X3]:k9_relat_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))=>v2_funct_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t122_funct_1)).
% 0.14/0.36  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.14/0.36  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.14/0.36  fof(c_0_4, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(![X2, X3]:k9_relat_1(X1,k6_subset_1(X2,X3))=k6_subset_1(k9_relat_1(X1,X2),k9_relat_1(X1,X3))=>v2_funct_1(X1)))), inference(assume_negation,[status(cth)],[t124_funct_1])).
% 0.14/0.36  fof(c_0_5, plain, ![X8]:(~v1_relat_1(X8)|~v1_funct_1(X8)|(k9_relat_1(X8,k3_xboole_0(esk1_1(X8),esk2_1(X8)))!=k3_xboole_0(k9_relat_1(X8,esk1_1(X8)),k9_relat_1(X8,esk2_1(X8)))|v2_funct_1(X8))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t122_funct_1])])])).
% 0.14/0.36  fof(c_0_6, plain, ![X4, X5]:k4_xboole_0(X4,k4_xboole_0(X4,X5))=k3_xboole_0(X4,X5), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.14/0.36  fof(c_0_7, negated_conjecture, ![X12, X13]:((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(k9_relat_1(esk3_0,k6_subset_1(X12,X13))=k6_subset_1(k9_relat_1(esk3_0,X12),k9_relat_1(esk3_0,X13))&~v2_funct_1(esk3_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.14/0.36  fof(c_0_8, plain, ![X6, X7]:k6_subset_1(X6,X7)=k4_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.14/0.36  cnf(c_0_9, plain, (v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|k9_relat_1(X1,k3_xboole_0(esk1_1(X1),esk2_1(X1)))!=k3_xboole_0(k9_relat_1(X1,esk1_1(X1)),k9_relat_1(X1,esk2_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.36  cnf(c_0_10, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.36  cnf(c_0_11, negated_conjecture, (k9_relat_1(esk3_0,k6_subset_1(X1,X2))=k6_subset_1(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.36  cnf(c_0_12, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.36  cnf(c_0_13, negated_conjecture, (~v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.36  cnf(c_0_14, plain, (v2_funct_1(X1)|k9_relat_1(X1,k4_xboole_0(esk1_1(X1),k4_xboole_0(esk1_1(X1),esk2_1(X1))))!=k4_xboole_0(k9_relat_1(X1,esk1_1(X1)),k4_xboole_0(k9_relat_1(X1,esk1_1(X1)),k9_relat_1(X1,esk2_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_10]), c_0_10])).
% 0.14/0.36  cnf(c_0_15, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.36  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.36  cnf(c_0_17, negated_conjecture, (k9_relat_1(esk3_0,k4_xboole_0(X1,X2))=k4_xboole_0(k9_relat_1(esk3_0,X1),k9_relat_1(esk3_0,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_12])).
% 0.14/0.36  cnf(c_0_18, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])]), c_0_17]), c_0_17])]), ['proof']).
% 0.14/0.36  # SZS output end CNFRefutation
% 0.14/0.36  # Proof object total steps             : 19
% 0.14/0.36  # Proof object clause steps            : 10
% 0.14/0.36  # Proof object formula steps           : 9
% 0.14/0.36  # Proof object conjectures             : 9
% 0.14/0.36  # Proof object clause conjectures      : 6
% 0.14/0.36  # Proof object formula conjectures     : 3
% 0.14/0.36  # Proof object initial clauses used    : 7
% 0.14/0.36  # Proof object initial formulas used   : 4
% 0.14/0.36  # Proof object generating inferences   : 1
% 0.14/0.36  # Proof object simplifying inferences  : 10
% 0.14/0.36  # Training examples: 0 positive, 0 negative
% 0.14/0.36  # Parsed axioms                        : 4
% 0.14/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.36  # Initial clauses                      : 7
% 0.14/0.36  # Removed in clause preprocessing      : 2
% 0.14/0.36  # Initial clauses in saturation        : 5
% 0.14/0.36  # Processed clauses                    : 11
% 0.14/0.36  # ...of these trivial                  : 0
% 0.14/0.36  # ...subsumed                          : 0
% 0.14/0.36  # ...remaining for further processing  : 10
% 0.14/0.36  # Other redundant clauses eliminated   : 0
% 0.14/0.36  # Clauses deleted for lack of memory   : 0
% 0.14/0.36  # Backward-subsumed                    : 0
% 0.14/0.36  # Backward-rewritten                   : 0
% 0.14/0.36  # Generated clauses                    : 1
% 0.14/0.36  # ...of the previous two non-trivial   : 1
% 0.14/0.36  # Contextual simplify-reflections      : 0
% 0.14/0.36  # Paramodulations                      : 1
% 0.14/0.36  # Factorizations                       : 0
% 0.14/0.36  # Equation resolutions                 : 0
% 0.14/0.36  # Propositional unsat checks           : 0
% 0.14/0.36  #    Propositional check models        : 0
% 0.14/0.36  #    Propositional check unsatisfiable : 0
% 0.14/0.36  #    Propositional clauses             : 0
% 0.14/0.36  #    Propositional clauses after purity: 0
% 0.14/0.36  #    Propositional unsat core size     : 0
% 0.14/0.36  #    Propositional preprocessing time  : 0.000
% 0.14/0.36  #    Propositional encoding time       : 0.000
% 0.14/0.36  #    Propositional solver time         : 0.000
% 0.14/0.36  #    Success case prop preproc time    : 0.000
% 0.14/0.36  #    Success case prop encoding time   : 0.000
% 0.14/0.36  #    Success case prop solver time     : 0.000
% 0.14/0.36  # Current number of processed clauses  : 5
% 0.14/0.36  #    Positive orientable unit clauses  : 3
% 0.14/0.36  #    Positive unorientable unit clauses: 0
% 0.14/0.36  #    Negative unit clauses             : 1
% 0.14/0.36  #    Non-unit-clauses                  : 1
% 0.14/0.36  # Current number of unprocessed clauses: 0
% 0.14/0.36  # ...number of literals in the above   : 0
% 0.14/0.36  # Current number of archived formulas  : 0
% 0.14/0.36  # Current number of archived clauses   : 7
% 0.14/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.36  # Unit Clause-clause subsumption calls : 0
% 0.14/0.36  # Rewrite failures with RHS unbound    : 0
% 0.14/0.36  # BW rewrite match attempts            : 0
% 0.14/0.36  # BW rewrite match successes           : 0
% 0.14/0.36  # Condensation attempts                : 0
% 0.14/0.36  # Condensation successes               : 0
% 0.14/0.36  # Termbank termtop insertions          : 527
% 0.14/0.36  
% 0.14/0.36  # -------------------------------------------------
% 0.14/0.36  # User time                : 0.025 s
% 0.14/0.36  # System time              : 0.004 s
% 0.14/0.36  # Total time               : 0.029 s
% 0.14/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
