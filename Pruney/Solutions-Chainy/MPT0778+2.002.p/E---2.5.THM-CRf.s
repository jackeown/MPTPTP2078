%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:47 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   14 (  20 expanded)
%              Number of clauses        :    7 (   8 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  34 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k2_wellord1(k2_wellord1(X3,X1),X2) = k2_wellord1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t27_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k2_wellord1(k2_wellord1(X3,X1),X2) = k2_wellord1(k2_wellord1(X3,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

fof(c_0_3,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_relat_1(X8)
      | k2_wellord1(k2_wellord1(X8,X6),X7) = k2_wellord1(X8,k3_xboole_0(X6,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_wellord1])])).

fof(c_0_4,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => k2_wellord1(k2_wellord1(X3,X1),X2) = k2_wellord1(k2_wellord1(X3,X2),X1) ) ),
    inference(assume_negation,[status(cth)],[t27_wellord1])).

cnf(c_0_6,plain,
    ( k2_wellord1(k2_wellord1(X1,X2),X3) = k2_wellord1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & k2_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0) != k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( k2_wellord1(X1,k3_xboole_0(X2,X3)) = k2_wellord1(k2_wellord1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( k2_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0) != k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k2_wellord1(k2_wellord1(X1,X2),X3) = k2_wellord1(k2_wellord1(X1,X3),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:38:16 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.12/0.36  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.025 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t26_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k2_wellord1(k2_wellord1(X3,X1),X2)=k2_wellord1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 0.12/0.36  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.12/0.36  fof(t27_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>k2_wellord1(k2_wellord1(X3,X1),X2)=k2_wellord1(k2_wellord1(X3,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_wellord1)).
% 0.12/0.36  fof(c_0_3, plain, ![X6, X7, X8]:(~v1_relat_1(X8)|k2_wellord1(k2_wellord1(X8,X6),X7)=k2_wellord1(X8,k3_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_wellord1])])).
% 0.12/0.36  fof(c_0_4, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.12/0.36  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>k2_wellord1(k2_wellord1(X3,X1),X2)=k2_wellord1(k2_wellord1(X3,X2),X1))), inference(assume_negation,[status(cth)],[t27_wellord1])).
% 0.12/0.36  cnf(c_0_6, plain, (k2_wellord1(k2_wellord1(X1,X2),X3)=k2_wellord1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.36  cnf(c_0_7, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  fof(c_0_8, negated_conjecture, (v1_relat_1(esk3_0)&k2_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0)!=k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.12/0.36  cnf(c_0_9, plain, (k2_wellord1(X1,k3_xboole_0(X2,X3))=k2_wellord1(k2_wellord1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.12/0.36  cnf(c_0_10, negated_conjecture, (k2_wellord1(k2_wellord1(esk3_0,esk1_0),esk2_0)!=k2_wellord1(k2_wellord1(esk3_0,esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.36  cnf(c_0_11, plain, (k2_wellord1(k2_wellord1(X1,X2),X3)=k2_wellord1(k2_wellord1(X1,X3),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_6, c_0_9])).
% 0.12/0.36  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.36  cnf(c_0_13, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 14
% 0.12/0.36  # Proof object clause steps            : 7
% 0.12/0.36  # Proof object formula steps           : 7
% 0.12/0.36  # Proof object conjectures             : 6
% 0.12/0.36  # Proof object clause conjectures      : 3
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 4
% 0.12/0.36  # Proof object initial formulas used   : 3
% 0.12/0.36  # Proof object generating inferences   : 3
% 0.12/0.36  # Proof object simplifying inferences  : 2
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 3
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 4
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 4
% 0.12/0.36  # Processed clauses                    : 13
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 3
% 0.12/0.36  # ...remaining for further processing  : 10
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 0
% 0.12/0.36  # Generated clauses                    : 19
% 0.12/0.36  # ...of the previous two non-trivial   : 9
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 19
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 6
% 0.12/0.36  #    Positive orientable unit clauses  : 1
% 0.12/0.36  #    Positive unorientable unit clauses: 1
% 0.12/0.36  #    Negative unit clauses             : 1
% 0.12/0.36  #    Non-unit-clauses                  : 3
% 0.12/0.36  # Current number of unprocessed clauses: 0
% 0.12/0.36  # ...number of literals in the above   : 0
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 4
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 7
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 7
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 3
% 0.12/0.36  # Unit Clause-clause subsumption calls : 0
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 0
% 0.12/0.36  # BW rewrite match successes           : 0
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 474
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.025 s
% 0.12/0.36  # System time              : 0.004 s
% 0.12/0.36  # Total time               : 0.029 s
% 0.12/0.36  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
