%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:34:56 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   18 (  43 expanded)
%              Number of clauses        :    9 (  18 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  43 expanded)
%              Number of equality atoms :   17 (  42 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t111_xboole_1,conjecture,(
    ! [X1,X2,X3] : k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] : k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k4_xboole_0(X1,X3),X2) ),
    inference(assume_negation,[status(cth)],[t111_xboole_1])).

fof(c_0_5,negated_conjecture,(
    k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk3_0,esk2_0)) != k3_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_7,plain,(
    ! [X10,X11,X12] : k3_xboole_0(X10,k4_xboole_0(X11,X12)) = k4_xboole_0(k3_xboole_0(X10,X11),X12) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_8,negated_conjecture,
    ( k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk3_0,esk2_0)) != k3_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k3_xboole_0(X8,X9)) = k4_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

cnf(c_0_12,negated_conjecture,
    ( k4_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(esk2_0,esk3_0)) != k3_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8,c_0_9]),c_0_9]),c_0_9])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k3_xboole_0(X2,k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_9]),c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( k3_xboole_0(esk2_0,k4_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))) != k3_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,X3))) = k3_xboole_0(X2,k4_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_13])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:02:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic U_____1261_C10_01_F1_AE_CS_SP_PS_RG_ND_S2S
% 0.19/0.36  # and selection function SelectNewComplexAHP.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.021 s
% 0.19/0.36  # Presaturation interreduction done
% 0.19/0.36  
% 0.19/0.36  # Proof found!
% 0.19/0.36  # SZS status Theorem
% 0.19/0.36  # SZS output start CNFRefutation
% 0.19/0.36  fof(t111_xboole_1, conjecture, ![X1, X2, X3]:k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k4_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_xboole_1)).
% 0.19/0.36  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.36  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.19/0.36  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.19/0.36  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k4_xboole_0(X1,X3),X2)), inference(assume_negation,[status(cth)],[t111_xboole_1])).
% 0.19/0.36  fof(c_0_5, negated_conjecture, k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk3_0,esk2_0))!=k3_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.19/0.36  fof(c_0_6, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.36  fof(c_0_7, plain, ![X10, X11, X12]:k3_xboole_0(X10,k4_xboole_0(X11,X12))=k4_xboole_0(k3_xboole_0(X10,X11),X12), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.19/0.36  cnf(c_0_8, negated_conjecture, (k4_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk3_0,esk2_0))!=k3_xboole_0(k4_xboole_0(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.36  cnf(c_0_9, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.36  cnf(c_0_10, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.36  fof(c_0_11, plain, ![X8, X9]:k4_xboole_0(X8,k3_xboole_0(X8,X9))=k4_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.19/0.36  cnf(c_0_12, negated_conjecture, (k4_xboole_0(k3_xboole_0(esk2_0,esk1_0),k3_xboole_0(esk2_0,esk3_0))!=k3_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8, c_0_9]), c_0_9]), c_0_9])).
% 0.19/0.36  cnf(c_0_13, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k3_xboole_0(X2,k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_9]), c_0_10])).
% 0.19/0.36  cnf(c_0_14, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.36  cnf(c_0_15, negated_conjecture, (k3_xboole_0(esk2_0,k4_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)))!=k3_xboole_0(esk2_0,k4_xboole_0(esk1_0,esk3_0))), inference(rw,[status(thm)],[c_0_12, c_0_10])).
% 0.19/0.36  cnf(c_0_16, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X1,X3)))=k3_xboole_0(X2,k4_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.36  cnf(c_0_17, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_13])]), ['proof']).
% 0.19/0.36  # SZS output end CNFRefutation
% 0.19/0.36  # Proof object total steps             : 18
% 0.19/0.36  # Proof object clause steps            : 9
% 0.19/0.36  # Proof object formula steps           : 9
% 0.19/0.36  # Proof object conjectures             : 7
% 0.19/0.36  # Proof object clause conjectures      : 4
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 4
% 0.19/0.36  # Proof object initial formulas used   : 4
% 0.19/0.36  # Proof object generating inferences   : 2
% 0.19/0.36  # Proof object simplifying inferences  : 8
% 0.19/0.36  # Training examples: 0 positive, 0 negative
% 0.19/0.36  # Parsed axioms                        : 5
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 5
% 0.19/0.36  # Removed in clause preprocessing      : 0
% 0.19/0.36  # Initial clauses in saturation        : 5
% 0.19/0.36  # Processed clauses                    : 47
% 0.19/0.36  # ...of these trivial                  : 7
% 0.19/0.36  # ...subsumed                          : 17
% 0.19/0.36  # ...remaining for further processing  : 23
% 0.19/0.36  # Other redundant clauses eliminated   : 0
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 0
% 0.19/0.36  # Backward-rewritten                   : 3
% 0.19/0.36  # Generated clauses                    : 218
% 0.19/0.36  # ...of the previous two non-trivial   : 177
% 0.19/0.36  # Contextual simplify-reflections      : 0
% 0.19/0.36  # Paramodulations                      : 218
% 0.19/0.36  # Factorizations                       : 0
% 0.19/0.36  # Equation resolutions                 : 0
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 15
% 0.19/0.36  #    Positive orientable unit clauses  : 10
% 0.19/0.36  #    Positive unorientable unit clauses: 5
% 0.19/0.36  #    Negative unit clauses             : 0
% 0.19/0.36  #    Non-unit-clauses                  : 0
% 0.19/0.36  # Current number of unprocessed clauses: 140
% 0.19/0.36  # ...number of literals in the above   : 140
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 8
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.36  # Unit Clause-clause subsumption calls : 16
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 77
% 0.19/0.36  # BW rewrite match successes           : 28
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 2005
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.022 s
% 0.19/0.36  # System time              : 0.004 s
% 0.19/0.36  # Total time               : 0.026 s
% 0.19/0.36  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
