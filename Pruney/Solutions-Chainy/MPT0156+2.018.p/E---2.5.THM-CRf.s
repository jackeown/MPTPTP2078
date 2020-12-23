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
% DateTime   : Thu Dec  3 10:35:43 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   22 (  28 expanded)
%              Number of clauses        :    9 (  11 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  28 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_enumset1,conjecture,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(assume_negation,[status(cth)],[t72_enumset1])).

fof(c_0_7,plain,(
    ! [X8,X9,X10,X11] : k2_enumset1(X8,X9,X10,X11) = k2_xboole_0(k1_tarski(X8),k1_enumset1(X9,X10,X11)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_8,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_9,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_10,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k5_xboole_0(X6,k4_xboole_0(X7,X6)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_11,plain,(
    ! [X12,X13,X14,X15,X16] : k3_enumset1(X12,X13,X14,X15,X16) = k2_xboole_0(k2_tarski(X12,X13),k1_enumset1(X14,X15,X16)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

fof(c_0_12,negated_conjecture,(
    k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_13,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0) != k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_20,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_15]),c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n002.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 17:12:51 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.11/0.34  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 0.11/0.34  # and selection function SelectNewComplexAHP.
% 0.11/0.34  #
% 0.11/0.34  # Preprocessing time       : 0.026 s
% 0.11/0.34  # Presaturation interreduction done
% 0.11/0.34  
% 0.11/0.34  # Proof found!
% 0.11/0.34  # SZS status Theorem
% 0.11/0.34  # SZS output start CNFRefutation
% 0.11/0.34  fof(t72_enumset1, conjecture, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.11/0.34  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.11/0.34  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.11/0.34  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.11/0.34  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.11/0.34  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 0.11/0.34  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(assume_negation,[status(cth)],[t72_enumset1])).
% 0.11/0.34  fof(c_0_7, plain, ![X8, X9, X10, X11]:k2_enumset1(X8,X9,X10,X11)=k2_xboole_0(k1_tarski(X8),k1_enumset1(X9,X10,X11)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.11/0.34  fof(c_0_8, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.11/0.34  fof(c_0_9, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.11/0.34  fof(c_0_10, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k5_xboole_0(X6,k4_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.11/0.34  fof(c_0_11, plain, ![X12, X13, X14, X15, X16]:k3_enumset1(X12,X13,X14,X15,X16)=k2_xboole_0(k2_tarski(X12,X13),k1_enumset1(X14,X15,X16)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 0.11/0.34  fof(c_0_12, negated_conjecture, k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.11/0.34  cnf(c_0_13, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.11/0.34  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.11/0.34  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.34  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.34  cnf(c_0_17, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.34  cnf(c_0_18, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)!=k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.34  cnf(c_0_19, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_enumset1(X1,X1,X1),k4_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])).
% 0.11/0.34  cnf(c_0_20, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_15]), c_0_16])).
% 0.11/0.34  cnf(c_0_21, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])]), ['proof']).
% 0.11/0.34  # SZS output end CNFRefutation
% 0.11/0.34  # Proof object total steps             : 22
% 0.11/0.34  # Proof object clause steps            : 9
% 0.11/0.34  # Proof object formula steps           : 13
% 0.11/0.34  # Proof object conjectures             : 5
% 0.11/0.34  # Proof object clause conjectures      : 2
% 0.11/0.34  # Proof object formula conjectures     : 3
% 0.11/0.34  # Proof object initial clauses used    : 6
% 0.11/0.34  # Proof object initial formulas used   : 6
% 0.11/0.34  # Proof object generating inferences   : 0
% 0.11/0.34  # Proof object simplifying inferences  : 8
% 0.11/0.34  # Training examples: 0 positive, 0 negative
% 0.11/0.34  # Parsed axioms                        : 6
% 0.11/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.34  # Initial clauses                      : 6
% 0.11/0.34  # Removed in clause preprocessing      : 5
% 0.11/0.34  # Initial clauses in saturation        : 1
% 0.11/0.34  # Processed clauses                    : 1
% 0.11/0.34  # ...of these trivial                  : 0
% 0.11/0.34  # ...subsumed                          : 0
% 0.11/0.34  # ...remaining for further processing  : 0
% 0.11/0.34  # Other redundant clauses eliminated   : 0
% 0.11/0.34  # Clauses deleted for lack of memory   : 0
% 0.11/0.34  # Backward-subsumed                    : 0
% 0.11/0.34  # Backward-rewritten                   : 0
% 0.11/0.34  # Generated clauses                    : 0
% 0.11/0.34  # ...of the previous two non-trivial   : 0
% 0.11/0.34  # Contextual simplify-reflections      : 0
% 0.11/0.34  # Paramodulations                      : 0
% 0.11/0.34  # Factorizations                       : 0
% 0.11/0.34  # Equation resolutions                 : 0
% 0.11/0.34  # Propositional unsat checks           : 0
% 0.11/0.34  #    Propositional check models        : 0
% 0.11/0.34  #    Propositional check unsatisfiable : 0
% 0.11/0.34  #    Propositional clauses             : 0
% 0.11/0.34  #    Propositional clauses after purity: 0
% 0.11/0.34  #    Propositional unsat core size     : 0
% 0.11/0.34  #    Propositional preprocessing time  : 0.000
% 0.11/0.34  #    Propositional encoding time       : 0.000
% 0.11/0.34  #    Propositional solver time         : 0.000
% 0.11/0.34  #    Success case prop preproc time    : 0.000
% 0.11/0.34  #    Success case prop encoding time   : 0.000
% 0.11/0.34  #    Success case prop solver time     : 0.000
% 0.11/0.34  # Current number of processed clauses  : 0
% 0.11/0.34  #    Positive orientable unit clauses  : 0
% 0.11/0.34  #    Positive unorientable unit clauses: 0
% 0.11/0.34  #    Negative unit clauses             : 0
% 0.11/0.34  #    Non-unit-clauses                  : 0
% 0.11/0.34  # Current number of unprocessed clauses: 0
% 0.11/0.34  # ...number of literals in the above   : 0
% 0.11/0.34  # Current number of archived formulas  : 0
% 0.11/0.34  # Current number of archived clauses   : 5
% 0.11/0.34  # Clause-clause subsumption calls (NU) : 0
% 0.11/0.34  # Rec. Clause-clause subsumption calls : 0
% 0.11/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.11/0.34  # Unit Clause-clause subsumption calls : 0
% 0.11/0.34  # Rewrite failures with RHS unbound    : 0
% 0.11/0.34  # BW rewrite match attempts            : 0
% 0.11/0.34  # BW rewrite match successes           : 0
% 0.11/0.34  # Condensation attempts                : 0
% 0.11/0.34  # Condensation successes               : 0
% 0.11/0.34  # Termbank termtop insertions          : 269
% 0.11/0.34  
% 0.11/0.34  # -------------------------------------------------
% 0.11/0.34  # User time                : 0.024 s
% 0.11/0.34  # System time              : 0.005 s
% 0.11/0.34  # Total time               : 0.029 s
% 0.11/0.34  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
