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
% DateTime   : Thu Dec  3 10:35:29 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   30 (  49 expanded)
%              Number of clauses        :   15 (  22 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  49 expanded)
%              Number of equality atoms :   29 (  48 expanded)
%              Maximal formula depth    :    3 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t69_enumset1,conjecture,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_7,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k5_xboole_0(X10,k4_xboole_0(X11,X10)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_8,plain,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(assume_negation,[status(cth)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_xboole_0(k1_tarski(X12),k1_tarski(X13)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_14,plain,(
    ! [X7] : k4_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_15,negated_conjecture,(
    k2_tarski(esk1_0,esk1_0) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X3,X4] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,X3) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_21,negated_conjecture,
    ( k2_tarski(esk1_0,esk1_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_12]),c_0_12])).

cnf(c_0_24,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_19,c_0_12])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk1_0),k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk1_0)))) != k1_tarski(esk1_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_25]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:11:50 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.17/0.33  # Version: 2.5pre002
% 0.17/0.33  # No SInE strategy applied
% 0.17/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.34  # AutoSched0-Mode selected heuristic U_____102_C09_12_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.17/0.34  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.17/0.34  #
% 0.17/0.34  # Preprocessing time       : 0.012 s
% 0.17/0.34  # Presaturation interreduction done
% 0.17/0.34  
% 0.17/0.34  # Proof found!
% 0.17/0.34  # SZS status Theorem
% 0.17/0.34  # SZS output start CNFRefutation
% 0.17/0.34  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.17/0.34  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.17/0.34  fof(t69_enumset1, conjecture, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.17/0.34  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.17/0.34  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.17/0.34  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.17/0.34  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.17/0.34  fof(c_0_7, plain, ![X10, X11]:k2_xboole_0(X10,X11)=k5_xboole_0(X10,k4_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.17/0.34  fof(c_0_8, plain, ![X5, X6]:k4_xboole_0(X5,X6)=k5_xboole_0(X5,k3_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.17/0.34  fof(c_0_9, negated_conjecture, ~(![X1]:k2_tarski(X1,X1)=k1_tarski(X1)), inference(assume_negation,[status(cth)],[t69_enumset1])).
% 0.17/0.34  fof(c_0_10, plain, ![X12, X13]:k2_tarski(X12,X13)=k2_xboole_0(k1_tarski(X12),k1_tarski(X13)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.17/0.34  cnf(c_0_11, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.34  cnf(c_0_12, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.34  fof(c_0_13, plain, ![X8, X9]:k4_xboole_0(X8,k4_xboole_0(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.17/0.34  fof(c_0_14, plain, ![X7]:k4_xboole_0(X7,k1_xboole_0)=X7, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.17/0.34  fof(c_0_15, negated_conjecture, k2_tarski(esk1_0,esk1_0)!=k1_tarski(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.17/0.34  cnf(c_0_16, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.34  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.17/0.34  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.34  cnf(c_0_19, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.34  fof(c_0_20, plain, ![X3, X4]:k3_xboole_0(X3,X4)=k3_xboole_0(X4,X3), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.17/0.34  cnf(c_0_21, negated_conjecture, (k2_tarski(esk1_0,esk1_0)!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.34  cnf(c_0_22, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.17/0.34  cnf(c_0_23, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_12]), c_0_12])).
% 0.17/0.34  cnf(c_0_24, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_19, c_0_12])).
% 0.17/0.34  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.17/0.34  cnf(c_0_26, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk1_0),k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk1_0))))!=k1_tarski(esk1_0)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.17/0.34  cnf(c_0_27, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k3_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.17/0.34  cnf(c_0_28, plain, (k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.17/0.34  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_25]), c_0_28])]), ['proof']).
% 0.17/0.34  # SZS output end CNFRefutation
% 0.17/0.34  # Proof object total steps             : 30
% 0.17/0.34  # Proof object clause steps            : 15
% 0.17/0.34  # Proof object formula steps           : 15
% 0.17/0.34  # Proof object conjectures             : 6
% 0.17/0.34  # Proof object clause conjectures      : 3
% 0.17/0.34  # Proof object formula conjectures     : 3
% 0.17/0.34  # Proof object initial clauses used    : 7
% 0.17/0.34  # Proof object initial formulas used   : 7
% 0.17/0.34  # Proof object generating inferences   : 2
% 0.17/0.34  # Proof object simplifying inferences  : 10
% 0.17/0.34  # Training examples: 0 positive, 0 negative
% 0.17/0.34  # Parsed axioms                        : 7
% 0.17/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.34  # Initial clauses                      : 7
% 0.17/0.34  # Removed in clause preprocessing      : 3
% 0.17/0.34  # Initial clauses in saturation        : 4
% 0.17/0.34  # Processed clauses                    : 14
% 0.17/0.34  # ...of these trivial                  : 2
% 0.17/0.34  # ...subsumed                          : 0
% 0.17/0.34  # ...remaining for further processing  : 12
% 0.17/0.34  # Other redundant clauses eliminated   : 0
% 0.17/0.34  # Clauses deleted for lack of memory   : 0
% 0.17/0.34  # Backward-subsumed                    : 0
% 0.17/0.34  # Backward-rewritten                   : 1
% 0.17/0.34  # Generated clauses                    : 22
% 0.17/0.34  # ...of the previous two non-trivial   : 12
% 0.17/0.34  # Contextual simplify-reflections      : 0
% 0.17/0.34  # Paramodulations                      : 22
% 0.17/0.34  # Factorizations                       : 0
% 0.17/0.34  # Equation resolutions                 : 0
% 0.17/0.34  # Propositional unsat checks           : 0
% 0.17/0.34  #    Propositional check models        : 0
% 0.17/0.34  #    Propositional check unsatisfiable : 0
% 0.17/0.34  #    Propositional clauses             : 0
% 0.17/0.34  #    Propositional clauses after purity: 0
% 0.17/0.34  #    Propositional unsat core size     : 0
% 0.17/0.34  #    Propositional preprocessing time  : 0.000
% 0.17/0.34  #    Propositional encoding time       : 0.000
% 0.17/0.34  #    Propositional solver time         : 0.000
% 0.17/0.34  #    Success case prop preproc time    : 0.000
% 0.17/0.34  #    Success case prop encoding time   : 0.000
% 0.17/0.34  #    Success case prop solver time     : 0.000
% 0.17/0.34  # Current number of processed clauses  : 7
% 0.17/0.34  #    Positive orientable unit clauses  : 6
% 0.17/0.34  #    Positive unorientable unit clauses: 1
% 0.17/0.34  #    Negative unit clauses             : 0
% 0.17/0.34  #    Non-unit-clauses                  : 0
% 0.17/0.34  # Current number of unprocessed clauses: 6
% 0.17/0.34  # ...number of literals in the above   : 6
% 0.17/0.34  # Current number of archived formulas  : 0
% 0.17/0.34  # Current number of archived clauses   : 8
% 0.17/0.34  # Clause-clause subsumption calls (NU) : 0
% 0.17/0.34  # Rec. Clause-clause subsumption calls : 0
% 0.17/0.34  # Non-unit clause-clause subsumptions  : 0
% 0.17/0.34  # Unit Clause-clause subsumption calls : 0
% 0.17/0.34  # Rewrite failures with RHS unbound    : 0
% 0.17/0.34  # BW rewrite match attempts            : 11
% 0.17/0.34  # BW rewrite match successes           : 7
% 0.17/0.34  # Condensation attempts                : 0
% 0.17/0.34  # Condensation successes               : 0
% 0.17/0.34  # Termbank termtop insertions          : 439
% 0.17/0.34  
% 0.17/0.34  # -------------------------------------------------
% 0.17/0.34  # User time                : 0.015 s
% 0.17/0.34  # System time              : 0.000 s
% 0.17/0.34  # Total time               : 0.015 s
% 0.17/0.34  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
