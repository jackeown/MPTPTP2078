%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:00 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  46 expanded)
%              Number of clauses        :   15 (  21 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  53 expanded)
%              Number of equality atoms :   11 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t24_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t31_xboole_1,conjecture,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(c_0_6,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X11,X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_7,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_8,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X13,X14,X15] : k2_xboole_0(X13,k3_xboole_0(X14,X15)) = k3_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(X13,X15)) ),
    inference(variable_rename,[status(thm)],[t24_xboole_1])).

fof(c_0_13,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(assume_negation,[status(cth)],[t31_xboole_1])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3)) = k2_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( r1_tarski(k3_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X3,X4))),k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1)) = k2_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk1_0,esk2_0)),k2_xboole_0(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_11]),c_0_18]),c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_xboole_0(X1,X4)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:39:06 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  # Version: 2.5pre002
% 0.13/0.36  # No SInE strategy applied
% 0.13/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.43  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.22/0.43  # and selection function SelectNewComplexAHP.
% 0.22/0.43  #
% 0.22/0.43  # Preprocessing time       : 0.026 s
% 0.22/0.43  # Presaturation interreduction done
% 0.22/0.43  
% 0.22/0.43  # Proof found!
% 0.22/0.43  # SZS status Theorem
% 0.22/0.43  # SZS output start CNFRefutation
% 0.22/0.43  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.22/0.43  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.22/0.43  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.22/0.43  fof(t24_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 0.22/0.43  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.22/0.43  fof(t31_xboole_1, conjecture, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.22/0.43  fof(c_0_6, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X11,X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.22/0.43  fof(c_0_7, plain, ![X8, X9]:r1_tarski(k3_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.22/0.43  fof(c_0_8, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.22/0.43  cnf(c_0_9, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.22/0.43  cnf(c_0_10, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.22/0.43  cnf(c_0_11, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.22/0.43  fof(c_0_12, plain, ![X13, X14, X15]:k2_xboole_0(X13,k3_xboole_0(X14,X15))=k3_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(X13,X15)), inference(variable_rename,[status(thm)],[t24_xboole_1])).
% 0.22/0.43  fof(c_0_13, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.22/0.43  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(assume_negation,[status(cth)],[t31_xboole_1])).
% 0.22/0.43  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.22/0.43  cnf(c_0_16, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.22/0.43  cnf(c_0_17, plain, (k2_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.43  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.22/0.43  fof(c_0_19, negated_conjecture, ~r1_tarski(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.22/0.43  cnf(c_0_20, plain, (r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.22/0.43  cnf(c_0_21, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X3))=k2_xboole_0(X2,k3_xboole_0(X1,X3))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.22/0.43  cnf(c_0_22, negated_conjecture, (~r1_tarski(k2_xboole_0(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk3_0)),k2_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.22/0.43  cnf(c_0_23, plain, (r1_tarski(k3_xboole_0(X1,k2_xboole_0(X2,k3_xboole_0(X3,X4))),k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.22/0.43  cnf(c_0_24, plain, (k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X3,X1))=k2_xboole_0(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.22/0.43  cnf(c_0_25, negated_conjecture, (~r1_tarski(k2_xboole_0(k3_xboole_0(esk3_0,esk1_0),k3_xboole_0(esk1_0,esk2_0)),k2_xboole_0(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_11]), c_0_18]), c_0_18])).
% 0.22/0.43  cnf(c_0_26, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)),k2_xboole_0(X1,X4))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.22/0.43  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26])]), ['proof']).
% 0.22/0.43  # SZS output end CNFRefutation
% 0.22/0.43  # Proof object total steps             : 28
% 0.22/0.43  # Proof object clause steps            : 15
% 0.22/0.43  # Proof object formula steps           : 13
% 0.22/0.43  # Proof object conjectures             : 6
% 0.22/0.43  # Proof object clause conjectures      : 3
% 0.22/0.43  # Proof object formula conjectures     : 3
% 0.22/0.43  # Proof object initial clauses used    : 6
% 0.22/0.43  # Proof object initial formulas used   : 6
% 0.22/0.43  # Proof object generating inferences   : 7
% 0.22/0.43  # Proof object simplifying inferences  : 5
% 0.22/0.43  # Training examples: 0 positive, 0 negative
% 0.22/0.43  # Parsed axioms                        : 6
% 0.22/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.43  # Initial clauses                      : 6
% 0.22/0.43  # Removed in clause preprocessing      : 0
% 0.22/0.43  # Initial clauses in saturation        : 6
% 0.22/0.43  # Processed clauses                    : 473
% 0.22/0.43  # ...of these trivial                  : 244
% 0.22/0.43  # ...subsumed                          : 83
% 0.22/0.43  # ...remaining for further processing  : 146
% 0.22/0.43  # Other redundant clauses eliminated   : 0
% 0.22/0.43  # Clauses deleted for lack of memory   : 0
% 0.22/0.43  # Backward-subsumed                    : 2
% 0.22/0.43  # Backward-rewritten                   : 23
% 0.22/0.43  # Generated clauses                    : 5578
% 0.22/0.43  # ...of the previous two non-trivial   : 4532
% 0.22/0.43  # Contextual simplify-reflections      : 0
% 0.22/0.43  # Paramodulations                      : 5578
% 0.22/0.43  # Factorizations                       : 0
% 0.22/0.43  # Equation resolutions                 : 0
% 0.22/0.43  # Propositional unsat checks           : 0
% 0.22/0.43  #    Propositional check models        : 0
% 0.22/0.43  #    Propositional check unsatisfiable : 0
% 0.22/0.43  #    Propositional clauses             : 0
% 0.22/0.43  #    Propositional clauses after purity: 0
% 0.22/0.43  #    Propositional unsat core size     : 0
% 0.22/0.43  #    Propositional preprocessing time  : 0.000
% 0.22/0.43  #    Propositional encoding time       : 0.000
% 0.22/0.43  #    Propositional solver time         : 0.000
% 0.22/0.43  #    Success case prop preproc time    : 0.000
% 0.22/0.43  #    Success case prop encoding time   : 0.000
% 0.22/0.43  #    Success case prop solver time     : 0.000
% 0.22/0.43  # Current number of processed clauses  : 115
% 0.22/0.43  #    Positive orientable unit clauses  : 97
% 0.22/0.43  #    Positive unorientable unit clauses: 5
% 0.22/0.43  #    Negative unit clauses             : 0
% 0.22/0.43  #    Non-unit-clauses                  : 13
% 0.22/0.43  # Current number of unprocessed clauses: 4049
% 0.22/0.43  # ...number of literals in the above   : 4356
% 0.22/0.43  # Current number of archived formulas  : 0
% 0.22/0.43  # Current number of archived clauses   : 31
% 0.22/0.43  # Clause-clause subsumption calls (NU) : 299
% 0.22/0.43  # Rec. Clause-clause subsumption calls : 299
% 0.22/0.43  # Non-unit clause-clause subsumptions  : 50
% 0.22/0.43  # Unit Clause-clause subsumption calls : 39
% 0.22/0.43  # Rewrite failures with RHS unbound    : 0
% 0.22/0.43  # BW rewrite match attempts            : 805
% 0.22/0.43  # BW rewrite match successes           : 31
% 0.22/0.43  # Condensation attempts                : 0
% 0.22/0.43  # Condensation successes               : 0
% 0.22/0.43  # Termbank termtop insertions          : 51362
% 0.22/0.43  
% 0.22/0.43  # -------------------------------------------------
% 0.22/0.43  # User time                : 0.071 s
% 0.22/0.43  # System time              : 0.007 s
% 0.22/0.43  # Total time               : 0.078 s
% 0.22/0.43  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
