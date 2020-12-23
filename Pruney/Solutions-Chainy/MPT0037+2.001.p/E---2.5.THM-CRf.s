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
% DateTime   : Thu Dec  3 10:31:59 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   27 (  39 expanded)
%              Number of clauses        :   14 (  17 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  48 expanded)
%              Number of equality atoms :   25 (  37 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t30_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,k3_xboole_0(X3,X2)) = k3_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,X2)
       => k2_xboole_0(X1,k3_xboole_0(X3,X2)) = k3_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t30_xboole_1])).

fof(c_0_7,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k2_xboole_0(X8,X9) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_8,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & k2_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk2_0)) != k3_xboole_0(k2_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_10,plain,(
    ! [X12,X13,X14] : k3_xboole_0(X12,k2_xboole_0(X13,X14)) = k2_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X12,X14)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

fof(c_0_11,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_12,plain,(
    ! [X10,X11] : k3_xboole_0(X10,k2_xboole_0(X10,X11)) = X10 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( k2_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk2_0)) != k3_xboole_0(k2_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k3_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk2_0) != k2_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1)) = k3_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk1_0)) != k2_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_xboole_0(X1,esk1_0)) = k2_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:47:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.35  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.19/0.35  # and selection function SelectNewComplexAHP.
% 0.19/0.35  #
% 0.19/0.35  # Preprocessing time       : 0.013 s
% 0.19/0.35  # Presaturation interreduction done
% 0.19/0.35  
% 0.19/0.35  # Proof found!
% 0.19/0.35  # SZS status Theorem
% 0.19/0.35  # SZS output start CNFRefutation
% 0.19/0.35  fof(t30_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,k3_xboole_0(X3,X2))=k3_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_xboole_1)).
% 0.19/0.35  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.35  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.35  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.19/0.35  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.35  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.19/0.35  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,k3_xboole_0(X3,X2))=k3_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t30_xboole_1])).
% 0.19/0.35  fof(c_0_7, plain, ![X8, X9]:(~r1_tarski(X8,X9)|k2_xboole_0(X8,X9)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.35  fof(c_0_8, negated_conjecture, (r1_tarski(esk1_0,esk2_0)&k2_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk2_0))!=k3_xboole_0(k2_xboole_0(esk1_0,esk3_0),esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.19/0.35  fof(c_0_9, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.35  fof(c_0_10, plain, ![X12, X13, X14]:k3_xboole_0(X12,k2_xboole_0(X13,X14))=k2_xboole_0(k3_xboole_0(X12,X13),k3_xboole_0(X12,X14)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.19/0.35  fof(c_0_11, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.35  fof(c_0_12, plain, ![X10, X11]:k3_xboole_0(X10,k2_xboole_0(X10,X11))=X10, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.19/0.35  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.35  cnf(c_0_14, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.35  cnf(c_0_15, negated_conjecture, (k2_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk2_0))!=k3_xboole_0(k2_xboole_0(esk1_0,esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.35  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.35  cnf(c_0_17, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.35  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.35  cnf(c_0_19, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.35  cnf(c_0_20, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.35  cnf(c_0_21, negated_conjecture, (k3_xboole_0(k2_xboole_0(esk3_0,esk1_0),esk2_0)!=k2_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk2_0))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.35  cnf(c_0_22, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))=k3_xboole_0(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.35  cnf(c_0_23, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)=esk1_0), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.35  cnf(c_0_24, negated_conjecture, (k3_xboole_0(esk2_0,k2_xboole_0(esk3_0,esk1_0))!=k2_xboole_0(esk1_0,k3_xboole_0(esk3_0,esk2_0))), inference(rw,[status(thm)],[c_0_21, c_0_18])).
% 0.19/0.35  cnf(c_0_25, negated_conjecture, (k3_xboole_0(esk2_0,k2_xboole_0(X1,esk1_0))=k2_xboole_0(esk1_0,k3_xboole_0(esk2_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_16])).
% 0.19/0.35  cnf(c_0_26, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_18])]), ['proof']).
% 0.19/0.35  # SZS output end CNFRefutation
% 0.19/0.35  # Proof object total steps             : 27
% 0.19/0.35  # Proof object clause steps            : 14
% 0.19/0.35  # Proof object formula steps           : 13
% 0.19/0.35  # Proof object conjectures             : 11
% 0.19/0.35  # Proof object clause conjectures      : 8
% 0.19/0.35  # Proof object formula conjectures     : 3
% 0.19/0.35  # Proof object initial clauses used    : 7
% 0.19/0.35  # Proof object initial formulas used   : 6
% 0.19/0.35  # Proof object generating inferences   : 4
% 0.19/0.35  # Proof object simplifying inferences  : 6
% 0.19/0.35  # Training examples: 0 positive, 0 negative
% 0.19/0.35  # Parsed axioms                        : 6
% 0.19/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.35  # Initial clauses                      : 7
% 0.19/0.35  # Removed in clause preprocessing      : 0
% 0.19/0.35  # Initial clauses in saturation        : 7
% 0.19/0.35  # Processed clauses                    : 128
% 0.19/0.35  # ...of these trivial                  : 64
% 0.19/0.35  # ...subsumed                          : 2
% 0.19/0.35  # ...remaining for further processing  : 62
% 0.19/0.35  # Other redundant clauses eliminated   : 0
% 0.19/0.35  # Clauses deleted for lack of memory   : 0
% 0.19/0.35  # Backward-subsumed                    : 0
% 0.19/0.35  # Backward-rewritten                   : 17
% 0.19/0.35  # Generated clauses                    : 708
% 0.19/0.35  # ...of the previous two non-trivial   : 343
% 0.19/0.35  # Contextual simplify-reflections      : 0
% 0.19/0.35  # Paramodulations                      : 708
% 0.19/0.35  # Factorizations                       : 0
% 0.19/0.35  # Equation resolutions                 : 0
% 0.19/0.35  # Propositional unsat checks           : 0
% 0.19/0.35  #    Propositional check models        : 0
% 0.19/0.35  #    Propositional check unsatisfiable : 0
% 0.19/0.35  #    Propositional clauses             : 0
% 0.19/0.35  #    Propositional clauses after purity: 0
% 0.19/0.35  #    Propositional unsat core size     : 0
% 0.19/0.35  #    Propositional preprocessing time  : 0.000
% 0.19/0.35  #    Propositional encoding time       : 0.000
% 0.19/0.35  #    Propositional solver time         : 0.000
% 0.19/0.35  #    Success case prop preproc time    : 0.000
% 0.19/0.35  #    Success case prop encoding time   : 0.000
% 0.19/0.35  #    Success case prop solver time     : 0.000
% 0.19/0.35  # Current number of processed clauses  : 38
% 0.19/0.35  #    Positive orientable unit clauses  : 35
% 0.19/0.35  #    Positive unorientable unit clauses: 2
% 0.19/0.35  #    Negative unit clauses             : 0
% 0.19/0.35  #    Non-unit-clauses                  : 1
% 0.19/0.35  # Current number of unprocessed clauses: 219
% 0.19/0.35  # ...number of literals in the above   : 219
% 0.19/0.35  # Current number of archived formulas  : 0
% 0.19/0.35  # Current number of archived clauses   : 24
% 0.19/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.35  # Unit Clause-clause subsumption calls : 1
% 0.19/0.35  # Rewrite failures with RHS unbound    : 0
% 0.19/0.35  # BW rewrite match attempts            : 95
% 0.19/0.35  # BW rewrite match successes           : 41
% 0.19/0.35  # Condensation attempts                : 0
% 0.19/0.35  # Condensation successes               : 0
% 0.19/0.35  # Termbank termtop insertions          : 5058
% 0.19/0.35  
% 0.19/0.35  # -------------------------------------------------
% 0.19/0.35  # User time                : 0.014 s
% 0.19/0.35  # System time              : 0.004 s
% 0.19/0.35  # Total time               : 0.018 s
% 0.19/0.35  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
