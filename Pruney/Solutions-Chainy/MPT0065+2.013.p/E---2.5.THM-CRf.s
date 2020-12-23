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
% DateTime   : Thu Dec  3 10:32:30 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   30 (  90 expanded)
%              Number of clauses        :   17 (  37 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 211 expanded)
%              Number of equality atoms :   14 (  39 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X2,X3) )
     => r2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(irreflexivity_r2_xboole_0,axiom,(
    ! [X1,X2] : ~ r2_xboole_0(X1,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_xboole_0(X1,X2)
          & r1_tarski(X2,X3) )
       => r2_xboole_0(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t58_xboole_1])).

fof(c_0_7,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | ~ r2_xboole_0(X6,X7) )
      & ( X6 != X7
        | ~ r2_xboole_0(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | X6 = X7
        | r2_xboole_0(X6,X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

fof(c_0_8,negated_conjecture,
    ( r2_xboole_0(esk1_0,esk2_0)
    & r1_tarski(esk2_0,esk3_0)
    & ~ r2_xboole_0(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r2_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(k2_xboole_0(X9,X10),X11)
      | r1_tarski(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_22,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_23,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( esk3_0 = esk1_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X8] : ~ r2_xboole_0(X8,X8) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_xboole_0])])).

cnf(c_0_27,negated_conjecture,
    ( esk2_0 = esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_24]),c_0_16])).

cnf(c_0_28,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_27]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:18:21 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___008_C45_F1_PI_S5PRR_SE_Q4_CS_SP_S4S
% 0.12/0.35  # and selection function SelectNewComplexAHPNS.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.026 s
% 0.12/0.35  
% 0.12/0.35  # Proof found!
% 0.12/0.35  # SZS status Theorem
% 0.12/0.35  # SZS output start CNFRefutation
% 0.12/0.35  fof(t58_xboole_1, conjecture, ![X1, X2, X3]:((r2_xboole_0(X1,X2)&r1_tarski(X2,X3))=>r2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 0.12/0.35  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.12/0.35  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.12/0.35  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.12/0.35  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.12/0.35  fof(irreflexivity_r2_xboole_0, axiom, ![X1, X2]:~(r2_xboole_0(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 0.12/0.35  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:((r2_xboole_0(X1,X2)&r1_tarski(X2,X3))=>r2_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t58_xboole_1])).
% 0.12/0.35  fof(c_0_7, plain, ![X6, X7]:(((r1_tarski(X6,X7)|~r2_xboole_0(X6,X7))&(X6!=X7|~r2_xboole_0(X6,X7)))&(~r1_tarski(X6,X7)|X6=X7|r2_xboole_0(X6,X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.12/0.35  fof(c_0_8, negated_conjecture, ((r2_xboole_0(esk1_0,esk2_0)&r1_tarski(esk2_0,esk3_0))&~r2_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.12/0.35  fof(c_0_9, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.12/0.35  cnf(c_0_10, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.35  cnf(c_0_11, negated_conjecture, (r2_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.35  fof(c_0_12, plain, ![X9, X10, X11]:(~r1_tarski(k2_xboole_0(X9,X10),X11)|r1_tarski(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.12/0.35  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.35  cnf(c_0_14, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.35  cnf(c_0_15, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.35  cnf(c_0_16, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.35  cnf(c_0_17, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.35  cnf(c_0_18, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.35  cnf(c_0_19, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.35  cnf(c_0_20, negated_conjecture, (r1_tarski(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.35  cnf(c_0_21, negated_conjecture, (~r2_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.35  fof(c_0_22, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.12/0.35  cnf(c_0_23, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_13, c_0_18])).
% 0.12/0.35  cnf(c_0_24, negated_conjecture, (esk3_0=esk1_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.12/0.35  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.35  fof(c_0_26, plain, ![X8]:~r2_xboole_0(X8,X8), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_xboole_0])])).
% 0.12/0.35  cnf(c_0_27, negated_conjecture, (esk2_0=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_24]), c_0_16])).
% 0.12/0.35  cnf(c_0_28, plain, (~r2_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.35  cnf(c_0_29, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_27]), c_0_28]), ['proof']).
% 0.12/0.35  # SZS output end CNFRefutation
% 0.12/0.35  # Proof object total steps             : 30
% 0.12/0.35  # Proof object clause steps            : 17
% 0.12/0.35  # Proof object formula steps           : 13
% 0.12/0.35  # Proof object conjectures             : 14
% 0.12/0.35  # Proof object clause conjectures      : 11
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 9
% 0.12/0.35  # Proof object initial formulas used   : 6
% 0.12/0.35  # Proof object generating inferences   : 6
% 0.12/0.35  # Proof object simplifying inferences  : 7
% 0.12/0.35  # Training examples: 0 positive, 0 negative
% 0.12/0.35  # Parsed axioms                        : 6
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 10
% 0.12/0.35  # Removed in clause preprocessing      : 0
% 0.12/0.35  # Initial clauses in saturation        : 10
% 0.12/0.35  # Processed clauses                    : 20
% 0.12/0.35  # ...of these trivial                  : 0
% 0.12/0.35  # ...subsumed                          : 1
% 0.12/0.35  # ...remaining for further processing  : 19
% 0.12/0.35  # Other redundant clauses eliminated   : 1
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 0
% 0.12/0.35  # Backward-rewritten                   : 10
% 0.12/0.35  # Generated clauses                    : 14
% 0.12/0.35  # ...of the previous two non-trivial   : 20
% 0.12/0.35  # Contextual simplify-reflections      : 0
% 0.12/0.35  # Paramodulations                      : 13
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 1
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 8
% 0.12/0.35  #    Positive orientable unit clauses  : 2
% 0.12/0.35  #    Positive unorientable unit clauses: 1
% 0.12/0.35  #    Negative unit clauses             : 1
% 0.12/0.35  #    Non-unit-clauses                  : 4
% 0.12/0.35  # Current number of unprocessed clauses: 8
% 0.12/0.35  # ...number of literals in the above   : 12
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 10
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.35  # Unit Clause-clause subsumption calls : 1
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 6
% 0.12/0.35  # BW rewrite match successes           : 6
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 559
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.025 s
% 0.12/0.35  # System time              : 0.005 s
% 0.12/0.35  # Total time               : 0.030 s
% 0.12/0.35  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
