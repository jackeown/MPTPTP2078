%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:56 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   29 (  44 expanded)
%              Number of clauses        :   16 (  19 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  83 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t27_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(c_0_6,plain,(
    ! [X12,X13] : r1_tarski(k3_xboole_0(X12,X13),X12) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_7,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4) )
       => r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)) ) ),
    inference(assume_negation,[status(cth)],[t27_xboole_1])).

fof(c_0_9,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k2_xboole_0(X10,X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_10,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_13,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X14,X16)
      | r1_tarski(X14,k3_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_14,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(k2_xboole_0(X7,X8),X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X2) = X2 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk1_0,esk3_0),esk4_0)
    | ~ r1_tarski(k3_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk1_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_26,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.32  % Computer   : n001.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 15:35:15 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  # Version: 2.5pre002
% 0.10/0.32  # No SInE strategy applied
% 0.10/0.32  # Trying AutoSched0 for 299 seconds
% 0.18/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S061I
% 0.18/0.34  # and selection function SelectMaxLComplexAPPNTNp.
% 0.18/0.34  #
% 0.18/0.34  # Preprocessing time       : 0.020 s
% 0.18/0.34  # Presaturation interreduction done
% 0.18/0.34  
% 0.18/0.34  # Proof found!
% 0.18/0.34  # SZS status Theorem
% 0.18/0.34  # SZS output start CNFRefutation
% 0.18/0.34  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.18/0.34  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.18/0.34  fof(t27_xboole_1, conjecture, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 0.18/0.34  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.18/0.34  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.18/0.34  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.18/0.34  fof(c_0_6, plain, ![X12, X13]:r1_tarski(k3_xboole_0(X12,X13),X12), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.18/0.34  fof(c_0_7, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.18/0.34  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))), inference(assume_negation,[status(cth)],[t27_xboole_1])).
% 0.18/0.34  fof(c_0_9, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k2_xboole_0(X10,X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.18/0.34  cnf(c_0_10, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.34  cnf(c_0_11, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  fof(c_0_12, negated_conjecture, ((r1_tarski(esk1_0,esk2_0)&r1_tarski(esk3_0,esk4_0))&~r1_tarski(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.18/0.34  fof(c_0_13, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|~r1_tarski(X14,X16)|r1_tarski(X14,k3_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.18/0.34  fof(c_0_14, plain, ![X7, X8, X9]:(~r1_tarski(k2_xboole_0(X7,X8),X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.18/0.34  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.34  cnf(c_0_16, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.18/0.34  cnf(c_0_17, negated_conjecture, (~r1_tarski(k3_xboole_0(esk1_0,esk3_0),k3_xboole_0(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.34  cnf(c_0_18, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.34  cnf(c_0_19, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.34  cnf(c_0_20, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X2)=X2), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.18/0.34  cnf(c_0_21, negated_conjecture, (~r1_tarski(k3_xboole_0(esk1_0,esk3_0),esk4_0)|~r1_tarski(k3_xboole_0(esk1_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.34  cnf(c_0_22, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.34  cnf(c_0_23, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.34  cnf(c_0_24, plain, (k2_xboole_0(k3_xboole_0(X1,X2),X1)=X1), inference(spm,[status(thm)],[c_0_15, c_0_10])).
% 0.18/0.34  cnf(c_0_25, negated_conjecture, (~r1_tarski(k3_xboole_0(esk1_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.18/0.34  cnf(c_0_26, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_19, c_0_24])).
% 0.18/0.34  cnf(c_0_27, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.34  cnf(c_0_28, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])]), ['proof']).
% 0.18/0.34  # SZS output end CNFRefutation
% 0.18/0.34  # Proof object total steps             : 29
% 0.18/0.34  # Proof object clause steps            : 16
% 0.18/0.34  # Proof object formula steps           : 13
% 0.18/0.34  # Proof object conjectures             : 9
% 0.18/0.34  # Proof object clause conjectures      : 6
% 0.18/0.34  # Proof object formula conjectures     : 3
% 0.18/0.34  # Proof object initial clauses used    : 8
% 0.18/0.34  # Proof object initial formulas used   : 6
% 0.18/0.34  # Proof object generating inferences   : 8
% 0.18/0.34  # Proof object simplifying inferences  : 4
% 0.18/0.34  # Training examples: 0 positive, 0 negative
% 0.18/0.34  # Parsed axioms                        : 6
% 0.18/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.34  # Initial clauses                      : 8
% 0.18/0.34  # Removed in clause preprocessing      : 0
% 0.18/0.34  # Initial clauses in saturation        : 8
% 0.18/0.34  # Processed clauses                    : 38
% 0.18/0.34  # ...of these trivial                  : 1
% 0.18/0.34  # ...subsumed                          : 5
% 0.18/0.34  # ...remaining for further processing  : 32
% 0.18/0.34  # Other redundant clauses eliminated   : 0
% 0.18/0.34  # Clauses deleted for lack of memory   : 0
% 0.18/0.34  # Backward-subsumed                    : 0
% 0.18/0.34  # Backward-rewritten                   : 0
% 0.18/0.34  # Generated clauses                    : 43
% 0.18/0.34  # ...of the previous two non-trivial   : 37
% 0.18/0.34  # Contextual simplify-reflections      : 0
% 0.18/0.34  # Paramodulations                      : 43
% 0.18/0.34  # Factorizations                       : 0
% 0.18/0.34  # Equation resolutions                 : 0
% 0.18/0.34  # Propositional unsat checks           : 0
% 0.18/0.34  #    Propositional check models        : 0
% 0.18/0.34  #    Propositional check unsatisfiable : 0
% 0.18/0.34  #    Propositional clauses             : 0
% 0.18/0.34  #    Propositional clauses after purity: 0
% 0.18/0.34  #    Propositional unsat core size     : 0
% 0.18/0.34  #    Propositional preprocessing time  : 0.000
% 0.18/0.34  #    Propositional encoding time       : 0.000
% 0.18/0.34  #    Propositional solver time         : 0.000
% 0.18/0.34  #    Success case prop preproc time    : 0.000
% 0.18/0.34  #    Success case prop encoding time   : 0.000
% 0.18/0.34  #    Success case prop solver time     : 0.000
% 0.18/0.34  # Current number of processed clauses  : 24
% 0.18/0.34  #    Positive orientable unit clauses  : 8
% 0.18/0.34  #    Positive unorientable unit clauses: 1
% 0.18/0.34  #    Negative unit clauses             : 4
% 0.18/0.34  #    Non-unit-clauses                  : 11
% 0.18/0.34  # Current number of unprocessed clauses: 15
% 0.18/0.34  # ...number of literals in the above   : 33
% 0.18/0.34  # Current number of archived formulas  : 0
% 0.18/0.34  # Current number of archived clauses   : 8
% 0.18/0.34  # Clause-clause subsumption calls (NU) : 65
% 0.18/0.34  # Rec. Clause-clause subsumption calls : 65
% 0.18/0.34  # Non-unit clause-clause subsumptions  : 4
% 0.18/0.34  # Unit Clause-clause subsumption calls : 14
% 0.18/0.34  # Rewrite failures with RHS unbound    : 0
% 0.18/0.34  # BW rewrite match attempts            : 19
% 0.18/0.34  # BW rewrite match successes           : 12
% 0.18/0.34  # Condensation attempts                : 0
% 0.18/0.34  # Condensation successes               : 0
% 0.18/0.34  # Termbank termtop insertions          : 798
% 0.18/0.34  
% 0.18/0.34  # -------------------------------------------------
% 0.18/0.34  # User time                : 0.022 s
% 0.18/0.34  # System time              : 0.002 s
% 0.18/0.34  # Total time               : 0.024 s
% 0.18/0.34  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
