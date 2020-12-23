%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:08 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   26 (  32 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  68 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t129_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k8_relat_1(X2,k8_relat_1(X1,X3)) = k8_relat_1(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(t108_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(t119_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k8_relat_1(X1,X2)) = k3_xboole_0(k2_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => k8_relat_1(X2,k8_relat_1(X1,X3)) = k8_relat_1(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t129_relat_1])).

fof(c_0_7,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(k3_xboole_0(X6,X8),X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & r1_tarski(esk1_0,esk2_0)
    & k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0)) != k8_relat_1(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | ~ r1_tarski(k2_relat_1(X14),X13)
      | k8_relat_1(X13,X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | k2_relat_1(k8_relat_1(X11,X12)) = k3_xboole_0(k2_relat_1(X12),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).

fof(c_0_11,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X10)
      | v1_relat_1(k8_relat_1(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_12,plain,
    ( r1_tarski(k3_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_15,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_relat_1(k8_relat_1(X2,X1)) = k3_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk1_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(X2,X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(k3_xboole_0(k2_relat_1(X3),X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0)) != k8_relat_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( k8_relat_1(esk2_0,k8_relat_1(esk1_0,X1)) = k8_relat_1(esk1_0,X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.30  % Computer   : n019.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 10:01:07 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.15/0.31  # Version: 2.5pre002
% 0.15/0.31  # No SInE strategy applied
% 0.15/0.31  # Trying AutoSched0 for 299 seconds
% 0.15/0.32  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.15/0.32  # and selection function SelectCQIPrecWNTNp.
% 0.15/0.32  #
% 0.15/0.32  # Preprocessing time       : 0.014 s
% 0.15/0.32  # Presaturation interreduction done
% 0.15/0.32  
% 0.15/0.32  # Proof found!
% 0.15/0.32  # SZS status Theorem
% 0.15/0.32  # SZS output start CNFRefutation
% 0.15/0.32  fof(t129_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X2,k8_relat_1(X1,X3))=k8_relat_1(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 0.15/0.32  fof(t108_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k3_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 0.15/0.32  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 0.15/0.32  fof(t119_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k8_relat_1(X1,X2))=k3_xboole_0(k2_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 0.15/0.32  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.15/0.32  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.15/0.32  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k8_relat_1(X2,k8_relat_1(X1,X3))=k8_relat_1(X1,X3)))), inference(assume_negation,[status(cth)],[t129_relat_1])).
% 0.15/0.32  fof(c_0_7, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|r1_tarski(k3_xboole_0(X6,X8),X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t108_xboole_1])])).
% 0.15/0.32  fof(c_0_8, negated_conjecture, (v1_relat_1(esk3_0)&(r1_tarski(esk1_0,esk2_0)&k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0))!=k8_relat_1(esk1_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.15/0.32  fof(c_0_9, plain, ![X13, X14]:(~v1_relat_1(X14)|(~r1_tarski(k2_relat_1(X14),X13)|k8_relat_1(X13,X14)=X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.15/0.32  fof(c_0_10, plain, ![X11, X12]:(~v1_relat_1(X12)|k2_relat_1(k8_relat_1(X11,X12))=k3_xboole_0(k2_relat_1(X12),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_relat_1])])).
% 0.15/0.32  fof(c_0_11, plain, ![X9, X10]:(~v1_relat_1(X10)|v1_relat_1(k8_relat_1(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.15/0.32  cnf(c_0_12, plain, (r1_tarski(k3_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.32  cnf(c_0_13, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.32  fof(c_0_14, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.15/0.32  cnf(c_0_15, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.32  cnf(c_0_16, plain, (k2_relat_1(k8_relat_1(X2,X1))=k3_xboole_0(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.15/0.32  cnf(c_0_17, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.15/0.32  cnf(c_0_18, negated_conjecture, (r1_tarski(k3_xboole_0(esk1_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.15/0.32  cnf(c_0_19, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.32  cnf(c_0_20, plain, (k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(X2,X3)|~v1_relat_1(X3)|~r1_tarski(k3_xboole_0(k2_relat_1(X3),X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.15/0.32  cnf(c_0_21, negated_conjecture, (r1_tarski(k3_xboole_0(X1,esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.15/0.32  cnf(c_0_22, negated_conjecture, (k8_relat_1(esk2_0,k8_relat_1(esk1_0,esk3_0))!=k8_relat_1(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.32  cnf(c_0_23, negated_conjecture, (k8_relat_1(esk2_0,k8_relat_1(esk1_0,X1))=k8_relat_1(esk1_0,X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.15/0.32  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.32  cnf(c_0_25, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])]), ['proof']).
% 0.15/0.32  # SZS output end CNFRefutation
% 0.15/0.32  # Proof object total steps             : 26
% 0.15/0.32  # Proof object clause steps            : 13
% 0.15/0.32  # Proof object formula steps           : 13
% 0.15/0.32  # Proof object conjectures             : 10
% 0.15/0.32  # Proof object clause conjectures      : 7
% 0.15/0.32  # Proof object formula conjectures     : 3
% 0.15/0.32  # Proof object initial clauses used    : 8
% 0.15/0.32  # Proof object initial formulas used   : 6
% 0.15/0.32  # Proof object generating inferences   : 5
% 0.15/0.32  # Proof object simplifying inferences  : 3
% 0.15/0.32  # Training examples: 0 positive, 0 negative
% 0.15/0.32  # Parsed axioms                        : 6
% 0.15/0.32  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.32  # Initial clauses                      : 8
% 0.15/0.32  # Removed in clause preprocessing      : 0
% 0.15/0.32  # Initial clauses in saturation        : 8
% 0.15/0.32  # Processed clauses                    : 34
% 0.15/0.32  # ...of these trivial                  : 7
% 0.15/0.32  # ...subsumed                          : 1
% 0.15/0.32  # ...remaining for further processing  : 26
% 0.15/0.32  # Other redundant clauses eliminated   : 0
% 0.15/0.32  # Clauses deleted for lack of memory   : 0
% 0.15/0.32  # Backward-subsumed                    : 0
% 0.15/0.32  # Backward-rewritten                   : 0
% 0.15/0.32  # Generated clauses                    : 52
% 0.15/0.32  # ...of the previous two non-trivial   : 39
% 0.15/0.32  # Contextual simplify-reflections      : 1
% 0.15/0.32  # Paramodulations                      : 52
% 0.15/0.32  # Factorizations                       : 0
% 0.15/0.32  # Equation resolutions                 : 0
% 0.15/0.32  # Propositional unsat checks           : 0
% 0.15/0.32  #    Propositional check models        : 0
% 0.15/0.32  #    Propositional check unsatisfiable : 0
% 0.15/0.32  #    Propositional clauses             : 0
% 0.15/0.32  #    Propositional clauses after purity: 0
% 0.15/0.32  #    Propositional unsat core size     : 0
% 0.15/0.32  #    Propositional preprocessing time  : 0.000
% 0.15/0.32  #    Propositional encoding time       : 0.000
% 0.15/0.32  #    Propositional solver time         : 0.000
% 0.15/0.32  #    Success case prop preproc time    : 0.000
% 0.15/0.32  #    Success case prop encoding time   : 0.000
% 0.15/0.32  #    Success case prop solver time     : 0.000
% 0.15/0.32  # Current number of processed clauses  : 18
% 0.15/0.32  #    Positive orientable unit clauses  : 9
% 0.15/0.32  #    Positive unorientable unit clauses: 1
% 0.15/0.32  #    Negative unit clauses             : 1
% 0.15/0.32  #    Non-unit-clauses                  : 7
% 0.15/0.32  # Current number of unprocessed clauses: 20
% 0.15/0.32  # ...number of literals in the above   : 36
% 0.15/0.32  # Current number of archived formulas  : 0
% 0.15/0.32  # Current number of archived clauses   : 8
% 0.15/0.32  # Clause-clause subsumption calls (NU) : 10
% 0.15/0.32  # Rec. Clause-clause subsumption calls : 9
% 0.15/0.32  # Non-unit clause-clause subsumptions  : 2
% 0.15/0.32  # Unit Clause-clause subsumption calls : 1
% 0.15/0.32  # Rewrite failures with RHS unbound    : 0
% 0.15/0.32  # BW rewrite match attempts            : 10
% 0.15/0.32  # BW rewrite match successes           : 6
% 0.15/0.32  # Condensation attempts                : 0
% 0.15/0.32  # Condensation successes               : 0
% 0.15/0.32  # Termbank termtop insertions          : 1058
% 0.15/0.32  
% 0.15/0.32  # -------------------------------------------------
% 0.15/0.32  # User time                : 0.017 s
% 0.15/0.32  # System time              : 0.000 s
% 0.15/0.32  # Total time               : 0.017 s
% 0.15/0.32  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
