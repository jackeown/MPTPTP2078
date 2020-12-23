%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:33:00 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   21 (  39 expanded)
%              Number of clauses        :   12 (  15 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  85 expanded)
%              Number of equality atoms :   22 (  50 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
        & r1_xboole_0(X1,X2)
        & r1_xboole_0(X3,X2) )
     => X1 = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X2)
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X3,X2) )
       => X1 = X3 ) ),
    inference(assume_negation,[status(cth)],[t71_xboole_1])).

fof(c_0_5,plain,(
    ! [X4,X5] :
      ( ( ~ r1_xboole_0(X4,X5)
        | k3_xboole_0(X4,X5) = k1_xboole_0 )
      & ( k3_xboole_0(X4,X5) != k1_xboole_0
        | r1_xboole_0(X4,X5) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

fof(c_0_6,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk2_0)
    & r1_xboole_0(esk1_0,esk2_0)
    & r1_xboole_0(esk3_0,esk2_0)
    & esk1_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),X7) = k4_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

fof(c_0_8,plain,(
    ! [X8,X9] : k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,X9)) = X8 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_9,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = k2_xboole_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk2_0) = k4_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,esk2_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( esk1_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_16]),c_0_17]),c_0_18]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 19:49:22 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.11/0.35  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.11/0.35  # and selection function SelectDiffNegLit.
% 0.11/0.35  #
% 0.11/0.35  # Preprocessing time       : 0.025 s
% 0.11/0.35  # Presaturation interreduction done
% 0.11/0.35  
% 0.11/0.35  # Proof found!
% 0.11/0.35  # SZS status Theorem
% 0.11/0.35  # SZS output start CNFRefutation
% 0.11/0.35  fof(t71_xboole_1, conjecture, ![X1, X2, X3]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)&r1_xboole_0(X1,X2))&r1_xboole_0(X3,X2))=>X1=X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 0.11/0.35  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.11/0.35  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.11/0.35  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.11/0.35  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:(((k2_xboole_0(X1,X2)=k2_xboole_0(X3,X2)&r1_xboole_0(X1,X2))&r1_xboole_0(X3,X2))=>X1=X3)), inference(assume_negation,[status(cth)],[t71_xboole_1])).
% 0.11/0.35  fof(c_0_5, plain, ![X4, X5]:((~r1_xboole_0(X4,X5)|k3_xboole_0(X4,X5)=k1_xboole_0)&(k3_xboole_0(X4,X5)!=k1_xboole_0|r1_xboole_0(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.11/0.35  fof(c_0_6, negated_conjecture, (((k2_xboole_0(esk1_0,esk2_0)=k2_xboole_0(esk3_0,esk2_0)&r1_xboole_0(esk1_0,esk2_0))&r1_xboole_0(esk3_0,esk2_0))&esk1_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.11/0.35  fof(c_0_7, plain, ![X6, X7]:k4_xboole_0(k2_xboole_0(X6,X7),X7)=k4_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.11/0.35  fof(c_0_8, plain, ![X8, X9]:k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,X9))=X8, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.11/0.35  cnf(c_0_9, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.11/0.35  cnf(c_0_10, negated_conjecture, (r1_xboole_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.35  cnf(c_0_11, negated_conjecture, (r1_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.35  cnf(c_0_12, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.11/0.35  cnf(c_0_13, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=k2_xboole_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.35  cnf(c_0_14, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.11/0.35  cnf(c_0_15, negated_conjecture, (k3_xboole_0(esk3_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.11/0.35  cnf(c_0_16, negated_conjecture, (k3_xboole_0(esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_9, c_0_11])).
% 0.11/0.35  cnf(c_0_17, negated_conjecture, (k4_xboole_0(esk1_0,esk2_0)=k4_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_12])).
% 0.11/0.35  cnf(c_0_18, negated_conjecture, (k2_xboole_0(k1_xboole_0,k4_xboole_0(esk3_0,esk2_0))=esk3_0), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.11/0.35  cnf(c_0_19, negated_conjecture, (esk1_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.35  cnf(c_0_20, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_16]), c_0_17]), c_0_18]), c_0_19]), ['proof']).
% 0.11/0.35  # SZS output end CNFRefutation
% 0.11/0.35  # Proof object total steps             : 21
% 0.11/0.35  # Proof object clause steps            : 12
% 0.11/0.35  # Proof object formula steps           : 9
% 0.11/0.35  # Proof object conjectures             : 12
% 0.11/0.35  # Proof object clause conjectures      : 9
% 0.11/0.35  # Proof object formula conjectures     : 3
% 0.11/0.35  # Proof object initial clauses used    : 7
% 0.11/0.35  # Proof object initial formulas used   : 4
% 0.11/0.35  # Proof object generating inferences   : 5
% 0.11/0.35  # Proof object simplifying inferences  : 4
% 0.11/0.35  # Training examples: 0 positive, 0 negative
% 0.11/0.35  # Parsed axioms                        : 4
% 0.11/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.35  # Initial clauses                      : 8
% 0.11/0.35  # Removed in clause preprocessing      : 0
% 0.11/0.35  # Initial clauses in saturation        : 8
% 0.11/0.35  # Processed clauses                    : 21
% 0.11/0.35  # ...of these trivial                  : 0
% 0.11/0.35  # ...subsumed                          : 0
% 0.11/0.35  # ...remaining for further processing  : 20
% 0.11/0.35  # Other redundant clauses eliminated   : 0
% 0.11/0.35  # Clauses deleted for lack of memory   : 0
% 0.11/0.35  # Backward-subsumed                    : 0
% 0.11/0.35  # Backward-rewritten                   : 0
% 0.11/0.35  # Generated clauses                    : 11
% 0.11/0.35  # ...of the previous two non-trivial   : 9
% 0.11/0.35  # Contextual simplify-reflections      : 0
% 0.11/0.35  # Paramodulations                      : 11
% 0.11/0.35  # Factorizations                       : 0
% 0.11/0.35  # Equation resolutions                 : 0
% 0.11/0.35  # Propositional unsat checks           : 0
% 0.11/0.35  #    Propositional check models        : 0
% 0.11/0.35  #    Propositional check unsatisfiable : 0
% 0.11/0.35  #    Propositional clauses             : 0
% 0.11/0.35  #    Propositional clauses after purity: 0
% 0.11/0.35  #    Propositional unsat core size     : 0
% 0.11/0.35  #    Propositional preprocessing time  : 0.000
% 0.11/0.35  #    Propositional encoding time       : 0.000
% 0.11/0.35  #    Propositional solver time         : 0.000
% 0.11/0.35  #    Success case prop preproc time    : 0.000
% 0.11/0.35  #    Success case prop encoding time   : 0.000
% 0.11/0.35  #    Success case prop solver time     : 0.000
% 0.11/0.35  # Current number of processed clauses  : 12
% 0.11/0.35  #    Positive orientable unit clauses  : 9
% 0.11/0.35  #    Positive unorientable unit clauses: 0
% 0.11/0.35  #    Negative unit clauses             : 1
% 0.11/0.35  #    Non-unit-clauses                  : 2
% 0.11/0.35  # Current number of unprocessed clauses: 4
% 0.11/0.35  # ...number of literals in the above   : 4
% 0.11/0.35  # Current number of archived formulas  : 0
% 0.11/0.35  # Current number of archived clauses   : 8
% 0.11/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.11/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.11/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.11/0.35  # Unit Clause-clause subsumption calls : 0
% 0.11/0.35  # Rewrite failures with RHS unbound    : 0
% 0.11/0.35  # BW rewrite match attempts            : 0
% 0.11/0.35  # BW rewrite match successes           : 0
% 0.11/0.35  # Condensation attempts                : 0
% 0.11/0.35  # Condensation successes               : 0
% 0.11/0.35  # Termbank termtop insertions          : 449
% 0.11/0.35  
% 0.11/0.35  # -------------------------------------------------
% 0.11/0.35  # User time                : 0.029 s
% 0.11/0.35  # System time              : 0.000 s
% 0.11/0.35  # Total time               : 0.029 s
% 0.11/0.35  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
