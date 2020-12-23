%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:35 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l58_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X3) )
     => r2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l58_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t62_xboole_1,conjecture,(
    ! [X1] : ~ r2_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_xboole_1)).

fof(irreflexivity_r2_xboole_0,axiom,(
    ! [X1,X2] : ~ r2_xboole_0(X1,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(c_0_4,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r2_xboole_0(X6,X7)
      | r2_xboole_0(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l58_xboole_1])])).

fof(c_0_5,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] : ~ r2_xboole_0(X1,k1_xboole_0) ),
    inference(assume_negation,[status(cth)],[t62_xboole_1])).

cnf(c_0_7,plain,
    ( r2_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,(
    r2_xboole_0(esk1_0,k1_xboole_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_10,plain,(
    ! [X4] : ~ r2_xboole_0(X4,X4) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_xboole_0])])).

cnf(c_0_11,plain,
    ( r2_xboole_0(k1_xboole_0,X1)
    | ~ r2_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r2_xboole_0(esk1_0,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 20:20:34 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.32  # Version: 2.5pre002
% 0.17/0.32  # No SInE strategy applied
% 0.17/0.32  # Trying AutoSched0 for 299 seconds
% 0.17/0.35  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.17/0.35  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.17/0.35  #
% 0.17/0.35  # Preprocessing time       : 0.026 s
% 0.17/0.35  # Presaturation interreduction done
% 0.17/0.35  
% 0.17/0.35  # Proof found!
% 0.17/0.35  # SZS status Theorem
% 0.17/0.35  # SZS output start CNFRefutation
% 0.17/0.35  fof(l58_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r2_xboole_0(X2,X3))=>r2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l58_xboole_1)).
% 0.17/0.35  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.17/0.35  fof(t62_xboole_1, conjecture, ![X1]:~(r2_xboole_0(X1,k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_xboole_1)).
% 0.17/0.35  fof(irreflexivity_r2_xboole_0, axiom, ![X1, X2]:~(r2_xboole_0(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 0.17/0.35  fof(c_0_4, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r2_xboole_0(X6,X7)|r2_xboole_0(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l58_xboole_1])])).
% 0.17/0.35  fof(c_0_5, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.17/0.35  fof(c_0_6, negated_conjecture, ~(![X1]:~(r2_xboole_0(X1,k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_xboole_1])).
% 0.17/0.35  cnf(c_0_7, plain, (r2_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r2_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.17/0.35  cnf(c_0_8, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.17/0.35  fof(c_0_9, negated_conjecture, r2_xboole_0(esk1_0,k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.17/0.35  fof(c_0_10, plain, ![X4]:~r2_xboole_0(X4,X4), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_xboole_0])])).
% 0.17/0.35  cnf(c_0_11, plain, (r2_xboole_0(k1_xboole_0,X1)|~r2_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.17/0.35  cnf(c_0_12, negated_conjecture, (r2_xboole_0(esk1_0,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.17/0.35  cnf(c_0_13, plain, (~r2_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.35  cnf(c_0_14, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), ['proof']).
% 0.17/0.35  # SZS output end CNFRefutation
% 0.17/0.35  # Proof object total steps             : 15
% 0.17/0.35  # Proof object clause steps            : 6
% 0.17/0.35  # Proof object formula steps           : 9
% 0.17/0.35  # Proof object conjectures             : 5
% 0.17/0.35  # Proof object clause conjectures      : 2
% 0.17/0.35  # Proof object formula conjectures     : 3
% 0.17/0.35  # Proof object initial clauses used    : 4
% 0.17/0.35  # Proof object initial formulas used   : 4
% 0.17/0.35  # Proof object generating inferences   : 2
% 0.17/0.35  # Proof object simplifying inferences  : 1
% 0.17/0.35  # Training examples: 0 positive, 0 negative
% 0.17/0.35  # Parsed axioms                        : 4
% 0.17/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.35  # Initial clauses                      : 4
% 0.17/0.35  # Removed in clause preprocessing      : 0
% 0.17/0.35  # Initial clauses in saturation        : 4
% 0.17/0.35  # Processed clauses                    : 9
% 0.17/0.35  # ...of these trivial                  : 0
% 0.17/0.35  # ...subsumed                          : 0
% 0.17/0.35  # ...remaining for further processing  : 9
% 0.17/0.35  # Other redundant clauses eliminated   : 0
% 0.17/0.35  # Clauses deleted for lack of memory   : 0
% 0.17/0.35  # Backward-subsumed                    : 0
% 0.17/0.35  # Backward-rewritten                   : 0
% 0.17/0.35  # Generated clauses                    : 2
% 0.17/0.35  # ...of the previous two non-trivial   : 1
% 0.17/0.35  # Contextual simplify-reflections      : 0
% 0.17/0.35  # Paramodulations                      : 2
% 0.17/0.35  # Factorizations                       : 0
% 0.17/0.35  # Equation resolutions                 : 0
% 0.17/0.35  # Propositional unsat checks           : 0
% 0.17/0.35  #    Propositional check models        : 0
% 0.17/0.35  #    Propositional check unsatisfiable : 0
% 0.17/0.35  #    Propositional clauses             : 0
% 0.17/0.35  #    Propositional clauses after purity: 0
% 0.17/0.35  #    Propositional unsat core size     : 0
% 0.17/0.35  #    Propositional preprocessing time  : 0.000
% 0.17/0.35  #    Propositional encoding time       : 0.000
% 0.17/0.35  #    Propositional solver time         : 0.000
% 0.17/0.35  #    Success case prop preproc time    : 0.000
% 0.17/0.35  #    Success case prop encoding time   : 0.000
% 0.17/0.35  #    Success case prop solver time     : 0.000
% 0.17/0.35  # Current number of processed clauses  : 5
% 0.17/0.35  #    Positive orientable unit clauses  : 2
% 0.17/0.35  #    Positive unorientable unit clauses: 0
% 0.17/0.35  #    Negative unit clauses             : 1
% 0.17/0.35  #    Non-unit-clauses                  : 2
% 0.17/0.35  # Current number of unprocessed clauses: 0
% 0.17/0.35  # ...number of literals in the above   : 0
% 0.17/0.35  # Current number of archived formulas  : 0
% 0.17/0.35  # Current number of archived clauses   : 4
% 0.17/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.17/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.17/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.17/0.35  # Unit Clause-clause subsumption calls : 1
% 0.17/0.35  # Rewrite failures with RHS unbound    : 0
% 0.17/0.35  # BW rewrite match attempts            : 0
% 0.17/0.35  # BW rewrite match successes           : 0
% 0.17/0.35  # Condensation attempts                : 0
% 0.17/0.35  # Condensation successes               : 0
% 0.17/0.35  # Termbank termtop insertions          : 236
% 0.17/0.35  
% 0.17/0.35  # -------------------------------------------------
% 0.17/0.35  # User time                : 0.022 s
% 0.17/0.35  # System time              : 0.007 s
% 0.17/0.35  # Total time               : 0.029 s
% 0.17/0.35  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
