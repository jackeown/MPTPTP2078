%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:48 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   19 (  28 expanded)
%              Number of clauses        :   10 (  11 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  60 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4) )
       => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)) ) ),
    inference(assume_negation,[status(cth)],[t13_xboole_1])).

fof(c_0_5,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk3_0),k2_xboole_0(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X12,X11)
      | r1_tarski(k2_xboole_0(X10,X12),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_7,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk3_0),k2_xboole_0(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | r1_tarski(X7,k2_xboole_0(X9,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_10,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k2_xboole_0(esk2_0,esk4_0))
    | ~ r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n017.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.17/0.32  % WCLimit    : 600
% 0.17/0.32  % DateTime   : Tue Dec  1 10:14:31 EST 2020
% 0.17/0.33  % CPUTime    : 
% 0.17/0.33  # Version: 2.5pre002
% 0.17/0.33  # No SInE strategy applied
% 0.17/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.17/0.35  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.17/0.35  #
% 0.17/0.35  # Preprocessing time       : 0.026 s
% 0.17/0.35  # Presaturation interreduction done
% 0.17/0.35  
% 0.17/0.35  # Proof found!
% 0.17/0.35  # SZS status Theorem
% 0.17/0.35  # SZS output start CNFRefutation
% 0.17/0.35  fof(t13_xboole_1, conjecture, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 0.17/0.35  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.17/0.35  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.17/0.35  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.17/0.35  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)))), inference(assume_negation,[status(cth)],[t13_xboole_1])).
% 0.17/0.35  fof(c_0_5, negated_conjecture, ((r1_tarski(esk1_0,esk2_0)&r1_tarski(esk3_0,esk4_0))&~r1_tarski(k2_xboole_0(esk1_0,esk3_0),k2_xboole_0(esk2_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.17/0.35  fof(c_0_6, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X12,X11)|r1_tarski(k2_xboole_0(X10,X12),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.17/0.35  cnf(c_0_7, negated_conjecture, (~r1_tarski(k2_xboole_0(esk1_0,esk3_0),k2_xboole_0(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.17/0.35  cnf(c_0_8, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.17/0.35  fof(c_0_9, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|r1_tarski(X7,k2_xboole_0(X9,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.17/0.36  fof(c_0_10, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.17/0.36  cnf(c_0_11, negated_conjecture, (~r1_tarski(esk3_0,k2_xboole_0(esk2_0,esk4_0))|~r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.17/0.36  cnf(c_0_12, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.17/0.36  cnf(c_0_13, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.17/0.36  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.36  cnf(c_0_15, negated_conjecture, (~r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.17/0.36  cnf(c_0_16, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_12, c_0_14])).
% 0.17/0.36  cnf(c_0_17, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.17/0.36  cnf(c_0_18, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])]), ['proof']).
% 0.17/0.36  # SZS output end CNFRefutation
% 0.17/0.36  # Proof object total steps             : 19
% 0.17/0.36  # Proof object clause steps            : 10
% 0.17/0.36  # Proof object formula steps           : 9
% 0.17/0.36  # Proof object conjectures             : 9
% 0.17/0.36  # Proof object clause conjectures      : 6
% 0.17/0.36  # Proof object formula conjectures     : 3
% 0.17/0.36  # Proof object initial clauses used    : 6
% 0.17/0.36  # Proof object initial formulas used   : 4
% 0.17/0.36  # Proof object generating inferences   : 4
% 0.17/0.36  # Proof object simplifying inferences  : 4
% 0.17/0.36  # Training examples: 0 positive, 0 negative
% 0.17/0.36  # Parsed axioms                        : 4
% 0.17/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.36  # Initial clauses                      : 6
% 0.17/0.36  # Removed in clause preprocessing      : 0
% 0.17/0.36  # Initial clauses in saturation        : 6
% 0.17/0.36  # Processed clauses                    : 22
% 0.17/0.36  # ...of these trivial                  : 0
% 0.17/0.36  # ...subsumed                          : 3
% 0.17/0.36  # ...remaining for further processing  : 19
% 0.17/0.36  # Other redundant clauses eliminated   : 0
% 0.17/0.36  # Clauses deleted for lack of memory   : 0
% 0.17/0.36  # Backward-subsumed                    : 0
% 0.17/0.36  # Backward-rewritten                   : 0
% 0.17/0.36  # Generated clauses                    : 15
% 0.17/0.36  # ...of the previous two non-trivial   : 14
% 0.17/0.36  # Contextual simplify-reflections      : 0
% 0.17/0.36  # Paramodulations                      : 15
% 0.17/0.36  # Factorizations                       : 0
% 0.17/0.36  # Equation resolutions                 : 0
% 0.17/0.36  # Propositional unsat checks           : 0
% 0.17/0.36  #    Propositional check models        : 0
% 0.17/0.36  #    Propositional check unsatisfiable : 0
% 0.17/0.36  #    Propositional clauses             : 0
% 0.17/0.36  #    Propositional clauses after purity: 0
% 0.17/0.36  #    Propositional unsat core size     : 0
% 0.17/0.36  #    Propositional preprocessing time  : 0.000
% 0.17/0.36  #    Propositional encoding time       : 0.000
% 0.17/0.36  #    Propositional solver time         : 0.000
% 0.17/0.36  #    Success case prop preproc time    : 0.000
% 0.17/0.36  #    Success case prop encoding time   : 0.000
% 0.17/0.36  #    Success case prop solver time     : 0.000
% 0.17/0.36  # Current number of processed clauses  : 13
% 0.17/0.36  #    Positive orientable unit clauses  : 2
% 0.17/0.36  #    Positive unorientable unit clauses: 1
% 0.17/0.36  #    Negative unit clauses             : 6
% 0.17/0.36  #    Non-unit-clauses                  : 4
% 0.17/0.36  # Current number of unprocessed clauses: 3
% 0.17/0.36  # ...number of literals in the above   : 8
% 0.17/0.36  # Current number of archived formulas  : 0
% 0.17/0.36  # Current number of archived clauses   : 6
% 0.17/0.36  # Clause-clause subsumption calls (NU) : 20
% 0.17/0.36  # Rec. Clause-clause subsumption calls : 20
% 0.17/0.36  # Non-unit clause-clause subsumptions  : 3
% 0.17/0.36  # Unit Clause-clause subsumption calls : 8
% 0.17/0.36  # Rewrite failures with RHS unbound    : 0
% 0.17/0.36  # BW rewrite match attempts            : 10
% 0.17/0.36  # BW rewrite match successes           : 10
% 0.17/0.36  # Condensation attempts                : 0
% 0.17/0.36  # Condensation successes               : 0
% 0.17/0.36  # Termbank termtop insertions          : 469
% 0.17/0.36  
% 0.17/0.36  # -------------------------------------------------
% 0.17/0.36  # User time                : 0.027 s
% 0.17/0.36  # System time              : 0.002 s
% 0.17/0.36  # Total time               : 0.030 s
% 0.17/0.36  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
