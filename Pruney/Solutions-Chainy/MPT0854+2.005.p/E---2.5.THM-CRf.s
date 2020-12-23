%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:00 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   26 ( 117 expanded)
%              Number of clauses        :   17 (  52 expanded)
%              Number of leaves         :    4 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :   50 ( 240 expanded)
%              Number of equality atoms :   14 (  74 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
       => ( r2_hidden(k1_mcart_1(X1),X2)
          & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t10_mcart_1])).

fof(c_0_5,plain,(
    ! [X6,X7,X8] :
      ( ~ r2_hidden(X6,k2_zfmisc_1(X7,X8))
      | k4_tarski(esk1_1(X6),esk2_1(X6)) = X6 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

fof(c_0_6,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))
    & ( ~ r2_hidden(k1_mcart_1(esk3_0),esk4_0)
      | ~ r2_hidden(k2_mcart_1(esk3_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X15,X16] :
      ( k1_mcart_1(k4_tarski(X15,X16)) = X15
      & k2_mcart_1(k4_tarski(X15,X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_8,plain,
    ( k4_tarski(esk1_1(X1),esk2_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( k4_tarski(esk1_1(esk3_0),esk2_1(esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( esk1_1(esk3_0) = k1_mcart_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_13,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),esk2_1(esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_15,plain,(
    ! [X11,X12,X13,X14] :
      ( ( r2_hidden(X11,X13)
        | ~ r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14)) )
      & ( r2_hidden(X12,X14)
        | ~ r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14)) )
      & ( ~ r2_hidden(X11,X13)
        | ~ r2_hidden(X12,X14)
        | r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_16,negated_conjecture,
    ( esk2_1(esk3_0) = k2_mcart_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_14,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk3_0),X1)
    | ~ r2_hidden(esk3_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(esk3_0),esk4_0)
    | ~ r2_hidden(k2_mcart_1(esk3_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk3_0),X1)
    | ~ r2_hidden(esk3_0,k2_zfmisc_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(k2_mcart_1(esk3_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22])])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_9]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:11:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.18/0.36  # and selection function SelectNewComplexAHPNS.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.026 s
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t10_mcart_1, conjecture, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.18/0.36  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.18/0.36  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.18/0.36  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.18/0.36  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3)))), inference(assume_negation,[status(cth)],[t10_mcart_1])).
% 0.18/0.36  fof(c_0_5, plain, ![X6, X7, X8]:(~r2_hidden(X6,k2_zfmisc_1(X7,X8))|k4_tarski(esk1_1(X6),esk2_1(X6))=X6), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.18/0.36  fof(c_0_6, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))&(~r2_hidden(k1_mcart_1(esk3_0),esk4_0)|~r2_hidden(k2_mcart_1(esk3_0),esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.18/0.36  fof(c_0_7, plain, ![X15, X16]:(k1_mcart_1(k4_tarski(X15,X16))=X15&k2_mcart_1(k4_tarski(X15,X16))=X16), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.18/0.36  cnf(c_0_8, plain, (k4_tarski(esk1_1(X1),esk2_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.18/0.36  cnf(c_0_9, negated_conjecture, (r2_hidden(esk3_0,k2_zfmisc_1(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.36  cnf(c_0_10, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.36  cnf(c_0_11, negated_conjecture, (k4_tarski(esk1_1(esk3_0),esk2_1(esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.18/0.36  cnf(c_0_12, negated_conjecture, (esk1_1(esk3_0)=k1_mcart_1(esk3_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.18/0.36  cnf(c_0_13, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.36  cnf(c_0_14, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),esk2_1(esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.18/0.36  fof(c_0_15, plain, ![X11, X12, X13, X14]:(((r2_hidden(X11,X13)|~r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14)))&(r2_hidden(X12,X14)|~r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14))))&(~r2_hidden(X11,X13)|~r2_hidden(X12,X14)|r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.18/0.36  cnf(c_0_16, negated_conjecture, (esk2_1(esk3_0)=k2_mcart_1(esk3_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.18/0.36  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_18, negated_conjecture, (k4_tarski(k1_mcart_1(esk3_0),k2_mcart_1(esk3_0))=esk3_0), inference(rw,[status(thm)],[c_0_14, c_0_16])).
% 0.18/0.36  cnf(c_0_19, negated_conjecture, (r2_hidden(k1_mcart_1(esk3_0),X1)|~r2_hidden(esk3_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.18/0.36  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_21, negated_conjecture, (~r2_hidden(k1_mcart_1(esk3_0),esk4_0)|~r2_hidden(k2_mcart_1(esk3_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.36  cnf(c_0_22, negated_conjecture, (r2_hidden(k1_mcart_1(esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_19, c_0_9])).
% 0.18/0.36  cnf(c_0_23, negated_conjecture, (r2_hidden(k2_mcart_1(esk3_0),X1)|~r2_hidden(esk3_0,k2_zfmisc_1(X2,X1))), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 0.18/0.36  cnf(c_0_24, negated_conjecture, (~r2_hidden(k2_mcart_1(esk3_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22])])).
% 0.18/0.36  cnf(c_0_25, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_9]), c_0_24]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 26
% 0.18/0.36  # Proof object clause steps            : 17
% 0.18/0.36  # Proof object formula steps           : 9
% 0.18/0.36  # Proof object conjectures             : 15
% 0.18/0.36  # Proof object clause conjectures      : 12
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 7
% 0.18/0.36  # Proof object initial formulas used   : 4
% 0.18/0.36  # Proof object generating inferences   : 7
% 0.18/0.36  # Proof object simplifying inferences  : 5
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 4
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 8
% 0.18/0.36  # Removed in clause preprocessing      : 0
% 0.18/0.36  # Initial clauses in saturation        : 8
% 0.18/0.36  # Processed clauses                    : 17
% 0.18/0.36  # ...of these trivial                  : 0
% 0.18/0.36  # ...subsumed                          : 0
% 0.18/0.36  # ...remaining for further processing  : 17
% 0.18/0.36  # Other redundant clauses eliminated   : 0
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 3
% 0.18/0.36  # Generated clauses                    : 14
% 0.18/0.36  # ...of the previous two non-trivial   : 16
% 0.18/0.36  # Contextual simplify-reflections      : 0
% 0.18/0.36  # Paramodulations                      : 14
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 0
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 14
% 0.18/0.36  #    Positive orientable unit clauses  : 7
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 1
% 0.18/0.36  #    Non-unit-clauses                  : 6
% 0.18/0.36  # Current number of unprocessed clauses: 2
% 0.18/0.36  # ...number of literals in the above   : 4
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 3
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 3
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 2
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.36  # Unit Clause-clause subsumption calls : 1
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 3
% 0.18/0.36  # BW rewrite match successes           : 3
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 656
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.025 s
% 0.18/0.36  # System time              : 0.004 s
% 0.18/0.36  # Total time               : 0.030 s
% 0.18/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
