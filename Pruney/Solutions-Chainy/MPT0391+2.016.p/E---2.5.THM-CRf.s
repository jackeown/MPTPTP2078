%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:09 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   23 (  29 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  61 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_xboole_0(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_hidden(X1,X2)
          & r1_xboole_0(X1,X3) )
       => r1_xboole_0(k1_setfam_1(X2),X3) ) ),
    inference(assume_negation,[status(cth)],[t9_setfam_1])).

fof(c_0_6,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | r1_tarski(k1_setfam_1(X12),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

fof(c_0_7,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    & r1_xboole_0(esk1_0,esk3_0)
    & ~ r1_xboole_0(k1_setfam_1(esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_9,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | r1_xboole_0(X8,k4_xboole_0(X10,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_10,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X6,X7] :
      ( ( ~ r1_xboole_0(X6,X7)
        | k4_xboole_0(X6,X7) = X6 )
      & ( k4_xboole_0(X6,X7) != X6
        | r1_xboole_0(X6,X7) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(k1_setfam_1(esk2_0),k4_xboole_0(X1,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk1_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_xboole_0(k1_setfam_1(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.29  % Computer   : n020.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % WCLimit    : 600
% 0.10/0.29  % DateTime   : Tue Dec  1 17:55:07 EST 2020
% 0.10/0.29  % CPUTime    : 
% 0.10/0.29  # Version: 2.5pre002
% 0.10/0.30  # No SInE strategy applied
% 0.10/0.30  # Trying AutoSched0 for 299 seconds
% 0.10/0.31  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.10/0.31  # and selection function SelectCQIPrecWNTNp.
% 0.10/0.31  #
% 0.10/0.31  # Preprocessing time       : 0.014 s
% 0.10/0.31  # Presaturation interreduction done
% 0.10/0.31  
% 0.10/0.31  # Proof found!
% 0.10/0.31  # SZS status Theorem
% 0.10/0.31  # SZS output start CNFRefutation
% 0.10/0.31  fof(t9_setfam_1, conjecture, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_xboole_0(X1,X3))=>r1_xboole_0(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_setfam_1)).
% 0.10/0.31  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.10/0.31  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.10/0.31  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.10/0.31  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.10/0.31  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:((r2_hidden(X1,X2)&r1_xboole_0(X1,X3))=>r1_xboole_0(k1_setfam_1(X2),X3))), inference(assume_negation,[status(cth)],[t9_setfam_1])).
% 0.10/0.31  fof(c_0_6, plain, ![X11, X12]:(~r2_hidden(X11,X12)|r1_tarski(k1_setfam_1(X12),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.10/0.31  fof(c_0_7, negated_conjecture, ((r2_hidden(esk1_0,esk2_0)&r1_xboole_0(esk1_0,esk3_0))&~r1_xboole_0(k1_setfam_1(esk2_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.10/0.31  fof(c_0_8, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.10/0.31  fof(c_0_9, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|r1_xboole_0(X8,k4_xboole_0(X10,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.10/0.31  cnf(c_0_10, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.10/0.31  cnf(c_0_11, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.10/0.31  fof(c_0_12, plain, ![X6, X7]:((~r1_xboole_0(X6,X7)|k4_xboole_0(X6,X7)=X6)&(k4_xboole_0(X6,X7)!=X6|r1_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.10/0.31  cnf(c_0_13, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.10/0.31  cnf(c_0_14, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.10/0.31  cnf(c_0_15, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.10/0.31  cnf(c_0_16, negated_conjecture, (r1_tarski(k1_setfam_1(esk2_0),esk1_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.10/0.31  cnf(c_0_17, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.31  cnf(c_0_18, negated_conjecture, (r1_xboole_0(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.10/0.31  cnf(c_0_19, negated_conjecture, (r1_xboole_0(k1_setfam_1(esk2_0),k4_xboole_0(X1,esk1_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.10/0.31  cnf(c_0_20, negated_conjecture, (k4_xboole_0(esk3_0,esk1_0)=esk3_0), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.10/0.31  cnf(c_0_21, negated_conjecture, (~r1_xboole_0(k1_setfam_1(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.10/0.31  cnf(c_0_22, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), ['proof']).
% 0.10/0.31  # SZS output end CNFRefutation
% 0.10/0.31  # Proof object total steps             : 23
% 0.10/0.31  # Proof object clause steps            : 12
% 0.10/0.31  # Proof object formula steps           : 11
% 0.10/0.31  # Proof object conjectures             : 11
% 0.10/0.31  # Proof object clause conjectures      : 8
% 0.10/0.31  # Proof object formula conjectures     : 3
% 0.10/0.31  # Proof object initial clauses used    : 7
% 0.10/0.31  # Proof object initial formulas used   : 5
% 0.10/0.31  # Proof object generating inferences   : 5
% 0.10/0.31  # Proof object simplifying inferences  : 1
% 0.10/0.31  # Training examples: 0 positive, 0 negative
% 0.10/0.31  # Parsed axioms                        : 5
% 0.10/0.31  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.31  # Initial clauses                      : 8
% 0.10/0.31  # Removed in clause preprocessing      : 0
% 0.10/0.31  # Initial clauses in saturation        : 8
% 0.10/0.31  # Processed clauses                    : 21
% 0.10/0.31  # ...of these trivial                  : 0
% 0.10/0.31  # ...subsumed                          : 0
% 0.10/0.31  # ...remaining for further processing  : 21
% 0.10/0.31  # Other redundant clauses eliminated   : 0
% 0.10/0.31  # Clauses deleted for lack of memory   : 0
% 0.10/0.31  # Backward-subsumed                    : 0
% 0.10/0.31  # Backward-rewritten                   : 0
% 0.10/0.31  # Generated clauses                    : 11
% 0.10/0.31  # ...of the previous two non-trivial   : 7
% 0.10/0.31  # Contextual simplify-reflections      : 0
% 0.10/0.31  # Paramodulations                      : 11
% 0.10/0.31  # Factorizations                       : 0
% 0.10/0.31  # Equation resolutions                 : 0
% 0.10/0.31  # Propositional unsat checks           : 0
% 0.10/0.31  #    Propositional check models        : 0
% 0.10/0.31  #    Propositional check unsatisfiable : 0
% 0.10/0.31  #    Propositional clauses             : 0
% 0.10/0.31  #    Propositional clauses after purity: 0
% 0.10/0.31  #    Propositional unsat core size     : 0
% 0.10/0.31  #    Propositional preprocessing time  : 0.000
% 0.10/0.31  #    Propositional encoding time       : 0.000
% 0.10/0.31  #    Propositional solver time         : 0.000
% 0.10/0.31  #    Success case prop preproc time    : 0.000
% 0.10/0.31  #    Success case prop encoding time   : 0.000
% 0.10/0.31  #    Success case prop solver time     : 0.000
% 0.10/0.31  # Current number of processed clauses  : 13
% 0.10/0.31  #    Positive orientable unit clauses  : 7
% 0.10/0.31  #    Positive unorientable unit clauses: 0
% 0.10/0.31  #    Negative unit clauses             : 1
% 0.10/0.31  #    Non-unit-clauses                  : 5
% 0.10/0.31  # Current number of unprocessed clauses: 0
% 0.10/0.31  # ...number of literals in the above   : 0
% 0.10/0.31  # Current number of archived formulas  : 0
% 0.10/0.31  # Current number of archived clauses   : 8
% 0.10/0.31  # Clause-clause subsumption calls (NU) : 6
% 0.10/0.31  # Rec. Clause-clause subsumption calls : 6
% 0.10/0.31  # Non-unit clause-clause subsumptions  : 0
% 0.10/0.31  # Unit Clause-clause subsumption calls : 0
% 0.10/0.31  # Rewrite failures with RHS unbound    : 0
% 0.10/0.31  # BW rewrite match attempts            : 0
% 0.10/0.31  # BW rewrite match successes           : 0
% 0.10/0.31  # Condensation attempts                : 0
% 0.10/0.31  # Condensation successes               : 0
% 0.10/0.31  # Termbank termtop insertions          : 526
% 0.10/0.31  
% 0.10/0.31  # -------------------------------------------------
% 0.10/0.31  # User time                : 0.015 s
% 0.10/0.31  # System time              : 0.002 s
% 0.10/0.31  # Total time               : 0.017 s
% 0.10/0.31  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
