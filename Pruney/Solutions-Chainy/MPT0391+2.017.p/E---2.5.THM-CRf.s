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
% DateTime   : Thu Dec  3 10:47:09 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   19 (  25 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  58 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_hidden(X1,X2)
          & r1_xboole_0(X1,X3) )
       => r1_xboole_0(k1_setfam_1(X2),X3) ) ),
    inference(assume_negation,[status(cth)],[t9_setfam_1])).

fof(c_0_5,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k4_xboole_0(X7,X8) = X7 )
      & ( k4_xboole_0(X7,X8) != X7
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_6,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    & r1_xboole_0(esk1_0,esk3_0)
    & ~ r1_xboole_0(k1_setfam_1(esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X4,X5,X6] :
      ( ( r1_tarski(X4,X5)
        | ~ r1_tarski(X4,k4_xboole_0(X5,X6)) )
      & ( r1_xboole_0(X4,X6)
        | ~ r1_tarski(X4,k4_xboole_0(X5,X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_8,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X9,X10] :
      ( ~ r2_hidden(X9,X10)
      | r1_tarski(k1_setfam_1(X10),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_11,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk3_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(X1,esk3_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_xboole_0(k1_setfam_1(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:52:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.12/0.37  # and selection function SelectCQIPrecWNTNp.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.038 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t9_setfam_1, conjecture, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_xboole_0(X1,X3))=>r1_xboole_0(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_setfam_1)).
% 0.12/0.37  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.12/0.37  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.12/0.37  fof(t4_setfam_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(k1_setfam_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 0.12/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:((r2_hidden(X1,X2)&r1_xboole_0(X1,X3))=>r1_xboole_0(k1_setfam_1(X2),X3))), inference(assume_negation,[status(cth)],[t9_setfam_1])).
% 0.12/0.38  fof(c_0_5, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k4_xboole_0(X7,X8)=X7)&(k4_xboole_0(X7,X8)!=X7|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.12/0.38  fof(c_0_6, negated_conjecture, ((r2_hidden(esk1_0,esk2_0)&r1_xboole_0(esk1_0,esk3_0))&~r1_xboole_0(k1_setfam_1(esk2_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.12/0.38  fof(c_0_7, plain, ![X4, X5, X6]:((r1_tarski(X4,X5)|~r1_tarski(X4,k4_xboole_0(X5,X6)))&(r1_xboole_0(X4,X6)|~r1_tarski(X4,k4_xboole_0(X5,X6)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.12/0.38  cnf(c_0_8, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.38  cnf(c_0_9, negated_conjecture, (r1_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  fof(c_0_10, plain, ![X9, X10]:(~r2_hidden(X9,X10)|r1_tarski(k1_setfam_1(X10),X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).
% 0.12/0.38  cnf(c_0_11, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_12, negated_conjecture, (k4_xboole_0(esk1_0,esk3_0)=esk1_0), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.12/0.38  cnf(c_0_13, plain, (r1_tarski(k1_setfam_1(X2),X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_14, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (r1_xboole_0(X1,esk3_0)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.38  cnf(c_0_16, negated_conjecture, (r1_tarski(k1_setfam_1(esk2_0),esk1_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.38  cnf(c_0_17, negated_conjecture, (~r1_xboole_0(k1_setfam_1(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 19
% 0.12/0.38  # Proof object clause steps            : 10
% 0.12/0.38  # Proof object formula steps           : 9
% 0.12/0.38  # Proof object conjectures             : 10
% 0.12/0.38  # Proof object clause conjectures      : 7
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 6
% 0.12/0.38  # Proof object initial formulas used   : 4
% 0.12/0.38  # Proof object generating inferences   : 4
% 0.12/0.38  # Proof object simplifying inferences  : 1
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 4
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 8
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 8
% 0.12/0.38  # Processed clauses                    : 18
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 0
% 0.12/0.38  # ...remaining for further processing  : 18
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 0
% 0.12/0.38  # Generated clauses                    : 5
% 0.12/0.38  # ...of the previous two non-trivial   : 3
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 5
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 10
% 0.12/0.38  #    Positive orientable unit clauses  : 4
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 1
% 0.12/0.38  #    Non-unit-clauses                  : 5
% 0.12/0.38  # Current number of unprocessed clauses: 1
% 0.12/0.38  # ...number of literals in the above   : 2
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 8
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 2
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 2
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.38  # Unit Clause-clause subsumption calls : 0
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 0
% 0.12/0.38  # BW rewrite match successes           : 0
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 458
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.038 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.042 s
% 0.12/0.38  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
