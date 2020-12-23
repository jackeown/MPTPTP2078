%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:45 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   16 (  29 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    2 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  89 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X2,X3) )
       => r1_tarski(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t1_xboole_1])).

fof(c_0_3,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_4,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_5,c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r2_hidden(esk1_2(X1,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_0,X1),esk3_0)
    | r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n018.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:14:11 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___008_C45_F1_PI_SE_Q4_CS_SP_S0Y
% 0.12/0.35  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.026 s
% 0.12/0.35  
% 0.12/0.35  # Proof found!
% 0.12/0.35  # SZS status Theorem
% 0.12/0.35  # SZS output start CNFRefutation
% 0.12/0.35  fof(t1_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.12/0.35  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.35  fof(c_0_2, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3))), inference(assume_negation,[status(cth)],[t1_xboole_1])).
% 0.12/0.35  fof(c_0_3, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.35  fof(c_0_4, negated_conjecture, ((r1_tarski(esk2_0,esk3_0)&r1_tarski(esk3_0,esk4_0))&~r1_tarski(esk2_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).
% 0.12/0.35  cnf(c_0_5, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.35  cnf(c_0_6, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.35  cnf(c_0_7, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.35  cnf(c_0_8, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.35  cnf(c_0_9, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_5, c_0_6])).
% 0.12/0.35  cnf(c_0_10, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk2_0)), inference(spm,[status(thm)],[c_0_5, c_0_7])).
% 0.12/0.35  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.35  cnf(c_0_12, negated_conjecture, (r1_tarski(X1,esk4_0)|~r2_hidden(esk1_2(X1,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.12/0.35  cnf(c_0_13, negated_conjecture, (r2_hidden(esk1_2(esk2_0,X1),esk3_0)|r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.35  cnf(c_0_14, negated_conjecture, (~r1_tarski(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.35  cnf(c_0_15, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), ['proof']).
% 0.12/0.35  # SZS output end CNFRefutation
% 0.12/0.35  # Proof object total steps             : 16
% 0.12/0.35  # Proof object clause steps            : 11
% 0.12/0.35  # Proof object formula steps           : 5
% 0.12/0.35  # Proof object conjectures             : 11
% 0.12/0.35  # Proof object clause conjectures      : 8
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 6
% 0.12/0.35  # Proof object initial formulas used   : 2
% 0.12/0.35  # Proof object generating inferences   : 5
% 0.12/0.35  # Proof object simplifying inferences  : 1
% 0.12/0.35  # Training examples: 0 positive, 0 negative
% 0.12/0.35  # Parsed axioms                        : 2
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 6
% 0.12/0.35  # Removed in clause preprocessing      : 0
% 0.12/0.35  # Initial clauses in saturation        : 6
% 0.12/0.35  # Processed clauses                    : 11
% 0.12/0.35  # ...of these trivial                  : 0
% 0.12/0.35  # ...subsumed                          : 0
% 0.12/0.35  # ...remaining for further processing  : 11
% 0.12/0.35  # Other redundant clauses eliminated   : 0
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 0
% 0.12/0.35  # Backward-rewritten                   : 0
% 0.12/0.35  # Generated clauses                    : 9
% 0.12/0.35  # ...of the previous two non-trivial   : 5
% 0.12/0.35  # Contextual simplify-reflections      : 0
% 0.12/0.35  # Paramodulations                      : 9
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 0
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
% 0.12/0.35  # Current number of processed clauses  : 11
% 0.12/0.35  #    Positive orientable unit clauses  : 3
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 1
% 0.12/0.35  #    Non-unit-clauses                  : 7
% 0.12/0.35  # Current number of unprocessed clauses: 0
% 0.12/0.35  # ...number of literals in the above   : 0
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 0
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 5
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 5
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.35  # Unit Clause-clause subsumption calls : 2
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 5
% 0.12/0.35  # BW rewrite match successes           : 0
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 427
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.027 s
% 0.12/0.35  # System time              : 0.002 s
% 0.12/0.35  # Total time               : 0.029 s
% 0.12/0.35  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
