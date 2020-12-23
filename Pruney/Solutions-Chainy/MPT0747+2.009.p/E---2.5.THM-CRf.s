%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:31 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  35 expanded)
%              Number of clauses        :   12 (  14 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :   45 ( 105 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t36_ordinal1,axiom,(
    ! [X1] :
      ~ ( ! [X2] :
            ( r2_hidden(X2,X1)
           => v3_ordinal1(X2) )
        & ! [X2] :
            ( v3_ordinal1(X2)
           => ~ r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_ordinal1)).

fof(t37_ordinal1,conjecture,(
    ! [X1] :
      ~ ! [X2] :
          ( r2_hidden(X2,X1)
        <=> v3_ordinal1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).

fof(c_0_3,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ r1_tarski(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_4,plain,(
    ! [X3] :
      ( ( v3_ordinal1(esk2_1(X3))
        | r2_hidden(esk1_1(X3),X3) )
      & ( r1_tarski(X3,esk2_1(X3))
        | r2_hidden(esk1_1(X3),X3) )
      & ( v3_ordinal1(esk2_1(X3))
        | ~ v3_ordinal1(esk1_1(X3)) )
      & ( r1_tarski(X3,esk2_1(X3))
        | ~ v3_ordinal1(esk1_1(X3)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_ordinal1])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ~ ! [X2] :
            ( r2_hidden(X2,X1)
          <=> v3_ordinal1(X2) ) ),
    inference(assume_negation,[status(cth)],[t37_ordinal1])).

cnf(c_0_6,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r1_tarski(X1,esk2_1(X1))
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,(
    ! [X9] :
      ( ( ~ r2_hidden(X9,esk3_0)
        | v3_ordinal1(X9) )
      & ( ~ v3_ordinal1(X9)
        | r2_hidden(X9,esk3_0) ) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,esk2_1(X1))
    | ~ v3_ordinal1(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | ~ r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v3_ordinal1(esk2_1(X1))
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( ~ v3_ordinal1(esk1_1(X1))
    | ~ r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_9])).

cnf(c_0_14,plain,
    ( v3_ordinal1(esk2_1(X1))
    | ~ v3_ordinal1(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ v3_ordinal1(esk1_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_11]),c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:58:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_N___023_B07_F1_SP_PI_Q7_CS_SE_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.026 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.38  fof(t36_ordinal1, axiom, ![X1]:~((![X2]:(r2_hidden(X2,X1)=>v3_ordinal1(X2))&![X2]:(v3_ordinal1(X2)=>~(r1_tarski(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_ordinal1)).
% 0.20/0.38  fof(t37_ordinal1, conjecture, ![X1]:~(![X2]:(r2_hidden(X2,X1)<=>v3_ordinal1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_ordinal1)).
% 0.20/0.38  fof(c_0_3, plain, ![X6, X7]:(~r2_hidden(X6,X7)|~r1_tarski(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.38  fof(c_0_4, plain, ![X3]:(((v3_ordinal1(esk2_1(X3))|r2_hidden(esk1_1(X3),X3))&(r1_tarski(X3,esk2_1(X3))|r2_hidden(esk1_1(X3),X3)))&((v3_ordinal1(esk2_1(X3))|~v3_ordinal1(esk1_1(X3)))&(r1_tarski(X3,esk2_1(X3))|~v3_ordinal1(esk1_1(X3))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_ordinal1])])])])])).
% 0.20/0.38  fof(c_0_5, negated_conjecture, ~(![X1]:~(![X2]:(r2_hidden(X2,X1)<=>v3_ordinal1(X2)))), inference(assume_negation,[status(cth)],[t37_ordinal1])).
% 0.20/0.38  cnf(c_0_6, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.20/0.38  cnf(c_0_7, plain, (r1_tarski(X1,esk2_1(X1))|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  fof(c_0_8, negated_conjecture, ![X9]:((~r2_hidden(X9,esk3_0)|v3_ordinal1(X9))&(~v3_ordinal1(X9)|r2_hidden(X9,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.38  cnf(c_0_9, plain, (r1_tarski(X1,esk2_1(X1))|~v3_ordinal1(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  cnf(c_0_10, plain, (r2_hidden(esk1_1(X1),X1)|~r2_hidden(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.20/0.38  cnf(c_0_11, negated_conjecture, (r2_hidden(X1,esk3_0)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_12, plain, (v3_ordinal1(esk2_1(X1))|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  cnf(c_0_13, plain, (~v3_ordinal1(esk1_1(X1))|~r2_hidden(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_6, c_0_9])).
% 0.20/0.38  cnf(c_0_14, plain, (v3_ordinal1(esk2_1(X1))|~v3_ordinal1(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (r2_hidden(esk1_1(esk3_0),esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (~v3_ordinal1(esk1_1(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_11]), c_0_14])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 19
% 0.20/0.38  # Proof object clause steps            : 12
% 0.20/0.38  # Proof object formula steps           : 7
% 0.20/0.38  # Proof object conjectures             : 8
% 0.20/0.38  # Proof object clause conjectures      : 5
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 7
% 0.20/0.38  # Proof object initial formulas used   : 3
% 0.20/0.38  # Proof object generating inferences   : 5
% 0.20/0.38  # Proof object simplifying inferences  : 3
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 3
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 7
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 7
% 0.20/0.38  # Processed clauses                    : 11
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 11
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 6
% 0.20/0.38  # ...of the previous two non-trivial   : 4
% 0.20/0.38  # Contextual simplify-reflections      : 2
% 0.20/0.38  # Paramodulations                      : 6
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 11
% 0.20/0.38  #    Positive orientable unit clauses  : 1
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 9
% 0.20/0.38  # Current number of unprocessed clauses: 0
% 0.20/0.38  # ...number of literals in the above   : 0
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 0
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 3
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 3
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.20/0.38  # Unit Clause-clause subsumption calls : 0
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 0
% 0.20/0.38  # BW rewrite match successes           : 0
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 462
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.025 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.029 s
% 0.20/0.38  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
