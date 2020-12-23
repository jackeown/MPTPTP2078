%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:31 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  52 expanded)
%              Number of clauses        :   19 (  24 expanded)
%              Number of leaves         :    4 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   70 ( 171 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(s1_xboole_0__e3_53__ordinal1,axiom,(
    ! [X1] :
    ? [X2] :
    ! [X3] :
      ( r2_hidden(X3,X2)
    <=> ( r2_hidden(X3,X1)
        & v3_ordinal1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

fof(t38_ordinal1,conjecture,(
    ! [X1] :
      ~ ! [X2] :
          ( v3_ordinal1(X2)
         => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_ordinal1)).

fof(c_0_4,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | ~ r1_tarski(X12,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_5,plain,(
    ! [X8] :
      ( ( v3_ordinal1(esk3_1(X8))
        | r2_hidden(esk2_1(X8),X8) )
      & ( r1_tarski(X8,esk3_1(X8))
        | r2_hidden(esk2_1(X8),X8) )
      & ( v3_ordinal1(esk3_1(X8))
        | ~ v3_ordinal1(esk2_1(X8)) )
      & ( r1_tarski(X8,esk3_1(X8))
        | ~ v3_ordinal1(esk2_1(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_ordinal1])])])])])).

fof(c_0_6,plain,(
    ! [X4,X6,X7] :
      ( ( r2_hidden(X6,X4)
        | ~ r2_hidden(X6,esk1_1(X4)) )
      & ( v3_ordinal1(X6)
        | ~ r2_hidden(X6,esk1_1(X4)) )
      & ( ~ r2_hidden(X7,X4)
        | ~ v3_ordinal1(X7)
        | r2_hidden(X7,esk1_1(X4)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[s1_xboole_0__e3_53__ordinal1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ~ ! [X2] :
            ( v3_ordinal1(X2)
           => r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t38_ordinal1])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,esk3_1(X1))
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,esk1_1(X2))
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v3_ordinal1(esk3_1(X1))
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_12,negated_conjecture,(
    ! [X14] :
      ( ~ v3_ordinal1(X14)
      | r2_hidden(X14,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,esk3_1(X1))
    | ~ v3_ordinal1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( v3_ordinal1(esk3_1(X1))
    | ~ v3_ordinal1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | ~ r2_hidden(esk3_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(esk3_1(X1),esk1_1(X2))
    | r2_hidden(esk2_1(X1),X1)
    | ~ r2_hidden(esk3_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( ~ v3_ordinal1(esk2_1(X1))
    | ~ r2_hidden(esk3_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk3_1(X1),esk1_1(X2))
    | ~ v3_ordinal1(esk2_1(X1))
    | ~ r2_hidden(esk3_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_1(esk1_1(X1)),esk1_1(X1))
    | ~ r2_hidden(esk3_1(esk1_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk3_1(X1),esk4_0)
    | r2_hidden(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_11])).

cnf(c_0_22,plain,
    ( ~ v3_ordinal1(esk2_1(esk1_1(X1)))
    | ~ r2_hidden(esk3_1(esk1_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk3_1(X1),esk4_0)
    | ~ v3_ordinal1(esk2_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_24,plain,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk1_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk2_1(esk1_1(esk4_0)),esk1_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( ~ v3_ordinal1(esk2_1(esk1_1(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:56:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_N___023_B07_F1_SP_PI_Q7_CS_SE_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.026 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.37  fof(t36_ordinal1, axiom, ![X1]:~((![X2]:(r2_hidden(X2,X1)=>v3_ordinal1(X2))&![X2]:(v3_ordinal1(X2)=>~(r1_tarski(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_ordinal1)).
% 0.19/0.37  fof(s1_xboole_0__e3_53__ordinal1, axiom, ![X1]:?[X2]:![X3]:(r2_hidden(X3,X2)<=>(r2_hidden(X3,X1)&v3_ordinal1(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s1_xboole_0__e3_53__ordinal1)).
% 0.19/0.37  fof(t38_ordinal1, conjecture, ![X1]:~(![X2]:(v3_ordinal1(X2)=>r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_ordinal1)).
% 0.19/0.37  fof(c_0_4, plain, ![X11, X12]:(~r2_hidden(X11,X12)|~r1_tarski(X12,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.37  fof(c_0_5, plain, ![X8]:(((v3_ordinal1(esk3_1(X8))|r2_hidden(esk2_1(X8),X8))&(r1_tarski(X8,esk3_1(X8))|r2_hidden(esk2_1(X8),X8)))&((v3_ordinal1(esk3_1(X8))|~v3_ordinal1(esk2_1(X8)))&(r1_tarski(X8,esk3_1(X8))|~v3_ordinal1(esk2_1(X8))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_ordinal1])])])])])).
% 0.19/0.37  fof(c_0_6, plain, ![X4, X6, X7]:(((r2_hidden(X6,X4)|~r2_hidden(X6,esk1_1(X4)))&(v3_ordinal1(X6)|~r2_hidden(X6,esk1_1(X4))))&(~r2_hidden(X7,X4)|~v3_ordinal1(X7)|r2_hidden(X7,esk1_1(X4)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[s1_xboole_0__e3_53__ordinal1])])])])])])).
% 0.19/0.37  fof(c_0_7, negated_conjecture, ~(![X1]:~(![X2]:(v3_ordinal1(X2)=>r2_hidden(X2,X1)))), inference(assume_negation,[status(cth)],[t38_ordinal1])).
% 0.19/0.37  cnf(c_0_8, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.37  cnf(c_0_9, plain, (r1_tarski(X1,esk3_1(X1))|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_10, plain, (r2_hidden(X1,esk1_1(X2))|~r2_hidden(X1,X2)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_11, plain, (v3_ordinal1(esk3_1(X1))|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  fof(c_0_12, negated_conjecture, ![X14]:(~v3_ordinal1(X14)|r2_hidden(X14,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.37  cnf(c_0_13, plain, (r1_tarski(X1,esk3_1(X1))|~v3_ordinal1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_14, plain, (v3_ordinal1(esk3_1(X1))|~v3_ordinal1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_15, plain, (r2_hidden(esk2_1(X1),X1)|~r2_hidden(esk3_1(X1),X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.37  cnf(c_0_16, plain, (r2_hidden(esk3_1(X1),esk1_1(X2))|r2_hidden(esk2_1(X1),X1)|~r2_hidden(esk3_1(X1),X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (r2_hidden(X1,esk4_0)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_18, plain, (~v3_ordinal1(esk2_1(X1))|~r2_hidden(esk3_1(X1),X1)), inference(spm,[status(thm)],[c_0_8, c_0_13])).
% 0.19/0.37  cnf(c_0_19, plain, (r2_hidden(esk3_1(X1),esk1_1(X2))|~v3_ordinal1(esk2_1(X1))|~r2_hidden(esk3_1(X1),X2)), inference(spm,[status(thm)],[c_0_10, c_0_14])).
% 0.19/0.37  cnf(c_0_20, plain, (r2_hidden(esk2_1(esk1_1(X1)),esk1_1(X1))|~r2_hidden(esk3_1(esk1_1(X1)),X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (r2_hidden(esk3_1(X1),esk4_0)|r2_hidden(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_17, c_0_11])).
% 0.19/0.37  cnf(c_0_22, plain, (~v3_ordinal1(esk2_1(esk1_1(X1)))|~r2_hidden(esk3_1(esk1_1(X1)),X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(esk3_1(X1),esk4_0)|~v3_ordinal1(esk2_1(X1))), inference(spm,[status(thm)],[c_0_17, c_0_14])).
% 0.19/0.37  cnf(c_0_24, plain, (v3_ordinal1(X1)|~r2_hidden(X1,esk1_1(X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(esk2_1(esk1_1(esk4_0)),esk1_1(esk4_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (~v3_ordinal1(esk2_1(esk1_1(esk4_0)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 28
% 0.19/0.37  # Proof object clause steps            : 19
% 0.19/0.37  # Proof object formula steps           : 9
% 0.19/0.37  # Proof object conjectures             : 9
% 0.19/0.37  # Proof object clause conjectures      : 6
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 8
% 0.19/0.37  # Proof object initial formulas used   : 4
% 0.19/0.37  # Proof object generating inferences   : 11
% 0.19/0.37  # Proof object simplifying inferences  : 1
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 4
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 9
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 9
% 0.19/0.37  # Processed clauses                    : 25
% 0.19/0.37  # ...of these trivial                  : 2
% 0.19/0.37  # ...subsumed                          : 2
% 0.19/0.37  # ...remaining for further processing  : 21
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 28
% 0.19/0.37  # ...of the previous two non-trivial   : 24
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 28
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 21
% 0.19/0.37  #    Positive orientable unit clauses  : 2
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 17
% 0.19/0.37  # Current number of unprocessed clauses: 8
% 0.19/0.37  # ...number of literals in the above   : 20
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 0
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 20
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 18
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.19/0.37  # Unit Clause-clause subsumption calls : 5
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 948
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.026 s
% 0.19/0.37  # System time              : 0.005 s
% 0.19/0.37  # Total time               : 0.031 s
% 0.19/0.37  # Maximum resident set size: 1552 pages
%------------------------------------------------------------------------------
