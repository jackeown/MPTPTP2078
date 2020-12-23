%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:08 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   17 (  26 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  84 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_ordinal1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_ordinal1(X3)
     => ( ( r2_hidden(X1,X2)
          & r2_hidden(X2,X3) )
       => r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_ordinal1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_ordinal1(X3)
       => ( ( r2_hidden(X1,X2)
            & r2_hidden(X2,X3) )
         => r2_hidden(X1,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t19_ordinal1])).

fof(c_0_4,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v1_ordinal1(X10)
        | ~ r2_hidden(X11,X10)
        | r1_tarski(X11,X10) )
      & ( r2_hidden(esk2_1(X12),X12)
        | v1_ordinal1(X12) )
      & ( ~ r1_tarski(esk2_1(X12),X12)
        | v1_ordinal1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_5,negated_conjecture,
    ( v1_ordinal1(esk5_0)
    & r2_hidden(esk3_0,esk4_0)
    & r2_hidden(esk4_0,esk5_0)
    & ~ r2_hidden(esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v1_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_9,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:53:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C12_11_nc_F1_SE_CS_SP_PS_S002A
% 0.12/0.36  # and selection function SelectNegativeLiterals.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.028 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t19_ordinal1, conjecture, ![X1, X2, X3]:(v1_ordinal1(X3)=>((r2_hidden(X1,X2)&r2_hidden(X2,X3))=>r2_hidden(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_ordinal1)).
% 0.12/0.36  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.12/0.36  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.36  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3]:(v1_ordinal1(X3)=>((r2_hidden(X1,X2)&r2_hidden(X2,X3))=>r2_hidden(X1,X3)))), inference(assume_negation,[status(cth)],[t19_ordinal1])).
% 0.12/0.36  fof(c_0_4, plain, ![X10, X11, X12]:((~v1_ordinal1(X10)|(~r2_hidden(X11,X10)|r1_tarski(X11,X10)))&((r2_hidden(esk2_1(X12),X12)|v1_ordinal1(X12))&(~r1_tarski(esk2_1(X12),X12)|v1_ordinal1(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.12/0.36  fof(c_0_5, negated_conjecture, (v1_ordinal1(esk5_0)&((r2_hidden(esk3_0,esk4_0)&r2_hidden(esk4_0,esk5_0))&~r2_hidden(esk3_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.12/0.36  cnf(c_0_6, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.36  cnf(c_0_7, negated_conjecture, (v1_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  fof(c_0_8, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.36  cnf(c_0_9, negated_conjecture, (r1_tarski(X1,esk5_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.12/0.36  cnf(c_0_10, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_11, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.36  cnf(c_0_12, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.36  cnf(c_0_13, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.36  cnf(c_0_14, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_15, negated_conjecture, (~r2_hidden(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.36  cnf(c_0_16, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 17
% 0.12/0.36  # Proof object clause steps            : 10
% 0.12/0.36  # Proof object formula steps           : 7
% 0.12/0.36  # Proof object conjectures             : 11
% 0.12/0.36  # Proof object clause conjectures      : 8
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 6
% 0.12/0.36  # Proof object initial formulas used   : 3
% 0.12/0.36  # Proof object generating inferences   : 4
% 0.12/0.36  # Proof object simplifying inferences  : 1
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 3
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 10
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 10
% 0.12/0.36  # Processed clauses                    : 23
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 23
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 0
% 0.12/0.36  # Generated clauses                    : 7
% 0.12/0.36  # ...of the previous two non-trivial   : 6
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 7
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 13
% 0.12/0.36  #    Positive orientable unit clauses  : 4
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 1
% 0.12/0.36  #    Non-unit-clauses                  : 8
% 0.12/0.36  # Current number of unprocessed clauses: 3
% 0.12/0.36  # ...number of literals in the above   : 8
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 10
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 2
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 2
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 0
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 0
% 0.12/0.36  # BW rewrite match successes           : 0
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 657
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.029 s
% 0.12/0.36  # System time              : 0.003 s
% 0.12/0.36  # Total time               : 0.032 s
% 0.12/0.36  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
