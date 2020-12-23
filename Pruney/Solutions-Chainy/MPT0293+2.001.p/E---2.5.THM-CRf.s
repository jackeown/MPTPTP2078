%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:21 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  75 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t80_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t79_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(t100_zfmisc_1,conjecture,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(c_0_6,plain,(
    ! [X14,X15] :
      ( ( ~ r1_tarski(k1_tarski(X14),X15)
        | r2_hidden(X14,X15) )
      & ( ~ r2_hidden(X14,X15)
        | r1_tarski(k1_tarski(X14),X15) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_7,plain,(
    ! [X20] : r1_tarski(k1_tarski(X20),k1_zfmisc_1(X20)) ),
    inference(variable_rename,[status(thm)],[t80_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X16,X17] :
      ( ~ r2_hidden(X16,X17)
      | r1_tarski(X16,k3_tarski(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

fof(c_0_9,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | r1_tarski(k1_zfmisc_1(X18),k1_zfmisc_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_tarski(esk1_2(X1,X2),k3_tarski(X1))
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(assume_negation,[status(cth)],[t100_zfmisc_1])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_zfmisc_1(esk1_2(X1,X2)),k1_zfmisc_1(k3_tarski(X1)))
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,negated_conjecture,(
    ~ r1_tarski(esk2_0,k1_zfmisc_1(k3_tarski(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_zfmisc_1(k3_tarski(X1)))
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k1_zfmisc_1(k3_tarski(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 19:04:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.22/0.53  # and selection function SelectSmallestOrientable.
% 0.22/0.53  #
% 0.22/0.53  # Preprocessing time       : 0.016 s
% 0.22/0.53  # Presaturation interreduction done
% 0.22/0.53  
% 0.22/0.53  # Proof found!
% 0.22/0.53  # SZS status Theorem
% 0.22/0.53  # SZS output start CNFRefutation
% 0.22/0.53  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.22/0.53  fof(t80_zfmisc_1, axiom, ![X1]:r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 0.22/0.53  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.22/0.53  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.22/0.53  fof(t79_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 0.22/0.53  fof(t100_zfmisc_1, conjecture, ![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 0.22/0.53  fof(c_0_6, plain, ![X14, X15]:((~r1_tarski(k1_tarski(X14),X15)|r2_hidden(X14,X15))&(~r2_hidden(X14,X15)|r1_tarski(k1_tarski(X14),X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.22/0.53  fof(c_0_7, plain, ![X20]:r1_tarski(k1_tarski(X20),k1_zfmisc_1(X20)), inference(variable_rename,[status(thm)],[t80_zfmisc_1])).
% 0.22/0.53  fof(c_0_8, plain, ![X16, X17]:(~r2_hidden(X16,X17)|r1_tarski(X16,k3_tarski(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.22/0.53  fof(c_0_9, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.22/0.53  cnf(c_0_10, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.22/0.53  cnf(c_0_11, plain, (r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.22/0.53  fof(c_0_12, plain, ![X18, X19]:(~r1_tarski(X18,X19)|r1_tarski(k1_zfmisc_1(X18),k1_zfmisc_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_zfmisc_1])])).
% 0.22/0.53  cnf(c_0_13, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.22/0.53  cnf(c_0_14, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.53  cnf(c_0_15, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.53  cnf(c_0_16, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.22/0.53  cnf(c_0_17, plain, (r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.53  cnf(c_0_18, plain, (r1_tarski(esk1_2(X1,X2),k3_tarski(X1))|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.22/0.53  fof(c_0_19, negated_conjecture, ~(![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(assume_negation,[status(cth)],[t100_zfmisc_1])).
% 0.22/0.53  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.22/0.53  cnf(c_0_21, plain, (r1_tarski(k1_zfmisc_1(esk1_2(X1,X2)),k1_zfmisc_1(k3_tarski(X1)))|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.22/0.53  fof(c_0_22, negated_conjecture, ~r1_tarski(esk2_0,k1_zfmisc_1(k3_tarski(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.22/0.53  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.53  cnf(c_0_24, plain, (r2_hidden(esk1_2(X1,X2),k1_zfmisc_1(k3_tarski(X1)))|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.22/0.53  cnf(c_0_25, negated_conjecture, (~r1_tarski(esk2_0,k1_zfmisc_1(k3_tarski(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.22/0.53  cnf(c_0_26, plain, (r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.22/0.53  cnf(c_0_27, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26])]), ['proof']).
% 0.22/0.53  # SZS output end CNFRefutation
% 0.22/0.53  # Proof object total steps             : 28
% 0.22/0.53  # Proof object clause steps            : 15
% 0.22/0.53  # Proof object formula steps           : 13
% 0.22/0.53  # Proof object conjectures             : 5
% 0.22/0.53  # Proof object clause conjectures      : 2
% 0.22/0.53  # Proof object formula conjectures     : 3
% 0.22/0.53  # Proof object initial clauses used    : 8
% 0.22/0.53  # Proof object initial formulas used   : 6
% 0.22/0.53  # Proof object generating inferences   : 6
% 0.22/0.53  # Proof object simplifying inferences  : 2
% 0.22/0.53  # Training examples: 0 positive, 0 negative
% 0.22/0.53  # Parsed axioms                        : 8
% 0.22/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.53  # Initial clauses                      : 15
% 0.22/0.53  # Removed in clause preprocessing      : 0
% 0.22/0.53  # Initial clauses in saturation        : 15
% 0.22/0.53  # Processed clauses                    : 1133
% 0.22/0.53  # ...of these trivial                  : 66
% 0.22/0.53  # ...subsumed                          : 6
% 0.22/0.53  # ...remaining for further processing  : 1061
% 0.22/0.53  # Other redundant clauses eliminated   : 2
% 0.22/0.53  # Clauses deleted for lack of memory   : 0
% 0.22/0.53  # Backward-subsumed                    : 1
% 0.22/0.53  # Backward-rewritten                   : 3
% 0.22/0.53  # Generated clauses                    : 19473
% 0.22/0.53  # ...of the previous two non-trivial   : 18792
% 0.22/0.53  # Contextual simplify-reflections      : 0
% 0.22/0.53  # Paramodulations                      : 19471
% 0.22/0.53  # Factorizations                       : 0
% 0.22/0.53  # Equation resolutions                 : 2
% 0.22/0.53  # Propositional unsat checks           : 0
% 0.22/0.53  #    Propositional check models        : 0
% 0.22/0.53  #    Propositional check unsatisfiable : 0
% 0.22/0.53  #    Propositional clauses             : 0
% 0.22/0.53  #    Propositional clauses after purity: 0
% 0.22/0.53  #    Propositional unsat core size     : 0
% 0.22/0.53  #    Propositional preprocessing time  : 0.000
% 0.22/0.53  #    Propositional encoding time       : 0.000
% 0.22/0.53  #    Propositional solver time         : 0.000
% 0.22/0.53  #    Success case prop preproc time    : 0.000
% 0.22/0.53  #    Success case prop encoding time   : 0.000
% 0.22/0.53  #    Success case prop solver time     : 0.000
% 0.22/0.53  # Current number of processed clauses  : 1041
% 0.22/0.53  #    Positive orientable unit clauses  : 739
% 0.22/0.53  #    Positive unorientable unit clauses: 0
% 0.22/0.53  #    Negative unit clauses             : 0
% 0.22/0.53  #    Non-unit-clauses                  : 302
% 0.22/0.53  # Current number of unprocessed clauses: 17688
% 0.22/0.53  # ...number of literals in the above   : 19353
% 0.22/0.53  # Current number of archived formulas  : 0
% 0.22/0.53  # Current number of archived clauses   : 18
% 0.22/0.53  # Clause-clause subsumption calls (NU) : 6800
% 0.22/0.53  # Rec. Clause-clause subsumption calls : 6753
% 0.22/0.53  # Non-unit clause-clause subsumptions  : 7
% 0.22/0.53  # Unit Clause-clause subsumption calls : 22
% 0.22/0.53  # Rewrite failures with RHS unbound    : 0
% 0.22/0.53  # BW rewrite match attempts            : 15002
% 0.22/0.53  # BW rewrite match successes           : 3
% 0.22/0.53  # Condensation attempts                : 0
% 0.22/0.53  # Condensation successes               : 0
% 0.22/0.53  # Termbank termtop insertions          : 348168
% 0.22/0.53  
% 0.22/0.53  # -------------------------------------------------
% 0.22/0.53  # User time                : 0.150 s
% 0.22/0.53  # System time              : 0.017 s
% 0.22/0.53  # Total time               : 0.167 s
% 0.22/0.53  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
