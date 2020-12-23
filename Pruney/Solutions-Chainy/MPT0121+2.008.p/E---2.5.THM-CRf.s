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
% DateTime   : Thu Dec  3 10:34:58 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   19 (  40 expanded)
%              Number of clauses        :   12 (  16 expanded)
%              Number of leaves         :    3 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 ( 114 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t114_xboole_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X4)
        & r1_xboole_0(X2,X4)
        & r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_xboole_0(X1,X4)
          & r1_xboole_0(X2,X4)
          & r1_xboole_0(X3,X4) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) ) ),
    inference(assume_negation,[status(cth)],[t114_xboole_1])).

fof(c_0_4,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk4_0)
    & r1_xboole_0(esk2_0,esk4_0)
    & r1_xboole_0(esk3_0,esk4_0)
    & ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_6,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X7,X8,X9] :
      ( ( r1_xboole_0(X7,k2_xboole_0(X8,X9))
        | ~ r1_xboole_0(X7,X8)
        | ~ r1_xboole_0(X7,X9) )
      & ( r1_xboole_0(X7,X8)
        | ~ r1_xboole_0(X7,k2_xboole_0(X8,X9)) )
      & ( r1_xboole_0(X7,X9)
        | ~ r1_xboole_0(X7,k2_xboole_0(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_9,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_11,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,k2_xboole_0(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_16,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_11]),c_0_16]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:22:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S02FN
% 0.13/0.36  # and selection function PSelectNonAntiRROptimalLit.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.026 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t114_xboole_1, conjecture, ![X1, X2, X3, X4]:(((r1_xboole_0(X1,X4)&r1_xboole_0(X2,X4))&r1_xboole_0(X3,X4))=>r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_xboole_1)).
% 0.13/0.36  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.13/0.36  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.13/0.36  fof(c_0_3, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_xboole_0(X1,X4)&r1_xboole_0(X2,X4))&r1_xboole_0(X3,X4))=>r1_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4))), inference(assume_negation,[status(cth)],[t114_xboole_1])).
% 0.13/0.36  fof(c_0_4, negated_conjecture, (((r1_xboole_0(esk1_0,esk4_0)&r1_xboole_0(esk2_0,esk4_0))&r1_xboole_0(esk3_0,esk4_0))&~r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.13/0.36  fof(c_0_5, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.13/0.36  cnf(c_0_6, negated_conjecture, (~r1_xboole_0(k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_7, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.36  fof(c_0_8, plain, ![X7, X8, X9]:((r1_xboole_0(X7,k2_xboole_0(X8,X9))|~r1_xboole_0(X7,X8)|~r1_xboole_0(X7,X9))&((r1_xboole_0(X7,X8)|~r1_xboole_0(X7,k2_xboole_0(X8,X9)))&(r1_xboole_0(X7,X9)|~r1_xboole_0(X7,k2_xboole_0(X8,X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.13/0.36  cnf(c_0_9, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_10, negated_conjecture, (~r1_xboole_0(esk4_0,k2_xboole_0(k2_xboole_0(esk1_0,esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.13/0.36  cnf(c_0_11, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.36  cnf(c_0_12, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_7, c_0_9])).
% 0.13/0.36  cnf(c_0_13, negated_conjecture, (r1_xboole_0(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_14, negated_conjecture, (r1_xboole_0(esk1_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.36  cnf(c_0_15, negated_conjecture, (~r1_xboole_0(esk4_0,k2_xboole_0(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])])).
% 0.13/0.36  cnf(c_0_16, negated_conjecture, (r1_xboole_0(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_7, c_0_13])).
% 0.13/0.36  cnf(c_0_17, negated_conjecture, (r1_xboole_0(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_7, c_0_14])).
% 0.13/0.36  cnf(c_0_18, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_11]), c_0_16]), c_0_17])]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 19
% 0.13/0.36  # Proof object clause steps            : 12
% 0.13/0.36  # Proof object formula steps           : 7
% 0.13/0.36  # Proof object conjectures             : 13
% 0.13/0.36  # Proof object clause conjectures      : 10
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 6
% 0.13/0.36  # Proof object initial formulas used   : 3
% 0.13/0.36  # Proof object generating inferences   : 6
% 0.13/0.36  # Proof object simplifying inferences  : 5
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 3
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 8
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 8
% 0.13/0.36  # Processed clauses                    : 21
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 0
% 0.13/0.36  # ...remaining for further processing  : 21
% 0.13/0.36  # Other redundant clauses eliminated   : 0
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 0
% 0.13/0.36  # Generated clauses                    : 12
% 0.13/0.36  # ...of the previous two non-trivial   : 8
% 0.13/0.36  # Contextual simplify-reflections      : 0
% 0.13/0.36  # Paramodulations                      : 12
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 0
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 13
% 0.13/0.36  #    Positive orientable unit clauses  : 6
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 3
% 0.13/0.36  #    Non-unit-clauses                  : 4
% 0.13/0.36  # Current number of unprocessed clauses: 3
% 0.13/0.36  # ...number of literals in the above   : 7
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 8
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 18
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 18
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.36  # Unit Clause-clause subsumption calls : 3
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 0
% 0.13/0.36  # BW rewrite match successes           : 0
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 561
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.028 s
% 0.13/0.36  # System time              : 0.001 s
% 0.13/0.36  # Total time               : 0.029 s
% 0.13/0.36  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
