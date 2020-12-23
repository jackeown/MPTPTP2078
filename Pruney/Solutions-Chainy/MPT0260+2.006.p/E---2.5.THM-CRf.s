%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:51 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   27 (  36 expanded)
%              Number of clauses        :   14 (  16 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   63 (  75 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
          & r2_hidden(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t55_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X17,X18,X19] :
      ( ( r2_hidden(X17,X19)
        | ~ r1_tarski(k2_tarski(X17,X18),X19) )
      & ( r2_hidden(X18,X19)
        | ~ r1_tarski(k2_tarski(X17,X18),X19) )
      & ( ~ r2_hidden(X17,X19)
        | ~ r2_hidden(X18,X19)
        | r1_tarski(k2_tarski(X17,X18),X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

fof(c_0_8,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_9,plain,(
    ! [X14,X15,X16] : k2_enumset1(X14,X14,X15,X16) = k1_enumset1(X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_10,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X4,X5,X7,X8,X9] :
      ( ( r2_hidden(esk1_2(X4,X5),X4)
        | r1_xboole_0(X4,X5) )
      & ( r2_hidden(esk1_2(X4,X5),X5)
        | r1_xboole_0(X4,X5) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | ~ r1_xboole_0(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_12,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)
    & r2_hidden(esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(esk2_0,X1)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_14]),c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_24,c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.09/0.31  % Computer   : n002.cluster.edu
% 0.09/0.31  % Model      : x86_64 x86_64
% 0.09/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.31  % Memory     : 8042.1875MB
% 0.09/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.31  % CPULimit   : 60
% 0.09/0.31  % WCLimit    : 600
% 0.09/0.31  % DateTime   : Tue Dec  1 16:51:06 EST 2020
% 0.09/0.31  % CPUTime    : 
% 0.09/0.31  # Version: 2.5pre002
% 0.09/0.31  # No SInE strategy applied
% 0.09/0.31  # Trying AutoSched0 for 299 seconds
% 0.16/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.16/0.34  # and selection function SelectComplexExceptRRHorn.
% 0.16/0.34  #
% 0.16/0.34  # Preprocessing time       : 0.026 s
% 0.16/0.34  # Presaturation interreduction done
% 0.16/0.34  
% 0.16/0.34  # Proof found!
% 0.16/0.34  # SZS status Theorem
% 0.16/0.34  # SZS output start CNFRefutation
% 0.16/0.34  fof(t55_zfmisc_1, conjecture, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.16/0.34  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.16/0.34  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.16/0.34  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.16/0.34  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.16/0.34  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.16/0.34  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3)))), inference(assume_negation,[status(cth)],[t55_zfmisc_1])).
% 0.16/0.34  fof(c_0_7, plain, ![X17, X18, X19]:(((r2_hidden(X17,X19)|~r1_tarski(k2_tarski(X17,X18),X19))&(r2_hidden(X18,X19)|~r1_tarski(k2_tarski(X17,X18),X19)))&(~r2_hidden(X17,X19)|~r2_hidden(X18,X19)|r1_tarski(k2_tarski(X17,X18),X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.16/0.34  fof(c_0_8, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.16/0.34  fof(c_0_9, plain, ![X14, X15, X16]:k2_enumset1(X14,X14,X15,X16)=k1_enumset1(X14,X15,X16), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.16/0.34  fof(c_0_10, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.16/0.34  fof(c_0_11, plain, ![X4, X5, X7, X8, X9]:(((r2_hidden(esk1_2(X4,X5),X4)|r1_xboole_0(X4,X5))&(r2_hidden(esk1_2(X4,X5),X5)|r1_xboole_0(X4,X5)))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|~r1_xboole_0(X7,X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.16/0.34  fof(c_0_12, negated_conjecture, (r1_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)&r2_hidden(esk2_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.16/0.34  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.16/0.34  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.16/0.34  cnf(c_0_15, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.16/0.34  cnf(c_0_16, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.16/0.34  cnf(c_0_17, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.16/0.34  cnf(c_0_18, negated_conjecture, (r2_hidden(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.16/0.34  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_enumset1(X1,X1,X1,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.16/0.34  cnf(c_0_20, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_16])).
% 0.16/0.34  cnf(c_0_21, negated_conjecture, (r1_xboole_0(k2_tarski(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.16/0.34  cnf(c_0_22, negated_conjecture, (~r2_hidden(esk2_0,X1)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.16/0.34  cnf(c_0_23, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.16/0.34  cnf(c_0_24, negated_conjecture, (r1_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_14]), c_0_15])).
% 0.16/0.34  cnf(c_0_25, negated_conjecture, (~r1_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.16/0.34  cnf(c_0_26, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_24, c_0_25]), ['proof']).
% 0.16/0.34  # SZS output end CNFRefutation
% 0.16/0.34  # Proof object total steps             : 27
% 0.16/0.34  # Proof object clause steps            : 14
% 0.16/0.34  # Proof object formula steps           : 13
% 0.16/0.34  # Proof object conjectures             : 9
% 0.16/0.34  # Proof object clause conjectures      : 6
% 0.16/0.34  # Proof object formula conjectures     : 3
% 0.16/0.34  # Proof object initial clauses used    : 7
% 0.16/0.34  # Proof object initial formulas used   : 6
% 0.16/0.34  # Proof object generating inferences   : 3
% 0.16/0.34  # Proof object simplifying inferences  : 6
% 0.16/0.34  # Training examples: 0 positive, 0 negative
% 0.16/0.34  # Parsed axioms                        : 6
% 0.16/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.34  # Initial clauses                      : 13
% 0.16/0.34  # Removed in clause preprocessing      : 2
% 0.16/0.34  # Initial clauses in saturation        : 11
% 0.16/0.34  # Processed clauses                    : 44
% 0.16/0.34  # ...of these trivial                  : 0
% 0.16/0.34  # ...subsumed                          : 5
% 0.16/0.34  # ...remaining for further processing  : 39
% 0.16/0.34  # Other redundant clauses eliminated   : 2
% 0.16/0.34  # Clauses deleted for lack of memory   : 0
% 0.16/0.34  # Backward-subsumed                    : 0
% 0.16/0.34  # Backward-rewritten                   : 0
% 0.16/0.34  # Generated clauses                    : 45
% 0.16/0.34  # ...of the previous two non-trivial   : 37
% 0.16/0.34  # Contextual simplify-reflections      : 0
% 0.16/0.34  # Paramodulations                      : 42
% 0.16/0.34  # Factorizations                       : 0
% 0.16/0.34  # Equation resolutions                 : 2
% 0.16/0.34  # Propositional unsat checks           : 0
% 0.16/0.34  #    Propositional check models        : 0
% 0.16/0.34  #    Propositional check unsatisfiable : 0
% 0.16/0.34  #    Propositional clauses             : 0
% 0.16/0.34  #    Propositional clauses after purity: 0
% 0.16/0.34  #    Propositional unsat core size     : 0
% 0.16/0.34  #    Propositional preprocessing time  : 0.000
% 0.16/0.34  #    Propositional encoding time       : 0.000
% 0.16/0.34  #    Propositional solver time         : 0.000
% 0.16/0.34  #    Success case prop preproc time    : 0.000
% 0.16/0.34  #    Success case prop encoding time   : 0.000
% 0.16/0.34  #    Success case prop solver time     : 0.000
% 0.16/0.34  # Current number of processed clauses  : 26
% 0.16/0.34  #    Positive orientable unit clauses  : 5
% 0.16/0.34  #    Positive unorientable unit clauses: 0
% 0.16/0.34  #    Negative unit clauses             : 5
% 0.16/0.34  #    Non-unit-clauses                  : 16
% 0.16/0.34  # Current number of unprocessed clauses: 14
% 0.16/0.34  # ...number of literals in the above   : 30
% 0.16/0.34  # Current number of archived formulas  : 0
% 0.16/0.34  # Current number of archived clauses   : 13
% 0.16/0.34  # Clause-clause subsumption calls (NU) : 46
% 0.16/0.34  # Rec. Clause-clause subsumption calls : 41
% 0.16/0.34  # Non-unit clause-clause subsumptions  : 2
% 0.16/0.34  # Unit Clause-clause subsumption calls : 14
% 0.16/0.34  # Rewrite failures with RHS unbound    : 0
% 0.16/0.34  # BW rewrite match attempts            : 1
% 0.16/0.34  # BW rewrite match successes           : 0
% 0.16/0.34  # Condensation attempts                : 0
% 0.16/0.34  # Condensation successes               : 0
% 0.16/0.34  # Termbank termtop insertions          : 1133
% 0.16/0.34  
% 0.16/0.34  # -------------------------------------------------
% 0.16/0.34  # User time                : 0.028 s
% 0.16/0.34  # System time              : 0.002 s
% 0.16/0.34  # Total time               : 0.030 s
% 0.16/0.34  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
