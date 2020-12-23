%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:59 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   27 (  48 expanded)
%              Number of clauses        :   18 (  22 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 180 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t1_mcart_1,conjecture,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(c_0_4,plain,(
    ! [X12,X13,X15] :
      ( ( r2_hidden(esk2_2(X12,X13),X13)
        | ~ r2_hidden(X12,X13) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,esk2_2(X12,X13))
        | ~ r2_hidden(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

fof(c_0_5,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_2(X5,X6),X5)
        | r1_xboole_0(X5,X6) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | r1_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_6,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk2_2(X3,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ~ ( X1 != k1_xboole_0
          & ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r1_xboole_0(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t1_mcart_1])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r1_xboole_0(X1,esk2_2(X2,X3))
    | ~ r2_hidden(esk1_2(X1,esk2_2(X2,X3)),X3)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

fof(c_0_12,negated_conjecture,(
    ! [X17] :
      ( esk3_0 != k1_xboole_0
      & ( ~ r2_hidden(X17,esk3_0)
        | ~ r1_xboole_0(X17,esk3_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,esk2_2(X2,X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(X1,esk3_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_2(esk1_2(X1,X2),X1),X1)
    | r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_10])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_7])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,esk2_2(esk1_2(X2,X1),X1))
    | r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_7])).

fof(c_0_20,plain,(
    ! [X11] :
      ( ( r1_xboole_0(X11,X11)
        | X11 != k1_xboole_0 )
      & ( X11 = k1_xboole_0
        | ~ r1_xboole_0(X11,X11) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_21,negated_conjecture,
    ( r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(esk2_2(esk1_2(esk3_0,X1),esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r1_xboole_0(esk2_2(esk1_2(X1,X2),X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___008_C45_F1_PI_S5PRR_SE_Q4_CS_SP_S4S
% 0.13/0.37  # and selection function SelectNewComplexAHPNS.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 0.13/0.37  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.13/0.37  fof(t1_mcart_1, conjecture, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 0.13/0.37  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.13/0.37  fof(c_0_4, plain, ![X12, X13, X15]:((r2_hidden(esk2_2(X12,X13),X13)|~r2_hidden(X12,X13))&(~r2_hidden(X15,X13)|~r2_hidden(X15,esk2_2(X12,X13))|~r2_hidden(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.13/0.37  fof(c_0_5, plain, ![X5, X6, X8, X9, X10]:(((r2_hidden(esk1_2(X5,X6),X5)|r1_xboole_0(X5,X6))&(r2_hidden(esk1_2(X5,X6),X6)|r1_xboole_0(X5,X6)))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|~r1_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.13/0.37  cnf(c_0_6, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,esk2_2(X3,X2))|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_7, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1)))))), inference(assume_negation,[status(cth)],[t1_mcart_1])).
% 0.13/0.37  cnf(c_0_9, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_11, plain, (r1_xboole_0(X1,esk2_2(X2,X3))|~r2_hidden(esk1_2(X1,esk2_2(X2,X3)),X3)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.13/0.37  fof(c_0_12, negated_conjecture, ![X17]:(esk3_0!=k1_xboole_0&(~r2_hidden(X17,esk3_0)|~r1_xboole_0(X17,esk3_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.13/0.37  cnf(c_0_13, plain, (r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.37  cnf(c_0_14, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.37  cnf(c_0_15, plain, (r1_xboole_0(X1,esk2_2(X2,X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_11, c_0_10])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (~r2_hidden(X1,esk3_0)|~r1_xboole_0(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_17, plain, (r2_hidden(esk2_2(esk1_2(X1,X2),X1),X1)|r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_13, c_0_10])).
% 0.13/0.37  cnf(c_0_18, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_14, c_0_7])).
% 0.13/0.37  cnf(c_0_19, plain, (r1_xboole_0(X1,esk2_2(esk1_2(X2,X1),X1))|r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_15, c_0_7])).
% 0.13/0.37  fof(c_0_20, plain, ![X11]:((r1_xboole_0(X11,X11)|X11!=k1_xboole_0)&(X11=k1_xboole_0|~r1_xboole_0(X11,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (r1_xboole_0(esk3_0,X1)|~r1_xboole_0(esk2_2(esk1_2(esk3_0,X1),esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.37  cnf(c_0_22, plain, (r1_xboole_0(esk2_2(esk1_2(X1,X2),X2),X2)|r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.37  cnf(c_0_23, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (r1_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 27
% 0.13/0.37  # Proof object clause steps            : 18
% 0.13/0.37  # Proof object formula steps           : 9
% 0.13/0.37  # Proof object conjectures             : 8
% 0.13/0.37  # Proof object clause conjectures      : 5
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 8
% 0.13/0.37  # Proof object initial formulas used   : 4
% 0.13/0.37  # Proof object generating inferences   : 10
% 0.13/0.37  # Proof object simplifying inferences  : 1
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 4
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 9
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 9
% 0.13/0.37  # Processed clauses                    : 34
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 2
% 0.13/0.37  # ...remaining for further processing  : 32
% 0.13/0.37  # Other redundant clauses eliminated   : 1
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 1
% 0.13/0.37  # Generated clauses                    : 47
% 0.13/0.37  # ...of the previous two non-trivial   : 35
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 46
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 1
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 30
% 0.13/0.37  #    Positive orientable unit clauses  : 3
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 26
% 0.13/0.37  # Current number of unprocessed clauses: 10
% 0.13/0.37  # ...number of literals in the above   : 21
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 1
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 119
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 119
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 1
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1163
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.028 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
