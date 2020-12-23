%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:37 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   29 ( 478 expanded)
%              Number of clauses        :   20 ( 210 expanded)
%              Number of leaves         :    4 ( 126 expanded)
%              Depth                    :   13
%              Number of atoms          :   49 ( 776 expanded)
%              Number of equality atoms :   48 ( 775 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_mcart_1(X1,X2,X3,X4) = k4_mcart_1(X5,X6,X7,X8)
     => ( X1 = X5
        & X2 = X6
        & X3 = X7
        & X4 = X8 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_mcart_1)).

fof(d4_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( k4_mcart_1(X1,X2,X3,X4) = k4_mcart_1(X5,X6,X7,X8)
       => ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ),
    inference(assume_negation,[status(cth)],[t33_mcart_1])).

fof(c_0_5,plain,(
    ! [X12,X13,X14,X15] : k4_mcart_1(X12,X13,X14,X15) = k4_tarski(k3_mcart_1(X12,X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[d4_mcart_1])).

fof(c_0_6,plain,(
    ! [X9,X10,X11] : k3_mcart_1(X9,X10,X11) = k4_tarski(k4_tarski(X9,X10),X11) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_7,negated_conjecture,
    ( k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)
    & ( esk1_0 != esk5_0
      | esk2_0 != esk6_0
      | esk3_0 != esk7_0
      | esk4_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k3_mcart_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X16,X17] :
      ( k1_mcart_1(k4_tarski(X16,X17)) = X16
      & k2_mcart_1(k4_tarski(X16,X17)) = X17 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_11,negated_conjecture,
    ( k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k4_mcart_1(X1,X2,X3,X4) = k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0) = k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( esk4_0 = esk8_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_13])).

cnf(c_0_16,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk8_0) = k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0) = k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( esk3_0 = esk7_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_18]),c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k4_tarski(k4_tarski(esk1_0,esk2_0),esk7_0) = k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_21,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0
    | esk4_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( k4_tarski(esk1_0,esk2_0) = k4_tarski(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_20]),c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0
    | esk3_0 != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_15])])).

cnf(c_0_24,negated_conjecture,
    ( esk1_0 = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_22]),c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( esk1_0 != esk5_0
    | esk2_0 != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_19])])).

cnf(c_0_26,negated_conjecture,
    ( k4_tarski(esk5_0,esk2_0) = k4_tarski(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( esk2_0 != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_26]),c_0_13]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:05:09 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.17/0.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.17/0.35  #
% 0.17/0.35  # Preprocessing time       : 0.026 s
% 0.17/0.35  # Presaturation interreduction done
% 0.17/0.35  
% 0.17/0.35  # Proof found!
% 0.17/0.35  # SZS status Theorem
% 0.17/0.35  # SZS output start CNFRefutation
% 0.17/0.35  fof(t33_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_mcart_1(X1,X2,X3,X4)=k4_mcart_1(X5,X6,X7,X8)=>(((X1=X5&X2=X6)&X3=X7)&X4=X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_mcart_1)).
% 0.17/0.35  fof(d4_mcart_1, axiom, ![X1, X2, X3, X4]:k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 0.17/0.35  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.17/0.35  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.17/0.35  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:(k4_mcart_1(X1,X2,X3,X4)=k4_mcart_1(X5,X6,X7,X8)=>(((X1=X5&X2=X6)&X3=X7)&X4=X8))), inference(assume_negation,[status(cth)],[t33_mcart_1])).
% 0.17/0.35  fof(c_0_5, plain, ![X12, X13, X14, X15]:k4_mcart_1(X12,X13,X14,X15)=k4_tarski(k3_mcart_1(X12,X13,X14),X15), inference(variable_rename,[status(thm)],[d4_mcart_1])).
% 0.17/0.35  fof(c_0_6, plain, ![X9, X10, X11]:k3_mcart_1(X9,X10,X11)=k4_tarski(k4_tarski(X9,X10),X11), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.17/0.35  fof(c_0_7, negated_conjecture, (k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)&(esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.17/0.35  cnf(c_0_8, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k3_mcart_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.17/0.35  cnf(c_0_9, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.17/0.35  fof(c_0_10, plain, ![X16, X17]:(k1_mcart_1(k4_tarski(X16,X17))=X16&k2_mcart_1(k4_tarski(X16,X17))=X17), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.17/0.35  cnf(c_0_11, negated_conjecture, (k4_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=k4_mcart_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.35  cnf(c_0_12, plain, (k4_mcart_1(X1,X2,X3,X4)=k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.17/0.35  cnf(c_0_13, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.35  cnf(c_0_14, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0)=k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_12])).
% 0.17/0.35  cnf(c_0_15, negated_conjecture, (esk4_0=esk8_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_13])).
% 0.17/0.35  cnf(c_0_16, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.17/0.35  cnf(c_0_17, negated_conjecture, (k4_tarski(k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0),esk8_0)=k4_tarski(k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0),esk8_0)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.17/0.35  cnf(c_0_18, negated_conjecture, (k4_tarski(k4_tarski(esk1_0,esk2_0),esk3_0)=k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_16])).
% 0.17/0.35  cnf(c_0_19, negated_conjecture, (esk3_0=esk7_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_18]), c_0_13])).
% 0.17/0.35  cnf(c_0_20, negated_conjecture, (k4_tarski(k4_tarski(esk1_0,esk2_0),esk7_0)=k4_tarski(k4_tarski(esk5_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.17/0.35  cnf(c_0_21, negated_conjecture, (esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0|esk4_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.35  cnf(c_0_22, negated_conjecture, (k4_tarski(esk1_0,esk2_0)=k4_tarski(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_20]), c_0_16])).
% 0.17/0.35  cnf(c_0_23, negated_conjecture, (esk1_0!=esk5_0|esk2_0!=esk6_0|esk3_0!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_15])])).
% 0.17/0.35  cnf(c_0_24, negated_conjecture, (esk1_0=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_22]), c_0_16])).
% 0.17/0.35  cnf(c_0_25, negated_conjecture, (esk1_0!=esk5_0|esk2_0!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_19])])).
% 0.17/0.35  cnf(c_0_26, negated_conjecture, (k4_tarski(esk5_0,esk2_0)=k4_tarski(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_22, c_0_24])).
% 0.17/0.35  cnf(c_0_27, negated_conjecture, (esk2_0!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_24])])).
% 0.17/0.35  cnf(c_0_28, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_26]), c_0_13]), c_0_27]), ['proof']).
% 0.17/0.35  # SZS output end CNFRefutation
% 0.17/0.35  # Proof object total steps             : 29
% 0.17/0.35  # Proof object clause steps            : 20
% 0.17/0.35  # Proof object formula steps           : 9
% 0.17/0.35  # Proof object conjectures             : 18
% 0.17/0.35  # Proof object clause conjectures      : 15
% 0.17/0.35  # Proof object formula conjectures     : 3
% 0.17/0.35  # Proof object initial clauses used    : 6
% 0.17/0.35  # Proof object initial formulas used   : 4
% 0.17/0.35  # Proof object generating inferences   : 6
% 0.17/0.35  # Proof object simplifying inferences  : 19
% 0.17/0.35  # Training examples: 0 positive, 0 negative
% 0.17/0.35  # Parsed axioms                        : 4
% 0.17/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.35  # Initial clauses                      : 6
% 0.17/0.35  # Removed in clause preprocessing      : 2
% 0.17/0.35  # Initial clauses in saturation        : 4
% 0.17/0.35  # Processed clauses                    : 20
% 0.17/0.35  # ...of these trivial                  : 0
% 0.17/0.35  # ...subsumed                          : 0
% 0.17/0.35  # ...remaining for further processing  : 19
% 0.17/0.35  # Other redundant clauses eliminated   : 0
% 0.17/0.35  # Clauses deleted for lack of memory   : 0
% 0.17/0.35  # Backward-subsumed                    : 0
% 0.17/0.35  # Backward-rewritten                   : 8
% 0.17/0.35  # Generated clauses                    : 12
% 0.17/0.35  # ...of the previous two non-trivial   : 15
% 0.17/0.35  # Contextual simplify-reflections      : 0
% 0.17/0.35  # Paramodulations                      : 12
% 0.17/0.35  # Factorizations                       : 0
% 0.17/0.35  # Equation resolutions                 : 0
% 0.17/0.35  # Propositional unsat checks           : 0
% 0.17/0.35  #    Propositional check models        : 0
% 0.17/0.35  #    Propositional check unsatisfiable : 0
% 0.17/0.35  #    Propositional clauses             : 0
% 0.17/0.35  #    Propositional clauses after purity: 0
% 0.17/0.35  #    Propositional unsat core size     : 0
% 0.17/0.35  #    Propositional preprocessing time  : 0.000
% 0.17/0.35  #    Propositional encoding time       : 0.000
% 0.17/0.35  #    Propositional solver time         : 0.000
% 0.17/0.35  #    Success case prop preproc time    : 0.000
% 0.17/0.35  #    Success case prop encoding time   : 0.000
% 0.17/0.35  #    Success case prop solver time     : 0.000
% 0.17/0.35  # Current number of processed clauses  : 7
% 0.17/0.35  #    Positive orientable unit clauses  : 6
% 0.17/0.35  #    Positive unorientable unit clauses: 0
% 0.17/0.35  #    Negative unit clauses             : 1
% 0.17/0.35  #    Non-unit-clauses                  : 0
% 0.17/0.35  # Current number of unprocessed clauses: 0
% 0.17/0.35  # ...number of literals in the above   : 0
% 0.17/0.35  # Current number of archived formulas  : 0
% 0.17/0.35  # Current number of archived clauses   : 14
% 0.17/0.35  # Clause-clause subsumption calls (NU) : 0
% 0.17/0.35  # Rec. Clause-clause subsumption calls : 0
% 0.17/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.17/0.35  # Unit Clause-clause subsumption calls : 0
% 0.17/0.35  # Rewrite failures with RHS unbound    : 0
% 0.17/0.35  # BW rewrite match attempts            : 5
% 0.17/0.35  # BW rewrite match successes           : 5
% 0.17/0.35  # Condensation attempts                : 0
% 0.17/0.35  # Condensation successes               : 0
% 0.17/0.35  # Termbank termtop insertions          : 519
% 0.17/0.35  
% 0.17/0.35  # -------------------------------------------------
% 0.17/0.35  # User time                : 0.026 s
% 0.17/0.35  # System time              : 0.004 s
% 0.17/0.35  # Total time               : 0.030 s
% 0.17/0.35  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
