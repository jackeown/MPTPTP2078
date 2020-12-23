%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:32:32 EST 2020

% Result     : CounterSatisfiable 0.18s
% Output     : Saturation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 260 expanded)
%              Number of clauses        :   24 ( 111 expanded)
%              Number of leaves         :    5 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 ( 627 expanded)
%              Number of equality atoms :   15 ( 109 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X3) )
     => r2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(irreflexivity_r2_xboole_0,axiom,(
    ! [X1,X2] : ~ r2_xboole_0(X1,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X2,X3) )
       => r2_xboole_0(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t59_xboole_1])).

fof(c_0_6,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k2_xboole_0(X10,X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_7,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r2_xboole_0(esk2_0,esk3_0)
    & ~ r2_xboole_0(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(k2_xboole_0(X7,X8),X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_9,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | ~ r2_xboole_0(X4,X5) )
      & ( X4 != X5
        | ~ r2_xboole_0(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | X4 = X5
        | r2_xboole_0(X4,X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( r2_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15]),
    [final]).

cnf(c_0_18,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_17]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( esk1_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_21]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_10,c_0_22]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( esk2_0 = esk1_0
    | r2_xboole_0(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_10])).

fof(c_0_26,plain,(
    ! [X6] : ~ r2_xboole_0(X6,X6) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_xboole_0])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_22]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_22]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( esk2_0 = esk3_0
    | r2_xboole_0(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_22]),c_0_22]),
    [final]).

cnf(c_0_31,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_27]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_28]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_13,c_0_22]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:14:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___008_C45_F1_PI_S5PRR_SE_Q4_CS_SP_S4S
% 0.18/0.36  # and selection function SelectNewComplexAHPNS.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.028 s
% 0.18/0.36  
% 0.18/0.36  # No proof found!
% 0.18/0.36  # SZS status CounterSatisfiable
% 0.18/0.36  # SZS output start Saturation
% 0.18/0.36  fof(t59_xboole_1, conjecture, ![X1, X2, X3]:((r1_tarski(X1,X2)&r2_xboole_0(X2,X3))=>r2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_xboole_1)).
% 0.18/0.36  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.18/0.36  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.18/0.36  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.18/0.36  fof(irreflexivity_r2_xboole_0, axiom, ![X1, X2]:~(r2_xboole_0(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 0.18/0.36  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:((r1_tarski(X1,X2)&r2_xboole_0(X2,X3))=>r2_xboole_0(X1,X3))), inference(assume_negation,[status(cth)],[t59_xboole_1])).
% 0.18/0.36  fof(c_0_6, plain, ![X10, X11]:(~r1_tarski(X10,X11)|k2_xboole_0(X10,X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.18/0.36  fof(c_0_7, negated_conjecture, ((r1_tarski(esk1_0,esk2_0)&r2_xboole_0(esk2_0,esk3_0))&~r2_xboole_0(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.18/0.36  fof(c_0_8, plain, ![X7, X8, X9]:(~r1_tarski(k2_xboole_0(X7,X8),X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.18/0.36  cnf(c_0_9, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.18/0.36  cnf(c_0_10, negated_conjecture, (r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.36  fof(c_0_11, plain, ![X4, X5]:(((r1_tarski(X4,X5)|~r2_xboole_0(X4,X5))&(X4!=X5|~r2_xboole_0(X4,X5)))&(~r1_tarski(X4,X5)|X4=X5|r2_xboole_0(X4,X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.18/0.36  cnf(c_0_12, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.18/0.36  cnf(c_0_13, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.18/0.36  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.18/0.36  cnf(c_0_15, negated_conjecture, (r2_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.18/0.36  cnf(c_0_16, negated_conjecture, (r1_tarski(esk1_0,X1)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.18/0.36  cnf(c_0_17, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_15]), ['final']).
% 0.18/0.36  cnf(c_0_18, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.18/0.36  cnf(c_0_19, negated_conjecture, (r1_tarski(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.36  cnf(c_0_20, negated_conjecture, (~r2_xboole_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.36  cnf(c_0_21, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_9, c_0_17]), ['final']).
% 0.18/0.36  cnf(c_0_22, negated_conjecture, (esk1_0=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), ['final']).
% 0.18/0.36  cnf(c_0_23, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_12, c_0_21]), ['final']).
% 0.18/0.36  cnf(c_0_24, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_10, c_0_22]), ['final']).
% 0.18/0.36  cnf(c_0_25, negated_conjecture, (esk2_0=esk1_0|r2_xboole_0(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_18, c_0_10])).
% 0.18/0.36  fof(c_0_26, plain, ![X6]:~r2_xboole_0(X6,X6), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_xboole_0])])).
% 0.18/0.36  cnf(c_0_27, negated_conjecture, (r1_tarski(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_23, c_0_24]), ['final']).
% 0.18/0.36  cnf(c_0_28, negated_conjecture, (r1_tarski(esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_19, c_0_22]), ['final']).
% 0.18/0.36  cnf(c_0_29, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(esk2_0,X1)), inference(rw,[status(thm)],[c_0_16, c_0_22]), ['final']).
% 0.18/0.36  cnf(c_0_30, negated_conjecture, (esk2_0=esk3_0|r2_xboole_0(esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_22]), c_0_22]), ['final']).
% 0.18/0.36  cnf(c_0_31, plain, (~r2_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.18/0.36  cnf(c_0_32, negated_conjecture, (k2_xboole_0(esk2_0,esk2_0)=esk2_0), inference(spm,[status(thm)],[c_0_9, c_0_27]), ['final']).
% 0.18/0.36  cnf(c_0_33, negated_conjecture, (k2_xboole_0(esk3_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_9, c_0_28]), ['final']).
% 0.18/0.36  cnf(c_0_34, negated_conjecture, (k2_xboole_0(esk3_0,esk2_0)=esk2_0), inference(rw,[status(thm)],[c_0_13, c_0_22]), ['final']).
% 0.18/0.36  # SZS output end Saturation
% 0.18/0.36  # Proof object total steps             : 35
% 0.18/0.36  # Proof object clause steps            : 24
% 0.18/0.36  # Proof object formula steps           : 11
% 0.18/0.36  # Proof object conjectures             : 22
% 0.18/0.36  # Proof object clause conjectures      : 19
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 8
% 0.18/0.36  # Proof object initial formulas used   : 5
% 0.18/0.36  # Proof object generating inferences   : 11
% 0.18/0.36  # Proof object simplifying inferences  : 7
% 0.18/0.36  # Parsed axioms                        : 5
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 9
% 0.18/0.36  # Removed in clause preprocessing      : 0
% 0.18/0.36  # Initial clauses in saturation        : 9
% 0.18/0.36  # Processed clauses                    : 30
% 0.18/0.36  # ...of these trivial                  : 1
% 0.18/0.36  # ...subsumed                          : 4
% 0.18/0.36  # ...remaining for further processing  : 25
% 0.18/0.36  # Other redundant clauses eliminated   : 1
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 0
% 0.18/0.36  # Backward-rewritten                   : 6
% 0.18/0.36  # Generated clauses                    : 24
% 0.18/0.36  # ...of the previous two non-trivial   : 22
% 0.18/0.36  # Contextual simplify-reflections      : 0
% 0.18/0.36  # Paramodulations                      : 23
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 1
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 18
% 0.18/0.36  #    Positive orientable unit clauses  : 10
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 1
% 0.18/0.36  #    Non-unit-clauses                  : 7
% 0.18/0.36  # Current number of unprocessed clauses: 0
% 0.18/0.36  # ...number of literals in the above   : 0
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 6
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 2
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 2
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.18/0.36  # Unit Clause-clause subsumption calls : 1
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 1
% 0.18/0.36  # BW rewrite match successes           : 1
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 606
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.028 s
% 0.18/0.37  # System time              : 0.003 s
% 0.18/0.37  # Total time               : 0.031 s
% 0.18/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
