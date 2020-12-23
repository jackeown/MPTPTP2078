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
% DateTime   : Thu Dec  3 10:34:49 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   24 (  62 expanded)
%              Number of clauses        :   15 (  27 expanded)
%              Number of leaves         :    4 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 ( 155 expanded)
%              Number of equality atoms :    3 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t107_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k5_xboole_0(X2,X3))
    <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).

fof(l98_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,k5_xboole_0(X2,X3))
      <=> ( r1_tarski(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,k3_xboole_0(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t107_xboole_1])).

fof(c_0_5,negated_conjecture,
    ( ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
      | ~ r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) )
    & ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
      | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) )
    & ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
      | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k4_xboole_0(k2_xboole_0(X4,X5),k3_xboole_0(X4,X5)) ),
    inference(variable_rename,[status(thm)],[l98_xboole_1])).

fof(c_0_7,plain,(
    ! [X6,X7,X8] :
      ( ( r1_tarski(X6,X7)
        | ~ r1_tarski(X6,k4_xboole_0(X7,X8)) )
      & ( r1_xboole_0(X6,X8)
        | ~ r1_tarski(X6,k4_xboole_0(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_8,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_11,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_xboole_0(X9,X11)
      | r1_tarski(X9,k4_xboole_0(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_10,c_0_9])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))
    | ~ r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk1_0,k4_xboole_0(X1,k3_xboole_0(esk2_0,esk3_0)))
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])]),c_0_18])])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:10:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___008_C45_F1_PI_S5PRR_SE_Q4_CS_SP_S4S
% 0.14/0.37  # and selection function SelectNewComplexAHPNS.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.026 s
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t107_xboole_1, conjecture, ![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_xboole_1)).
% 0.14/0.37  fof(l98_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l98_xboole_1)).
% 0.14/0.37  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.14/0.37  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.14/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:(r1_tarski(X1,k5_xboole_0(X2,X3))<=>(r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,k3_xboole_0(X2,X3))))), inference(assume_negation,[status(cth)],[t107_xboole_1])).
% 0.14/0.37  fof(c_0_5, negated_conjecture, ((~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|(~r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))))&((r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0)))&(r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.14/0.37  fof(c_0_6, plain, ![X4, X5]:k5_xboole_0(X4,X5)=k4_xboole_0(k2_xboole_0(X4,X5),k3_xboole_0(X4,X5)), inference(variable_rename,[status(thm)],[l98_xboole_1])).
% 0.14/0.37  fof(c_0_7, plain, ![X6, X7, X8]:((r1_tarski(X6,X7)|~r1_tarski(X6,k4_xboole_0(X7,X8)))&(r1_xboole_0(X6,X8)|~r1_tarski(X6,k4_xboole_0(X7,X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.14/0.37  cnf(c_0_8, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.37  cnf(c_0_9, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.37  cnf(c_0_10, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.37  fof(c_0_11, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_xboole_0(X9,X11)|r1_tarski(X9,k4_xboole_0(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.14/0.37  cnf(c_0_12, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_13, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.14/0.37  cnf(c_0_14, negated_conjecture, (~r1_tarski(esk1_0,k5_xboole_0(esk2_0,esk3_0))|~r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.37  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_16, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_10, c_0_9])).
% 0.14/0.37  cnf(c_0_17, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  cnf(c_0_18, negated_conjecture, (r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.37  cnf(c_0_19, negated_conjecture, (~r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))|~r1_xboole_0(esk1_0,k3_xboole_0(esk2_0,esk3_0))|~r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_14, c_0_9])).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, (r1_tarski(esk1_0,k2_xboole_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.37  cnf(c_0_21, negated_conjecture, (r1_tarski(esk1_0,k4_xboole_0(X1,k3_xboole_0(esk2_0,esk3_0)))|~r1_tarski(esk1_0,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.37  cnf(c_0_22, negated_conjecture, (~r1_tarski(esk1_0,k4_xboole_0(k2_xboole_0(esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20])]), c_0_18])])).
% 0.14/0.37  cnf(c_0_23, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_22]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 24
% 0.14/0.37  # Proof object clause steps            : 15
% 0.14/0.37  # Proof object formula steps           : 9
% 0.14/0.37  # Proof object conjectures             : 14
% 0.14/0.37  # Proof object clause conjectures      : 11
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 7
% 0.14/0.37  # Proof object initial formulas used   : 4
% 0.14/0.37  # Proof object generating inferences   : 4
% 0.14/0.37  # Proof object simplifying inferences  : 8
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 4
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 7
% 0.14/0.37  # Removed in clause preprocessing      : 1
% 0.14/0.37  # Initial clauses in saturation        : 6
% 0.14/0.37  # Processed clauses                    : 10
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 10
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 3
% 0.14/0.37  # Generated clauses                    : 6
% 0.14/0.37  # ...of the previous two non-trivial   : 6
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 6
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 0
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 7
% 0.14/0.37  #    Positive orientable unit clauses  : 2
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 1
% 0.14/0.37  #    Non-unit-clauses                  : 4
% 0.14/0.37  # Current number of unprocessed clauses: 0
% 0.14/0.37  # ...number of literals in the above   : 0
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 4
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 1
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 2
% 0.14/0.37  # BW rewrite match successes           : 2
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 602
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.026 s
% 0.14/0.37  # System time              : 0.003 s
% 0.14/0.37  # Total time               : 0.029 s
% 0.14/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
