%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:42:00 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 (  78 expanded)
%              Number of clauses        :   15 (  30 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  92 expanded)
%              Number of equality atoms :   22 (  70 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_xboole_0(k1_tarski(X1),X2)
      | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t79_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(l31_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_xboole_0(k1_tarski(X1),X2)
        | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    inference(assume_negation,[status(cth)],[t58_zfmisc_1])).

fof(c_0_8,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk1_0),esk2_0)
    & k3_xboole_0(k1_tarski(esk1_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X10] : k1_enumset1(X10,X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

fof(c_0_10,plain,(
    ! [X7,X8,X9] : k2_enumset1(X7,X7,X8,X9) = k1_enumset1(X7,X8,X9) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_11,plain,(
    ! [X11,X12,X13,X14] : k4_enumset1(X11,X11,X11,X12,X13,X14) = k2_enumset1(X11,X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t79_enumset1])).

fof(c_0_12,plain,(
    ! [X15,X16] :
      ( r2_hidden(X15,X16)
      | r1_xboole_0(k1_tarski(X15),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_13,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk1_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_18,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | k3_xboole_0(X18,k1_tarski(X17)) = k1_tarski(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14]),c_0_15]),c_0_15]),c_0_16]),c_0_16])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X2,k1_tarski(X1)) = k1_tarski(X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_14]),c_0_15]),c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( k3_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)) != k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X2,k4_enumset1(X1,X1,X1,X1,X1,X1)) = k4_enumset1(X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_14]),c_0_14]),c_0_15]),c_0_15]),c_0_16]),c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:41:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.22/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.22/0.38  #
% 0.22/0.38  # Preprocessing time       : 0.026 s
% 0.22/0.38  # Presaturation interreduction done
% 0.22/0.38  
% 0.22/0.38  # Proof found!
% 0.22/0.38  # SZS status Theorem
% 0.22/0.38  # SZS output start CNFRefutation
% 0.22/0.38  fof(t58_zfmisc_1, conjecture, ![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 0.22/0.38  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 0.22/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.22/0.38  fof(t79_enumset1, axiom, ![X1, X2, X3, X4]:k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 0.22/0.38  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.22/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.22/0.38  fof(l31_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 0.22/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1))), inference(assume_negation,[status(cth)],[t58_zfmisc_1])).
% 0.22/0.38  fof(c_0_8, negated_conjecture, (~r1_xboole_0(k1_tarski(esk1_0),esk2_0)&k3_xboole_0(k1_tarski(esk1_0),esk2_0)!=k1_tarski(esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.22/0.38  fof(c_0_9, plain, ![X10]:k1_enumset1(X10,X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.22/0.38  fof(c_0_10, plain, ![X7, X8, X9]:k2_enumset1(X7,X7,X8,X9)=k1_enumset1(X7,X8,X9), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.22/0.38  fof(c_0_11, plain, ![X11, X12, X13, X14]:k4_enumset1(X11,X11,X11,X12,X13,X14)=k2_enumset1(X11,X12,X13,X14), inference(variable_rename,[status(thm)],[t79_enumset1])).
% 0.22/0.38  fof(c_0_12, plain, ![X15, X16]:(r2_hidden(X15,X16)|r1_xboole_0(k1_tarski(X15),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.22/0.38  cnf(c_0_13, negated_conjecture, (k3_xboole_0(k1_tarski(esk1_0),esk2_0)!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.22/0.38  cnf(c_0_14, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.38  cnf(c_0_15, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.22/0.38  cnf(c_0_16, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.22/0.38  fof(c_0_17, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.22/0.38  fof(c_0_18, plain, ![X17, X18]:(~r2_hidden(X17,X18)|k3_xboole_0(X18,k1_tarski(X17))=k1_tarski(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l31_zfmisc_1])])).
% 0.22/0.38  cnf(c_0_19, negated_conjecture, (~r1_xboole_0(k1_tarski(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.22/0.38  cnf(c_0_20, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.38  cnf(c_0_21, negated_conjecture, (k3_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14]), c_0_15]), c_0_15]), c_0_16]), c_0_16])).
% 0.22/0.38  cnf(c_0_22, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.22/0.38  cnf(c_0_23, plain, (k3_xboole_0(X2,k1_tarski(X1))=k1_tarski(X1)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.22/0.38  cnf(c_0_24, negated_conjecture, (~r1_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_14]), c_0_15]), c_0_16])).
% 0.22/0.38  cnf(c_0_25, plain, (r2_hidden(X1,X2)|r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_14]), c_0_15]), c_0_16])).
% 0.22/0.38  cnf(c_0_26, negated_conjecture, (k3_xboole_0(esk2_0,k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))!=k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.22/0.38  cnf(c_0_27, plain, (k3_xboole_0(X2,k4_enumset1(X1,X1,X1,X1,X1,X1))=k4_enumset1(X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_14]), c_0_14]), c_0_15]), c_0_15]), c_0_16]), c_0_16])).
% 0.22/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.22/0.38  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])]), ['proof']).
% 0.22/0.38  # SZS output end CNFRefutation
% 0.22/0.38  # Proof object total steps             : 30
% 0.22/0.38  # Proof object clause steps            : 15
% 0.22/0.38  # Proof object formula steps           : 15
% 0.22/0.38  # Proof object conjectures             : 10
% 0.22/0.38  # Proof object clause conjectures      : 7
% 0.22/0.38  # Proof object formula conjectures     : 3
% 0.22/0.38  # Proof object initial clauses used    : 8
% 0.22/0.38  # Proof object initial formulas used   : 7
% 0.22/0.38  # Proof object generating inferences   : 2
% 0.22/0.38  # Proof object simplifying inferences  : 21
% 0.22/0.38  # Training examples: 0 positive, 0 negative
% 0.22/0.38  # Parsed axioms                        : 7
% 0.22/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.38  # Initial clauses                      : 8
% 0.22/0.38  # Removed in clause preprocessing      : 3
% 0.22/0.38  # Initial clauses in saturation        : 5
% 0.22/0.38  # Processed clauses                    : 12
% 0.22/0.38  # ...of these trivial                  : 0
% 0.22/0.38  # ...subsumed                          : 0
% 0.22/0.38  # ...remaining for further processing  : 12
% 0.22/0.38  # Other redundant clauses eliminated   : 0
% 0.22/0.38  # Clauses deleted for lack of memory   : 0
% 0.22/0.38  # Backward-subsumed                    : 0
% 0.22/0.38  # Backward-rewritten                   : 1
% 0.22/0.38  # Generated clauses                    : 4
% 0.22/0.38  # ...of the previous two non-trivial   : 2
% 0.22/0.38  # Contextual simplify-reflections      : 0
% 0.22/0.38  # Paramodulations                      : 4
% 0.22/0.38  # Factorizations                       : 0
% 0.22/0.38  # Equation resolutions                 : 0
% 0.22/0.38  # Propositional unsat checks           : 0
% 0.22/0.38  #    Propositional check models        : 0
% 0.22/0.38  #    Propositional check unsatisfiable : 0
% 0.22/0.38  #    Propositional clauses             : 0
% 0.22/0.38  #    Propositional clauses after purity: 0
% 0.22/0.38  #    Propositional unsat core size     : 0
% 0.22/0.38  #    Propositional preprocessing time  : 0.000
% 0.22/0.38  #    Propositional encoding time       : 0.000
% 0.22/0.38  #    Propositional solver time         : 0.000
% 0.22/0.38  #    Success case prop preproc time    : 0.000
% 0.22/0.38  #    Success case prop encoding time   : 0.000
% 0.22/0.38  #    Success case prop solver time     : 0.000
% 0.22/0.38  # Current number of processed clauses  : 6
% 0.22/0.38  #    Positive orientable unit clauses  : 1
% 0.22/0.38  #    Positive unorientable unit clauses: 1
% 0.22/0.38  #    Negative unit clauses             : 2
% 0.22/0.38  #    Non-unit-clauses                  : 2
% 0.22/0.38  # Current number of unprocessed clauses: 0
% 0.22/0.38  # ...number of literals in the above   : 0
% 0.22/0.38  # Current number of archived formulas  : 0
% 0.22/0.38  # Current number of archived clauses   : 9
% 0.22/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.22/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.22/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.22/0.38  # Unit Clause-clause subsumption calls : 0
% 0.22/0.38  # Rewrite failures with RHS unbound    : 0
% 0.22/0.38  # BW rewrite match attempts            : 2
% 0.22/0.38  # BW rewrite match successes           : 2
% 0.22/0.38  # Condensation attempts                : 0
% 0.22/0.38  # Condensation successes               : 0
% 0.22/0.38  # Termbank termtop insertions          : 459
% 0.22/0.38  
% 0.22/0.38  # -------------------------------------------------
% 0.22/0.38  # User time                : 0.026 s
% 0.22/0.38  # System time              : 0.004 s
% 0.22/0.38  # Total time               : 0.030 s
% 0.22/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
