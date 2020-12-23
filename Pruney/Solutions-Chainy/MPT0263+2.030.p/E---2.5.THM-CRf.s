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
% DateTime   : Thu Dec  3 10:41:59 EST 2020

% Result     : Theorem 0.10s
% Output     : CNFRefutation 0.10s
% Verified   : 
% Statistics : Number of formulae       :   32 (  62 expanded)
%              Number of clauses        :   17 (  26 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  78 expanded)
%              Number of equality atoms :   24 (  54 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_xboole_0(k1_tarski(X1),X2)
      | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_xboole_0(k1_tarski(X1),X2)
        | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    inference(assume_negation,[status(cth)],[t58_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,X11)
      | k2_xboole_0(k1_tarski(X10),X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

fof(c_0_9,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_10,plain,(
    ! [X8,X9] : k2_enumset1(X8,X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_11,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk1_0),esk2_0)
    & k3_xboole_0(k1_tarski(esk1_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_12,plain,(
    ! [X5,X6] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_13,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X12,X13] :
      ( r2_hidden(X12,X13)
      | r1_xboole_0(k1_tarski(X12),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_17,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk1_0),esk2_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X3,X4] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,X3) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k3_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk2_0) != k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_14]),c_0_14]),c_0_15]),c_0_15])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) = k2_enumset1(X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_14]),c_0_15])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_14]),c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)) != k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(X2,X2,X2,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.32  % Computer   : n021.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 17:52:34 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  # Version: 2.5pre002
% 0.10/0.32  # No SInE strategy applied
% 0.10/0.32  # Trying AutoSched0 for 299 seconds
% 0.10/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.10/0.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.10/0.35  #
% 0.10/0.35  # Preprocessing time       : 0.026 s
% 0.10/0.35  # Presaturation interreduction done
% 0.10/0.35  
% 0.10/0.35  # Proof found!
% 0.10/0.35  # SZS status Theorem
% 0.10/0.35  # SZS output start CNFRefutation
% 0.10/0.35  fof(t58_zfmisc_1, conjecture, ![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 0.10/0.35  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.10/0.35  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.10/0.35  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.10/0.35  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.10/0.35  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.10/0.35  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.10/0.35  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(r1_xboole_0(k1_tarski(X1),X2)|k3_xboole_0(k1_tarski(X1),X2)=k1_tarski(X1))), inference(assume_negation,[status(cth)],[t58_zfmisc_1])).
% 0.10/0.35  fof(c_0_8, plain, ![X10, X11]:(~r2_hidden(X10,X11)|k2_xboole_0(k1_tarski(X10),X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.10/0.35  fof(c_0_9, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.10/0.35  fof(c_0_10, plain, ![X8, X9]:k2_enumset1(X8,X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.10/0.35  fof(c_0_11, negated_conjecture, (~r1_xboole_0(k1_tarski(esk1_0),esk2_0)&k3_xboole_0(k1_tarski(esk1_0),esk2_0)!=k1_tarski(esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.10/0.35  fof(c_0_12, plain, ![X5, X6]:k3_xboole_0(X5,k2_xboole_0(X5,X6))=X5, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.10/0.35  cnf(c_0_13, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.10/0.35  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.10/0.35  cnf(c_0_15, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.10/0.35  fof(c_0_16, plain, ![X12, X13]:(r2_hidden(X12,X13)|r1_xboole_0(k1_tarski(X12),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.10/0.35  cnf(c_0_17, negated_conjecture, (k3_xboole_0(k1_tarski(esk1_0),esk2_0)!=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.10/0.35  fof(c_0_18, plain, ![X3, X4]:k3_xboole_0(X3,X4)=k3_xboole_0(X4,X3), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.10/0.35  cnf(c_0_19, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.10/0.35  cnf(c_0_20, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_15])).
% 0.10/0.35  cnf(c_0_21, negated_conjecture, (~r1_xboole_0(k1_tarski(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.10/0.35  cnf(c_0_22, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.10/0.35  cnf(c_0_23, negated_conjecture, (k3_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)!=k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_14]), c_0_14]), c_0_15]), c_0_15])).
% 0.10/0.35  cnf(c_0_24, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.10/0.35  cnf(c_0_25, plain, (k3_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)=k2_enumset1(X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.10/0.35  cnf(c_0_26, negated_conjecture, (~r1_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_14]), c_0_15])).
% 0.10/0.35  cnf(c_0_27, plain, (r2_hidden(X1,X2)|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_14]), c_0_15])).
% 0.10/0.35  cnf(c_0_28, negated_conjecture, (k3_xboole_0(esk2_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))!=k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.10/0.35  cnf(c_0_29, plain, (k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))=k2_enumset1(X2,X2,X2,X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.10/0.35  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.10/0.35  cnf(c_0_31, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])]), ['proof']).
% 0.10/0.35  # SZS output end CNFRefutation
% 0.10/0.35  # Proof object total steps             : 32
% 0.10/0.35  # Proof object clause steps            : 17
% 0.10/0.35  # Proof object formula steps           : 15
% 0.10/0.35  # Proof object conjectures             : 10
% 0.10/0.35  # Proof object clause conjectures      : 7
% 0.10/0.35  # Proof object formula conjectures     : 3
% 0.10/0.35  # Proof object initial clauses used    : 8
% 0.10/0.35  # Proof object initial formulas used   : 7
% 0.10/0.35  # Proof object generating inferences   : 4
% 0.10/0.35  # Proof object simplifying inferences  : 13
% 0.10/0.35  # Training examples: 0 positive, 0 negative
% 0.10/0.35  # Parsed axioms                        : 7
% 0.10/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.10/0.35  # Initial clauses                      : 8
% 0.10/0.35  # Removed in clause preprocessing      : 2
% 0.10/0.35  # Initial clauses in saturation        : 6
% 0.10/0.35  # Processed clauses                    : 16
% 0.10/0.35  # ...of these trivial                  : 0
% 0.10/0.35  # ...subsumed                          : 0
% 0.10/0.35  # ...remaining for further processing  : 16
% 0.10/0.35  # Other redundant clauses eliminated   : 0
% 0.10/0.35  # Clauses deleted for lack of memory   : 0
% 0.10/0.35  # Backward-subsumed                    : 0
% 0.10/0.35  # Backward-rewritten                   : 1
% 0.10/0.35  # Generated clauses                    : 8
% 0.10/0.35  # ...of the previous two non-trivial   : 5
% 0.10/0.35  # Contextual simplify-reflections      : 0
% 0.10/0.35  # Paramodulations                      : 8
% 0.10/0.35  # Factorizations                       : 0
% 0.10/0.35  # Equation resolutions                 : 0
% 0.10/0.35  # Propositional unsat checks           : 0
% 0.10/0.35  #    Propositional check models        : 0
% 0.10/0.35  #    Propositional check unsatisfiable : 0
% 0.10/0.35  #    Propositional clauses             : 0
% 0.10/0.35  #    Propositional clauses after purity: 0
% 0.10/0.35  #    Propositional unsat core size     : 0
% 0.10/0.35  #    Propositional preprocessing time  : 0.000
% 0.10/0.35  #    Propositional encoding time       : 0.000
% 0.10/0.35  #    Propositional solver time         : 0.000
% 0.10/0.35  #    Success case prop preproc time    : 0.000
% 0.10/0.35  #    Success case prop encoding time   : 0.000
% 0.10/0.35  #    Success case prop solver time     : 0.000
% 0.10/0.35  # Current number of processed clauses  : 9
% 0.10/0.35  #    Positive orientable unit clauses  : 2
% 0.10/0.35  #    Positive unorientable unit clauses: 1
% 0.10/0.35  #    Negative unit clauses             : 2
% 0.10/0.35  #    Non-unit-clauses                  : 4
% 0.10/0.35  # Current number of unprocessed clauses: 1
% 0.10/0.35  # ...number of literals in the above   : 2
% 0.10/0.35  # Current number of archived formulas  : 0
% 0.10/0.35  # Current number of archived clauses   : 9
% 0.10/0.35  # Clause-clause subsumption calls (NU) : 2
% 0.10/0.35  # Rec. Clause-clause subsumption calls : 2
% 0.10/0.35  # Non-unit clause-clause subsumptions  : 0
% 0.10/0.35  # Unit Clause-clause subsumption calls : 0
% 0.10/0.35  # Rewrite failures with RHS unbound    : 0
% 0.10/0.35  # BW rewrite match attempts            : 6
% 0.10/0.35  # BW rewrite match successes           : 6
% 0.10/0.35  # Condensation attempts                : 0
% 0.10/0.35  # Condensation successes               : 0
% 0.10/0.35  # Termbank termtop insertions          : 464
% 0.10/0.35  
% 0.10/0.35  # -------------------------------------------------
% 0.10/0.35  # User time                : 0.025 s
% 0.10/0.35  # System time              : 0.005 s
% 0.10/0.35  # Total time               : 0.030 s
% 0.10/0.35  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
