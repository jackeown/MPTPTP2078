%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:09 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   35 (  89 expanded)
%              Number of clauses        :   18 (  40 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 ( 107 expanded)
%              Number of equality atoms :   17 (  62 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_zfmisc_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(l20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t49_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X8),X9),X9)
      | r2_hidden(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l20_zfmisc_1])])).

fof(c_0_10,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,negated_conjecture,(
    k2_xboole_0(k1_tarski(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X3,X4] : k2_xboole_0(X3,X4) = k2_xboole_0(X4,X3) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_15,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk1_0),esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X12,X13] :
      ( ~ r1_xboole_0(k1_tarski(X12),X13)
      | ~ r2_hidden(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k2_tarski(X1,X1),X2),X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_15,c_0_13])).

fof(c_0_20,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_21,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,X11)
      | k2_xboole_0(k1_tarski(X10),X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

cnf(c_0_22,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(X2,k2_tarski(X1,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k2_xboole_0(esk2_0,k2_tarski(esk1_0,esk1_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k2_tarski(X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_13])).

fof(c_0_30,plain,(
    ! [X6] : r1_xboole_0(X6,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_18]),c_0_24])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S017A
% 0.13/0.37  # and selection function PSelectMinOptimalLit.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t49_zfmisc_1, conjecture, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.13/0.37  fof(l20_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l20_zfmisc_1)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.13/0.37  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.13/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.37  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.13/0.37  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.13/0.37  fof(c_0_8, negated_conjecture, ~(![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(assume_negation,[status(cth)],[t49_zfmisc_1])).
% 0.13/0.37  fof(c_0_9, plain, ![X8, X9]:(~r1_tarski(k2_xboole_0(k1_tarski(X8),X9),X9)|r2_hidden(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l20_zfmisc_1])])).
% 0.13/0.37  fof(c_0_10, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  fof(c_0_11, negated_conjecture, k2_xboole_0(k1_tarski(esk1_0),esk2_0)=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.13/0.37  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_13, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  fof(c_0_14, plain, ![X3, X4]:k2_xboole_0(X3,X4)=k2_xboole_0(X4,X3), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (k2_xboole_0(k1_tarski(esk1_0),esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  fof(c_0_16, plain, ![X12, X13]:(~r1_xboole_0(k1_tarski(X12),X13)|~r2_hidden(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.13/0.37  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(k2_tarski(X1,X1),X2),X2)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.37  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (k2_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_15, c_0_13])).
% 0.13/0.37  fof(c_0_20, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.37  fof(c_0_21, plain, ![X10, X11]:(~r2_hidden(X10,X11)|k2_xboole_0(k1_tarski(X10),X11)=X11), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.13/0.37  cnf(c_0_22, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(X2,k2_tarski(X1,X1)),X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (k2_xboole_0(esk2_0,k2_tarski(esk1_0,esk1_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.13/0.37  cnf(c_0_25, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_26, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k2_tarski(X1,X1),X2)), inference(rw,[status(thm)],[c_0_22, c_0_13])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.13/0.37  cnf(c_0_29, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_13])).
% 0.13/0.37  fof(c_0_30, plain, ![X6]:r1_xboole_0(X6,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (~r1_xboole_0(k2_tarski(esk1_0,esk1_0),esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (esk2_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_18]), c_0_24])).
% 0.13/0.37  cnf(c_0_33, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 35
% 0.13/0.37  # Proof object clause steps            : 18
% 0.13/0.37  # Proof object formula steps           : 17
% 0.13/0.37  # Proof object conjectures             : 10
% 0.13/0.37  # Proof object clause conjectures      : 7
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 8
% 0.13/0.37  # Proof object initial formulas used   : 8
% 0.13/0.37  # Proof object generating inferences   : 4
% 0.13/0.37  # Proof object simplifying inferences  : 12
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 8
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 8
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 7
% 0.13/0.37  # Processed clauses                    : 20
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 1
% 0.13/0.37  # ...remaining for further processing  : 19
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 4
% 0.13/0.37  # Generated clauses                    : 7
% 0.13/0.37  # ...of the previous two non-trivial   : 9
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 7
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
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
% 0.13/0.37  # Current number of processed clauses  : 8
% 0.13/0.37  #    Positive orientable unit clauses  : 3
% 0.13/0.37  #    Positive unorientable unit clauses: 1
% 0.13/0.37  #    Negative unit clauses             : 0
% 0.13/0.37  #    Non-unit-clauses                  : 4
% 0.13/0.37  # Current number of unprocessed clauses: 2
% 0.13/0.37  # ...number of literals in the above   : 4
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 12
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 3
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 3
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.37  # Unit Clause-clause subsumption calls : 1
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 3
% 0.13/0.37  # BW rewrite match successes           : 3
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 490
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.027 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.029 s
% 0.13/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
