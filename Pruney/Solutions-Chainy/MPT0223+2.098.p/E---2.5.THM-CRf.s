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
% DateTime   : Thu Dec  3 10:37:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  63 expanded)
%              Number of clauses        :   15 (  26 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 ( 101 expanded)
%              Number of equality atoms :   27 (  72 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t78_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(t17_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(t16_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
        & X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(t76_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t18_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X6,X7,X8] : k3_xboole_0(X6,k2_xboole_0(X7,X8)) = k2_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X8)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

fof(c_0_9,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) = k1_tarski(esk1_0)
    & esk1_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X4,X5] : k2_xboole_0(X4,k3_xboole_0(X4,X5)) = X4 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_11,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_xboole_0(X12,X13)
      | k3_xboole_0(X12,k2_xboole_0(X13,X14)) = k3_xboole_0(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).

cnf(c_0_12,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) = k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),X1)) = k1_tarski(esk1_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

fof(c_0_17,plain,(
    ! [X17,X18] :
      ( X17 = X18
      | r1_xboole_0(k1_tarski(X17),k1_tarski(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ~ r1_xboole_0(k1_tarski(X15),k1_tarski(X16))
      | X15 != X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).

fof(c_0_19,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_xboole_0(X9,X10)
      | r1_xboole_0(k3_xboole_0(X11,X9),k3_xboole_0(X11,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_xboole_1])])).

cnf(c_0_20,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk1_0),X1) = k1_tarski(esk1_0)
    | ~ r1_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk1_0),X1) = k1_tarski(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_26,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_xboole_0(X1,X2) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_25]),c_0_26])).

cnf(c_0_28,plain,
    ( X1 = X2 ),
    inference(sr,[status(thm)],[c_0_21,c_0_27])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_22,c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:55:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053N
% 0.20/0.37  # and selection function HSelectMinInfpos.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t18_zfmisc_1, conjecture, ![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 0.20/0.37  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.20/0.37  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.20/0.37  fof(t78_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 0.20/0.37  fof(t17_zfmisc_1, axiom, ![X1, X2]:(X1!=X2=>r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 0.20/0.37  fof(t16_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),k1_tarski(X2))&X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 0.20/0.37  fof(t76_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 0.20/0.37  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t18_zfmisc_1])).
% 0.20/0.37  fof(c_0_8, plain, ![X6, X7, X8]:k3_xboole_0(X6,k2_xboole_0(X7,X8))=k2_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X8)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.20/0.37  fof(c_0_9, negated_conjecture, (k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))=k1_tarski(esk1_0)&esk1_0!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.20/0.37  fof(c_0_10, plain, ![X4, X5]:k2_xboole_0(X4,k3_xboole_0(X4,X5))=X4, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.20/0.37  fof(c_0_11, plain, ![X12, X13, X14]:(~r1_xboole_0(X12,X13)|k3_xboole_0(X12,k2_xboole_0(X13,X14))=k3_xboole_0(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).
% 0.20/0.37  cnf(c_0_12, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  cnf(c_0_13, negated_conjecture, (k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_14, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_15, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  cnf(c_0_16, negated_conjecture, (k3_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),X1))=k1_tarski(esk1_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.20/0.37  fof(c_0_17, plain, ![X17, X18]:(X17=X18|r1_xboole_0(k1_tarski(X17),k1_tarski(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).
% 0.20/0.37  fof(c_0_18, plain, ![X15, X16]:(~r1_xboole_0(k1_tarski(X15),k1_tarski(X16))|X15!=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).
% 0.20/0.37  fof(c_0_19, plain, ![X9, X10, X11]:(~r1_xboole_0(X9,X10)|r1_xboole_0(k3_xboole_0(X11,X9),k3_xboole_0(X11,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_xboole_1])])).
% 0.20/0.37  cnf(c_0_20, negated_conjecture, (k3_xboole_0(k1_tarski(esk1_0),X1)=k1_tarski(esk1_0)|~r1_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.37  cnf(c_0_21, plain, (X1=X2|r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.37  cnf(c_0_22, negated_conjecture, (esk1_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_23, plain, (~r1_xboole_0(k1_tarski(X1),k1_tarski(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_24, plain, (r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, (k3_xboole_0(k1_tarski(esk1_0),X1)=k1_tarski(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.20/0.37  cnf(c_0_26, plain, (~r1_xboole_0(k1_tarski(X1),k1_tarski(X1))), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, (~r1_xboole_0(X1,X2)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_25]), c_0_26])).
% 0.20/0.37  cnf(c_0_28, plain, (X1=X2), inference(sr,[status(thm)],[c_0_21, c_0_27])).
% 0.20/0.37  cnf(c_0_29, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_22, c_0_28]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 30
% 0.20/0.37  # Proof object clause steps            : 15
% 0.20/0.37  # Proof object formula steps           : 15
% 0.20/0.37  # Proof object conjectures             : 10
% 0.20/0.37  # Proof object clause conjectures      : 7
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 8
% 0.20/0.37  # Proof object initial formulas used   : 7
% 0.20/0.37  # Proof object generating inferences   : 4
% 0.20/0.37  # Proof object simplifying inferences  : 7
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 7
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 8
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 8
% 0.20/0.37  # Processed clauses                    : 23
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 23
% 0.20/0.37  # Other redundant clauses eliminated   : 1
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 5
% 0.20/0.37  # Backward-rewritten                   : 3
% 0.20/0.37  # Generated clauses                    : 32
% 0.20/0.37  # ...of the previous two non-trivial   : 19
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 29
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 1
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 4
% 0.20/0.37  #    Positive orientable unit clauses  : 0
% 0.20/0.37  #    Positive unorientable unit clauses: 1
% 0.20/0.37  #    Negative unit clauses             : 2
% 0.20/0.37  #    Non-unit-clauses                  : 1
% 0.20/0.37  # Current number of unprocessed clauses: 12
% 0.20/0.37  # ...number of literals in the above   : 20
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 18
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 3
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 3
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 9
% 0.20/0.37  # Rewrite failures with RHS unbound    : 32
% 0.20/0.37  # BW rewrite match attempts            : 29
% 0.20/0.37  # BW rewrite match successes           : 27
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 817
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.024 s
% 0.20/0.37  # System time              : 0.006 s
% 0.20/0.37  # Total time               : 0.030 s
% 0.20/0.37  # Maximum resident set size: 1560 pages
%------------------------------------------------------------------------------
