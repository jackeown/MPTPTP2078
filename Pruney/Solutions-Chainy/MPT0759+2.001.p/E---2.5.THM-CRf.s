%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:40 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 102 expanded)
%              Number of clauses        :   16 (  42 expanded)
%              Number of leaves         :    9 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 ( 121 expanded)
%              Number of equality atoms :   30 (  96 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_ordinal1,conjecture,(
    ! [X1] : k6_subset_1(k1_ordinal1(X1),k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t144_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3)
        & X3 != k4_xboole_0(X3,k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] : k6_subset_1(k1_ordinal1(X1),k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t52_ordinal1])).

fof(c_0_10,plain,(
    ! [X18] : k1_ordinal1(X18) = k2_xboole_0(X18,k1_tarski(X18)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_11,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,negated_conjecture,(
    k6_subset_1(k1_ordinal1(esk1_0),k1_tarski(esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,plain,(
    ! [X16,X17] : k6_subset_1(X16,X17) = k4_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_14,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X11,X12] : k3_tarski(k2_tarski(X11,X12)) = k2_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X9,X10] : k2_enumset1(X9,X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_18,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),X7) = k4_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_19,negated_conjecture,
    ( k6_subset_1(k1_ordinal1(esk1_0),k1_tarski(esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X13,X14,X15] :
      ( r2_hidden(X13,X15)
      | r2_hidden(X14,X15)
      | X15 = k4_xboole_0(X15,k2_tarski(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)) != esk1_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_15]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_23]),c_0_23])).

cnf(c_0_27,plain,
    ( k4_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_22]),c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X3,X2)
    | X2 = k4_xboole_0(X2,k2_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_29,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | ~ r2_hidden(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)) != esk1_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( X2 = k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))
    | r2_hidden(X3,X2)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:52:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t52_ordinal1, conjecture, ![X1]:k6_subset_1(k1_ordinal1(X1),k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_ordinal1)).
% 0.12/0.36  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.12/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.36  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.12/0.36  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.12/0.36  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.12/0.36  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.12/0.36  fof(t144_zfmisc_1, axiom, ![X1, X2, X3]:~(((~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))&X3!=k4_xboole_0(X3,k2_tarski(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 0.12/0.36  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.12/0.36  fof(c_0_9, negated_conjecture, ~(![X1]:k6_subset_1(k1_ordinal1(X1),k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t52_ordinal1])).
% 0.12/0.36  fof(c_0_10, plain, ![X18]:k1_ordinal1(X18)=k2_xboole_0(X18,k1_tarski(X18)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.12/0.36  fof(c_0_11, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.36  fof(c_0_12, negated_conjecture, k6_subset_1(k1_ordinal1(esk1_0),k1_tarski(esk1_0))!=esk1_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.12/0.36  fof(c_0_13, plain, ![X16, X17]:k6_subset_1(X16,X17)=k4_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.12/0.36  cnf(c_0_14, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.36  cnf(c_0_15, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  fof(c_0_16, plain, ![X11, X12]:k3_tarski(k2_tarski(X11,X12))=k2_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.12/0.36  fof(c_0_17, plain, ![X9, X10]:k2_enumset1(X9,X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.12/0.36  fof(c_0_18, plain, ![X6, X7]:k4_xboole_0(k2_xboole_0(X6,X7),X7)=k4_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.12/0.36  cnf(c_0_19, negated_conjecture, (k6_subset_1(k1_ordinal1(esk1_0),k1_tarski(esk1_0))!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.36  cnf(c_0_20, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.36  cnf(c_0_21, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.36  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_24, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  fof(c_0_25, plain, ![X13, X14, X15]:(r2_hidden(X13,X15)|r2_hidden(X14,X15)|X15=k4_xboole_0(X15,k2_tarski(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t144_zfmisc_1])])])).
% 0.12/0.36  cnf(c_0_26, negated_conjecture, (k4_xboole_0(k3_tarski(k2_enumset1(esk1_0,esk1_0,esk1_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))!=esk1_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_15]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_23]), c_0_23])).
% 0.12/0.36  cnf(c_0_27, plain, (k4_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_22]), c_0_23])).
% 0.12/0.36  cnf(c_0_28, plain, (r2_hidden(X1,X2)|r2_hidden(X3,X2)|X2=k4_xboole_0(X2,k2_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.36  fof(c_0_29, plain, ![X4, X5]:(~r2_hidden(X4,X5)|~r2_hidden(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.12/0.36  cnf(c_0_30, negated_conjecture, (k4_xboole_0(esk1_0,k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))!=esk1_0), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.36  cnf(c_0_31, plain, (X2=k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X3))|r2_hidden(X3,X2)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_28, c_0_23])).
% 0.12/0.36  cnf(c_0_32, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.36  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.36  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_33])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 35
% 0.12/0.36  # Proof object clause steps            : 16
% 0.12/0.36  # Proof object formula steps           : 19
% 0.12/0.36  # Proof object conjectures             : 8
% 0.12/0.36  # Proof object clause conjectures      : 5
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 9
% 0.12/0.36  # Proof object initial formulas used   : 9
% 0.12/0.36  # Proof object generating inferences   : 2
% 0.12/0.36  # Proof object simplifying inferences  : 14
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 9
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 9
% 0.12/0.36  # Removed in clause preprocessing      : 5
% 0.12/0.36  # Initial clauses in saturation        : 4
% 0.12/0.36  # Processed clauses                    : 10
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 10
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 1
% 0.12/0.36  # Generated clauses                    : 3
% 0.12/0.36  # ...of the previous two non-trivial   : 3
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 3
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 5
% 0.12/0.36  #    Positive orientable unit clauses  : 2
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 1
% 0.12/0.36  #    Non-unit-clauses                  : 2
% 0.12/0.36  # Current number of unprocessed clauses: 1
% 0.12/0.36  # ...number of literals in the above   : 3
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 10
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 1
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 1
% 0.12/0.36  # BW rewrite match successes           : 1
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 484
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.025 s
% 0.12/0.36  # System time              : 0.005 s
% 0.12/0.36  # Total time               : 0.030 s
% 0.12/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
