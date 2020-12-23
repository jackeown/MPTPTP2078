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
% DateTime   : Thu Dec  3 10:51:48 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   30 (  44 expanded)
%              Number of clauses        :   15 (  19 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  75 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t177_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2))) ) ),
    inference(assume_negation,[status(cth)],[t177_relat_1])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X14,X15] : k6_subset_1(X14,X15) = k4_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,k2_xboole_0(X12,X13))
      | r1_tarski(k4_xboole_0(X11,X12),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_13,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | k10_relat_1(X18,k2_xboole_0(X16,X17)) = k2_xboole_0(k10_relat_1(X18,X16),k10_relat_1(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k4_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_11])).

cnf(c_0_15,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_18,plain,(
    ! [X9,X10] : k2_xboole_0(X9,k4_xboole_0(X10,X9)) = k2_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_19,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | r1_tarski(X6,k2_xboole_0(X8,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_20,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk3_0,esk1_0),k2_xboole_0(k10_relat_1(esk3_0,esk2_0),k10_relat_1(esk3_0,k4_xboole_0(esk1_0,esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k2_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)) = k10_relat_1(esk3_0,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,k2_xboole_0(esk2_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk3_0,k2_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,k10_relat_1(esk3_0,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:30:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S061I
% 0.15/0.38  # and selection function SelectMaxLComplexAPPNTNp.
% 0.15/0.38  #
% 0.15/0.38  # Preprocessing time       : 0.026 s
% 0.15/0.38  # Presaturation interreduction done
% 0.15/0.38  
% 0.15/0.38  # Proof found!
% 0.15/0.38  # SZS status Theorem
% 0.15/0.38  # SZS output start CNFRefutation
% 0.15/0.38  fof(t177_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_relat_1)).
% 0.15/0.38  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.15/0.38  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.15/0.38  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 0.15/0.38  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.15/0.38  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.15/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.15/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2))))), inference(assume_negation,[status(cth)],[t177_relat_1])).
% 0.15/0.38  fof(c_0_8, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.15/0.38  fof(c_0_9, plain, ![X14, X15]:k6_subset_1(X14,X15)=k4_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.15/0.38  cnf(c_0_10, negated_conjecture, (~r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.38  cnf(c_0_11, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.38  fof(c_0_12, plain, ![X11, X12, X13]:(~r1_tarski(X11,k2_xboole_0(X12,X13))|r1_tarski(k4_xboole_0(X11,X12),X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.15/0.38  fof(c_0_13, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|k10_relat_1(X18,k2_xboole_0(X16,X17))=k2_xboole_0(k10_relat_1(X18,X16),k10_relat_1(X18,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.15/0.38  cnf(c_0_14, negated_conjecture, (~r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k4_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_11]), c_0_11])).
% 0.15/0.38  cnf(c_0_15, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.38  cnf(c_0_16, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.38  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.38  fof(c_0_18, plain, ![X9, X10]:k2_xboole_0(X9,k4_xboole_0(X10,X9))=k2_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.15/0.38  fof(c_0_19, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|r1_tarski(X6,k2_xboole_0(X8,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.15/0.38  fof(c_0_20, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.15/0.38  cnf(c_0_21, negated_conjecture, (~r1_tarski(k10_relat_1(esk3_0,esk1_0),k2_xboole_0(k10_relat_1(esk3_0,esk2_0),k10_relat_1(esk3_0,k4_xboole_0(esk1_0,esk2_0))))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.15/0.38  cnf(c_0_22, negated_conjecture, (k2_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))=k10_relat_1(esk3_0,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.15/0.38  cnf(c_0_23, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.38  cnf(c_0_24, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.15/0.38  cnf(c_0_25, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.38  cnf(c_0_26, negated_conjecture, (~r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,k2_xboole_0(esk2_0,esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.15/0.38  cnf(c_0_27, negated_conjecture, (r1_tarski(X1,k10_relat_1(esk3_0,k2_xboole_0(X2,X3)))|~r1_tarski(X1,k10_relat_1(esk3_0,X3))), inference(spm,[status(thm)],[c_0_24, c_0_22])).
% 0.15/0.38  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_25])).
% 0.15/0.38  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])]), ['proof']).
% 0.15/0.38  # SZS output end CNFRefutation
% 0.15/0.38  # Proof object total steps             : 30
% 0.15/0.38  # Proof object clause steps            : 15
% 0.15/0.38  # Proof object formula steps           : 15
% 0.15/0.38  # Proof object conjectures             : 11
% 0.15/0.38  # Proof object clause conjectures      : 8
% 0.15/0.38  # Proof object formula conjectures     : 3
% 0.15/0.38  # Proof object initial clauses used    : 8
% 0.15/0.38  # Proof object initial formulas used   : 7
% 0.15/0.38  # Proof object generating inferences   : 4
% 0.15/0.38  # Proof object simplifying inferences  : 7
% 0.15/0.38  # Training examples: 0 positive, 0 negative
% 0.15/0.38  # Parsed axioms                        : 7
% 0.15/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.38  # Initial clauses                      : 10
% 0.15/0.38  # Removed in clause preprocessing      : 1
% 0.15/0.38  # Initial clauses in saturation        : 9
% 0.15/0.38  # Processed clauses                    : 26
% 0.15/0.38  # ...of these trivial                  : 0
% 0.15/0.38  # ...subsumed                          : 0
% 0.15/0.38  # ...remaining for further processing  : 26
% 0.15/0.38  # Other redundant clauses eliminated   : 2
% 0.15/0.38  # Clauses deleted for lack of memory   : 0
% 0.15/0.38  # Backward-subsumed                    : 0
% 0.15/0.38  # Backward-rewritten                   : 1
% 0.15/0.38  # Generated clauses                    : 22
% 0.15/0.38  # ...of the previous two non-trivial   : 17
% 0.15/0.38  # Contextual simplify-reflections      : 0
% 0.15/0.38  # Paramodulations                      : 20
% 0.15/0.38  # Factorizations                       : 0
% 0.15/0.38  # Equation resolutions                 : 2
% 0.15/0.38  # Propositional unsat checks           : 0
% 0.15/0.38  #    Propositional check models        : 0
% 0.15/0.38  #    Propositional check unsatisfiable : 0
% 0.15/0.38  #    Propositional clauses             : 0
% 0.15/0.38  #    Propositional clauses after purity: 0
% 0.15/0.38  #    Propositional unsat core size     : 0
% 0.15/0.38  #    Propositional preprocessing time  : 0.000
% 0.15/0.38  #    Propositional encoding time       : 0.000
% 0.15/0.38  #    Propositional solver time         : 0.000
% 0.15/0.38  #    Success case prop preproc time    : 0.000
% 0.15/0.38  #    Success case prop encoding time   : 0.000
% 0.15/0.38  #    Success case prop solver time     : 0.000
% 0.15/0.38  # Current number of processed clauses  : 15
% 0.15/0.38  #    Positive orientable unit clauses  : 5
% 0.15/0.38  #    Positive unorientable unit clauses: 0
% 0.15/0.38  #    Negative unit clauses             : 3
% 0.15/0.38  #    Non-unit-clauses                  : 7
% 0.15/0.38  # Current number of unprocessed clauses: 8
% 0.15/0.38  # ...number of literals in the above   : 18
% 0.15/0.38  # Current number of archived formulas  : 0
% 0.15/0.38  # Current number of archived clauses   : 10
% 0.15/0.38  # Clause-clause subsumption calls (NU) : 5
% 0.15/0.38  # Rec. Clause-clause subsumption calls : 5
% 0.15/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.15/0.38  # Unit Clause-clause subsumption calls : 2
% 0.15/0.38  # Rewrite failures with RHS unbound    : 0
% 0.15/0.38  # BW rewrite match attempts            : 2
% 0.15/0.38  # BW rewrite match successes           : 1
% 0.15/0.38  # Condensation attempts                : 0
% 0.15/0.38  # Condensation successes               : 0
% 0.15/0.38  # Termbank termtop insertions          : 845
% 0.15/0.38  
% 0.15/0.38  # -------------------------------------------------
% 0.15/0.38  # User time                : 0.026 s
% 0.15/0.38  # System time              : 0.005 s
% 0.15/0.38  # Total time               : 0.031 s
% 0.15/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
