%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:47 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   30 (  39 expanded)
%              Number of clauses        :   15 (  17 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  60 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t175_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t177_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_relat_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(c_0_7,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,k2_xboole_0(X9,X10))
      | r1_tarski(k4_xboole_0(X8,X9),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_8,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X17)
      | k10_relat_1(X17,k2_xboole_0(X15,X16)) = k2_xboole_0(k10_relat_1(X17,X15),k10_relat_1(X17,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).

fof(c_0_9,plain,(
    ! [X11,X12] : r1_tarski(X11,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_10,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2))) ) ),
    inference(assume_negation,[status(cth)],[t177_relat_1])).

cnf(c_0_12,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k10_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(X6,X7) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & ~ r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_18,plain,(
    ! [X13,X14] : k6_subset_1(X13,X14) = k4_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_19,plain,
    ( r1_tarski(k4_xboole_0(X1,k10_relat_1(X2,X3)),k10_relat_1(X2,X4))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,k2_xboole_0(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r1_tarski(k4_xboole_0(X1,k10_relat_1(X2,X3)),k10_relat_1(X2,k4_xboole_0(X4,X3)))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k10_relat_1(X2,k2_xboole_0(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_xboole_0(X3,X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k4_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_23])).

cnf(c_0_27,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3)),k10_relat_1(X1,k4_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 0.48/0.67  # AutoSched0-Mode selected heuristic G_____Y1346__C12_02_nc_F1_AE_CS_SP_S2S
% 0.48/0.67  # and selection function SelectNewComplexAHP.
% 0.48/0.67  #
% 0.48/0.67  # Preprocessing time       : 0.026 s
% 0.48/0.67  # Presaturation interreduction done
% 0.48/0.67  
% 0.48/0.67  # Proof found!
% 0.48/0.67  # SZS status Theorem
% 0.48/0.67  # SZS output start CNFRefutation
% 0.48/0.67  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.48/0.67  fof(t175_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 0.48/0.67  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.48/0.67  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.48/0.67  fof(t177_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_relat_1)).
% 0.48/0.67  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.48/0.67  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.48/0.67  fof(c_0_7, plain, ![X8, X9, X10]:(~r1_tarski(X8,k2_xboole_0(X9,X10))|r1_tarski(k4_xboole_0(X8,X9),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.48/0.67  fof(c_0_8, plain, ![X15, X16, X17]:(~v1_relat_1(X17)|k10_relat_1(X17,k2_xboole_0(X15,X16))=k2_xboole_0(k10_relat_1(X17,X15),k10_relat_1(X17,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t175_relat_1])])).
% 0.48/0.67  fof(c_0_9, plain, ![X11, X12]:r1_tarski(X11,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.48/0.67  fof(c_0_10, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.48/0.67  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k6_subset_1(k10_relat_1(X3,X1),k10_relat_1(X3,X2)),k10_relat_1(X3,k6_subset_1(X1,X2))))), inference(assume_negation,[status(cth)],[t177_relat_1])).
% 0.48/0.67  cnf(c_0_12, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.48/0.67  cnf(c_0_13, plain, (k10_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.48/0.67  fof(c_0_14, plain, ![X6, X7]:k2_xboole_0(X6,k4_xboole_0(X7,X6))=k2_xboole_0(X6,X7), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.48/0.67  cnf(c_0_15, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.48/0.67  cnf(c_0_16, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.48/0.67  fof(c_0_17, negated_conjecture, (v1_relat_1(esk3_0)&~r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.48/0.67  fof(c_0_18, plain, ![X13, X14]:k6_subset_1(X13,X14)=k4_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.48/0.67  cnf(c_0_19, plain, (r1_tarski(k4_xboole_0(X1,k10_relat_1(X2,X3)),k10_relat_1(X2,X4))|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,k2_xboole_0(X3,X4)))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.48/0.67  cnf(c_0_20, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.48/0.67  cnf(c_0_21, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.48/0.67  cnf(c_0_22, negated_conjecture, (~r1_tarski(k6_subset_1(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k6_subset_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.67  cnf(c_0_23, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.48/0.67  cnf(c_0_24, plain, (r1_tarski(k4_xboole_0(X1,k10_relat_1(X2,X3)),k10_relat_1(X2,k4_xboole_0(X4,X3)))|~v1_relat_1(X2)|~r1_tarski(X1,k10_relat_1(X2,k2_xboole_0(X3,X4)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.48/0.67  cnf(c_0_25, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,k2_xboole_0(X3,X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_13])).
% 0.48/0.67  cnf(c_0_26, negated_conjecture, (~r1_tarski(k4_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,k4_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_23])).
% 0.48/0.67  cnf(c_0_27, plain, (r1_tarski(k4_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3)),k10_relat_1(X1,k4_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.48/0.67  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.48/0.67  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])]), ['proof']).
% 0.48/0.67  # SZS output end CNFRefutation
% 0.48/0.67  # Proof object total steps             : 30
% 0.48/0.67  # Proof object clause steps            : 15
% 0.48/0.67  # Proof object formula steps           : 15
% 0.48/0.67  # Proof object conjectures             : 7
% 0.48/0.67  # Proof object clause conjectures      : 4
% 0.48/0.67  # Proof object formula conjectures     : 3
% 0.48/0.67  # Proof object initial clauses used    : 8
% 0.48/0.67  # Proof object initial formulas used   : 7
% 0.48/0.67  # Proof object generating inferences   : 6
% 0.48/0.67  # Proof object simplifying inferences  : 4
% 0.48/0.67  # Training examples: 0 positive, 0 negative
% 0.48/0.67  # Parsed axioms                        : 7
% 0.48/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.67  # Initial clauses                      : 8
% 0.48/0.67  # Removed in clause preprocessing      : 1
% 0.48/0.67  # Initial clauses in saturation        : 7
% 0.48/0.67  # Processed clauses                    : 2570
% 0.48/0.67  # ...of these trivial                  : 1248
% 0.48/0.67  # ...subsumed                          : 227
% 0.48/0.67  # ...remaining for further processing  : 1095
% 0.48/0.67  # Other redundant clauses eliminated   : 0
% 0.48/0.67  # Clauses deleted for lack of memory   : 0
% 0.48/0.67  # Backward-subsumed                    : 0
% 0.48/0.67  # Backward-rewritten                   : 0
% 0.48/0.67  # Generated clauses                    : 27797
% 0.48/0.67  # ...of the previous two non-trivial   : 25234
% 0.48/0.67  # Contextual simplify-reflections      : 0
% 0.48/0.67  # Paramodulations                      : 27797
% 0.48/0.67  # Factorizations                       : 0
% 0.48/0.67  # Equation resolutions                 : 0
% 0.48/0.67  # Propositional unsat checks           : 0
% 0.48/0.67  #    Propositional check models        : 0
% 0.48/0.67  #    Propositional check unsatisfiable : 0
% 0.48/0.67  #    Propositional clauses             : 0
% 0.48/0.67  #    Propositional clauses after purity: 0
% 0.48/0.67  #    Propositional unsat core size     : 0
% 0.48/0.67  #    Propositional preprocessing time  : 0.000
% 0.48/0.67  #    Propositional encoding time       : 0.000
% 0.48/0.67  #    Propositional solver time         : 0.000
% 0.48/0.67  #    Success case prop preproc time    : 0.000
% 0.48/0.67  #    Success case prop encoding time   : 0.000
% 0.48/0.67  #    Success case prop solver time     : 0.000
% 0.48/0.67  # Current number of processed clauses  : 1088
% 0.48/0.67  #    Positive orientable unit clauses  : 929
% 0.48/0.67  #    Positive unorientable unit clauses: 1
% 0.48/0.67  #    Negative unit clauses             : 1
% 0.48/0.67  #    Non-unit-clauses                  : 157
% 0.48/0.67  # Current number of unprocessed clauses: 22678
% 0.48/0.67  # ...number of literals in the above   : 28840
% 0.48/0.67  # Current number of archived formulas  : 0
% 0.48/0.67  # Current number of archived clauses   : 8
% 0.48/0.67  # Clause-clause subsumption calls (NU) : 9028
% 0.48/0.67  # Rec. Clause-clause subsumption calls : 9028
% 0.48/0.67  # Non-unit clause-clause subsumptions  : 227
% 0.48/0.67  # Unit Clause-clause subsumption calls : 43
% 0.48/0.67  # Rewrite failures with RHS unbound    : 0
% 0.48/0.67  # BW rewrite match attempts            : 162424
% 0.48/0.67  # BW rewrite match successes           : 4
% 0.48/0.67  # Condensation attempts                : 0
% 0.48/0.67  # Condensation successes               : 0
% 0.48/0.67  # Termbank termtop insertions          : 497637
% 0.48/0.67  
% 0.48/0.67  # -------------------------------------------------
% 0.48/0.67  # User time                : 0.309 s
% 0.48/0.67  # System time              : 0.017 s
% 0.48/0.67  # Total time               : 0.327 s
% 0.48/0.67  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
