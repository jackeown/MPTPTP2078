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
% DateTime   : Thu Dec  3 10:35:11 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 201 expanded)
%              Number of clauses        :   21 (  82 expanded)
%              Number of leaves         :    9 (  59 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 ( 201 expanded)
%              Number of equality atoms :   39 ( 200 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_xboole_1,axiom,(
    ! [X1,X2,X3,X4] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(t55_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(t53_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

fof(c_0_9,plain,(
    ! [X7,X8,X9,X10] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X7,X8),X9),X10) = k2_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X9),X10)) ),
    inference(variable_rename,[status(thm)],[t113_xboole_1])).

fof(c_0_10,plain,(
    ! [X11,X12] : k2_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,X12),k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_11,plain,(
    ! [X15,X16,X17] : k1_enumset1(X15,X16,X17) = k2_xboole_0(k2_tarski(X15,X16),k1_tarski(X17)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_12,plain,(
    ! [X13,X14] : k2_tarski(X13,X14) = k2_xboole_0(k1_tarski(X13),k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_13,plain,(
    ! [X18,X19,X20,X21] : k2_enumset1(X18,X19,X20,X21) = k2_xboole_0(k1_enumset1(X18,X19,X20),k1_tarski(X21)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_14,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X22,X23,X24,X25,X26] : k3_enumset1(X22,X23,X24,X25,X26) = k2_xboole_0(k2_enumset1(X22,X23,X24,X25),k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X27,X28,X29,X30,X31,X32] : k4_enumset1(X27,X28,X29,X30,X31,X32) = k2_xboole_0(k1_tarski(X27),k3_enumset1(X28,X29,X30,X31,X32)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(assume_negation,[status(cth)],[t55_enumset1])).

cnf(c_0_22,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4))),k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_15]),c_0_15]),c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_15]),c_0_15])).

cnf(c_0_24,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_15])).

fof(c_0_26,plain,(
    ! [X33,X34,X35,X36,X37,X38] : k4_enumset1(X33,X34,X35,X36,X37,X38) = k2_xboole_0(k1_enumset1(X33,X34,X35),k1_enumset1(X36,X37,X38)) ),
    inference(variable_rename,[status(thm)],[t53_enumset1])).

cnf(c_0_27,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,negated_conjecture,(
    k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_29,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))) = k5_xboole_0(k5_xboole_0(X1,k1_enumset1(X2,X3,X4)),k3_xboole_0(X1,k1_enumset1(X2,X3,X4))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_15]),c_0_25]),c_0_25])).

cnf(c_0_31,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)),k3_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_enumset1(X2,X3,X4)),k3_xboole_0(X1,k1_enumset1(X2,X3,X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_enumset1(X2,X3,X4)),k3_xboole_0(X1,k1_enumset1(X2,X3,X4))),k1_tarski(X5))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_enumset1(X3,X4,X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_enumset1(X3,X4,X5))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_29])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5))) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_30])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)),k3_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_15]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k3_xboole_0(k1_tarski(esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) != k5_xboole_0(k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0)),k3_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_15]),c_0_32])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)),k3_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)),k3_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_23]),c_0_23]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.026 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t113_xboole_1, axiom, ![X1, X2, X3, X4]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_xboole_1)).
% 0.14/0.38  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.14/0.38  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 0.14/0.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.14/0.38  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.14/0.38  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 0.14/0.38  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 0.14/0.38  fof(t55_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 0.14/0.38  fof(t53_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_enumset1)).
% 0.14/0.38  fof(c_0_9, plain, ![X7, X8, X9, X10]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X7,X8),X9),X10)=k2_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X9),X10)), inference(variable_rename,[status(thm)],[t113_xboole_1])).
% 0.14/0.38  fof(c_0_10, plain, ![X11, X12]:k2_xboole_0(X11,X12)=k5_xboole_0(k5_xboole_0(X11,X12),k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.14/0.38  fof(c_0_11, plain, ![X15, X16, X17]:k1_enumset1(X15,X16,X17)=k2_xboole_0(k2_tarski(X15,X16),k1_tarski(X17)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.14/0.38  fof(c_0_12, plain, ![X13, X14]:k2_tarski(X13,X14)=k2_xboole_0(k1_tarski(X13),k1_tarski(X14)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.14/0.38  fof(c_0_13, plain, ![X18, X19, X20, X21]:k2_enumset1(X18,X19,X20,X21)=k2_xboole_0(k1_enumset1(X18,X19,X20),k1_tarski(X21)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.14/0.38  cnf(c_0_14, plain, (k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_16, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_17, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  fof(c_0_18, plain, ![X22, X23, X24, X25, X26]:k3_enumset1(X22,X23,X24,X25,X26)=k2_xboole_0(k2_enumset1(X22,X23,X24,X25),k1_tarski(X26)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.14/0.38  cnf(c_0_19, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  fof(c_0_20, plain, ![X27, X28, X29, X30, X31, X32]:k4_enumset1(X27,X28,X29,X30,X31,X32)=k2_xboole_0(k1_tarski(X27),k3_enumset1(X28,X29,X30,X31,X32)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.14/0.38  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(assume_negation,[status(cth)],[t55_enumset1])).
% 0.14/0.38  cnf(c_0_22, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4))=k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4))),k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_15]), c_0_15]), c_0_15]), c_0_15]), c_0_15])).
% 0.14/0.38  cnf(c_0_23, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_15]), c_0_15])).
% 0.14/0.38  cnf(c_0_24, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_25, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)))), inference(rw,[status(thm)],[c_0_19, c_0_15])).
% 0.14/0.38  fof(c_0_26, plain, ![X33, X34, X35, X36, X37, X38]:k4_enumset1(X33,X34,X35,X36,X37,X38)=k2_xboole_0(k1_enumset1(X33,X34,X35),k1_enumset1(X36,X37,X38)), inference(variable_rename,[status(thm)],[t53_enumset1])).
% 0.14/0.38  cnf(c_0_27, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  fof(c_0_28, negated_conjecture, k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.14/0.38  cnf(c_0_29, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)))=k5_xboole_0(k5_xboole_0(X1,k1_enumset1(X2,X3,X4)),k3_xboole_0(X1,k1_enumset1(X2,X3,X4)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.38  cnf(c_0_30, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_15]), c_0_25]), c_0_25])).
% 0.14/0.38  cnf(c_0_31, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_32, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)),k3_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)))), inference(rw,[status(thm)],[c_0_27, c_0_15])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k2_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_34, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_enumset1(X2,X3,X4)),k3_xboole_0(X1,k1_enumset1(X2,X3,X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_enumset1(X2,X3,X4)),k3_xboole_0(X1,k1_enumset1(X2,X3,X4))),k1_tarski(X5)))=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_enumset1(X3,X4,X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_enumset1(X3,X4,X5)))), inference(spm,[status(thm)],[c_0_29, c_0_29])).
% 0.14/0.38  cnf(c_0_35, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5)))=k3_enumset1(X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_23]), c_0_30])).
% 0.14/0.38  cnf(c_0_36, plain, (k5_xboole_0(k5_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)),k3_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)))=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_15]), c_0_32])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k3_xboole_0(k1_tarski(esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))!=k5_xboole_0(k5_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0)),k3_xboole_0(k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),k1_tarski(esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_15]), c_0_32])).
% 0.14/0.38  cnf(c_0_38, plain, (k5_xboole_0(k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)),k3_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)))=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)),k3_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_23]), c_0_23]), c_0_36])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 40
% 0.14/0.38  # Proof object clause steps            : 21
% 0.14/0.38  # Proof object formula steps           : 19
% 0.14/0.38  # Proof object conjectures             : 6
% 0.14/0.38  # Proof object clause conjectures      : 3
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 9
% 0.14/0.38  # Proof object initial formulas used   : 9
% 0.14/0.38  # Proof object generating inferences   : 4
% 0.14/0.38  # Proof object simplifying inferences  : 24
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 9
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 9
% 0.14/0.38  # Removed in clause preprocessing      : 4
% 0.14/0.38  # Initial clauses in saturation        : 5
% 0.14/0.38  # Processed clauses                    : 20
% 0.14/0.38  # ...of these trivial                  : 4
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 16
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 3
% 0.14/0.38  # Generated clauses                    : 134
% 0.14/0.38  # ...of the previous two non-trivial   : 128
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 134
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 8
% 0.14/0.38  #    Positive orientable unit clauses  : 7
% 0.14/0.38  #    Positive unorientable unit clauses: 1
% 0.14/0.38  #    Negative unit clauses             : 0
% 0.14/0.38  #    Non-unit-clauses                  : 0
% 0.14/0.38  # Current number of unprocessed clauses: 116
% 0.14/0.38  # ...number of literals in the above   : 116
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 12
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 0
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 0
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.38  # Unit Clause-clause subsumption calls : 0
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 17
% 0.14/0.38  # BW rewrite match successes           : 3
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 14724
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.032 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.037 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
