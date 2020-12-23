%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:08 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 124 expanded)
%              Number of clauses        :   19 (  51 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 ( 124 expanded)
%              Number of equality atoms :   35 ( 123 expanded)
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

fof(t51_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(l62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(c_0_8,plain,(
    ! [X7,X8,X9,X10] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X7,X8),X9),X10) = k2_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X9),X10)) ),
    inference(variable_rename,[status(thm)],[t113_xboole_1])).

fof(c_0_9,plain,(
    ! [X11,X12] : k2_xboole_0(X11,X12) = k5_xboole_0(k5_xboole_0(X11,X12),k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_10,plain,(
    ! [X21,X22,X23] : k1_enumset1(X21,X22,X23) = k2_xboole_0(k2_tarski(X21,X22),k1_tarski(X23)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_11,plain,(
    ! [X19,X20] : k2_tarski(X19,X20) = k2_xboole_0(k1_tarski(X19),k1_tarski(X20)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_12,plain,(
    ! [X24,X25,X26,X27] : k2_enumset1(X24,X25,X26,X27) = k2_xboole_0(k1_enumset1(X24,X25,X26),k1_tarski(X27)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_13,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X28,X29,X30,X31,X32] : k3_enumset1(X28,X29,X30,X31,X32) = k2_xboole_0(k2_enumset1(X28,X29,X30,X31),k1_tarski(X32)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(assume_negation,[status(cth)],[t51_enumset1])).

fof(c_0_20,plain,(
    ! [X13,X14,X15,X16,X17,X18] : k4_enumset1(X13,X14,X15,X16,X17,X18) = k2_xboole_0(k1_enumset1(X13,X14,X15),k1_enumset1(X16,X17,X18)) ),
    inference(variable_rename,[status(thm)],[l62_enumset1])).

cnf(c_0_21,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4))),k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14]),c_0_14]),c_0_14]),c_0_14]),c_0_14])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_14]),c_0_14])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_14])).

fof(c_0_25,negated_conjecture,(
    k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k2_xboole_0(k1_tarski(esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_26,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))) = k5_xboole_0(k5_xboole_0(X1,k1_enumset1(X2,X3,X4)),k3_xboole_0(X1,k1_enumset1(X2,X3,X4))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_14]),c_0_24]),c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k2_xboole_0(k1_tarski(esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_14])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),X4))),k3_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),X4)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),X4),k3_xboole_0(k1_enumset1(X1,X2,X3),X4)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5))) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_enumset1(esk4_0,esk5_0,esk6_0)),k3_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_enumset1(esk4_0,esk5_0,esk6_0))) != k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k3_xboole_0(k1_tarski(esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_14]),c_0_30])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)),k3_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:25:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.46/0.65  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.46/0.65  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.46/0.65  #
% 0.46/0.65  # Preprocessing time       : 0.032 s
% 0.46/0.65  # Presaturation interreduction done
% 0.46/0.65  
% 0.46/0.65  # Proof found!
% 0.46/0.65  # SZS status Theorem
% 0.46/0.65  # SZS output start CNFRefutation
% 0.46/0.65  fof(t113_xboole_1, axiom, ![X1, X2, X3, X4]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_xboole_1)).
% 0.46/0.65  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.46/0.65  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 0.46/0.65  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.46/0.65  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.46/0.65  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 0.46/0.65  fof(t51_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 0.46/0.65  fof(l62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 0.46/0.65  fof(c_0_8, plain, ![X7, X8, X9, X10]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X7,X8),X9),X10)=k2_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X9),X10)), inference(variable_rename,[status(thm)],[t113_xboole_1])).
% 0.46/0.65  fof(c_0_9, plain, ![X11, X12]:k2_xboole_0(X11,X12)=k5_xboole_0(k5_xboole_0(X11,X12),k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.46/0.65  fof(c_0_10, plain, ![X21, X22, X23]:k1_enumset1(X21,X22,X23)=k2_xboole_0(k2_tarski(X21,X22),k1_tarski(X23)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.46/0.65  fof(c_0_11, plain, ![X19, X20]:k2_tarski(X19,X20)=k2_xboole_0(k1_tarski(X19),k1_tarski(X20)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.46/0.65  fof(c_0_12, plain, ![X24, X25, X26, X27]:k2_enumset1(X24,X25,X26,X27)=k2_xboole_0(k1_enumset1(X24,X25,X26),k1_tarski(X27)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.46/0.65  cnf(c_0_13, plain, (k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.65  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.46/0.65  cnf(c_0_15, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.46/0.65  cnf(c_0_16, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.46/0.65  fof(c_0_17, plain, ![X28, X29, X30, X31, X32]:k3_enumset1(X28,X29,X30,X31,X32)=k2_xboole_0(k2_enumset1(X28,X29,X30,X31),k1_tarski(X32)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.46/0.65  cnf(c_0_18, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.46/0.65  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(assume_negation,[status(cth)],[t51_enumset1])).
% 0.46/0.65  fof(c_0_20, plain, ![X13, X14, X15, X16, X17, X18]:k4_enumset1(X13,X14,X15,X16,X17,X18)=k2_xboole_0(k1_enumset1(X13,X14,X15),k1_enumset1(X16,X17,X18)), inference(variable_rename,[status(thm)],[l62_enumset1])).
% 0.46/0.65  cnf(c_0_21, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4))=k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4))),k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14]), c_0_14]), c_0_14]), c_0_14]), c_0_14])).
% 0.46/0.65  cnf(c_0_22, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_14]), c_0_14])).
% 0.46/0.65  cnf(c_0_23, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.46/0.65  cnf(c_0_24, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)))), inference(rw,[status(thm)],[c_0_18, c_0_14])).
% 0.46/0.65  fof(c_0_25, negated_conjecture, k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k2_xboole_0(k1_tarski(esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.46/0.65  cnf(c_0_26, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.46/0.65  cnf(c_0_27, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)))=k5_xboole_0(k5_xboole_0(X1,k1_enumset1(X2,X3,X4)),k3_xboole_0(X1,k1_enumset1(X2,X3,X4)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.46/0.65  cnf(c_0_28, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_14]), c_0_24]), c_0_24])).
% 0.46/0.65  cnf(c_0_29, negated_conjecture, (k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k2_xboole_0(k1_tarski(esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.46/0.65  cnf(c_0_30, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)))), inference(rw,[status(thm)],[c_0_26, c_0_14])).
% 0.46/0.65  cnf(c_0_31, plain, (k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),X4))),k3_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X3)),k3_xboole_0(k1_tarski(X2),k1_tarski(X3))),X4))))=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),X4),k3_xboole_0(k1_enumset1(X1,X2,X3),X4))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.46/0.65  cnf(c_0_32, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5)))=k3_enumset1(X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_22]), c_0_28])).
% 0.46/0.65  cnf(c_0_33, negated_conjecture, (k5_xboole_0(k5_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_enumset1(esk4_0,esk5_0,esk6_0)),k3_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k1_enumset1(esk4_0,esk5_0,esk6_0)))!=k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)),k3_xboole_0(k1_tarski(esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_14]), c_0_30])).
% 0.46/0.65  cnf(c_0_34, plain, (k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)))=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)),k3_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.46/0.65  cnf(c_0_35, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])]), ['proof']).
% 0.46/0.65  # SZS output end CNFRefutation
% 0.46/0.65  # Proof object total steps             : 36
% 0.46/0.65  # Proof object clause steps            : 19
% 0.46/0.65  # Proof object formula steps           : 17
% 0.46/0.65  # Proof object conjectures             : 6
% 0.46/0.65  # Proof object clause conjectures      : 3
% 0.46/0.65  # Proof object formula conjectures     : 3
% 0.46/0.65  # Proof object initial clauses used    : 8
% 0.46/0.65  # Proof object initial formulas used   : 8
% 0.46/0.65  # Proof object generating inferences   : 4
% 0.46/0.65  # Proof object simplifying inferences  : 19
% 0.46/0.65  # Training examples: 0 positive, 0 negative
% 0.46/0.65  # Parsed axioms                        : 8
% 0.46/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.65  # Initial clauses                      : 8
% 0.46/0.65  # Removed in clause preprocessing      : 4
% 0.46/0.65  # Initial clauses in saturation        : 4
% 0.46/0.65  # Processed clauses                    : 23
% 0.46/0.65  # ...of these trivial                  : 6
% 0.46/0.65  # ...subsumed                          : 0
% 0.46/0.65  # ...remaining for further processing  : 17
% 0.46/0.65  # Other redundant clauses eliminated   : 0
% 0.46/0.65  # Clauses deleted for lack of memory   : 0
% 0.46/0.65  # Backward-subsumed                    : 0
% 0.46/0.65  # Backward-rewritten                   : 4
% 0.46/0.65  # Generated clauses                    : 1083
% 0.46/0.65  # ...of the previous two non-trivial   : 1069
% 0.46/0.65  # Contextual simplify-reflections      : 0
% 0.46/0.65  # Paramodulations                      : 1083
% 0.46/0.65  # Factorizations                       : 0
% 0.46/0.65  # Equation resolutions                 : 0
% 0.46/0.65  # Propositional unsat checks           : 0
% 0.46/0.65  #    Propositional check models        : 0
% 0.46/0.65  #    Propositional check unsatisfiable : 0
% 0.46/0.65  #    Propositional clauses             : 0
% 0.46/0.65  #    Propositional clauses after purity: 0
% 0.46/0.65  #    Propositional unsat core size     : 0
% 0.46/0.65  #    Propositional preprocessing time  : 0.000
% 0.46/0.65  #    Propositional encoding time       : 0.000
% 0.46/0.65  #    Propositional solver time         : 0.000
% 0.46/0.65  #    Success case prop preproc time    : 0.000
% 0.46/0.65  #    Success case prop encoding time   : 0.000
% 0.46/0.65  #    Success case prop solver time     : 0.000
% 0.46/0.65  # Current number of processed clauses  : 9
% 0.46/0.65  #    Positive orientable unit clauses  : 7
% 0.46/0.65  #    Positive unorientable unit clauses: 2
% 0.46/0.65  #    Negative unit clauses             : 0
% 0.46/0.65  #    Non-unit-clauses                  : 0
% 0.46/0.65  # Current number of unprocessed clauses: 1047
% 0.46/0.65  # ...number of literals in the above   : 1047
% 0.46/0.65  # Current number of archived formulas  : 0
% 0.46/0.65  # Current number of archived clauses   : 12
% 0.46/0.65  # Clause-clause subsumption calls (NU) : 0
% 0.46/0.65  # Rec. Clause-clause subsumption calls : 0
% 0.46/0.65  # Non-unit clause-clause subsumptions  : 0
% 0.46/0.65  # Unit Clause-clause subsumption calls : 0
% 0.46/0.65  # Rewrite failures with RHS unbound    : 0
% 0.46/0.65  # BW rewrite match attempts            : 26
% 0.46/0.65  # BW rewrite match successes           : 4
% 0.46/0.65  # Condensation attempts                : 0
% 0.46/0.65  # Condensation successes               : 0
% 0.46/0.65  # Termbank termtop insertions          : 847621
% 0.46/0.65  
% 0.46/0.65  # -------------------------------------------------
% 0.46/0.65  # User time                : 0.289 s
% 0.46/0.65  # System time              : 0.004 s
% 0.46/0.65  # Total time               : 0.293 s
% 0.46/0.65  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
