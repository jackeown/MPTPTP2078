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
% DateTime   : Thu Dec  3 10:35:13 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 345 expanded)
%              Number of clauses        :   21 ( 140 expanded)
%              Number of leaves         :    8 ( 102 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 ( 345 expanded)
%              Number of equality atoms :   37 ( 344 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_xboole_1,axiom,(
    ! [X1,X2,X3,X4] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4) = k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t46_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(l68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(t57_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

fof(c_0_8,plain,(
    ! [X8,X9,X10,X11] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X8,X9),X10),X11) = k2_xboole_0(X8,k2_xboole_0(k2_xboole_0(X9,X10),X11)) ),
    inference(variable_rename,[status(thm)],[t113_xboole_1])).

fof(c_0_9,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k5_xboole_0(k5_xboole_0(X12,X13),k3_xboole_0(X12,X13)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

fof(c_0_10,plain,(
    ! [X23,X24,X25] : k1_enumset1(X23,X24,X25) = k2_xboole_0(k2_tarski(X23,X24),k1_tarski(X25)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_11,plain,(
    ! [X21,X22] : k2_tarski(X21,X22) = k2_xboole_0(k1_tarski(X21),k1_tarski(X22)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_12,plain,(
    ! [X26,X27,X28,X29] : k2_enumset1(X26,X27,X28,X29) = k2_xboole_0(k1_enumset1(X26,X27,X28),k1_tarski(X29)) ),
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
    ! [X30,X31,X32,X33,X34] : k3_enumset1(X30,X31,X32,X33,X34) = k2_xboole_0(k2_enumset1(X30,X31,X32,X33),k1_tarski(X34)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4))),k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14]),c_0_14]),c_0_14]),c_0_14]),c_0_14])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_14]),c_0_14])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_14])).

fof(c_0_23,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20] : k5_enumset1(X14,X15,X16,X17,X18,X19,X20) = k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k1_enumset1(X18,X19,X20)) ),
    inference(variable_rename,[status(thm)],[l68_enumset1])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(assume_negation,[status(cth)],[t57_enumset1])).

cnf(c_0_25,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4))) = k5_xboole_0(k5_xboole_0(X1,k1_enumset1(X2,X3,X4)),k3_xboole_0(X1,k1_enumset1(X2,X3,X4))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_14]),c_0_22]),c_0_22])).

cnf(c_0_27,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,negated_conjecture,(
    k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_29,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5))) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_26])).

cnf(c_0_30,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_enumset1(X5,X6,X7)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_enumset1(X5,X6,X7))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_14]),c_0_22]),c_0_22])).

cnf(c_0_31,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_enumset1(X4,X5,X6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_enumset1(X4,X5,X6))) = k5_xboole_0(k5_xboole_0(X1,k3_enumset1(X2,X3,X4,X5,X6)),k3_xboole_0(X1,k3_enumset1(X2,X3,X4,X5,X6))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_29])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))),k1_enumset1(X5,X6,X7)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))),k1_enumset1(X5,X6,X7))) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))),k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))),k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_16]),c_0_14]),c_0_14])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k3_enumset1(X3,X4,X5,X6,X7)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k3_enumset1(X3,X4,X5,X6,X7))) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_20]),c_0_31]),c_0_31]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:52:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.47/0.69  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.47/0.69  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.47/0.69  #
% 0.47/0.69  # Preprocessing time       : 0.039 s
% 0.47/0.69  # Presaturation interreduction done
% 0.47/0.69  
% 0.47/0.69  # Proof found!
% 0.47/0.69  # SZS status Theorem
% 0.47/0.69  # SZS output start CNFRefutation
% 0.47/0.69  fof(t113_xboole_1, axiom, ![X1, X2, X3, X4]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_xboole_1)).
% 0.47/0.69  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.47/0.69  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 0.47/0.69  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.47/0.69  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 0.47/0.69  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 0.47/0.69  fof(l68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 0.47/0.69  fof(t57_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 0.47/0.69  fof(c_0_8, plain, ![X8, X9, X10, X11]:k2_xboole_0(k2_xboole_0(k2_xboole_0(X8,X9),X10),X11)=k2_xboole_0(X8,k2_xboole_0(k2_xboole_0(X9,X10),X11)), inference(variable_rename,[status(thm)],[t113_xboole_1])).
% 0.47/0.69  fof(c_0_9, plain, ![X12, X13]:k2_xboole_0(X12,X13)=k5_xboole_0(k5_xboole_0(X12,X13),k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.47/0.69  fof(c_0_10, plain, ![X23, X24, X25]:k1_enumset1(X23,X24,X25)=k2_xboole_0(k2_tarski(X23,X24),k1_tarski(X25)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.47/0.69  fof(c_0_11, plain, ![X21, X22]:k2_tarski(X21,X22)=k2_xboole_0(k1_tarski(X21),k1_tarski(X22)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.47/0.69  fof(c_0_12, plain, ![X26, X27, X28, X29]:k2_enumset1(X26,X27,X28,X29)=k2_xboole_0(k1_enumset1(X26,X27,X28),k1_tarski(X29)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.47/0.69  cnf(c_0_13, plain, (k2_xboole_0(k2_xboole_0(k2_xboole_0(X1,X2),X3),X4)=k2_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.47/0.69  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.47/0.69  cnf(c_0_15, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.47/0.69  cnf(c_0_16, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.47/0.69  fof(c_0_17, plain, ![X30, X31, X32, X33, X34]:k3_enumset1(X30,X31,X32,X33,X34)=k2_xboole_0(k2_enumset1(X30,X31,X32,X33),k1_tarski(X34)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.47/0.69  cnf(c_0_18, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.69  cnf(c_0_19, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)),X3)),X4))=k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4))),k3_xboole_0(X1,k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4),k3_xboole_0(k5_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)),X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_14]), c_0_14]), c_0_14]), c_0_14]), c_0_14]), c_0_14])).
% 0.47/0.69  cnf(c_0_20, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_tarski(X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_14]), c_0_14])).
% 0.47/0.69  cnf(c_0_21, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.69  cnf(c_0_22, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)))), inference(rw,[status(thm)],[c_0_18, c_0_14])).
% 0.47/0.69  fof(c_0_23, plain, ![X14, X15, X16, X17, X18, X19, X20]:k5_enumset1(X14,X15,X16,X17,X18,X19,X20)=k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k1_enumset1(X18,X19,X20)), inference(variable_rename,[status(thm)],[l68_enumset1])).
% 0.47/0.69  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))), inference(assume_negation,[status(cth)],[t57_enumset1])).
% 0.47/0.69  cnf(c_0_25, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_tarski(X4)))=k5_xboole_0(k5_xboole_0(X1,k1_enumset1(X2,X3,X4)),k3_xboole_0(X1,k1_enumset1(X2,X3,X4)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.47/0.69  cnf(c_0_26, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_tarski(X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_14]), c_0_22]), c_0_22])).
% 0.47/0.69  cnf(c_0_27, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.47/0.69  fof(c_0_28, negated_conjecture, k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k2_tarski(esk1_0,esk2_0),k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.47/0.69  cnf(c_0_29, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k1_enumset1(X3,X4,X5)))=k3_enumset1(X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_20]), c_0_26])).
% 0.47/0.69  cnf(c_0_30, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_enumset1(X5,X6,X7)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))),k1_enumset1(X5,X6,X7)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_14]), c_0_22]), c_0_22])).
% 0.47/0.69  cnf(c_0_31, plain, (k5_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)))=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)))), inference(spm,[status(thm)],[c_0_25, c_0_20])).
% 0.47/0.69  cnf(c_0_32, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k2_tarski(esk1_0,esk2_0),k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.69  cnf(c_0_33, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_enumset1(X4,X5,X6)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k1_tarski(X2)),k3_xboole_0(X1,k1_tarski(X2))),k1_tarski(X3))),k1_enumset1(X4,X5,X6)))=k5_xboole_0(k5_xboole_0(X1,k3_enumset1(X2,X3,X4,X5,X6)),k3_xboole_0(X1,k3_enumset1(X2,X3,X4,X5,X6)))), inference(spm,[status(thm)],[c_0_19, c_0_29])).
% 0.47/0.69  cnf(c_0_34, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))),k1_enumset1(X5,X6,X7)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)),k3_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))),k1_enumset1(X5,X6,X7)))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_31])).
% 0.47/0.69  cnf(c_0_35, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))),k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))),k3_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_16]), c_0_14]), c_0_14])).
% 0.47/0.69  cnf(c_0_36, plain, (k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k3_enumset1(X3,X4,X5,X6,X7)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X2)),k3_xboole_0(k1_tarski(X1),k1_tarski(X2))),k3_enumset1(X3,X4,X5,X6,X7)))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_20]), c_0_31]), c_0_31]), c_0_34])).
% 0.47/0.69  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])]), ['proof']).
% 0.47/0.69  # SZS output end CNFRefutation
% 0.47/0.69  # Proof object total steps             : 38
% 0.47/0.69  # Proof object clause steps            : 21
% 0.47/0.69  # Proof object formula steps           : 17
% 0.47/0.69  # Proof object conjectures             : 6
% 0.47/0.69  # Proof object clause conjectures      : 3
% 0.47/0.69  # Proof object formula conjectures     : 3
% 0.47/0.69  # Proof object initial clauses used    : 8
% 0.47/0.69  # Proof object initial formulas used   : 8
% 0.47/0.69  # Proof object generating inferences   : 5
% 0.47/0.69  # Proof object simplifying inferences  : 27
% 0.47/0.69  # Training examples: 0 positive, 0 negative
% 0.47/0.69  # Parsed axioms                        : 8
% 0.47/0.69  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.69  # Initial clauses                      : 8
% 0.47/0.69  # Removed in clause preprocessing      : 3
% 0.47/0.69  # Initial clauses in saturation        : 5
% 0.47/0.69  # Processed clauses                    : 35
% 0.47/0.69  # ...of these trivial                  : 10
% 0.47/0.69  # ...subsumed                          : 0
% 0.47/0.69  # ...remaining for further processing  : 25
% 0.47/0.69  # Other redundant clauses eliminated   : 0
% 0.47/0.69  # Clauses deleted for lack of memory   : 0
% 0.47/0.69  # Backward-subsumed                    : 0
% 0.47/0.69  # Backward-rewritten                   : 5
% 0.47/0.69  # Generated clauses                    : 1637
% 0.47/0.69  # ...of the previous two non-trivial   : 1619
% 0.47/0.69  # Contextual simplify-reflections      : 0
% 0.47/0.69  # Paramodulations                      : 1637
% 0.47/0.69  # Factorizations                       : 0
% 0.47/0.69  # Equation resolutions                 : 0
% 0.47/0.69  # Propositional unsat checks           : 0
% 0.47/0.69  #    Propositional check models        : 0
% 0.47/0.69  #    Propositional check unsatisfiable : 0
% 0.47/0.69  #    Propositional clauses             : 0
% 0.47/0.69  #    Propositional clauses after purity: 0
% 0.47/0.69  #    Propositional unsat core size     : 0
% 0.47/0.69  #    Propositional preprocessing time  : 0.000
% 0.47/0.69  #    Propositional encoding time       : 0.000
% 0.47/0.69  #    Propositional solver time         : 0.000
% 0.47/0.69  #    Success case prop preproc time    : 0.000
% 0.47/0.69  #    Success case prop encoding time   : 0.000
% 0.47/0.69  #    Success case prop solver time     : 0.000
% 0.47/0.69  # Current number of processed clauses  : 15
% 0.47/0.69  #    Positive orientable unit clauses  : 13
% 0.47/0.69  #    Positive unorientable unit clauses: 2
% 0.47/0.69  #    Negative unit clauses             : 0
% 0.47/0.69  #    Non-unit-clauses                  : 0
% 0.47/0.69  # Current number of unprocessed clauses: 1587
% 0.47/0.69  # ...number of literals in the above   : 1587
% 0.47/0.69  # Current number of archived formulas  : 0
% 0.47/0.69  # Current number of archived clauses   : 13
% 0.47/0.69  # Clause-clause subsumption calls (NU) : 0
% 0.47/0.69  # Rec. Clause-clause subsumption calls : 0
% 0.47/0.69  # Non-unit clause-clause subsumptions  : 0
% 0.47/0.69  # Unit Clause-clause subsumption calls : 0
% 0.47/0.69  # Rewrite failures with RHS unbound    : 0
% 0.47/0.69  # BW rewrite match attempts            : 42
% 0.47/0.69  # BW rewrite match successes           : 4
% 0.47/0.69  # Condensation attempts                : 0
% 0.47/0.69  # Condensation successes               : 0
% 0.47/0.69  # Termbank termtop insertions          : 1222043
% 0.47/0.69  
% 0.47/0.69  # -------------------------------------------------
% 0.47/0.69  # User time                : 0.336 s
% 0.47/0.69  # System time              : 0.005 s
% 0.47/0.69  # Total time               : 0.341 s
% 0.47/0.69  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
