%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:02 EST 2020

% Result     : Theorem 1.18s
% Output     : CNFRefutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 183 expanded)
%              Number of clauses        :   26 (  78 expanded)
%              Number of leaves         :   10 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 ( 183 expanded)
%              Number of equality atoms :   46 ( 182 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t43_enumset1,conjecture,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(c_0_10,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X20) = k5_xboole_0(X19,k4_xboole_0(X20,X19)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_11,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,plain,(
    ! [X21,X22] : k2_tarski(X21,X22) = k2_xboole_0(k1_tarski(X21),k1_tarski(X22)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(assume_negation,[status(cth)],[t43_enumset1])).

fof(c_0_16,plain,(
    ! [X23,X24,X25] : k1_enumset1(X23,X24,X25) = k2_xboole_0(k1_tarski(X23),k2_tarski(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,plain,(
    ! [X16,X17,X18] : k5_xboole_0(k5_xboole_0(X16,X17),X18) = k5_xboole_0(X16,k5_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_20,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

fof(c_0_21,plain,(
    ! [X10,X11,X12] : k5_xboole_0(k3_xboole_0(X10,X11),k3_xboole_0(X12,X11)) = k3_xboole_0(k5_xboole_0(X10,X12),X11) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

fof(c_0_22,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_23,plain,(
    ! [X13,X14,X15] : k3_xboole_0(k3_xboole_0(X13,X14),X15) = k3_xboole_0(X13,k3_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

fof(c_0_24,negated_conjecture,(
    k1_enumset1(esk1_0,esk2_0,esk3_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k1_enumset1(esk1_0,esk2_0,esk3_0) != k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_18]),c_0_26]),c_0_26])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_27])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1)) = k3_xboole_0(k5_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k3_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_30]),c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k1_enumset1(esk1_0,esk2_0,esk3_0) != k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)))),k5_xboole_0(k1_tarski(esk3_0),k3_xboole_0(k1_tarski(esk3_0),k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_18]),c_0_26]),c_0_26])).

cnf(c_0_39,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_27]),c_0_27])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X4,X2))) = k5_xboole_0(X3,k3_xboole_0(k5_xboole_0(X1,X4),X2)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_29])).

cnf(c_0_41,plain,
    ( k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X3,X4)) = k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),X4),X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_31])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X4,X2)) = k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X3),X4),X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k5_xboole_0(k1_tarski(esk3_0),k5_xboole_0(k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),k3_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k5_xboole_0(k1_tarski(esk3_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))))))))) != k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k5_xboole_0(k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k5_xboole_0(k1_tarski(esk3_0),k3_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)))),k1_tarski(esk3_0)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_30]),c_0_30]),c_0_30]),c_0_39]),c_0_30]),c_0_30]),c_0_30]),c_0_27]),c_0_27])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X4,X2))) = k5_xboole_0(X3,k3_xboole_0(X2,k5_xboole_0(X1,X4))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_45,plain,
    ( k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X3) = k3_xboole_0(k5_xboole_0(X3,k3_xboole_0(X2,X3)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_28]),c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_30]),c_0_45]),c_0_30]),c_0_29]),c_0_34]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:13:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.18/1.38  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 1.18/1.38  # and selection function SelectNewComplexAHP.
% 1.18/1.38  #
% 1.18/1.38  # Preprocessing time       : 0.040 s
% 1.18/1.38  # Presaturation interreduction done
% 1.18/1.38  
% 1.18/1.38  # Proof found!
% 1.18/1.38  # SZS status Theorem
% 1.18/1.38  # SZS output start CNFRefutation
% 1.18/1.38  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.18/1.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.18/1.38  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.18/1.38  fof(t43_enumset1, conjecture, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 1.18/1.38  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 1.18/1.38  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 1.18/1.38  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 1.18/1.38  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 1.18/1.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.18/1.38  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 1.18/1.38  fof(c_0_10, plain, ![X19, X20]:k2_xboole_0(X19,X20)=k5_xboole_0(X19,k4_xboole_0(X20,X19)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 1.18/1.38  fof(c_0_11, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.18/1.38  fof(c_0_12, plain, ![X21, X22]:k2_tarski(X21,X22)=k2_xboole_0(k1_tarski(X21),k1_tarski(X22)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 1.18/1.38  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.18/1.38  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.18/1.38  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(assume_negation,[status(cth)],[t43_enumset1])).
% 1.18/1.38  fof(c_0_16, plain, ![X23, X24, X25]:k1_enumset1(X23,X24,X25)=k2_xboole_0(k1_tarski(X23),k2_tarski(X24,X25)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 1.18/1.38  cnf(c_0_17, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.18/1.38  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 1.18/1.38  fof(c_0_19, plain, ![X16, X17, X18]:k5_xboole_0(k5_xboole_0(X16,X17),X18)=k5_xboole_0(X16,k5_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 1.18/1.38  fof(c_0_20, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k5_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 1.18/1.38  fof(c_0_21, plain, ![X10, X11, X12]:k5_xboole_0(k3_xboole_0(X10,X11),k3_xboole_0(X12,X11))=k3_xboole_0(k5_xboole_0(X10,X12),X11), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 1.18/1.38  fof(c_0_22, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.18/1.38  fof(c_0_23, plain, ![X13, X14, X15]:k3_xboole_0(k3_xboole_0(X13,X14),X15)=k3_xboole_0(X13,k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 1.18/1.38  fof(c_0_24, negated_conjecture, k1_enumset1(esk1_0,esk2_0,esk3_0)!=k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 1.18/1.38  cnf(c_0_25, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.18/1.38  cnf(c_0_26, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 1.18/1.38  cnf(c_0_27, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.18/1.38  cnf(c_0_28, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.18/1.38  cnf(c_0_29, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.18/1.38  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.18/1.38  cnf(c_0_31, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.18/1.38  cnf(c_0_32, negated_conjecture, (k1_enumset1(esk1_0,esk2_0,esk3_0)!=k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.18/1.38  cnf(c_0_33, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_18]), c_0_26]), c_0_26])).
% 1.18/1.38  cnf(c_0_34, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X3))=k5_xboole_0(X2,k5_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_27])).
% 1.18/1.38  cnf(c_0_35, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.18/1.38  cnf(c_0_36, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))=k3_xboole_0(k5_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.18/1.38  cnf(c_0_37, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(X2,k3_xboole_0(X1,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_30]), c_0_31])).
% 1.18/1.38  cnf(c_0_38, negated_conjecture, (k1_enumset1(esk1_0,esk2_0,esk3_0)!=k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)))),k5_xboole_0(k1_tarski(esk3_0),k3_xboole_0(k1_tarski(esk3_0),k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk1_0)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_18]), c_0_26]), c_0_26])).
% 1.18/1.38  cnf(c_0_39, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k5_xboole_0(k3_xboole_0(k1_tarski(X3),k1_tarski(X2)),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X3),k3_xboole_0(k1_tarski(X3),k1_tarski(X2)))),k1_tarski(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_27]), c_0_27])).
% 1.18/1.38  cnf(c_0_40, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X4,X2)))=k5_xboole_0(X3,k3_xboole_0(k5_xboole_0(X1,X4),X2))), inference(spm,[status(thm)],[c_0_34, c_0_29])).
% 1.18/1.38  cnf(c_0_41, plain, (k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X3,X4))=k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X2),X4),X3)), inference(spm,[status(thm)],[c_0_35, c_0_31])).
% 1.18/1.38  cnf(c_0_42, plain, (k5_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,X3)),k3_xboole_0(X4,X2))=k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X3),X4),X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.18/1.38  cnf(c_0_43, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k5_xboole_0(k1_tarski(esk3_0),k5_xboole_0(k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)),k3_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k5_xboole_0(k1_tarski(esk3_0),k3_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)))))))))!=k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k5_xboole_0(k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),k5_xboole_0(k1_tarski(esk3_0),k3_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k1_tarski(esk2_0),k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)))),k1_tarski(esk3_0))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_30]), c_0_30]), c_0_30]), c_0_39]), c_0_30]), c_0_30]), c_0_30]), c_0_27]), c_0_27])).
% 1.18/1.38  cnf(c_0_44, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X3,k3_xboole_0(X4,X2)))=k5_xboole_0(X3,k3_xboole_0(X2,k5_xboole_0(X1,X4)))), inference(spm,[status(thm)],[c_0_40, c_0_30])).
% 1.18/1.38  cnf(c_0_45, plain, (k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X3)=k3_xboole_0(k5_xboole_0(X3,k3_xboole_0(X2,X3)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_28]), c_0_28])).
% 1.18/1.38  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_30]), c_0_45]), c_0_30]), c_0_29]), c_0_34]), c_0_34])]), ['proof']).
% 1.18/1.38  # SZS output end CNFRefutation
% 1.18/1.38  # Proof object total steps             : 47
% 1.18/1.38  # Proof object clause steps            : 26
% 1.18/1.38  # Proof object formula steps           : 21
% 1.18/1.38  # Proof object conjectures             : 7
% 1.18/1.38  # Proof object clause conjectures      : 4
% 1.18/1.38  # Proof object formula conjectures     : 3
% 1.18/1.38  # Proof object initial clauses used    : 10
% 1.18/1.38  # Proof object initial formulas used   : 10
% 1.18/1.38  # Proof object generating inferences   : 9
% 1.18/1.38  # Proof object simplifying inferences  : 31
% 1.18/1.38  # Training examples: 0 positive, 0 negative
% 1.18/1.38  # Parsed axioms                        : 10
% 1.18/1.38  # Removed by relevancy pruning/SinE    : 0
% 1.18/1.38  # Initial clauses                      : 10
% 1.18/1.38  # Removed in clause preprocessing      : 3
% 1.18/1.38  # Initial clauses in saturation        : 7
% 1.18/1.38  # Processed clauses                    : 2852
% 1.18/1.38  # ...of these trivial                  : 1374
% 1.18/1.38  # ...subsumed                          : 1251
% 1.18/1.38  # ...remaining for further processing  : 227
% 1.18/1.38  # Other redundant clauses eliminated   : 0
% 1.18/1.38  # Clauses deleted for lack of memory   : 0
% 1.18/1.38  # Backward-subsumed                    : 4
% 1.18/1.38  # Backward-rewritten                   : 25
% 1.18/1.38  # Generated clauses                    : 131242
% 1.18/1.38  # ...of the previous two non-trivial   : 128070
% 1.18/1.38  # Contextual simplify-reflections      : 0
% 1.18/1.38  # Paramodulations                      : 131242
% 1.18/1.38  # Factorizations                       : 0
% 1.18/1.38  # Equation resolutions                 : 0
% 1.18/1.38  # Propositional unsat checks           : 0
% 1.18/1.38  #    Propositional check models        : 0
% 1.18/1.38  #    Propositional check unsatisfiable : 0
% 1.18/1.38  #    Propositional clauses             : 0
% 1.18/1.38  #    Propositional clauses after purity: 0
% 1.18/1.38  #    Propositional unsat core size     : 0
% 1.18/1.38  #    Propositional preprocessing time  : 0.000
% 1.18/1.38  #    Propositional encoding time       : 0.000
% 1.18/1.38  #    Propositional solver time         : 0.000
% 1.18/1.38  #    Success case prop preproc time    : 0.000
% 1.18/1.38  #    Success case prop encoding time   : 0.000
% 1.18/1.38  #    Success case prop solver time     : 0.000
% 1.18/1.38  # Current number of processed clauses  : 191
% 1.18/1.38  #    Positive orientable unit clauses  : 59
% 1.18/1.38  #    Positive unorientable unit clauses: 132
% 1.18/1.38  #    Negative unit clauses             : 0
% 1.18/1.38  #    Non-unit-clauses                  : 0
% 1.18/1.38  # Current number of unprocessed clauses: 125212
% 1.18/1.38  # ...number of literals in the above   : 125212
% 1.18/1.38  # Current number of archived formulas  : 0
% 1.18/1.38  # Current number of archived clauses   : 39
% 1.18/1.38  # Clause-clause subsumption calls (NU) : 0
% 1.18/1.38  # Rec. Clause-clause subsumption calls : 0
% 1.18/1.38  # Non-unit clause-clause subsumptions  : 0
% 1.18/1.38  # Unit Clause-clause subsumption calls : 3549
% 1.18/1.38  # Rewrite failures with RHS unbound    : 0
% 1.18/1.38  # BW rewrite match attempts            : 3313
% 1.18/1.38  # BW rewrite match successes           : 897
% 1.18/1.38  # Condensation attempts                : 0
% 1.18/1.38  # Condensation successes               : 0
% 1.18/1.38  # Termbank termtop insertions          : 2382860
% 1.18/1.39  
% 1.18/1.39  # -------------------------------------------------
% 1.18/1.39  # User time                : 0.971 s
% 1.18/1.39  # System time              : 0.070 s
% 1.18/1.39  # Total time               : 1.042 s
% 1.18/1.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
