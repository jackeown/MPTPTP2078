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
% DateTime   : Thu Dec  3 10:35:27 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 347 expanded)
%              Number of clauses        :   25 ( 146 expanded)
%              Number of leaves         :   10 ( 100 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 ( 347 expanded)
%              Number of equality atoms :   45 ( 346 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t67_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(c_0_10,plain,(
    ! [X25,X26] : k2_tarski(X25,X26) = k2_xboole_0(k1_tarski(X25),k1_tarski(X26)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_11,plain,(
    ! [X15,X16] : k2_xboole_0(X15,X16) = k5_xboole_0(X15,k4_xboole_0(X16,X15)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_12,plain,(
    ! [X34,X35,X36,X37,X38] : k3_enumset1(X34,X35,X36,X37,X38) = k2_xboole_0(k1_tarski(X34),k2_enumset1(X35,X36,X37,X38)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_13,plain,(
    ! [X27,X28,X29] : k1_enumset1(X27,X28,X29) = k2_xboole_0(k1_tarski(X27),k2_tarski(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(assume_negation,[status(cth)],[t67_enumset1])).

fof(c_0_17,plain,(
    ! [X39,X40,X41,X42,X43,X44] : k4_enumset1(X39,X40,X41,X42,X43,X44) = k2_xboole_0(k1_tarski(X39),k3_enumset1(X40,X41,X42,X43,X44)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_18,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] : k6_enumset1(X17,X18,X19,X20,X21,X22,X23,X24) = k2_xboole_0(k2_enumset1(X17,X18,X19,X20),k2_enumset1(X21,X22,X23,X24)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

fof(c_0_20,plain,(
    ! [X9,X10,X11] : k2_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_21,plain,(
    ! [X30,X31,X32,X33] : k2_enumset1(X30,X31,X32,X33) = k2_xboole_0(k1_tarski(X30),k1_enumset1(X31,X32,X33)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_24,negated_conjecture,(
    k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_25,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_27,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X12,X13,X14] : k5_xboole_0(k5_xboole_0(X12,X13),X14) = k5_xboole_0(X12,k5_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_15]),c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_15]),c_0_26])).

cnf(c_0_34,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_15])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_15]),c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_15]),c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0))) != k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0))),k4_xboole_0(k5_xboole_0(k1_tarski(esk7_0),k4_xboole_0(k1_tarski(esk8_0),k1_tarski(esk7_0))),k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_15]),c_0_23]),c_0_33]),c_0_33]),c_0_34])).

cnf(c_0_39,plain,
    ( k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k1_tarski(X1),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)),X5)) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),X5) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0)),k4_xboole_0(k5_xboole_0(k1_tarski(esk7_0),k4_xboole_0(k1_tarski(esk8_0),k1_tarski(esk7_0))),k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0)))))) != k5_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_36])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(X5,k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_37]),c_0_36]),c_0_39]),c_0_36]),c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k5_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk7_0),k4_xboole_0(k1_tarski(esk8_0),k1_tarski(esk7_0))),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0))),k1_tarski(esk2_0))),k1_tarski(esk1_0))) != k5_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_39]),c_0_36]),c_0_39])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:49:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.026 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.20/0.37  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.37  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.20/0.37  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.20/0.37  fof(t67_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 0.20/0.37  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.20/0.37  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 0.20/0.37  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.20/0.37  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.20/0.37  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.20/0.37  fof(c_0_10, plain, ![X25, X26]:k2_tarski(X25,X26)=k2_xboole_0(k1_tarski(X25),k1_tarski(X26)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.20/0.37  fof(c_0_11, plain, ![X15, X16]:k2_xboole_0(X15,X16)=k5_xboole_0(X15,k4_xboole_0(X16,X15)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.37  fof(c_0_12, plain, ![X34, X35, X36, X37, X38]:k3_enumset1(X34,X35,X36,X37,X38)=k2_xboole_0(k1_tarski(X34),k2_enumset1(X35,X36,X37,X38)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.20/0.37  fof(c_0_13, plain, ![X27, X28, X29]:k1_enumset1(X27,X28,X29)=k2_xboole_0(k1_tarski(X27),k2_tarski(X28,X29)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.20/0.37  cnf(c_0_14, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))), inference(assume_negation,[status(cth)],[t67_enumset1])).
% 0.20/0.37  fof(c_0_17, plain, ![X39, X40, X41, X42, X43, X44]:k4_enumset1(X39,X40,X41,X42,X43,X44)=k2_xboole_0(k1_tarski(X39),k3_enumset1(X40,X41,X42,X43,X44)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.20/0.37  cnf(c_0_18, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  fof(c_0_19, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:k6_enumset1(X17,X18,X19,X20,X21,X22,X23,X24)=k2_xboole_0(k2_enumset1(X17,X18,X19,X20),k2_enumset1(X21,X22,X23,X24)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.20/0.37  fof(c_0_20, plain, ![X9, X10, X11]:k2_xboole_0(k2_xboole_0(X9,X10),X11)=k2_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.20/0.37  fof(c_0_21, plain, ![X30, X31, X32, X33]:k2_enumset1(X30,X31,X32,X33)=k2_xboole_0(k1_tarski(X30),k1_enumset1(X31,X32,X33)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.20/0.37  cnf(c_0_22, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.37  cnf(c_0_23, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.37  fof(c_0_24, negated_conjecture, k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.37  cnf(c_0_25, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.37  cnf(c_0_26, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_18, c_0_15])).
% 0.20/0.37  cnf(c_0_27, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_28, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  fof(c_0_29, plain, ![X12, X13, X14]:k5_xboole_0(k5_xboole_0(X12,X13),X14)=k5_xboole_0(X12,k5_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.20/0.37  cnf(c_0_30, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.37  cnf(c_0_31, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_15]), c_0_23])).
% 0.20/0.37  cnf(c_0_32, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k2_tarski(esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.37  cnf(c_0_33, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_15]), c_0_26])).
% 0.20/0.37  cnf(c_0_34, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[c_0_27, c_0_15])).
% 0.20/0.37  cnf(c_0_35, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_15]), c_0_15]), c_0_15]), c_0_15])).
% 0.20/0.37  cnf(c_0_36, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.37  cnf(c_0_37, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_15]), c_0_31])).
% 0.20/0.37  cnf(c_0_38, negated_conjecture, (k5_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)))!=k5_xboole_0(k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0))),k4_xboole_0(k5_xboole_0(k1_tarski(esk7_0),k4_xboole_0(k1_tarski(esk8_0),k1_tarski(esk7_0))),k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_15]), c_0_23]), c_0_33]), c_0_33]), c_0_34])).
% 0.20/0.37  cnf(c_0_39, plain, (k5_xboole_0(X1,k5_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.37  cnf(c_0_40, plain, (k5_xboole_0(k1_tarski(X1),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)),X5))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),X5)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.37  cnf(c_0_41, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k5_xboole_0(k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0)),k4_xboole_0(k5_xboole_0(k1_tarski(esk7_0),k4_xboole_0(k1_tarski(esk8_0),k1_tarski(esk7_0))),k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k1_tarski(esk2_0))),k1_tarski(esk1_0))))))!=k5_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_38, c_0_36])).
% 0.20/0.37  cnf(c_0_42, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(X5,k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_37]), c_0_36]), c_0_39]), c_0_36]), c_0_39])).
% 0.20/0.37  cnf(c_0_43, negated_conjecture, (k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k5_xboole_0(k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk7_0),k4_xboole_0(k1_tarski(esk8_0),k1_tarski(esk7_0))),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0))),k1_tarski(esk2_0))),k1_tarski(esk1_0)))!=k5_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_39]), c_0_36]), c_0_39])).
% 0.20/0.37  cnf(c_0_44, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1)))), inference(spm,[status(thm)],[c_0_42, c_0_37])).
% 0.20/0.37  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_42])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 46
% 0.20/0.37  # Proof object clause steps            : 25
% 0.20/0.37  # Proof object formula steps           : 21
% 0.20/0.37  # Proof object conjectures             : 8
% 0.20/0.37  # Proof object clause conjectures      : 5
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 10
% 0.20/0.37  # Proof object initial formulas used   : 10
% 0.20/0.37  # Proof object generating inferences   : 3
% 0.20/0.37  # Proof object simplifying inferences  : 31
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 10
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 10
% 0.20/0.37  # Removed in clause preprocessing      : 6
% 0.20/0.37  # Initial clauses in saturation        : 4
% 0.20/0.37  # Processed clauses                    : 18
% 0.20/0.37  # ...of these trivial                  : 2
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 16
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 2
% 0.20/0.37  # Generated clauses                    : 67
% 0.20/0.37  # ...of the previous two non-trivial   : 48
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 67
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
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
% 0.20/0.37  # Current number of processed clauses  : 10
% 0.20/0.37  #    Positive orientable unit clauses  : 10
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 0
% 0.20/0.37  #    Non-unit-clauses                  : 0
% 0.20/0.37  # Current number of unprocessed clauses: 38
% 0.20/0.37  # ...number of literals in the above   : 38
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 12
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 8
% 0.20/0.37  # BW rewrite match successes           : 2
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 3978
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.026 s
% 0.20/0.37  # System time              : 0.007 s
% 0.20/0.37  # Total time               : 0.033 s
% 0.20/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
