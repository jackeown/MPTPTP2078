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
% DateTime   : Thu Dec  3 10:35:12 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 190 expanded)
%              Number of clauses        :   23 (  79 expanded)
%              Number of leaves         :   10 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 ( 190 expanded)
%              Number of equality atoms :   43 ( 189 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t54_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(t56_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

fof(l68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(c_0_10,plain,(
    ! [X25,X26,X27,X28,X29] : k3_enumset1(X25,X26,X27,X28,X29) = k2_xboole_0(k1_tarski(X25),k2_enumset1(X26,X27,X28,X29)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_11,plain,(
    ! [X11,X12] : k2_xboole_0(X11,X12) = k5_xboole_0(X11,k4_xboole_0(X12,X11)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_12,plain,(
    ! [X20,X21] : k2_tarski(X20,X21) = k2_xboole_0(k1_tarski(X20),k1_tarski(X21)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_13,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k4_enumset1(X30,X31,X32,X33,X34,X35) = k2_xboole_0(k1_tarski(X30),k3_enumset1(X31,X32,X33,X34,X35)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_14,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X22,X23,X24] : k1_enumset1(X22,X23,X24) = k2_xboole_0(k1_tarski(X22),k2_tarski(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X8,X9,X10] : k2_xboole_0(k2_xboole_0(X8,X9),X10) = k2_xboole_0(X8,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_19,plain,(
    ! [X36,X37,X38,X39,X40,X41] : k4_enumset1(X36,X37,X38,X39,X40,X41) = k2_xboole_0(k2_enumset1(X36,X37,X38,X39),k2_tarski(X40,X41)) ),
    inference(variable_rename,[status(thm)],[t54_enumset1])).

cnf(c_0_20,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_22,plain,(
    ! [X42,X43,X44,X45,X46,X47] : k4_enumset1(X42,X43,X44,X45,X46,X47) = k2_xboole_0(k3_enumset1(X42,X43,X44,X45,X46),k1_tarski(X47)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(assume_negation,[status(cth)],[t56_enumset1])).

fof(c_0_24,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19] : k5_enumset1(X13,X14,X15,X16,X17,X18,X19) = k2_xboole_0(k2_enumset1(X13,X14,X15,X16),k1_enumset1(X17,X18,X19)) ),
    inference(variable_rename,[status(thm)],[l68_enumset1])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_15]),c_0_21])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,negated_conjecture,(
    k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k1_tarski(esk1_0),k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_15]),c_0_26])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_15]),c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_35,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1))) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_15]),c_0_26]),c_0_29])).

cnf(c_0_36,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1))) = k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k4_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_15]),c_0_21]),c_0_21]),c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k2_xboole_0(k1_tarski(esk1_0),k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X7),k1_tarski(X6))),k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_15]),c_0_33])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(X7,k1_tarski(X6))),k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k2_enumset1(X3,X4,X5,X6),k4_xboole_0(X7,k2_enumset1(X3,X4,X5,X6))),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_34]),c_0_34]),c_0_34])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k2_enumset1(X2,X3,X4,X5),k4_xboole_0(k1_tarski(X6),k2_enumset1(X2,X3,X4,X5))),k1_tarski(X1))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0) != k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k4_xboole_0(k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk3_0))),k1_tarski(esk2_0))),k1_tarski(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_15]),c_0_29])).

cnf(c_0_42,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:15:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.12/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.12/0.37  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.12/0.37  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.12/0.37  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.12/0.37  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.12/0.37  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.12/0.37  fof(t54_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 0.12/0.37  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 0.12/0.37  fof(t56_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 0.12/0.37  fof(l68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 0.12/0.37  fof(c_0_10, plain, ![X25, X26, X27, X28, X29]:k3_enumset1(X25,X26,X27,X28,X29)=k2_xboole_0(k1_tarski(X25),k2_enumset1(X26,X27,X28,X29)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.12/0.37  fof(c_0_11, plain, ![X11, X12]:k2_xboole_0(X11,X12)=k5_xboole_0(X11,k4_xboole_0(X12,X11)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.12/0.37  fof(c_0_12, plain, ![X20, X21]:k2_tarski(X20,X21)=k2_xboole_0(k1_tarski(X20),k1_tarski(X21)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.12/0.37  fof(c_0_13, plain, ![X30, X31, X32, X33, X34, X35]:k4_enumset1(X30,X31,X32,X33,X34,X35)=k2_xboole_0(k1_tarski(X30),k3_enumset1(X31,X32,X33,X34,X35)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.12/0.37  cnf(c_0_14, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  fof(c_0_16, plain, ![X22, X23, X24]:k1_enumset1(X22,X23,X24)=k2_xboole_0(k1_tarski(X22),k2_tarski(X23,X24)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.12/0.37  cnf(c_0_17, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  fof(c_0_18, plain, ![X8, X9, X10]:k2_xboole_0(k2_xboole_0(X8,X9),X10)=k2_xboole_0(X8,k2_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.12/0.37  fof(c_0_19, plain, ![X36, X37, X38, X39, X40, X41]:k4_enumset1(X36,X37,X38,X39,X40,X41)=k2_xboole_0(k2_enumset1(X36,X37,X38,X39),k2_tarski(X40,X41)), inference(variable_rename,[status(thm)],[t54_enumset1])).
% 0.12/0.37  cnf(c_0_20, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_21, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.37  fof(c_0_22, plain, ![X42, X43, X44, X45, X46, X47]:k4_enumset1(X42,X43,X44,X45,X46,X47)=k2_xboole_0(k3_enumset1(X42,X43,X44,X45,X46),k1_tarski(X47)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.12/0.37  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_tarski(X1),k4_enumset1(X2,X3,X4,X5,X6,X7))), inference(assume_negation,[status(cth)],[t56_enumset1])).
% 0.12/0.37  fof(c_0_24, plain, ![X13, X14, X15, X16, X17, X18, X19]:k5_enumset1(X13,X14,X15,X16,X17,X18,X19)=k2_xboole_0(k2_enumset1(X13,X14,X15,X16),k1_enumset1(X17,X18,X19)), inference(variable_rename,[status(thm)],[l68_enumset1])).
% 0.12/0.37  cnf(c_0_25, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_26, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_17, c_0_15])).
% 0.12/0.37  cnf(c_0_27, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_28, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X5,X6))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_29, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_15]), c_0_21])).
% 0.12/0.37  cnf(c_0_30, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  fof(c_0_31, negated_conjecture, k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k1_tarski(esk1_0),k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.12/0.37  cnf(c_0_32, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_33, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_15]), c_0_26])).
% 0.12/0.37  cnf(c_0_34, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_15]), c_0_15]), c_0_15]), c_0_15])).
% 0.12/0.37  cnf(c_0_35, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1)))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_15]), c_0_26]), c_0_29])).
% 0.12/0.37  cnf(c_0_36, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1)))=k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k4_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_15]), c_0_21]), c_0_21]), c_0_29])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k2_xboole_0(k1_tarski(esk1_0),k4_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.37  cnf(c_0_38, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X7),k1_tarski(X6))),k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_15]), c_0_33])).
% 0.12/0.37  cnf(c_0_39, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(X7,k1_tarski(X6))),k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k2_enumset1(X3,X4,X5,X6),k4_xboole_0(X7,k2_enumset1(X3,X4,X5,X6))),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_34]), c_0_34]), c_0_34])).
% 0.12/0.37  cnf(c_0_40, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k2_enumset1(X2,X3,X4,X5),k4_xboole_0(k1_tarski(X6),k2_enumset1(X2,X3,X4,X5))),k1_tarski(X1)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_36, c_0_34])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (k5_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0)!=k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk2_0),k4_xboole_0(k5_xboole_0(k1_tarski(esk3_0),k4_xboole_0(k2_enumset1(esk4_0,esk5_0,esk6_0,esk7_0),k1_tarski(esk3_0))),k1_tarski(esk2_0))),k1_tarski(esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_15]), c_0_29])).
% 0.12/0.37  cnf(c_0_42, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_enumset1(X4,X5,X6,X7),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 44
% 0.12/0.37  # Proof object clause steps            : 23
% 0.12/0.37  # Proof object formula steps           : 21
% 0.12/0.37  # Proof object conjectures             : 6
% 0.12/0.37  # Proof object clause conjectures      : 3
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 10
% 0.12/0.37  # Proof object initial formulas used   : 10
% 0.12/0.37  # Proof object generating inferences   : 1
% 0.12/0.37  # Proof object simplifying inferences  : 29
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 10
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 10
% 0.12/0.37  # Removed in clause preprocessing      : 5
% 0.12/0.37  # Initial clauses in saturation        : 5
% 0.12/0.37  # Processed clauses                    : 12
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 12
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 2
% 0.12/0.37  # Generated clauses                    : 9
% 0.12/0.37  # ...of the previous two non-trivial   : 5
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 9
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 5
% 0.12/0.37  #    Positive orientable unit clauses  : 5
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 0
% 0.12/0.37  #    Non-unit-clauses                  : 0
% 0.12/0.37  # Current number of unprocessed clauses: 3
% 0.12/0.37  # ...number of literals in the above   : 3
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 12
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 19
% 0.12/0.37  # BW rewrite match successes           : 2
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1521
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.002 s
% 0.12/0.37  # Total time               : 0.031 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
