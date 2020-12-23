%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:20 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 178 expanded)
%              Number of clauses        :   27 (  77 expanded)
%              Number of leaves         :   11 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 ( 178 expanded)
%              Number of equality atoms :   49 ( 177 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(l68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(t62_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(c_0_11,plain,(
    ! [X31,X32] : k2_tarski(X31,X32) = k2_xboole_0(k1_tarski(X31),k1_tarski(X32)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_12,plain,(
    ! [X14,X15] : k2_xboole_0(X14,X15) = k5_xboole_0(X14,k4_xboole_0(X15,X14)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_13,plain,(
    ! [X33,X34,X35] : k1_enumset1(X33,X34,X35) = k2_xboole_0(k1_tarski(X33),k2_tarski(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X40,X41,X42,X43,X44] : k3_enumset1(X40,X41,X42,X43,X44) = k2_xboole_0(k1_tarski(X40),k2_enumset1(X41,X42,X43,X44)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_17,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k2_xboole_0(X12,X13)) = k2_xboole_0(X12,X13) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

fof(c_0_18,plain,(
    ! [X36,X37,X38,X39] : k2_enumset1(X36,X37,X38,X39) = k2_xboole_0(k1_tarski(X36),k1_enumset1(X37,X38,X39)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X2) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_21,plain,(
    ! [X9,X10,X11] : k2_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_22,plain,(
    ! [X45,X46,X47,X48,X49] : k3_enumset1(X45,X46,X47,X48,X49) = k2_xboole_0(k2_enumset1(X45,X46,X47,X48),k1_tarski(X49)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k1_enumset1(X1,X2,X3) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_15]),c_0_20])).

fof(c_0_27,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22] : k5_enumset1(X16,X17,X18,X19,X20,X21,X22) = k2_xboole_0(k2_enumset1(X16,X17,X18,X19),k1_enumset1(X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[l68_enumset1])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(assume_negation,[status(cth)],[t62_enumset1])).

fof(c_0_29,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29,X30] : k6_enumset1(X23,X24,X25,X26,X27,X28,X29,X30) = k2_xboole_0(k2_enumset1(X23,X24,X25,X26),k2_enumset1(X27,X28,X29,X30)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_15])).

cnf(c_0_33,plain,
    ( k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1)) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_15]),c_0_26])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,negated_conjecture,(
    k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k1_tarski(esk1_0),k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_15]),c_0_15]),c_0_15]),c_0_15])).

cnf(c_0_39,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k1_tarski(X5),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_15]),c_0_32])).

cnf(c_0_40,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1))) = k2_enumset1(X1,X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X7),k1_tarski(X6))),k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_15]),c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k1_tarski(esk1_0),k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_15])).

cnf(c_0_44,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(X6,k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k2_enumset1(X2,X3,X4,X5),k4_xboole_0(X6,k2_enumset1(X2,X3,X4,X5))),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_38])).

cnf(c_0_45,plain,
    ( k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k1_tarski(X1))) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_34,c_0_40])).

cnf(c_0_46,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_enumset1(X1,X2,X3,X4))) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[c_0_41,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0))) != k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_15]),c_0_43])).

cnf(c_0_48,plain,
    ( k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4))) = k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:58:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.42  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.026 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.19/0.42  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.19/0.42  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.19/0.42  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.19/0.42  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 0.19/0.42  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.19/0.42  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.19/0.42  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 0.19/0.42  fof(l68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 0.19/0.42  fof(t62_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 0.19/0.42  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 0.19/0.42  fof(c_0_11, plain, ![X31, X32]:k2_tarski(X31,X32)=k2_xboole_0(k1_tarski(X31),k1_tarski(X32)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.19/0.42  fof(c_0_12, plain, ![X14, X15]:k2_xboole_0(X14,X15)=k5_xboole_0(X14,k4_xboole_0(X15,X14)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.19/0.42  fof(c_0_13, plain, ![X33, X34, X35]:k1_enumset1(X33,X34,X35)=k2_xboole_0(k1_tarski(X33),k2_tarski(X34,X35)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.19/0.42  cnf(c_0_14, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.42  cnf(c_0_15, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  fof(c_0_16, plain, ![X40, X41, X42, X43, X44]:k3_enumset1(X40,X41,X42,X43,X44)=k2_xboole_0(k1_tarski(X40),k2_enumset1(X41,X42,X43,X44)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.19/0.42  fof(c_0_17, plain, ![X12, X13]:k2_xboole_0(X12,k2_xboole_0(X12,X13))=k2_xboole_0(X12,X13), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 0.19/0.42  fof(c_0_18, plain, ![X36, X37, X38, X39]:k2_enumset1(X36,X37,X38,X39)=k2_xboole_0(k1_tarski(X36),k1_enumset1(X37,X38,X39)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.19/0.42  cnf(c_0_19, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_20, plain, (k2_tarski(X1,X2)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.42  fof(c_0_21, plain, ![X9, X10, X11]:k2_xboole_0(k2_xboole_0(X9,X10),X11)=k2_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.19/0.42  fof(c_0_22, plain, ![X45, X46, X47, X48, X49]:k3_enumset1(X45,X46,X47,X48,X49)=k2_xboole_0(k2_enumset1(X45,X46,X47,X48),k1_tarski(X49)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.19/0.42  cnf(c_0_23, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_24, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_25, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.42  cnf(c_0_26, plain, (k1_enumset1(X1,X2,X3)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_15]), c_0_20])).
% 0.19/0.42  fof(c_0_27, plain, ![X16, X17, X18, X19, X20, X21, X22]:k5_enumset1(X16,X17,X18,X19,X20,X21,X22)=k2_xboole_0(k2_enumset1(X16,X17,X18,X19),k1_enumset1(X20,X21,X22)), inference(variable_rename,[status(thm)],[l68_enumset1])).
% 0.19/0.42  fof(c_0_28, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(assume_negation,[status(cth)],[t62_enumset1])).
% 0.19/0.42  fof(c_0_29, plain, ![X23, X24, X25, X26, X27, X28, X29, X30]:k6_enumset1(X23,X24,X25,X26,X27,X28,X29,X30)=k2_xboole_0(k2_enumset1(X23,X24,X25,X26),k2_enumset1(X27,X28,X29,X30)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.19/0.42  cnf(c_0_30, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.42  cnf(c_0_31, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.42  cnf(c_0_32, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_23, c_0_15])).
% 0.19/0.42  cnf(c_0_33, plain, (k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X1))=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_15]), c_0_15]), c_0_15])).
% 0.19/0.42  cnf(c_0_34, plain, (k2_enumset1(X1,X2,X3,X4)=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k1_tarski(X2))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_15]), c_0_26])).
% 0.19/0.42  cnf(c_0_35, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.42  fof(c_0_36, negated_conjecture, k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k1_tarski(esk1_0),k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.19/0.42  cnf(c_0_37, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_38, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_15]), c_0_15]), c_0_15]), c_0_15])).
% 0.19/0.42  cnf(c_0_39, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1)))=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k1_tarski(X5),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_15]), c_0_32])).
% 0.19/0.42  cnf(c_0_40, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k1_tarski(X1)))=k2_enumset1(X1,X1,X2,X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.42  cnf(c_0_41, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k5_xboole_0(k1_tarski(X6),k4_xboole_0(k1_tarski(X7),k1_tarski(X6))),k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_15]), c_0_26])).
% 0.19/0.42  cnf(c_0_42, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k1_tarski(esk1_0),k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.42  cnf(c_0_43, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4)))), inference(rw,[status(thm)],[c_0_37, c_0_15])).
% 0.19/0.42  cnf(c_0_44, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(X6,k1_tarski(X5))),k2_enumset1(X1,X2,X3,X4)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k2_enumset1(X2,X3,X4,X5),k4_xboole_0(X6,k2_enumset1(X2,X3,X4,X5))),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_38])).
% 0.19/0.42  cnf(c_0_45, plain, (k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X2,X3,X4),k1_tarski(X1)))=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_34, c_0_40])).
% 0.19/0.42  cnf(c_0_46, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X5,X6,X7),k2_enumset1(X1,X2,X3,X4)))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[c_0_41, c_0_40])).
% 0.19/0.42  cnf(c_0_47, negated_conjecture, (k5_xboole_0(k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k2_enumset1(esk5_0,esk6_0,esk7_0,esk8_0),k2_enumset1(esk1_0,esk2_0,esk3_0,esk4_0)))!=k5_xboole_0(k1_tarski(esk1_0),k4_xboole_0(k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),k1_tarski(esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_15]), c_0_43])).
% 0.19/0.42  cnf(c_0_48, plain, (k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k2_enumset1(X1,X2,X3,X4)))=k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_tarski(X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.19/0.42  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 50
% 0.19/0.42  # Proof object clause steps            : 27
% 0.19/0.42  # Proof object formula steps           : 23
% 0.19/0.42  # Proof object conjectures             : 6
% 0.19/0.42  # Proof object clause conjectures      : 3
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 11
% 0.19/0.42  # Proof object initial formulas used   : 11
% 0.19/0.42  # Proof object generating inferences   : 3
% 0.19/0.42  # Proof object simplifying inferences  : 26
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 11
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 11
% 0.19/0.42  # Removed in clause preprocessing      : 5
% 0.19/0.42  # Initial clauses in saturation        : 6
% 0.19/0.42  # Processed clauses                    : 479
% 0.19/0.42  # ...of these trivial                  : 30
% 0.19/0.42  # ...subsumed                          : 338
% 0.19/0.42  # ...remaining for further processing  : 111
% 0.19/0.42  # Other redundant clauses eliminated   : 0
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 1
% 0.19/0.42  # Backward-rewritten                   : 19
% 0.19/0.42  # Generated clauses                    : 3909
% 0.19/0.42  # ...of the previous two non-trivial   : 1932
% 0.19/0.42  # Contextual simplify-reflections      : 0
% 0.19/0.42  # Paramodulations                      : 3909
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 0
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 85
% 0.19/0.42  #    Positive orientable unit clauses  : 58
% 0.19/0.42  #    Positive unorientable unit clauses: 27
% 0.19/0.42  #    Negative unit clauses             : 0
% 0.19/0.42  #    Non-unit-clauses                  : 0
% 0.19/0.42  # Current number of unprocessed clauses: 1436
% 0.19/0.42  # ...number of literals in the above   : 1436
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 31
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.42  # Unit Clause-clause subsumption calls : 1179
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 2529
% 0.19/0.42  # BW rewrite match successes           : 332
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 49513
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.074 s
% 0.19/0.42  # System time              : 0.004 s
% 0.19/0.42  # Total time               : 0.078 s
% 0.19/0.42  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
