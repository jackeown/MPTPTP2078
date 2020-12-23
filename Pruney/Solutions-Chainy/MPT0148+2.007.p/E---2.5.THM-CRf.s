%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:23 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   37 (  71 expanded)
%              Number of clauses        :   18 (  32 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   37 (  71 expanded)
%              Number of equality atoms :   36 (  70 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(t64_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(t62_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

fof(t63_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_9,plain,(
    ! [X14,X15,X16] : k1_enumset1(X14,X15,X16) = k2_xboole_0(k1_tarski(X14),k2_tarski(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t42_enumset1])).

fof(c_0_10,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_xboole_0(k1_tarski(X12),k1_tarski(X13)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_11,plain,(
    ! [X17,X18,X19,X20] : k2_enumset1(X17,X18,X19,X20) = k2_xboole_0(k1_tarski(X17),k1_enumset1(X18,X19,X20)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

cnf(c_0_12,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X21,X22,X23,X24,X25] : k3_enumset1(X21,X22,X23,X24,X25) = k2_xboole_0(k1_tarski(X21),k2_enumset1(X22,X23,X24,X25)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(assume_negation,[status(cth)],[t64_enumset1])).

fof(c_0_18,plain,(
    ! [X26,X27,X28,X29,X30,X31] : k4_enumset1(X26,X27,X28,X29,X30,X31) = k2_xboole_0(k1_tarski(X26),k3_enumset1(X27,X28,X29,X30,X31)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_19,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,negated_conjecture,(
    k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_22,plain,(
    ! [X32,X33,X34,X35,X36,X37,X38,X39] : k6_enumset1(X32,X33,X34,X35,X36,X37,X38,X39) = k2_xboole_0(k1_tarski(X32),k5_enumset1(X33,X34,X35,X36,X37,X38,X39)) ),
    inference(variable_rename,[status(thm)],[t62_enumset1])).

fof(c_0_23,plain,(
    ! [X40,X41,X42,X43,X44,X45,X46,X47] : k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47) = k2_xboole_0(k2_tarski(X40,X41),k4_enumset1(X42,X43,X44,X45,X46,X47)) ),
    inference(variable_rename,[status(thm)],[t63_enumset1])).

cnf(c_0_24,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X9,X10,X11] : k2_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_29,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk1_0),k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)) != k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk6_0),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_16]),c_0_25]),c_0_27])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k1_tarski(X8))))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_13]),c_0_30]),c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk6_0),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0)))))))) != k2_xboole_0(k1_tarski(esk1_0),k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_32])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k1_tarski(X8)))))))) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 17:10:30 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.33  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.12/0.33  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.33  #
% 0.12/0.33  # Preprocessing time       : 0.013 s
% 0.12/0.33  # Presaturation interreduction done
% 0.12/0.33  
% 0.12/0.33  # Proof found!
% 0.12/0.33  # SZS status Theorem
% 0.12/0.33  # SZS output start CNFRefutation
% 0.12/0.33  fof(t42_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 0.12/0.33  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.12/0.33  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.12/0.33  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.12/0.33  fof(t64_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_enumset1)).
% 0.12/0.33  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.12/0.33  fof(t62_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 0.12/0.33  fof(t63_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 0.12/0.33  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.12/0.33  fof(c_0_9, plain, ![X14, X15, X16]:k1_enumset1(X14,X15,X16)=k2_xboole_0(k1_tarski(X14),k2_tarski(X15,X16)), inference(variable_rename,[status(thm)],[t42_enumset1])).
% 0.12/0.33  fof(c_0_10, plain, ![X12, X13]:k2_tarski(X12,X13)=k2_xboole_0(k1_tarski(X12),k1_tarski(X13)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.12/0.33  fof(c_0_11, plain, ![X17, X18, X19, X20]:k2_enumset1(X17,X18,X19,X20)=k2_xboole_0(k1_tarski(X17),k1_enumset1(X18,X19,X20)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.12/0.33  cnf(c_0_12, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.33  cnf(c_0_13, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.33  fof(c_0_14, plain, ![X21, X22, X23, X24, X25]:k3_enumset1(X21,X22,X23,X24,X25)=k2_xboole_0(k1_tarski(X21),k2_enumset1(X22,X23,X24,X25)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.12/0.33  cnf(c_0_15, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.33  cnf(c_0_16, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.33  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))), inference(assume_negation,[status(cth)],[t64_enumset1])).
% 0.12/0.33  fof(c_0_18, plain, ![X26, X27, X28, X29, X30, X31]:k4_enumset1(X26,X27,X28,X29,X30,X31)=k2_xboole_0(k1_tarski(X26),k3_enumset1(X27,X28,X29,X30,X31)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.12/0.33  cnf(c_0_19, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.33  cnf(c_0_20, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.33  fof(c_0_21, negated_conjecture, k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.12/0.33  fof(c_0_22, plain, ![X32, X33, X34, X35, X36, X37, X38, X39]:k6_enumset1(X32,X33,X34,X35,X36,X37,X38,X39)=k2_xboole_0(k1_tarski(X32),k5_enumset1(X33,X34,X35,X36,X37,X38,X39)), inference(variable_rename,[status(thm)],[t62_enumset1])).
% 0.12/0.33  fof(c_0_23, plain, ![X40, X41, X42, X43, X44, X45, X46, X47]:k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)=k2_xboole_0(k2_tarski(X40,X41),k4_enumset1(X42,X43,X44,X45,X46,X47)), inference(variable_rename,[status(thm)],[t63_enumset1])).
% 0.12/0.33  cnf(c_0_24, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.33  cnf(c_0_25, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.33  cnf(c_0_26, negated_conjecture, (k6_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0)!=k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k3_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.33  cnf(c_0_27, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.33  fof(c_0_28, plain, ![X9, X10, X11]:k2_xboole_0(k2_xboole_0(X9,X10),X11)=k2_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.12/0.33  cnf(c_0_29, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_tarski(X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.33  cnf(c_0_30, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))))))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.33  cnf(c_0_31, negated_conjecture, (k2_xboole_0(k1_tarski(esk1_0),k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0))!=k2_xboole_0(k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk6_0),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_16]), c_0_25]), c_0_27])).
% 0.12/0.33  cnf(c_0_32, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.33  cnf(c_0_33, plain, (k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k1_tarski(X8)))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_13]), c_0_30]), c_0_27])).
% 0.12/0.33  cnf(c_0_34, negated_conjecture, (k2_xboole_0(k1_tarski(esk1_0),k2_xboole_0(k1_tarski(esk2_0),k2_xboole_0(k1_tarski(esk3_0),k2_xboole_0(k1_tarski(esk4_0),k2_xboole_0(k1_tarski(esk5_0),k2_xboole_0(k1_tarski(esk6_0),k2_xboole_0(k1_tarski(esk7_0),k1_tarski(esk8_0))))))))!=k2_xboole_0(k1_tarski(esk1_0),k5_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_32])).
% 0.12/0.33  cnf(c_0_35, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k1_tarski(X8))))))))=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(rw,[status(thm)],[c_0_33, c_0_32])).
% 0.12/0.33  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])]), ['proof']).
% 0.12/0.33  # SZS output end CNFRefutation
% 0.12/0.33  # Proof object total steps             : 37
% 0.12/0.33  # Proof object clause steps            : 18
% 0.12/0.33  # Proof object formula steps           : 19
% 0.12/0.33  # Proof object conjectures             : 7
% 0.12/0.33  # Proof object clause conjectures      : 4
% 0.12/0.33  # Proof object formula conjectures     : 3
% 0.12/0.33  # Proof object initial clauses used    : 9
% 0.12/0.33  # Proof object initial formulas used   : 9
% 0.12/0.33  # Proof object generating inferences   : 0
% 0.12/0.33  # Proof object simplifying inferences  : 15
% 0.12/0.33  # Training examples: 0 positive, 0 negative
% 0.12/0.33  # Parsed axioms                        : 9
% 0.12/0.33  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.33  # Initial clauses                      : 9
% 0.12/0.33  # Removed in clause preprocessing      : 6
% 0.12/0.33  # Initial clauses in saturation        : 3
% 0.12/0.33  # Processed clauses                    : 3
% 0.12/0.33  # ...of these trivial                  : 0
% 0.12/0.33  # ...subsumed                          : 0
% 0.12/0.33  # ...remaining for further processing  : 3
% 0.12/0.33  # Other redundant clauses eliminated   : 0
% 0.12/0.33  # Clauses deleted for lack of memory   : 0
% 0.12/0.33  # Backward-subsumed                    : 0
% 0.12/0.33  # Backward-rewritten                   : 1
% 0.12/0.33  # Generated clauses                    : 0
% 0.12/0.33  # ...of the previous two non-trivial   : 0
% 0.12/0.33  # Contextual simplify-reflections      : 0
% 0.12/0.33  # Paramodulations                      : 0
% 0.12/0.33  # Factorizations                       : 0
% 0.12/0.33  # Equation resolutions                 : 0
% 0.12/0.33  # Propositional unsat checks           : 0
% 0.12/0.33  #    Propositional check models        : 0
% 0.12/0.33  #    Propositional check unsatisfiable : 0
% 0.12/0.33  #    Propositional clauses             : 0
% 0.12/0.33  #    Propositional clauses after purity: 0
% 0.12/0.33  #    Propositional unsat core size     : 0
% 0.12/0.33  #    Propositional preprocessing time  : 0.000
% 0.12/0.33  #    Propositional encoding time       : 0.000
% 0.12/0.33  #    Propositional solver time         : 0.000
% 0.12/0.33  #    Success case prop preproc time    : 0.000
% 0.12/0.33  #    Success case prop encoding time   : 0.000
% 0.12/0.33  #    Success case prop solver time     : 0.000
% 0.12/0.33  # Current number of processed clauses  : 2
% 0.12/0.33  #    Positive orientable unit clauses  : 2
% 0.12/0.33  #    Positive unorientable unit clauses: 0
% 0.12/0.33  #    Negative unit clauses             : 0
% 0.12/0.33  #    Non-unit-clauses                  : 0
% 0.12/0.33  # Current number of unprocessed clauses: 0
% 0.12/0.33  # ...number of literals in the above   : 0
% 0.12/0.33  # Current number of archived formulas  : 0
% 0.12/0.33  # Current number of archived clauses   : 7
% 0.12/0.33  # Clause-clause subsumption calls (NU) : 0
% 0.12/0.33  # Rec. Clause-clause subsumption calls : 0
% 0.12/0.33  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.33  # Unit Clause-clause subsumption calls : 0
% 0.12/0.33  # Rewrite failures with RHS unbound    : 0
% 0.12/0.33  # BW rewrite match attempts            : 5
% 0.12/0.33  # BW rewrite match successes           : 1
% 0.12/0.33  # Condensation attempts                : 0
% 0.12/0.33  # Condensation successes               : 0
% 0.12/0.33  # Termbank termtop insertions          : 728
% 0.12/0.33  
% 0.12/0.33  # -------------------------------------------------
% 0.12/0.33  # User time                : 0.012 s
% 0.12/0.33  # System time              : 0.003 s
% 0.12/0.33  # Total time               : 0.015 s
% 0.12/0.33  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
