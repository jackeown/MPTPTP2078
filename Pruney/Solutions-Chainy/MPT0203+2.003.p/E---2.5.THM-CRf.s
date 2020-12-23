%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:38 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   39 (  99 expanded)
%              Number of clauses        :   18 (  38 expanded)
%              Number of leaves         :   10 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  99 expanded)
%              Number of equality atoms :   38 (  98 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(t91_enumset1,axiom,(
    ! [X1] : k4_enumset1(X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t129_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_enumset1)).

fof(l142_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(c_0_10,plain,(
    ! [X10,X11,X12] : k2_xboole_0(k2_xboole_0(X10,X11),X12) = k2_xboole_0(X10,k2_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_11,plain,(
    ! [X13,X14] : k2_xboole_0(X13,X14) = k5_xboole_0(X13,k4_xboole_0(X14,X13)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

fof(c_0_12,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k4_enumset1(X30,X31,X32,X33,X34,X35) = k2_xboole_0(k3_enumset1(X30,X31,X32,X33,X34),k1_tarski(X35)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

fof(c_0_13,plain,(
    ! [X48] : k4_enumset1(X48,X48,X48,X48,X48,X48) = k1_tarski(X48) ),
    inference(variable_rename,[status(thm)],[t91_enumset1])).

fof(c_0_14,plain,(
    ! [X43,X44,X45,X46,X47] : k4_enumset1(X43,X43,X44,X45,X46,X47) = k3_enumset1(X43,X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)) ),
    inference(assume_negation,[status(cth)],[t129_enumset1])).

fof(c_0_16,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22,X23] : k7_enumset1(X15,X16,X17,X18,X19,X20,X21,X22,X23) = k2_xboole_0(k2_enumset1(X15,X16,X17,X18),k3_enumset1(X19,X20,X21,X22,X23)) ),
    inference(variable_rename,[status(thm)],[l142_enumset1])).

fof(c_0_17,plain,(
    ! [X39,X40,X41,X42] : k3_enumset1(X39,X39,X40,X41,X42) = k2_enumset1(X39,X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_18,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X24,X25,X26,X27,X28,X29] : k4_enumset1(X24,X25,X26,X27,X28,X29) = k2_xboole_0(k1_tarski(X24),k3_enumset1(X25,X26,X27,X28,X29)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

fof(c_0_24,negated_conjecture,(
    k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k4_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_25,plain,(
    ! [X36,X37,X38] : k2_enumset1(X36,X36,X37,X38) = k1_enumset1(X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_26,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_29,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X6),k4_enumset1(X1,X1,X2,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_19]),c_0_21]),c_0_22]),c_0_22])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k4_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k4_xboole_0(k4_enumset1(X5,X5,X6,X7,X8,X9),k4_enumset1(X1,X1,X1,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_19]),c_0_27]),c_0_27]),c_0_22]),c_0_22]),c_0_22])).

cnf(c_0_34,plain,
    ( k5_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_xboole_0(k5_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X6),k4_xboole_0(X7,k4_enumset1(X6,X6,X6,X6,X6,X6))),k4_enumset1(X1,X1,X2,X3,X4,X5))) = k5_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k4_xboole_0(X7,k4_enumset1(X1,X2,X3,X4,X5,X6))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_xboole_0(k4_enumset1(X2,X2,X3,X4,X5,X6),k4_enumset1(X1,X1,X1,X1,X1,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_19]),c_0_21]),c_0_21]),c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k4_enumset1(esk5_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0))) != k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k4_xboole_0(k4_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_19]),c_0_32]),c_0_32]),c_0_27]),c_0_27]),c_0_22]),c_0_22]),c_0_33])).

cnf(c_0_37,plain,
    ( k5_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_xboole_0(k4_enumset1(X6,X7,X8,X9,X10,X11),k4_enumset1(X1,X1,X2,X3,X4,X5))) = k5_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k4_xboole_0(k4_enumset1(X7,X7,X8,X9,X10,X11),k4_enumset1(X1,X2,X3,X4,X5,X6))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:36:50 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.18/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.026 s
% 0.18/0.39  # Presaturation interreduction done
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.18/0.39  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.18/0.39  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 0.18/0.39  fof(t91_enumset1, axiom, ![X1]:k4_enumset1(X1,X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_enumset1)).
% 0.18/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.18/0.39  fof(t129_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_enumset1)).
% 0.18/0.39  fof(l142_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l142_enumset1)).
% 0.18/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.39  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.18/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.39  fof(c_0_10, plain, ![X10, X11, X12]:k2_xboole_0(k2_xboole_0(X10,X11),X12)=k2_xboole_0(X10,k2_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.18/0.39  fof(c_0_11, plain, ![X13, X14]:k2_xboole_0(X13,X14)=k5_xboole_0(X13,k4_xboole_0(X14,X13)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.18/0.39  fof(c_0_12, plain, ![X30, X31, X32, X33, X34, X35]:k4_enumset1(X30,X31,X32,X33,X34,X35)=k2_xboole_0(k3_enumset1(X30,X31,X32,X33,X34),k1_tarski(X35)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.18/0.39  fof(c_0_13, plain, ![X48]:k4_enumset1(X48,X48,X48,X48,X48,X48)=k1_tarski(X48), inference(variable_rename,[status(thm)],[t91_enumset1])).
% 0.18/0.39  fof(c_0_14, plain, ![X43, X44, X45, X46, X47]:k4_enumset1(X43,X43,X44,X45,X46,X47)=k3_enumset1(X43,X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.18/0.39  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9))), inference(assume_negation,[status(cth)],[t129_enumset1])).
% 0.18/0.39  fof(c_0_16, plain, ![X15, X16, X17, X18, X19, X20, X21, X22, X23]:k7_enumset1(X15,X16,X17,X18,X19,X20,X21,X22,X23)=k2_xboole_0(k2_enumset1(X15,X16,X17,X18),k3_enumset1(X19,X20,X21,X22,X23)), inference(variable_rename,[status(thm)],[l142_enumset1])).
% 0.18/0.39  fof(c_0_17, plain, ![X39, X40, X41, X42]:k3_enumset1(X39,X39,X40,X41,X42)=k2_enumset1(X39,X40,X41,X42), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.39  cnf(c_0_18, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.39  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.39  cnf(c_0_20, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  cnf(c_0_21, plain, (k4_enumset1(X1,X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.39  cnf(c_0_22, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.39  fof(c_0_23, plain, ![X24, X25, X26, X27, X28, X29]:k4_enumset1(X24,X25,X26,X27,X28,X29)=k2_xboole_0(k1_tarski(X24),k3_enumset1(X25,X26,X27,X28,X29)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.18/0.39  fof(c_0_24, negated_conjecture, k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k4_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.18/0.39  fof(c_0_25, plain, ![X36, X37, X38]:k2_enumset1(X36,X36,X37,X38)=k1_enumset1(X36,X37,X38), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.39  cnf(c_0_26, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.39  cnf(c_0_27, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.39  cnf(c_0_28, plain, (k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),k4_xboole_0(X3,k5_xboole_0(X1,k4_xboole_0(X2,X1))))=k5_xboole_0(X1,k4_xboole_0(k5_xboole_0(X2,k4_xboole_0(X3,X2)),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19]), c_0_19]), c_0_19])).
% 0.18/0.39  cnf(c_0_29, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X6),k4_enumset1(X1,X1,X2,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_19]), c_0_21]), c_0_22]), c_0_22])).
% 0.18/0.39  cnf(c_0_30, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  cnf(c_0_31, negated_conjecture, (k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k4_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.39  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.39  cnf(c_0_33, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k5_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k4_xboole_0(k4_enumset1(X5,X5,X6,X7,X8,X9),k4_enumset1(X1,X1,X1,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_19]), c_0_27]), c_0_27]), c_0_22]), c_0_22]), c_0_22])).
% 0.18/0.39  cnf(c_0_34, plain, (k5_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_xboole_0(k5_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X6),k4_xboole_0(X7,k4_enumset1(X6,X6,X6,X6,X6,X6))),k4_enumset1(X1,X1,X2,X3,X4,X5)))=k5_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k4_xboole_0(X7,k4_enumset1(X1,X2,X3,X4,X5,X6)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.39  cnf(c_0_35, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_xboole_0(k4_enumset1(X2,X2,X3,X4,X5,X6),k4_enumset1(X1,X1,X1,X1,X1,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_19]), c_0_21]), c_0_21]), c_0_22])).
% 0.18/0.39  cnf(c_0_36, negated_conjecture, (k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0),k4_xboole_0(k4_enumset1(esk5_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0)))!=k5_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k4_xboole_0(k4_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_19]), c_0_32]), c_0_32]), c_0_27]), c_0_27]), c_0_22]), c_0_22]), c_0_33])).
% 0.18/0.39  cnf(c_0_37, plain, (k5_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_xboole_0(k4_enumset1(X6,X7,X8,X9,X10,X11),k4_enumset1(X1,X1,X2,X3,X4,X5)))=k5_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k4_xboole_0(k4_enumset1(X7,X7,X8,X9,X10,X11),k4_enumset1(X1,X2,X3,X4,X5,X6)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.18/0.39  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 39
% 0.18/0.39  # Proof object clause steps            : 18
% 0.18/0.39  # Proof object formula steps           : 21
% 0.18/0.39  # Proof object conjectures             : 6
% 0.18/0.39  # Proof object clause conjectures      : 3
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 10
% 0.18/0.39  # Proof object initial formulas used   : 10
% 0.18/0.39  # Proof object generating inferences   : 2
% 0.18/0.39  # Proof object simplifying inferences  : 28
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 10
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 10
% 0.18/0.39  # Removed in clause preprocessing      : 6
% 0.18/0.39  # Initial clauses in saturation        : 4
% 0.18/0.39  # Processed clauses                    : 127
% 0.18/0.39  # ...of these trivial                  : 0
% 0.18/0.39  # ...subsumed                          : 80
% 0.18/0.39  # ...remaining for further processing  : 47
% 0.18/0.39  # Other redundant clauses eliminated   : 0
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 6
% 0.18/0.39  # Backward-rewritten                   : 2
% 0.18/0.39  # Generated clauses                    : 3285
% 0.18/0.39  # ...of the previous two non-trivial   : 2646
% 0.18/0.39  # Contextual simplify-reflections      : 0
% 0.18/0.39  # Paramodulations                      : 3285
% 0.18/0.39  # Factorizations                       : 0
% 0.18/0.39  # Equation resolutions                 : 0
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 35
% 0.18/0.39  #    Positive orientable unit clauses  : 5
% 0.18/0.39  #    Positive unorientable unit clauses: 30
% 0.18/0.39  #    Negative unit clauses             : 0
% 0.18/0.39  #    Non-unit-clauses                  : 0
% 0.18/0.39  # Current number of unprocessed clauses: 2472
% 0.18/0.39  # ...number of literals in the above   : 2472
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 18
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 0
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.39  # Unit Clause-clause subsumption calls : 511
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 1569
% 0.18/0.39  # BW rewrite match successes           : 538
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 28950
% 0.18/0.40  
% 0.18/0.40  # -------------------------------------------------
% 0.18/0.40  # User time                : 0.050 s
% 0.18/0.40  # System time              : 0.011 s
% 0.18/0.40  # Total time               : 0.061 s
% 0.18/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
