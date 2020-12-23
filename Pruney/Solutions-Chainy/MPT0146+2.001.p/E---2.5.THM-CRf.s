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
% DateTime   : Thu Dec  3 10:35:20 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 128 expanded)
%              Number of clauses        :   18 (  51 expanded)
%              Number of leaves         :    9 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   37 ( 128 expanded)
%              Number of equality atoms :   36 ( 127 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(t61_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t62_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(c_0_9,plain,(
    ! [X47,X48,X49] : k1_enumset1(X47,X48,X49) = k2_xboole_0(k2_tarski(X47,X48),k1_tarski(X49)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_10,plain,(
    ! [X45,X46] : k2_tarski(X45,X46) = k2_xboole_0(k1_tarski(X45),k1_tarski(X46)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_11,plain,(
    ! [X50,X51,X52,X53] : k2_enumset1(X50,X51,X52,X53) = k2_xboole_0(k1_enumset1(X50,X51,X52),k1_tarski(X53)) ),
    inference(variable_rename,[status(thm)],[t46_enumset1])).

cnf(c_0_12,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X54,X55,X56,X57,X58] : k3_enumset1(X54,X55,X56,X57,X58) = k2_xboole_0(k2_enumset1(X54,X55,X56,X57),k1_tarski(X58)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,plain,(
    ! [X59,X60,X61,X62,X63,X64] : k4_enumset1(X59,X60,X61,X62,X63,X64) = k2_xboole_0(k3_enumset1(X59,X60,X61,X62,X63),k1_tarski(X64)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

cnf(c_0_18,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X65,X66,X67,X68,X69,X70,X71] : k5_enumset1(X65,X66,X67,X68,X69,X70,X71) = k2_xboole_0(k4_enumset1(X65,X66,X67,X68,X69,X70),k1_tarski(X71)) ),
    inference(variable_rename,[status(thm)],[t61_enumset1])).

cnf(c_0_21,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_23,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43,X44] : k6_enumset1(X37,X38,X39,X40,X41,X42,X43,X44) = k2_xboole_0(k2_enumset1(X37,X38,X39,X40),k2_enumset1(X41,X42,X43,X44)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

cnf(c_0_24,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5)),k1_tarski(X6)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,plain,(
    ! [X14,X15,X16] : k2_xboole_0(k2_xboole_0(X14,X15),X16) = k2_xboole_0(X14,k2_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(assume_negation,[status(cth)],[t62_enumset1])).

cnf(c_0_28,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5)),k1_tarski(X6)),k1_tarski(X7)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_31,negated_conjecture,(
    k6_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0) != k2_xboole_0(k1_tarski(esk3_0),k5_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X5),k1_tarski(X6)),k1_tarski(X7)),k1_tarski(X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_19]),c_0_19])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7))))))) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k6_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0) != k2_xboole_0(k1_tarski(esk3_0),k5_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_30]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:34:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 0.12/0.36  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 0.12/0.36  fof(t46_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 0.12/0.36  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 0.12/0.36  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 0.12/0.36  fof(t61_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 0.12/0.36  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 0.12/0.36  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.12/0.36  fof(t62_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 0.12/0.36  fof(c_0_9, plain, ![X47, X48, X49]:k1_enumset1(X47,X48,X49)=k2_xboole_0(k2_tarski(X47,X48),k1_tarski(X49)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.12/0.36  fof(c_0_10, plain, ![X45, X46]:k2_tarski(X45,X46)=k2_xboole_0(k1_tarski(X45),k1_tarski(X46)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.12/0.36  fof(c_0_11, plain, ![X50, X51, X52, X53]:k2_enumset1(X50,X51,X52,X53)=k2_xboole_0(k1_enumset1(X50,X51,X52),k1_tarski(X53)), inference(variable_rename,[status(thm)],[t46_enumset1])).
% 0.12/0.36  cnf(c_0_12, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.36  cnf(c_0_13, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.36  fof(c_0_14, plain, ![X54, X55, X56, X57, X58]:k3_enumset1(X54,X55,X56,X57,X58)=k2_xboole_0(k2_enumset1(X54,X55,X56,X57),k1_tarski(X58)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.12/0.36  cnf(c_0_15, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X4))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  cnf(c_0_16, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.36  fof(c_0_17, plain, ![X59, X60, X61, X62, X63, X64]:k4_enumset1(X59,X60,X61,X62,X63,X64)=k2_xboole_0(k3_enumset1(X59,X60,X61,X62,X63),k1_tarski(X64)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.12/0.36  cnf(c_0_18, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_19, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.36  fof(c_0_20, plain, ![X65, X66, X67, X68, X69, X70, X71]:k5_enumset1(X65,X66,X67,X68,X69,X70,X71)=k2_xboole_0(k4_enumset1(X65,X66,X67,X68,X69,X70),k1_tarski(X71)), inference(variable_rename,[status(thm)],[t61_enumset1])).
% 0.12/0.36  cnf(c_0_21, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_22, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.36  fof(c_0_23, plain, ![X37, X38, X39, X40, X41, X42, X43, X44]:k6_enumset1(X37,X38,X39,X40,X41,X42,X43,X44)=k2_xboole_0(k2_enumset1(X37,X38,X39,X40),k2_enumset1(X41,X42,X43,X44)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.12/0.36  cnf(c_0_24, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X7))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.36  cnf(c_0_25, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5)),k1_tarski(X6))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.36  fof(c_0_26, plain, ![X14, X15, X16]:k2_xboole_0(k2_xboole_0(X14,X15),X16)=k2_xboole_0(X14,k2_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.12/0.36  fof(c_0_27, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))), inference(assume_negation,[status(cth)],[t62_enumset1])).
% 0.12/0.36  cnf(c_0_28, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.36  cnf(c_0_29, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k1_tarski(X5)),k1_tarski(X6)),k1_tarski(X7))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.36  cnf(c_0_30, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.36  fof(c_0_31, negated_conjecture, k6_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)!=k2_xboole_0(k1_tarski(esk3_0),k5_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.12/0.36  cnf(c_0_32, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k1_tarski(X4)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X5),k1_tarski(X6)),k1_tarski(X7)),k1_tarski(X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_19]), c_0_19])).
% 0.12/0.36  cnf(c_0_33, plain, (k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k1_tarski(X5),k2_xboole_0(k1_tarski(X6),k1_tarski(X7)))))))=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.12/0.36  cnf(c_0_34, negated_conjecture, (k6_enumset1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0)!=k2_xboole_0(k1_tarski(esk3_0),k5_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.36  cnf(c_0_35, plain, (k2_xboole_0(k1_tarski(X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))=k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_30]), c_0_33])).
% 0.12/0.36  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 37
% 0.12/0.36  # Proof object clause steps            : 18
% 0.12/0.36  # Proof object formula steps           : 19
% 0.12/0.36  # Proof object conjectures             : 5
% 0.12/0.36  # Proof object clause conjectures      : 2
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 9
% 0.12/0.36  # Proof object initial formulas used   : 9
% 0.12/0.36  # Proof object generating inferences   : 0
% 0.12/0.36  # Proof object simplifying inferences  : 34
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 14
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 24
% 0.12/0.36  # Removed in clause preprocessing      : 5
% 0.12/0.36  # Initial clauses in saturation        : 19
% 0.12/0.36  # Processed clauses                    : 23
% 0.12/0.36  # ...of these trivial                  : 1
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 22
% 0.12/0.36  # Other redundant clauses eliminated   : 10
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 1
% 0.12/0.36  # Generated clauses                    : 6
% 0.12/0.36  # ...of the previous two non-trivial   : 6
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 0
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 10
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 15
% 0.12/0.36  #    Positive orientable unit clauses  : 9
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 0
% 0.12/0.36  #    Non-unit-clauses                  : 6
% 0.12/0.36  # Current number of unprocessed clauses: 2
% 0.12/0.36  # ...number of literals in the above   : 9
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 6
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 10
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 6
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 3
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 5
% 0.12/0.36  # BW rewrite match successes           : 1
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 1769
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.027 s
% 0.12/0.36  # System time              : 0.004 s
% 0.12/0.36  # Total time               : 0.031 s
% 0.12/0.36  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
