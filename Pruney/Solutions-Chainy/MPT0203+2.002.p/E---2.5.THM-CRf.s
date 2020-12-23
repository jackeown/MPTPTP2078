%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:38 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  50 expanded)
%              Number of clauses        :   16 (  21 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  50 expanded)
%              Number of equality atoms :   34 (  49 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(t78_enumset1,axiom,(
    ! [X1,X2,X3] : k3_enumset1(X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(c_0_9,plain,(
    ! [X35,X36,X37,X38,X39,X40] : k4_enumset1(X35,X36,X37,X38,X39,X40) = k2_xboole_0(k3_enumset1(X35,X36,X37,X38,X39),k1_tarski(X40)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

fof(c_0_10,plain,(
    ! [X53] : k4_enumset1(X53,X53,X53,X53,X53,X53) = k1_tarski(X53) ),
    inference(variable_rename,[status(thm)],[t91_enumset1])).

fof(c_0_11,plain,(
    ! [X45,X46,X47,X48,X49] : k4_enumset1(X45,X45,X46,X47,X48,X49) = k3_enumset1(X45,X46,X47,X48,X49) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] : k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)) ),
    inference(assume_negation,[status(cth)],[t129_enumset1])).

fof(c_0_13,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22,X23] : k7_enumset1(X15,X16,X17,X18,X19,X20,X21,X22,X23) = k2_xboole_0(k2_enumset1(X15,X16,X17,X18),k3_enumset1(X19,X20,X21,X22,X23)) ),
    inference(variable_rename,[status(thm)],[l142_enumset1])).

fof(c_0_14,plain,(
    ! [X41,X42,X43,X44] : k3_enumset1(X41,X41,X42,X43,X44) = k2_enumset1(X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_15,plain,(
    ! [X12,X13,X14] : k2_xboole_0(k2_xboole_0(X12,X13),X14) = k2_xboole_0(X12,k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_16,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X29,X30,X31,X32,X33,X34] : k4_enumset1(X29,X30,X31,X32,X33,X34) = k2_xboole_0(k1_tarski(X29),k3_enumset1(X30,X31,X32,X33,X34)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

fof(c_0_20,negated_conjecture,(
    k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k4_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_21,plain,(
    ! [X50,X51,X52] : k3_enumset1(X50,X50,X50,X51,X52) = k1_enumset1(X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t78_enumset1])).

cnf(c_0_22,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X6)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_26,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0) != k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k4_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k4_enumset1(X5,X5,X6,X7,X8,X9)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_18]),c_0_18])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k2_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X6),X7)) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),X7) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X3,X4,X5,X6)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_17]),c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) != k2_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k4_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_18]),c_0_29])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_enumset1(X6,X7,X8,X9,X10,X11)) = k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k4_enumset1(X7,X7,X8,X9,X10,X11)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:35:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.19/0.50  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.026 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 0.19/0.50  fof(t91_enumset1, axiom, ![X1]:k4_enumset1(X1,X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_enumset1)).
% 0.19/0.50  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.50  fof(t129_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_enumset1)).
% 0.19/0.50  fof(l142_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l142_enumset1)).
% 0.19/0.50  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.50  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.19/0.50  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.19/0.50  fof(t78_enumset1, axiom, ![X1, X2, X3]:k3_enumset1(X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_enumset1)).
% 0.19/0.50  fof(c_0_9, plain, ![X35, X36, X37, X38, X39, X40]:k4_enumset1(X35,X36,X37,X38,X39,X40)=k2_xboole_0(k3_enumset1(X35,X36,X37,X38,X39),k1_tarski(X40)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.19/0.50  fof(c_0_10, plain, ![X53]:k4_enumset1(X53,X53,X53,X53,X53,X53)=k1_tarski(X53), inference(variable_rename,[status(thm)],[t91_enumset1])).
% 0.19/0.50  fof(c_0_11, plain, ![X45, X46, X47, X48, X49]:k4_enumset1(X45,X45,X46,X47,X48,X49)=k3_enumset1(X45,X46,X47,X48,X49), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.50  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6, X7, X8, X9]:k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k1_enumset1(X1,X2,X3),k4_enumset1(X4,X5,X6,X7,X8,X9))), inference(assume_negation,[status(cth)],[t129_enumset1])).
% 0.19/0.50  fof(c_0_13, plain, ![X15, X16, X17, X18, X19, X20, X21, X22, X23]:k7_enumset1(X15,X16,X17,X18,X19,X20,X21,X22,X23)=k2_xboole_0(k2_enumset1(X15,X16,X17,X18),k3_enumset1(X19,X20,X21,X22,X23)), inference(variable_rename,[status(thm)],[l142_enumset1])).
% 0.19/0.50  fof(c_0_14, plain, ![X41, X42, X43, X44]:k3_enumset1(X41,X41,X42,X43,X44)=k2_enumset1(X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.50  fof(c_0_15, plain, ![X12, X13, X14]:k2_xboole_0(k2_xboole_0(X12,X13),X14)=k2_xboole_0(X12,k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.19/0.50  cnf(c_0_16, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.50  cnf(c_0_17, plain, (k4_enumset1(X1,X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.50  cnf(c_0_18, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.50  fof(c_0_19, plain, ![X29, X30, X31, X32, X33, X34]:k4_enumset1(X29,X30,X31,X32,X33,X34)=k2_xboole_0(k1_tarski(X29),k3_enumset1(X30,X31,X32,X33,X34)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.19/0.50  fof(c_0_20, negated_conjecture, k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k4_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.19/0.50  fof(c_0_21, plain, ![X50, X51, X52]:k3_enumset1(X50,X50,X50,X51,X52)=k1_enumset1(X50,X51,X52), inference(variable_rename,[status(thm)],[t78_enumset1])).
% 0.19/0.50  cnf(c_0_22, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X6,X7,X8,X9))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.50  cnf(c_0_23, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.50  cnf(c_0_24, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.50  cnf(c_0_25, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X6))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.19/0.50  cnf(c_0_26, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.50  cnf(c_0_27, negated_conjecture, (k7_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0)!=k2_xboole_0(k1_enumset1(esk1_0,esk2_0,esk3_0),k4_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.50  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.50  cnf(c_0_29, plain, (k7_enumset1(X1,X2,X3,X4,X5,X6,X7,X8,X9)=k2_xboole_0(k4_enumset1(X1,X1,X1,X2,X3,X4),k4_enumset1(X5,X5,X6,X7,X8,X9))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_18]), c_0_18])).
% 0.19/0.50  cnf(c_0_30, plain, (k2_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k2_xboole_0(k4_enumset1(X6,X6,X6,X6,X6,X6),X7))=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),X7)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.50  cnf(c_0_31, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X2,X2,X3,X4,X5,X6))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_17]), c_0_18])).
% 0.19/0.50  cnf(c_0_32, negated_conjecture, (k2_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0))!=k2_xboole_0(k4_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,esk3_0),k4_enumset1(esk4_0,esk5_0,esk6_0,esk7_0,esk8_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_18]), c_0_29])).
% 0.19/0.50  cnf(c_0_33, plain, (k2_xboole_0(k4_enumset1(X1,X1,X2,X3,X4,X5),k4_enumset1(X6,X7,X8,X9,X10,X11))=k2_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k4_enumset1(X7,X7,X8,X9,X10,X11))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.50  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33])]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 35
% 0.19/0.50  # Proof object clause steps            : 16
% 0.19/0.50  # Proof object formula steps           : 19
% 0.19/0.50  # Proof object conjectures             : 6
% 0.19/0.50  # Proof object clause conjectures      : 3
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 9
% 0.19/0.50  # Proof object initial formulas used   : 9
% 0.19/0.50  # Proof object generating inferences   : 2
% 0.19/0.50  # Proof object simplifying inferences  : 12
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 11
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 11
% 0.19/0.50  # Removed in clause preprocessing      : 5
% 0.19/0.50  # Initial clauses in saturation        : 6
% 0.19/0.50  # Processed clauses                    : 479
% 0.19/0.50  # ...of these trivial                  : 68
% 0.19/0.50  # ...subsumed                          : 287
% 0.19/0.50  # ...remaining for further processing  : 124
% 0.19/0.50  # Other redundant clauses eliminated   : 0
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 3
% 0.19/0.50  # Backward-rewritten                   : 1
% 0.19/0.50  # Generated clauses                    : 20734
% 0.19/0.50  # ...of the previous two non-trivial   : 17409
% 0.19/0.50  # Contextual simplify-reflections      : 0
% 0.19/0.50  # Paramodulations                      : 20734
% 0.19/0.50  # Factorizations                       : 0
% 0.19/0.50  # Equation resolutions                 : 0
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 114
% 0.19/0.50  #    Positive orientable unit clauses  : 13
% 0.19/0.50  #    Positive unorientable unit clauses: 101
% 0.19/0.50  #    Negative unit clauses             : 0
% 0.19/0.50  #    Non-unit-clauses                  : 0
% 0.19/0.50  # Current number of unprocessed clauses: 16911
% 0.19/0.50  # ...number of literals in the above   : 16911
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 15
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 0
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 0
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.50  # Unit Clause-clause subsumption calls : 5455
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 10970
% 0.19/0.50  # BW rewrite match successes           : 2394
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 86607
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.156 s
% 0.19/0.50  # System time              : 0.007 s
% 0.19/0.50  # Total time               : 0.164 s
% 0.19/0.50  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
