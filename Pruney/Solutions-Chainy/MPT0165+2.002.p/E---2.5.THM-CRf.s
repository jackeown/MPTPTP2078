%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:52 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   35 (  79 expanded)
%              Number of clauses        :   16 (  32 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  79 expanded)
%              Number of equality atoms :   34 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(t81_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(t66_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t53_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).

fof(c_0_9,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] : k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X16) = k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k2_enumset1(X13,X14,X15,X16)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

fof(c_0_10,plain,(
    ! [X41,X42,X43,X44] : k3_enumset1(X41,X41,X42,X43,X44) = k2_enumset1(X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_11,plain,(
    ! [X17,X18,X19,X20,X21,X22] : k4_enumset1(X17,X18,X19,X20,X21,X22) = k2_xboole_0(k1_tarski(X17),k3_enumset1(X18,X19,X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

fof(c_0_12,plain,(
    ! [X37] : k2_tarski(X37,X37) = k1_tarski(X37) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X45,X46] : k2_enumset1(X45,X45,X45,X46) = k2_tarski(X45,X46) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(assume_negation,[status(cth)],[t81_enumset1])).

fof(c_0_15,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35,X36] : k6_enumset1(X29,X30,X31,X32,X33,X34,X35,X36) = k2_xboole_0(k3_enumset1(X29,X30,X31,X32,X33),k1_enumset1(X34,X35,X36)) ),
    inference(variable_rename,[status(thm)],[t66_enumset1])).

fof(c_0_16,plain,(
    ! [X38,X39,X40] : k2_enumset1(X38,X38,X39,X40) = k1_enumset1(X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_17,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X23,X24,X25,X26,X27,X28] : k4_enumset1(X23,X24,X25,X26,X27,X28) = k2_xboole_0(k1_enumset1(X23,X24,X25),k1_enumset1(X26,X27,X28)) ),
    inference(variable_rename,[status(thm)],[t53_enumset1])).

cnf(c_0_20,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,negated_conjecture,(
    k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_24,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X6,X7,X8)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

cnf(c_0_27,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X6,X7,X8)) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X6,X6,X6,X7,X8)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25]),c_0_18]),c_0_26])).

cnf(c_0_31,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k2_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X5,X6)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_25]),c_0_25]),c_0_18]),c_0_18]),c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk4_0,esk5_0,esk6_0)) != k2_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_28]),c_0_26])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X4,X5,X6)) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.038 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 0.13/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.39  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.13/0.39  fof(t81_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6]:k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 0.13/0.39  fof(t66_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 0.13/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.39  fof(t53_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_enumset1)).
% 0.13/0.39  fof(c_0_9, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X16)=k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k2_enumset1(X13,X14,X15,X16)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.13/0.39  fof(c_0_10, plain, ![X41, X42, X43, X44]:k3_enumset1(X41,X41,X42,X43,X44)=k2_enumset1(X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.39  fof(c_0_11, plain, ![X17, X18, X19, X20, X21, X22]:k4_enumset1(X17,X18,X19,X20,X21,X22)=k2_xboole_0(k1_tarski(X17),k3_enumset1(X18,X19,X20,X21,X22)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.13/0.39  fof(c_0_12, plain, ![X37]:k2_tarski(X37,X37)=k1_tarski(X37), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  fof(c_0_13, plain, ![X45, X46]:k2_enumset1(X45,X45,X45,X46)=k2_tarski(X45,X46), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.13/0.39  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(assume_negation,[status(cth)],[t81_enumset1])).
% 0.13/0.39  fof(c_0_15, plain, ![X29, X30, X31, X32, X33, X34, X35, X36]:k6_enumset1(X29,X30,X31,X32,X33,X34,X35,X36)=k2_xboole_0(k3_enumset1(X29,X30,X31,X32,X33),k1_enumset1(X34,X35,X36)), inference(variable_rename,[status(thm)],[t66_enumset1])).
% 0.13/0.39  fof(c_0_16, plain, ![X38, X39, X40]:k2_enumset1(X38,X38,X39,X40)=k1_enumset1(X38,X39,X40), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.39  cnf(c_0_17, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_18, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  fof(c_0_19, plain, ![X23, X24, X25, X26, X27, X28]:k4_enumset1(X23,X24,X25,X26,X27,X28)=k2_xboole_0(k1_enumset1(X23,X24,X25),k1_enumset1(X26,X27,X28)), inference(variable_rename,[status(thm)],[t53_enumset1])).
% 0.13/0.39  cnf(c_0_20, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  fof(c_0_23, negated_conjecture, k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.13/0.39  cnf(c_0_24, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_26, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X6,X7,X8))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18])).
% 0.13/0.39  cnf(c_0_27, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_28, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_18])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_30, plain, (k2_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X6,X7,X8))=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X6,X6,X6,X7,X8))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_25]), c_0_18]), c_0_26])).
% 0.13/0.39  cnf(c_0_31, plain, (k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6))=k2_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X5,X6))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_25]), c_0_25]), c_0_18]), c_0_18]), c_0_28])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (k2_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk4_0,esk5_0,esk6_0))!=k2_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_28]), c_0_26])).
% 0.13/0.39  cnf(c_0_33, plain, (k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X4,X5,X6))=k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 35
% 0.13/0.39  # Proof object clause steps            : 16
% 0.13/0.39  # Proof object formula steps           : 19
% 0.13/0.39  # Proof object conjectures             : 6
% 0.13/0.39  # Proof object clause conjectures      : 3
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 9
% 0.13/0.39  # Proof object initial formulas used   : 9
% 0.13/0.39  # Proof object generating inferences   : 1
% 0.13/0.39  # Proof object simplifying inferences  : 17
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 9
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 9
% 0.13/0.39  # Removed in clause preprocessing      : 6
% 0.13/0.39  # Initial clauses in saturation        : 3
% 0.13/0.39  # Processed clauses                    : 11
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 1
% 0.13/0.39  # ...remaining for further processing  : 10
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 1
% 0.13/0.39  # Generated clauses                    : 55
% 0.13/0.39  # ...of the previous two non-trivial   : 37
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 55
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 6
% 0.13/0.39  #    Positive orientable unit clauses  : 0
% 0.13/0.39  #    Positive unorientable unit clauses: 6
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 0
% 0.13/0.39  # Current number of unprocessed clauses: 32
% 0.13/0.39  # ...number of literals in the above   : 32
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 10
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.39  # Unit Clause-clause subsumption calls : 16
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 94
% 0.13/0.39  # BW rewrite match successes           : 15
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 1148
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.039 s
% 0.13/0.39  # System time              : 0.005 s
% 0.13/0.39  # Total time               : 0.044 s
% 0.13/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
