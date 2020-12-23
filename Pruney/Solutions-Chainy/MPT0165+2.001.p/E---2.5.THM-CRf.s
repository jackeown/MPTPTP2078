%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:52 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   54 (11007 expanded)
%              Number of clauses        :   31 (4760 expanded)
%              Number of leaves         :   11 (3123 expanded)
%              Depth                    :   15
%              Number of atoms          :   54 (11007 expanded)
%              Number of equality atoms :   53 (11006 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(t78_enumset1,axiom,(
    ! [X1,X2,X3] : k3_enumset1(X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(t59_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_enumset1)).

fof(l57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(t53_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).

fof(t81_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] : k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(c_0_11,plain,(
    ! [X38,X39,X40,X41,X42,X43,X44] : k5_enumset1(X38,X39,X40,X41,X42,X43,X44) = k2_xboole_0(k1_enumset1(X38,X39,X40),k2_enumset1(X41,X42,X43,X44)) ),
    inference(variable_rename,[status(thm)],[t58_enumset1])).

fof(c_0_12,plain,(
    ! [X55,X56,X57] : k3_enumset1(X55,X55,X55,X56,X57) = k1_enumset1(X55,X56,X57) ),
    inference(variable_rename,[status(thm)],[t78_enumset1])).

fof(c_0_13,plain,(
    ! [X22,X23,X24,X25] : k2_enumset1(X22,X23,X24,X25) = k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_14,plain,(
    ! [X52] : k2_tarski(X52,X52) = k1_tarski(X52) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X53,X54] : k2_enumset1(X53,X53,X53,X54) = k2_tarski(X53,X54) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_16,plain,(
    ! [X45,X46,X47,X48,X49,X50,X51] : k5_enumset1(X45,X46,X47,X48,X49,X50,X51) = k2_xboole_0(k2_enumset1(X45,X46,X47,X48),k1_enumset1(X49,X50,X51)) ),
    inference(variable_rename,[status(thm)],[t59_enumset1])).

cnf(c_0_17,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X9,X10,X11,X12,X13] : k3_enumset1(X9,X10,X11,X12,X13) = k2_xboole_0(k1_enumset1(X9,X10,X11),k2_tarski(X12,X13)) ),
    inference(variable_rename,[status(thm)],[l57_enumset1])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_25,plain,(
    ! [X26,X27,X28,X29,X30,X31] : k4_enumset1(X26,X27,X28,X29,X30,X31) = k2_xboole_0(k1_tarski(X26),k3_enumset1(X27,X28,X29,X30,X31)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_18])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X6,X7)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_18]),c_0_24])).

fof(c_0_29,plain,(
    ! [X32,X33,X34,X35,X36,X37] : k4_enumset1(X32,X33,X34,X35,X36,X37) = k2_xboole_0(k1_enumset1(X32,X33,X34),k1_enumset1(X35,X36,X37)) ),
    inference(variable_rename,[status(thm)],[t53_enumset1])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k2_enumset1(X4,X4,X4,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_22]),c_0_18])).

cnf(c_0_32,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k2_enumset1(X1,X2,X3,X4)) = k2_enumset1(X1,X2,X3,X4) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_21]),c_0_22])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k2_enumset1(X1,X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k2_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X5,X6)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_18]),c_0_18]),c_0_34])).

cnf(c_0_37,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(X1,X2,X2,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_35])).

cnf(c_0_38,plain,
    ( k3_enumset1(X1,X2,X2,X2,X3) = k2_enumset1(X1,X2,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_35]),c_0_35]),c_0_31]),c_0_37])).

cnf(c_0_39,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X2,X3,X4)) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_32,c_0_35])).

cnf(c_0_40,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X3,X3,X4)) = k3_enumset1(X1,X2,X3,X3,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_38]),c_0_38]),c_0_31])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X1,X2,X2,X3) = k2_enumset1(X1,X2,X2,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] : k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(assume_negation,[status(cth)],[t81_enumset1])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X2,X3,X3,X4) = k3_enumset1(X1,X2,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_41]),c_0_40]),c_0_38]),c_0_31])).

fof(c_0_44,negated_conjecture,(
    k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).

fof(c_0_45,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] : k6_enumset1(X14,X15,X16,X17,X18,X19,X20,X21) = k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k2_enumset1(X18,X19,X20,X21)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

cnf(c_0_46,plain,
    ( k3_enumset1(X1,X2,X3,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_43]),c_0_41]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) != k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X2,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_43,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0)) != k2_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_34]),c_0_48])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k2_xboole_0(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X4,X5,X6)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_49]),c_0_49])).

cnf(c_0_52,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X5,X6,X7)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_49]),c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.026 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t58_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 0.13/0.37  fof(t78_enumset1, axiom, ![X1, X2, X3]:k3_enumset1(X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_enumset1)).
% 0.13/0.37  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 0.13/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.37  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_enumset1)).
% 0.13/0.37  fof(t59_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_enumset1)).
% 0.13/0.37  fof(l57_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 0.13/0.37  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.13/0.37  fof(t53_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_enumset1)).
% 0.13/0.37  fof(t81_enumset1, conjecture, ![X1, X2, X3, X4, X5, X6]:k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 0.13/0.37  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 0.13/0.37  fof(c_0_11, plain, ![X38, X39, X40, X41, X42, X43, X44]:k5_enumset1(X38,X39,X40,X41,X42,X43,X44)=k2_xboole_0(k1_enumset1(X38,X39,X40),k2_enumset1(X41,X42,X43,X44)), inference(variable_rename,[status(thm)],[t58_enumset1])).
% 0.13/0.37  fof(c_0_12, plain, ![X55, X56, X57]:k3_enumset1(X55,X55,X55,X56,X57)=k1_enumset1(X55,X56,X57), inference(variable_rename,[status(thm)],[t78_enumset1])).
% 0.13/0.37  fof(c_0_13, plain, ![X22, X23, X24, X25]:k2_enumset1(X22,X23,X24,X25)=k2_xboole_0(k1_tarski(X22),k1_enumset1(X23,X24,X25)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.13/0.37  fof(c_0_14, plain, ![X52]:k2_tarski(X52,X52)=k1_tarski(X52), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.37  fof(c_0_15, plain, ![X53, X54]:k2_enumset1(X53,X53,X53,X54)=k2_tarski(X53,X54), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.13/0.37  fof(c_0_16, plain, ![X45, X46, X47, X48, X49, X50, X51]:k5_enumset1(X45,X46,X47,X48,X49,X50,X51)=k2_xboole_0(k2_enumset1(X45,X46,X47,X48),k1_enumset1(X49,X50,X51)), inference(variable_rename,[status(thm)],[t59_enumset1])).
% 0.13/0.37  cnf(c_0_17, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_enumset1(X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_18, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  fof(c_0_19, plain, ![X9, X10, X11, X12, X13]:k3_enumset1(X9,X10,X11,X12,X13)=k2_xboole_0(k1_enumset1(X9,X10,X11),k2_tarski(X12,X13)), inference(variable_rename,[status(thm)],[l57_enumset1])).
% 0.13/0.37  cnf(c_0_20, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_22, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_23, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_24, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.37  fof(c_0_25, plain, ![X26, X27, X28, X29, X30, X31]:k4_enumset1(X26,X27,X28,X29,X30,X31)=k2_xboole_0(k1_tarski(X26),k3_enumset1(X27,X28,X29,X30,X31)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.13/0.37  cnf(c_0_26, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_enumset1(X1,X2,X3),k2_tarski(X4,X5))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.37  cnf(c_0_27, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_18])).
% 0.13/0.37  cnf(c_0_28, plain, (k2_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X6,X7))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_18]), c_0_24])).
% 0.13/0.37  fof(c_0_29, plain, ![X32, X33, X34, X35, X36, X37]:k4_enumset1(X32,X33,X34,X35,X36,X37)=k2_xboole_0(k1_enumset1(X32,X33,X34),k1_enumset1(X35,X36,X37)), inference(variable_rename,[status(thm)],[t53_enumset1])).
% 0.13/0.37  cnf(c_0_30, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_31, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k2_enumset1(X4,X4,X4,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_22]), c_0_18])).
% 0.13/0.37  cnf(c_0_32, plain, (k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k2_enumset1(X1,X2,X3,X4))=k2_enumset1(X1,X2,X3,X4)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.37  cnf(c_0_33, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.37  cnf(c_0_34, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_21]), c_0_22])).
% 0.13/0.37  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k2_enumset1(X1,X1,X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.37  cnf(c_0_36, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6))=k2_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),k3_enumset1(X4,X4,X4,X5,X6))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_18]), c_0_18]), c_0_34])).
% 0.13/0.37  cnf(c_0_37, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X3))=k2_enumset1(X1,X2,X2,X3)), inference(spm,[status(thm)],[c_0_27, c_0_35])).
% 0.13/0.37  cnf(c_0_38, plain, (k3_enumset1(X1,X2,X2,X2,X3)=k2_enumset1(X1,X2,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_35]), c_0_35]), c_0_31]), c_0_37])).
% 0.13/0.37  cnf(c_0_39, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X2,X3,X4))=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_32, c_0_35])).
% 0.13/0.37  cnf(c_0_40, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X3,X3,X4))=k3_enumset1(X1,X2,X3,X3,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_38]), c_0_38]), c_0_31])).
% 0.13/0.37  cnf(c_0_41, plain, (k3_enumset1(X1,X1,X2,X2,X3)=k2_enumset1(X1,X2,X2,X3)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.37  fof(c_0_42, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(assume_negation,[status(cth)],[t81_enumset1])).
% 0.13/0.37  cnf(c_0_43, plain, (k3_enumset1(X1,X2,X3,X3,X4)=k3_enumset1(X1,X2,X2,X3,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_41]), c_0_40]), c_0_38]), c_0_31])).
% 0.13/0.37  fof(c_0_44, negated_conjecture, k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).
% 0.13/0.37  fof(c_0_45, plain, ![X14, X15, X16, X17, X18, X19, X20, X21]:k6_enumset1(X14,X15,X16,X17,X18,X19,X20,X21)=k2_xboole_0(k2_enumset1(X14,X15,X16,X17),k2_enumset1(X18,X19,X20,X21)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.13/0.37  cnf(c_0_46, plain, (k3_enumset1(X1,X2,X3,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_43]), c_0_41]), c_0_40])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)!=k4_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.37  cnf(c_0_48, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.37  cnf(c_0_49, plain, (k3_enumset1(X1,X2,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_43, c_0_46])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (k2_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0),k2_enumset1(esk3_0,esk4_0,esk5_0,esk6_0))!=k2_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_34]), c_0_48])).
% 0.13/0.37  cnf(c_0_51, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6))=k2_xboole_0(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X4,X5,X6))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_49]), c_0_49])).
% 0.13/0.37  cnf(c_0_52, plain, (k2_xboole_0(k2_enumset1(X1,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X5,X6,X7))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_49]), c_0_49])).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_52])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 54
% 0.13/0.37  # Proof object clause steps            : 31
% 0.13/0.37  # Proof object formula steps           : 23
% 0.13/0.37  # Proof object conjectures             : 6
% 0.13/0.37  # Proof object clause conjectures      : 3
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 11
% 0.13/0.37  # Proof object initial formulas used   : 11
% 0.13/0.37  # Proof object generating inferences   : 8
% 0.13/0.37  # Proof object simplifying inferences  : 34
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 11
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 11
% 0.13/0.37  # Removed in clause preprocessing      : 6
% 0.13/0.37  # Initial clauses in saturation        : 5
% 0.13/0.37  # Processed clauses                    : 39
% 0.13/0.37  # ...of these trivial                  : 2
% 0.13/0.37  # ...subsumed                          : 8
% 0.13/0.37  # ...remaining for further processing  : 29
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 12
% 0.13/0.37  # Generated clauses                    : 130
% 0.13/0.37  # ...of the previous two non-trivial   : 78
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 130
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 12
% 0.13/0.37  #    Positive orientable unit clauses  : 9
% 0.13/0.37  #    Positive unorientable unit clauses: 3
% 0.13/0.37  #    Negative unit clauses             : 0
% 0.13/0.37  #    Non-unit-clauses                  : 0
% 0.13/0.37  # Current number of unprocessed clauses: 34
% 0.13/0.37  # ...number of literals in the above   : 34
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 23
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 0
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 5
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 146
% 0.13/0.37  # BW rewrite match successes           : 46
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1691
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.027 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
