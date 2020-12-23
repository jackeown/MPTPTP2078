%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:35:43 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 512 expanded)
%              Number of clauses        :   35 ( 203 expanded)
%              Number of leaves         :   13 ( 154 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 ( 512 expanded)
%              Number of equality atoms :   61 ( 511 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t73_enumset1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t51_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(c_0_13,plain,(
    ! [X12,X13,X14] : k2_xboole_0(k2_xboole_0(X12,X13),X14) = k2_xboole_0(k2_xboole_0(X12,X14),k2_xboole_0(X13,X14)) ),
    inference(variable_rename,[status(thm)],[t5_xboole_1])).

fof(c_0_14,plain,(
    ! [X9,X10,X11] : k2_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(X9,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

fof(c_0_15,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_16,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X2))) = k2_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])).

fof(c_0_20,plain,(
    ! [X27,X28,X29,X30,X31] : k3_enumset1(X27,X28,X29,X30,X31) = k2_xboole_0(k2_enumset1(X27,X28,X29,X30),k1_tarski(X31)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

fof(c_0_21,plain,(
    ! [X38] : k2_tarski(X38,X38) = k1_tarski(X38) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X39,X40] : k1_enumset1(X39,X39,X40) = k2_tarski(X39,X40) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X41,X42,X43] : k2_enumset1(X41,X41,X42,X43) = k1_enumset1(X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X44,X45,X46,X47] : k3_enumset1(X44,X44,X45,X46,X47) = k2_enumset1(X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_25,plain,(
    ! [X17,X18,X19,X20,X21] : k3_enumset1(X17,X18,X19,X20,X21) = k2_xboole_0(k1_tarski(X17),k2_enumset1(X18,X19,X20,X21)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_27,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3))) = k2_xboole_0(X3,k2_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_17]),c_0_17])).

fof(c_0_28,plain,(
    ! [X22,X23,X24,X25,X26] : k3_enumset1(X22,X23,X24,X25,X26) = k2_xboole_0(k2_tarski(X22,X23),k1_enumset1(X24,X25,X26)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

fof(c_0_29,plain,(
    ! [X15,X16] : k2_tarski(X15,X16) = k2_tarski(X16,X15) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_30,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(assume_negation,[status(cth)],[t73_enumset1])).

fof(c_0_37,plain,(
    ! [X32,X33,X34,X35,X36,X37] : k4_enumset1(X32,X33,X34,X35,X36,X37) = k2_xboole_0(k1_tarski(X32),k3_enumset1(X33,X34,X35,X36,X37)) ),
    inference(variable_rename,[status(thm)],[t51_enumset1])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X3))) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_26])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_27])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,k2_xboole_0(X2,X3))) = k2_xboole_0(X2,k2_xboole_0(X3,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_18]),c_0_17])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X5,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_44,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X3,X4,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_34])).

fof(c_0_45,negated_conjecture,(
    k4_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_46,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X2)) = k2_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_17]),c_0_17]),c_0_40]),c_0_40])).

cnf(c_0_48,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X4,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_49,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_50,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X2,X3,X4,X5,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_43]),c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k4_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) != k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_53,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k3_enumset1(X5,X5,X5,X5,X5),k3_enumset1(X5,X1,X2,X3,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_44]),c_0_43])).

cnf(c_0_54,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X2,X3,X4,X5)) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_43]),c_0_44]),c_0_43])).

cnf(c_0_55,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X2,X1,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_48])).

cnf(c_0_56,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X3,X4,X5,X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k2_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)) != k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X2,X3,X4,X5)) = k3_enumset1(X2,X3,X4,X5,X1) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X5,X4,X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X1,X3,X4,X5,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n017.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 19:35:31 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.18/0.49  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.18/0.49  #
% 0.18/0.49  # Preprocessing time       : 0.026 s
% 0.18/0.49  # Presaturation interreduction done
% 0.18/0.49  
% 0.18/0.49  # Proof found!
% 0.18/0.49  # SZS status Theorem
% 0.18/0.49  # SZS output start CNFRefutation
% 0.18/0.49  fof(t5_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_1)).
% 0.18/0.49  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.18/0.49  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.18/0.49  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 0.18/0.49  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.49  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.49  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.49  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.49  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.18/0.49  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 0.18/0.49  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.18/0.49  fof(t73_enumset1, conjecture, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.18/0.49  fof(t51_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 0.18/0.49  fof(c_0_13, plain, ![X12, X13, X14]:k2_xboole_0(k2_xboole_0(X12,X13),X14)=k2_xboole_0(k2_xboole_0(X12,X14),k2_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[t5_xboole_1])).
% 0.18/0.49  fof(c_0_14, plain, ![X9, X10, X11]:k2_xboole_0(k2_xboole_0(X9,X10),X11)=k2_xboole_0(X9,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.18/0.49  fof(c_0_15, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.18/0.49  cnf(c_0_16, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.49  cnf(c_0_17, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.49  cnf(c_0_18, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.49  cnf(c_0_19, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X2)))=k2_xboole_0(X1,k2_xboole_0(X3,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_17])).
% 0.18/0.49  fof(c_0_20, plain, ![X27, X28, X29, X30, X31]:k3_enumset1(X27,X28,X29,X30,X31)=k2_xboole_0(k2_enumset1(X27,X28,X29,X30),k1_tarski(X31)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.18/0.49  fof(c_0_21, plain, ![X38]:k2_tarski(X38,X38)=k1_tarski(X38), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.49  fof(c_0_22, plain, ![X39, X40]:k1_enumset1(X39,X39,X40)=k2_tarski(X39,X40), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.49  fof(c_0_23, plain, ![X41, X42, X43]:k2_enumset1(X41,X41,X42,X43)=k1_enumset1(X41,X42,X43), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.49  fof(c_0_24, plain, ![X44, X45, X46, X47]:k3_enumset1(X44,X44,X45,X46,X47)=k2_enumset1(X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.49  fof(c_0_25, plain, ![X17, X18, X19, X20, X21]:k3_enumset1(X17,X18,X19,X20,X21)=k2_xboole_0(k1_tarski(X17),k2_enumset1(X18,X19,X20,X21)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.18/0.49  cnf(c_0_26, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X3,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_18, c_0_17])).
% 0.18/0.49  cnf(c_0_27, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X1,X3)))=k2_xboole_0(X3,k2_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_17]), c_0_17])).
% 0.18/0.49  fof(c_0_28, plain, ![X22, X23, X24, X25, X26]:k3_enumset1(X22,X23,X24,X25,X26)=k2_xboole_0(k2_tarski(X22,X23),k1_enumset1(X24,X25,X26)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 0.18/0.49  fof(c_0_29, plain, ![X15, X16]:k2_tarski(X15,X16)=k2_tarski(X16,X15), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.18/0.49  cnf(c_0_30, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.49  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.49  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.49  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.49  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.49  cnf(c_0_35, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.49  fof(c_0_36, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(assume_negation,[status(cth)],[t73_enumset1])).
% 0.18/0.49  fof(c_0_37, plain, ![X32, X33, X34, X35, X36, X37]:k4_enumset1(X32,X33,X34,X35,X36,X37)=k2_xboole_0(k1_tarski(X32),k3_enumset1(X33,X34,X35,X36,X37)), inference(variable_rename,[status(thm)],[t51_enumset1])).
% 0.18/0.49  cnf(c_0_38, plain, (k2_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X3)))=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_19, c_0_26])).
% 0.18/0.49  cnf(c_0_39, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X2,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_19, c_0_27])).
% 0.18/0.49  cnf(c_0_40, plain, (k2_xboole_0(X1,k2_xboole_0(X1,k2_xboole_0(X2,X3)))=k2_xboole_0(X2,k2_xboole_0(X3,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_18]), c_0_17])).
% 0.18/0.49  cnf(c_0_41, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.49  cnf(c_0_42, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.49  cnf(c_0_43, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X5,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_34])).
% 0.18/0.49  cnf(c_0_44, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X3,X4,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_34])).
% 0.18/0.49  fof(c_0_45, negated_conjecture, k4_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 0.18/0.49  cnf(c_0_46, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k1_tarski(X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.49  cnf(c_0_47, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X2))=k2_xboole_0(X1,k2_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_17]), c_0_17]), c_0_40]), c_0_40])).
% 0.18/0.49  cnf(c_0_48, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X4,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 0.18/0.49  cnf(c_0_49, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 0.18/0.49  cnf(c_0_50, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X2,X3,X4,X5,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_43]), c_0_44])).
% 0.18/0.49  cnf(c_0_51, negated_conjecture, (k4_enumset1(esk1_0,esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)!=k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.49  cnf(c_0_52, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X3,X4,X5,X6))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.18/0.49  cnf(c_0_53, plain, (k2_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X2,X3,X4,X5))=k2_xboole_0(k3_enumset1(X5,X5,X5,X5,X5),k3_enumset1(X5,X1,X2,X3,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_44]), c_0_43])).
% 0.18/0.49  cnf(c_0_54, plain, (k2_xboole_0(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X2,X3,X4,X5))=k3_enumset1(X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_43]), c_0_44]), c_0_43])).
% 0.18/0.49  cnf(c_0_55, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X2,X1,X3,X4,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_48])).
% 0.18/0.49  cnf(c_0_56, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X3,X4,X5,X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_50])).
% 0.18/0.49  cnf(c_0_57, negated_conjecture, (k2_xboole_0(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0))!=k3_enumset1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.18/0.49  cnf(c_0_58, plain, (k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X2,X3,X4,X5))=k3_enumset1(X2,X3,X4,X5,X1)), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.18/0.49  cnf(c_0_59, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X5,X4,X1,X2,X3)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.18/0.49  cnf(c_0_60, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X1,X3,X4,X5,X2)), inference(spm,[status(thm)],[c_0_50, c_0_55])).
% 0.18/0.49  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60])]), ['proof']).
% 0.18/0.49  # SZS output end CNFRefutation
% 0.18/0.49  # Proof object total steps             : 62
% 0.18/0.49  # Proof object clause steps            : 35
% 0.18/0.49  # Proof object formula steps           : 27
% 0.18/0.49  # Proof object conjectures             : 6
% 0.18/0.49  # Proof object clause conjectures      : 3
% 0.18/0.49  # Proof object formula conjectures     : 3
% 0.18/0.49  # Proof object initial clauses used    : 13
% 0.18/0.49  # Proof object initial formulas used   : 13
% 0.18/0.49  # Proof object generating inferences   : 13
% 0.18/0.49  # Proof object simplifying inferences  : 45
% 0.18/0.49  # Training examples: 0 positive, 0 negative
% 0.18/0.49  # Parsed axioms                        : 13
% 0.18/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.49  # Initial clauses                      : 13
% 0.18/0.49  # Removed in clause preprocessing      : 5
% 0.18/0.49  # Initial clauses in saturation        : 8
% 0.18/0.49  # Processed clauses                    : 1392
% 0.18/0.49  # ...of these trivial                  : 330
% 0.18/0.49  # ...subsumed                          : 936
% 0.18/0.49  # ...remaining for further processing  : 126
% 0.18/0.49  # Other redundant clauses eliminated   : 0
% 0.18/0.49  # Clauses deleted for lack of memory   : 0
% 0.18/0.49  # Backward-subsumed                    : 4
% 0.18/0.49  # Backward-rewritten                   : 6
% 0.18/0.49  # Generated clauses                    : 19654
% 0.18/0.49  # ...of the previous two non-trivial   : 16662
% 0.18/0.49  # Contextual simplify-reflections      : 0
% 0.18/0.49  # Paramodulations                      : 19654
% 0.18/0.49  # Factorizations                       : 0
% 0.18/0.49  # Equation resolutions                 : 0
% 0.18/0.49  # Propositional unsat checks           : 0
% 0.18/0.49  #    Propositional check models        : 0
% 0.18/0.49  #    Propositional check unsatisfiable : 0
% 0.18/0.49  #    Propositional clauses             : 0
% 0.18/0.49  #    Propositional clauses after purity: 0
% 0.18/0.49  #    Propositional unsat core size     : 0
% 0.18/0.49  #    Propositional preprocessing time  : 0.000
% 0.18/0.49  #    Propositional encoding time       : 0.000
% 0.18/0.49  #    Propositional solver time         : 0.000
% 0.18/0.49  #    Success case prop preproc time    : 0.000
% 0.18/0.49  #    Success case prop encoding time   : 0.000
% 0.18/0.49  #    Success case prop solver time     : 0.000
% 0.18/0.49  # Current number of processed clauses  : 108
% 0.18/0.49  #    Positive orientable unit clauses  : 36
% 0.18/0.49  #    Positive unorientable unit clauses: 72
% 0.18/0.49  #    Negative unit clauses             : 0
% 0.18/0.49  #    Non-unit-clauses                  : 0
% 0.18/0.49  # Current number of unprocessed clauses: 15284
% 0.18/0.49  # ...number of literals in the above   : 15284
% 0.18/0.49  # Current number of archived formulas  : 0
% 0.18/0.49  # Current number of archived clauses   : 23
% 0.18/0.49  # Clause-clause subsumption calls (NU) : 0
% 0.18/0.49  # Rec. Clause-clause subsumption calls : 0
% 0.18/0.49  # Non-unit clause-clause subsumptions  : 0
% 0.18/0.49  # Unit Clause-clause subsumption calls : 3262
% 0.18/0.49  # Rewrite failures with RHS unbound    : 0
% 0.18/0.49  # BW rewrite match attempts            : 7845
% 0.18/0.49  # BW rewrite match successes           : 2430
% 0.18/0.49  # Condensation attempts                : 0
% 0.18/0.49  # Condensation successes               : 0
% 0.18/0.49  # Termbank termtop insertions          : 114581
% 0.18/0.49  
% 0.18/0.49  # -------------------------------------------------
% 0.18/0.49  # User time                : 0.153 s
% 0.18/0.49  # System time              : 0.017 s
% 0.18/0.49  # Total time               : 0.170 s
% 0.18/0.49  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
