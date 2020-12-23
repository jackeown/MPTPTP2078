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
% DateTime   : Thu Dec  3 10:33:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  94 expanded)
%              Number of clauses        :   30 (  41 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 (  94 expanded)
%              Number of equality atoms :   60 (  93 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_xboole_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t93_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(t6_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(assume_negation,[status(cth)],[t94_xboole_1])).

fof(c_0_16,negated_conjecture,(
    k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_18,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_19,plain,(
    ! [X30,X31,X32] : k3_xboole_0(X30,k4_xboole_0(X31,X32)) = k4_xboole_0(k3_xboole_0(X30,X31),X32) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

fof(c_0_20,plain,(
    ! [X12,X13] : k3_xboole_0(X12,k2_xboole_0(X12,X13)) = X12 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_21,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X21,X22,X23] : k4_xboole_0(k4_xboole_0(X21,X22),X23) = k4_xboole_0(X21,k2_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_27,plain,(
    ! [X8,X9,X10] : k4_xboole_0(X8,k3_xboole_0(X9,X10)) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,X10)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

fof(c_0_28,plain,(
    ! [X16] : k3_xboole_0(X16,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k2_xboole_0(X24,X25)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_31,plain,(
    ! [X45,X46] : k2_xboole_0(X45,X46) = k2_xboole_0(k5_xboole_0(X45,X46),k3_xboole_0(X45,X46)) ),
    inference(variable_rename,[status(thm)],[t93_xboole_1])).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_23])).

cnf(c_0_33,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X38,X39] : k2_xboole_0(X38,k2_xboole_0(X38,X39)) = k2_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t6_xboole_1])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_22]),c_0_22])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_41,plain,(
    ! [X33,X34,X35] : k2_xboole_0(k2_xboole_0(X33,X34),X35) = k2_xboole_0(X33,k2_xboole_0(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_42,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_22])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_22])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_49,plain,(
    ! [X11] : k2_xboole_0(X11,k1_xboole_0) = X11 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_50,plain,(
    ! [X17,X18] : k2_xboole_0(X17,k4_xboole_0(X18,X17)) = k2_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_22]),c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(esk1_0,k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)))) != k2_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_36]),c_0_44])).

cnf(c_0_54,plain,
    ( k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))) = k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_51])).

cnf(c_0_59,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.56  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.56  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.56  #
% 0.20/0.56  # Preprocessing time       : 0.026 s
% 0.20/0.56  # Presaturation interreduction done
% 0.20/0.56  
% 0.20/0.56  # Proof found!
% 0.20/0.56  # SZS status Theorem
% 0.20/0.56  # SZS output start CNFRefutation
% 0.20/0.56  fof(t94_xboole_1, conjecture, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.20/0.56  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.56  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 0.20/0.56  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.20/0.56  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.20/0.56  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.56  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.20/0.56  fof(l36_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l36_xboole_1)).
% 0.20/0.56  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.56  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.20/0.56  fof(t93_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 0.20/0.56  fof(t6_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 0.20/0.56  fof(t4_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 0.20/0.56  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.56  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.20/0.56  fof(c_0_15, negated_conjecture, ~(![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(assume_negation,[status(cth)],[t94_xboole_1])).
% 0.20/0.56  fof(c_0_16, negated_conjecture, k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.56  fof(c_0_17, plain, ![X28, X29]:k4_xboole_0(X28,k4_xboole_0(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.56  fof(c_0_18, plain, ![X6, X7]:k5_xboole_0(X6,X7)=k2_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 0.20/0.56  fof(c_0_19, plain, ![X30, X31, X32]:k3_xboole_0(X30,k4_xboole_0(X31,X32))=k4_xboole_0(k3_xboole_0(X30,X31),X32), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.20/0.56  fof(c_0_20, plain, ![X12, X13]:k3_xboole_0(X12,k2_xboole_0(X12,X13))=X12, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.20/0.56  cnf(c_0_21, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k5_xboole_0(k5_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.56  cnf(c_0_22, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.56  cnf(c_0_23, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.56  fof(c_0_24, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.56  cnf(c_0_25, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.56  fof(c_0_26, plain, ![X21, X22, X23]:k4_xboole_0(k4_xboole_0(X21,X22),X23)=k4_xboole_0(X21,k2_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.20/0.56  fof(c_0_27, plain, ![X8, X9, X10]:k4_xboole_0(X8,k3_xboole_0(X9,X10))=k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,X10)), inference(variable_rename,[status(thm)],[l36_xboole_1])).
% 0.20/0.56  fof(c_0_28, plain, ![X16]:k3_xboole_0(X16,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.56  cnf(c_0_29, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.56  fof(c_0_30, plain, ![X24, X25]:k4_xboole_0(X24,k2_xboole_0(X24,X25))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.20/0.56  fof(c_0_31, plain, ![X45, X46]:k2_xboole_0(X45,X46)=k2_xboole_0(k5_xboole_0(X45,X46),k3_xboole_0(X45,X46)), inference(variable_rename,[status(thm)],[t93_xboole_1])).
% 0.20/0.56  cnf(c_0_32, negated_conjecture, (k2_xboole_0(esk1_0,esk2_0)!=k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))),k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_23])).
% 0.20/0.56  cnf(c_0_33, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.56  fof(c_0_34, plain, ![X38, X39]:k2_xboole_0(X38,k2_xboole_0(X38,X39))=k2_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t6_xboole_1])).
% 0.20/0.56  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_22]), c_0_22])).
% 0.20/0.56  cnf(c_0_36, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.56  cnf(c_0_37, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.56  cnf(c_0_38, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.56  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_29, c_0_22])).
% 0.20/0.56  cnf(c_0_40, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.56  fof(c_0_41, plain, ![X33, X34, X35]:k2_xboole_0(k2_xboole_0(X33,X34),X35)=k2_xboole_0(X33,k2_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[t4_xboole_1])).
% 0.20/0.56  cnf(c_0_42, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.56  cnf(c_0_43, negated_conjecture, (k2_xboole_0(k4_xboole_0(k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0)),k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))))!=k2_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.56  cnf(c_0_44, plain, (k2_xboole_0(X1,k2_xboole_0(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.56  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),X3))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.56  cnf(c_0_46, plain, (k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(rw,[status(thm)],[c_0_37, c_0_22])).
% 0.20/0.56  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_38, c_0_22])).
% 0.20/0.56  cnf(c_0_48, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.56  fof(c_0_49, plain, ![X11]:k2_xboole_0(X11,k1_xboole_0)=X11, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.56  fof(c_0_50, plain, ![X17, X18]:k2_xboole_0(X17,k4_xboole_0(X18,X17))=k2_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.20/0.56  cnf(c_0_51, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.56  cnf(c_0_52, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_22]), c_0_23])).
% 0.20/0.56  cnf(c_0_53, negated_conjecture, (k2_xboole_0(k4_xboole_0(esk1_0,k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(esk1_0,esk2_0),k4_xboole_0(esk2_0,esk1_0)),k4_xboole_0(esk1_0,k4_xboole_0(esk1_0,esk2_0))))!=k2_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_36]), c_0_44])).
% 0.20/0.56  cnf(c_0_54, plain, (k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)))=k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.56  cnf(c_0_55, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.56  cnf(c_0_56, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.56  cnf(c_0_57, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.56  cnf(c_0_58, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X3,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_33, c_0_51])).
% 0.20/0.56  cnf(c_0_59, plain, (k2_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X1,k4_xboole_0(X1,X2))))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_52, c_0_51])).
% 0.20/0.56  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58]), c_0_59])]), ['proof']).
% 0.20/0.56  # SZS output end CNFRefutation
% 0.20/0.56  # Proof object total steps             : 61
% 0.20/0.56  # Proof object clause steps            : 30
% 0.20/0.56  # Proof object formula steps           : 31
% 0.20/0.56  # Proof object conjectures             : 8
% 0.20/0.56  # Proof object clause conjectures      : 5
% 0.20/0.56  # Proof object formula conjectures     : 3
% 0.20/0.56  # Proof object initial clauses used    : 15
% 0.20/0.56  # Proof object initial formulas used   : 15
% 0.20/0.56  # Proof object generating inferences   : 2
% 0.20/0.56  # Proof object simplifying inferences  : 24
% 0.20/0.56  # Training examples: 0 positive, 0 negative
% 0.20/0.56  # Parsed axioms                        : 21
% 0.20/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.56  # Initial clauses                      : 21
% 0.20/0.56  # Removed in clause preprocessing      : 2
% 0.20/0.56  # Initial clauses in saturation        : 19
% 0.20/0.56  # Processed clauses                    : 1084
% 0.20/0.56  # ...of these trivial                  : 68
% 0.20/0.56  # ...subsumed                          : 803
% 0.20/0.56  # ...remaining for further processing  : 213
% 0.20/0.56  # Other redundant clauses eliminated   : 267
% 0.20/0.56  # Clauses deleted for lack of memory   : 0
% 0.20/0.56  # Backward-subsumed                    : 14
% 0.20/0.56  # Backward-rewritten                   : 27
% 0.20/0.56  # Generated clauses                    : 18521
% 0.20/0.56  # ...of the previous two non-trivial   : 14734
% 0.20/0.56  # Contextual simplify-reflections      : 0
% 0.20/0.56  # Paramodulations                      : 18254
% 0.20/0.56  # Factorizations                       : 0
% 0.20/0.56  # Equation resolutions                 : 267
% 0.20/0.56  # Propositional unsat checks           : 0
% 0.20/0.56  #    Propositional check models        : 0
% 0.20/0.56  #    Propositional check unsatisfiable : 0
% 0.20/0.56  #    Propositional clauses             : 0
% 0.20/0.56  #    Propositional clauses after purity: 0
% 0.20/0.56  #    Propositional unsat core size     : 0
% 0.20/0.56  #    Propositional preprocessing time  : 0.000
% 0.20/0.56  #    Propositional encoding time       : 0.000
% 0.20/0.56  #    Propositional solver time         : 0.000
% 0.20/0.56  #    Success case prop preproc time    : 0.000
% 0.20/0.56  #    Success case prop encoding time   : 0.000
% 0.20/0.56  #    Success case prop solver time     : 0.000
% 0.20/0.56  # Current number of processed clauses  : 153
% 0.20/0.56  #    Positive orientable unit clauses  : 63
% 0.20/0.56  #    Positive unorientable unit clauses: 20
% 0.20/0.56  #    Negative unit clauses             : 5
% 0.20/0.56  #    Non-unit-clauses                  : 65
% 0.20/0.56  # Current number of unprocessed clauses: 13650
% 0.20/0.56  # ...number of literals in the above   : 18064
% 0.20/0.56  # Current number of archived formulas  : 0
% 0.20/0.56  # Current number of archived clauses   : 62
% 0.20/0.56  # Clause-clause subsumption calls (NU) : 2148
% 0.20/0.56  # Rec. Clause-clause subsumption calls : 1893
% 0.20/0.56  # Non-unit clause-clause subsumptions  : 369
% 0.20/0.56  # Unit Clause-clause subsumption calls : 220
% 0.20/0.56  # Rewrite failures with RHS unbound    : 0
% 0.20/0.56  # BW rewrite match attempts            : 595
% 0.20/0.56  # BW rewrite match successes           : 126
% 0.20/0.56  # Condensation attempts                : 0
% 0.20/0.56  # Condensation successes               : 0
% 0.20/0.56  # Termbank termtop insertions          : 262995
% 0.20/0.56  
% 0.20/0.56  # -------------------------------------------------
% 0.20/0.56  # User time                : 0.201 s
% 0.20/0.56  # System time              : 0.014 s
% 0.20/0.56  # Total time               : 0.216 s
% 0.20/0.56  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
