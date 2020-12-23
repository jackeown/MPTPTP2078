%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:19 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 511 expanded)
%              Number of clauses        :   32 ( 202 expanded)
%              Number of leaves         :   13 ( 154 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 ( 519 expanded)
%              Number of equality atoms :   66 ( 518 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(t10_setfam_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(X1,X2)) != k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t12_setfam_1,conjecture,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(c_0_13,plain,(
    ! [X35,X36] : k3_tarski(k2_tarski(X35,X36)) = k2_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X37,X38] : k2_xboole_0(k1_tarski(X37),X38) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X24] : k2_tarski(X24,X24) = k1_tarski(X24) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X27,X28,X29] : k2_enumset1(X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X19,X20,X21,X22,X23] : k3_enumset1(X19,X20,X21,X22,X23) = k2_xboole_0(k1_tarski(X19),k2_enumset1(X20,X21,X22,X23)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_21,plain,(
    ! [X30,X31,X32,X33,X34] : k4_enumset1(X30,X30,X31,X32,X33,X34) = k3_enumset1(X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_22,plain,(
    ! [X15,X16,X17,X18] : k2_enumset1(X15,X16,X17,X18) = k2_xboole_0(k1_tarski(X15),k1_enumset1(X16,X17,X18)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_23,plain,(
    ! [X12,X13,X14] : k1_enumset1(X12,X13,X14) = k2_xboole_0(k2_tarski(X12,X13),k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_24,plain,(
    ! [X8,X9,X10,X11] : k2_enumset1(X8,X9,X10,X11) = k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X10,X11)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

cnf(c_0_25,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X39,X40] :
      ( X39 = k1_xboole_0
      | X40 = k1_xboole_0
      | k1_setfam_1(k2_xboole_0(X39,X40)) = k3_xboole_0(k1_setfam_1(X39),k1_setfam_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).

fof(c_0_35,plain,(
    ! [X41] : k1_setfam_1(k1_tarski(X41)) = X41 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

cnf(c_0_36,plain,
    ( k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_18]),c_0_27]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_26]),c_0_18]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_30])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_26]),c_0_18]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_26]),c_0_18]),c_0_18]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_40,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_18]),c_0_18]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k4_enumset1(X1,X1,X2,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_45,plain,
    ( k2_enumset1(X1,X2,X3,X3) = k2_enumset1(X1,X1,X2,X3) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_46,negated_conjecture,(
    ~ ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t12_setfam_1])).

cnf(c_0_47,plain,
    ( X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k1_setfam_1(k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_27]),c_0_28])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_26]),c_0_18]),c_0_28])).

cnf(c_0_49,plain,
    ( k2_enumset1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( k2_enumset1(X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_45]),c_0_40])).

fof(c_0_51,negated_conjecture,(
    k1_setfam_1(k2_tarski(esk1_0,esk2_0)) != k3_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_46])])])).

cnf(c_0_52,plain,
    ( k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5)) = k3_xboole_0(X1,k1_setfam_1(k2_enumset1(X2,X3,X4,X5))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_37]),c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk1_0,esk2_0)) != k3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_54,plain,
    ( k1_setfam_1(k2_enumset1(X1,X2,X2,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_48]),c_0_44])).

cnf(c_0_55,plain,
    ( k2_enumset1(X1,X2,X2,X2) = k2_enumset1(X1,X1,X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0)) != k3_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_18]),c_0_28])).

cnf(c_0_57,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:23:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.22/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.22/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.22/0.39  #
% 0.22/0.39  # Preprocessing time       : 0.026 s
% 0.22/0.39  # Presaturation interreduction done
% 0.22/0.39  
% 0.22/0.39  # Proof found!
% 0.22/0.39  # SZS status Theorem
% 0.22/0.39  # SZS output start CNFRefutation
% 0.22/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.22/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.22/0.39  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.22/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.22/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.22/0.39  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 0.22/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.22/0.39  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 0.22/0.39  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 0.22/0.39  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.22/0.39  fof(t10_setfam_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&k1_setfam_1(k2_xboole_0(X1,X2))!=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 0.22/0.39  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.22/0.39  fof(t12_setfam_1, conjecture, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.22/0.39  fof(c_0_13, plain, ![X35, X36]:k3_tarski(k2_tarski(X35,X36))=k2_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.22/0.39  fof(c_0_14, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.22/0.39  fof(c_0_15, plain, ![X37, X38]:k2_xboole_0(k1_tarski(X37),X38)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.22/0.39  fof(c_0_16, plain, ![X24]:k2_tarski(X24,X24)=k1_tarski(X24), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.22/0.39  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.22/0.39  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.22/0.39  fof(c_0_19, plain, ![X27, X28, X29]:k2_enumset1(X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.22/0.39  fof(c_0_20, plain, ![X19, X20, X21, X22, X23]:k3_enumset1(X19,X20,X21,X22,X23)=k2_xboole_0(k1_tarski(X19),k2_enumset1(X20,X21,X22,X23)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.22/0.39  fof(c_0_21, plain, ![X30, X31, X32, X33, X34]:k4_enumset1(X30,X30,X31,X32,X33,X34)=k3_enumset1(X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.22/0.39  fof(c_0_22, plain, ![X15, X16, X17, X18]:k2_enumset1(X15,X16,X17,X18)=k2_xboole_0(k1_tarski(X15),k1_enumset1(X16,X17,X18)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 0.22/0.39  fof(c_0_23, plain, ![X12, X13, X14]:k1_enumset1(X12,X13,X14)=k2_xboole_0(k2_tarski(X12,X13),k1_tarski(X14)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 0.22/0.39  fof(c_0_24, plain, ![X8, X9, X10, X11]:k2_enumset1(X8,X9,X10,X11)=k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X10,X11)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.22/0.39  cnf(c_0_25, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.39  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.39  cnf(c_0_27, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.22/0.39  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.22/0.39  cnf(c_0_29, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.22/0.39  cnf(c_0_30, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.22/0.39  cnf(c_0_31, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.22/0.39  cnf(c_0_32, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.22/0.39  cnf(c_0_33, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.22/0.39  fof(c_0_34, plain, ![X39, X40]:(X39=k1_xboole_0|X40=k1_xboole_0|k1_setfam_1(k2_xboole_0(X39,X40))=k3_xboole_0(k1_setfam_1(X39),k1_setfam_1(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).
% 0.22/0.39  fof(c_0_35, plain, ![X41]:k1_setfam_1(k1_tarski(X41))=X41, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 0.22/0.39  cnf(c_0_36, plain, (k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_18]), c_0_27]), c_0_28]), c_0_28]), c_0_28])).
% 0.22/0.39  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_26]), c_0_18]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_30])).
% 0.22/0.39  cnf(c_0_38, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_26]), c_0_18]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28])).
% 0.22/0.39  cnf(c_0_39, plain, (k2_enumset1(X1,X1,X2,X3)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_26]), c_0_18]), c_0_18]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_28])).
% 0.22/0.39  cnf(c_0_40, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2),k2_enumset1(X3,X3,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_18]), c_0_18]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28])).
% 0.22/0.39  cnf(c_0_41, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.22/0.39  cnf(c_0_42, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.22/0.39  cnf(c_0_43, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.22/0.39  cnf(c_0_44, plain, (k4_enumset1(X1,X1,X2,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_38, c_0_37])).
% 0.22/0.39  cnf(c_0_45, plain, (k2_enumset1(X1,X2,X3,X3)=k2_enumset1(X1,X1,X2,X3)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.22/0.39  fof(c_0_46, negated_conjecture, ~(![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t12_setfam_1])).
% 0.22/0.39  cnf(c_0_47, plain, (X2=k1_xboole_0|X1=k1_xboole_0|k1_setfam_1(k3_tarski(k2_enumset1(X1,X1,X1,X2)))=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_27]), c_0_28])).
% 0.22/0.39  cnf(c_0_48, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_26]), c_0_18]), c_0_28])).
% 0.22/0.39  cnf(c_0_49, plain, (k2_enumset1(X1,X2,X3,X4)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.22/0.39  cnf(c_0_50, plain, (k2_enumset1(X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_45]), c_0_40])).
% 0.22/0.39  fof(c_0_51, negated_conjecture, k1_setfam_1(k2_tarski(esk1_0,esk2_0))!=k3_xboole_0(esk1_0,esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_46])])])).
% 0.22/0.39  cnf(c_0_52, plain, (k1_setfam_1(k4_enumset1(X1,X1,X2,X3,X4,X5))=k3_xboole_0(X1,k1_setfam_1(k2_enumset1(X2,X3,X4,X5)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_37]), c_0_48]), c_0_49]), c_0_50])).
% 0.22/0.39  cnf(c_0_53, negated_conjecture, (k1_setfam_1(k2_tarski(esk1_0,esk2_0))!=k3_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.22/0.39  cnf(c_0_54, plain, (k1_setfam_1(k2_enumset1(X1,X2,X2,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_48]), c_0_44])).
% 0.22/0.39  cnf(c_0_55, plain, (k2_enumset1(X1,X2,X2,X2)=k2_enumset1(X1,X1,X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_45])).
% 0.22/0.39  cnf(c_0_56, negated_conjecture, (k1_setfam_1(k2_enumset1(esk1_0,esk1_0,esk1_0,esk2_0))!=k3_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_18]), c_0_28])).
% 0.22/0.39  cnf(c_0_57, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.22/0.39  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])]), ['proof']).
% 0.22/0.39  # SZS output end CNFRefutation
% 0.22/0.39  # Proof object total steps             : 59
% 0.22/0.39  # Proof object clause steps            : 32
% 0.22/0.39  # Proof object formula steps           : 27
% 0.22/0.39  # Proof object conjectures             : 6
% 0.22/0.39  # Proof object clause conjectures      : 3
% 0.22/0.39  # Proof object formula conjectures     : 3
% 0.22/0.39  # Proof object initial clauses used    : 13
% 0.22/0.39  # Proof object initial formulas used   : 13
% 0.22/0.39  # Proof object generating inferences   : 7
% 0.22/0.39  # Proof object simplifying inferences  : 53
% 0.22/0.39  # Training examples: 0 positive, 0 negative
% 0.22/0.39  # Parsed axioms                        : 14
% 0.22/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.39  # Initial clauses                      : 14
% 0.22/0.39  # Removed in clause preprocessing      : 5
% 0.22/0.39  # Initial clauses in saturation        : 9
% 0.22/0.39  # Processed clauses                    : 416
% 0.22/0.39  # ...of these trivial                  : 14
% 0.22/0.39  # ...subsumed                          : 344
% 0.22/0.39  # ...remaining for further processing  : 58
% 0.22/0.39  # Other redundant clauses eliminated   : 0
% 0.22/0.39  # Clauses deleted for lack of memory   : 0
% 0.22/0.39  # Backward-subsumed                    : 0
% 0.22/0.39  # Backward-rewritten                   : 6
% 0.22/0.39  # Generated clauses                    : 1199
% 0.22/0.39  # ...of the previous two non-trivial   : 678
% 0.22/0.39  # Contextual simplify-reflections      : 0
% 0.22/0.39  # Paramodulations                      : 1199
% 0.22/0.39  # Factorizations                       : 0
% 0.22/0.39  # Equation resolutions                 : 0
% 0.22/0.39  # Propositional unsat checks           : 0
% 0.22/0.39  #    Propositional check models        : 0
% 0.22/0.39  #    Propositional check unsatisfiable : 0
% 0.22/0.39  #    Propositional clauses             : 0
% 0.22/0.39  #    Propositional clauses after purity: 0
% 0.22/0.39  #    Propositional unsat core size     : 0
% 0.22/0.39  #    Propositional preprocessing time  : 0.000
% 0.22/0.39  #    Propositional encoding time       : 0.000
% 0.22/0.39  #    Propositional solver time         : 0.000
% 0.22/0.39  #    Success case prop preproc time    : 0.000
% 0.22/0.39  #    Success case prop encoding time   : 0.000
% 0.22/0.39  #    Success case prop solver time     : 0.000
% 0.22/0.39  # Current number of processed clauses  : 43
% 0.22/0.39  #    Positive orientable unit clauses  : 20
% 0.22/0.39  #    Positive unorientable unit clauses: 8
% 0.22/0.39  #    Negative unit clauses             : 9
% 0.22/0.39  #    Non-unit-clauses                  : 6
% 0.22/0.39  # Current number of unprocessed clauses: 260
% 0.22/0.39  # ...number of literals in the above   : 332
% 0.22/0.39  # Current number of archived formulas  : 0
% 0.22/0.39  # Current number of archived clauses   : 20
% 0.22/0.39  # Clause-clause subsumption calls (NU) : 27
% 0.22/0.39  # Rec. Clause-clause subsumption calls : 6
% 0.22/0.39  # Non-unit clause-clause subsumptions  : 6
% 0.22/0.39  # Unit Clause-clause subsumption calls : 89
% 0.22/0.39  # Rewrite failures with RHS unbound    : 0
% 0.22/0.39  # BW rewrite match attempts            : 359
% 0.22/0.39  # BW rewrite match successes           : 85
% 0.22/0.39  # Condensation attempts                : 0
% 0.22/0.39  # Condensation successes               : 0
% 0.22/0.39  # Termbank termtop insertions          : 8315
% 0.22/0.39  
% 0.22/0.39  # -------------------------------------------------
% 0.22/0.39  # User time                : 0.034 s
% 0.22/0.39  # System time              : 0.006 s
% 0.22/0.39  # Total time               : 0.041 s
% 0.22/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
