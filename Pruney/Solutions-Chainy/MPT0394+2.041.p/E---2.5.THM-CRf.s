%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:18 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   77 (629457 expanded)
%              Number of clauses        :   50 (249193 expanded)
%              Number of leaves         :   13 (188788 expanded)
%              Depth                    :   25
%              Number of atoms          :  123 (690960 expanded)
%              Number of equality atoms :  106 (677027 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t10_setfam_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(X1,X2)) != k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(t12_setfam_1,conjecture,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t19_zfmisc_1,axiom,(
    ! [X1,X2] : k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(t16_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
        & X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(c_0_13,plain,(
    ! [X30,X31] : k3_tarski(k2_tarski(X30,X31)) = k2_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_14,plain,(
    ! [X21,X22] : k1_enumset1(X21,X21,X22) = k2_tarski(X21,X22) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X36,X37] :
      ( X36 = k1_xboole_0
      | X37 = k1_xboole_0
      | k1_setfam_1(k2_xboole_0(X36,X37)) = k3_xboole_0(k1_setfam_1(X36),k1_setfam_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).

cnf(c_0_16,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X23,X24,X25] : k2_enumset1(X23,X23,X24,X25) = k1_enumset1(X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_19,plain,(
    ! [X26,X27,X28,X29] : k3_enumset1(X26,X26,X27,X28,X29) = k2_enumset1(X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_20,plain,(
    ! [X14,X15,X16,X17,X18,X19] : k4_enumset1(X14,X15,X16,X17,X18,X19) = k2_xboole_0(k3_enumset1(X14,X15,X16,X17,X18),k1_tarski(X19)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

fof(c_0_21,plain,(
    ! [X20] : k2_tarski(X20,X20) = k1_tarski(X20) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X38] : k1_setfam_1(k1_tarski(X38)) = X38 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X9,X10,X11,X12,X13] : k3_enumset1(X9,X10,X11,X12,X13) = k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_tarski(X13)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t12_setfam_1])).

cnf(c_0_32,plain,
    ( X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k1_setfam_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k3_tarski(k3_enumset1(k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X6,X6,X6,X6,X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_17]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_34,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_28]),c_0_17]),c_0_25]),c_0_26])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X34,X35] : k3_xboole_0(k1_tarski(X34),k2_tarski(X34,X35)) = k1_tarski(X34) ),
    inference(variable_rename,[status(thm)],[t19_zfmisc_1])).

fof(c_0_37,negated_conjecture,(
    k1_setfam_1(k2_tarski(esk1_0,esk2_0)) != k3_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_38,plain,
    ( k3_xboole_0(k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5)),X6) = k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6))
    | k3_enumset1(X1,X2,X3,X4,X5) = k1_xboole_0
    | k3_enumset1(X6,X6,X6,X6,X6) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X5,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_28]),c_0_17]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

fof(c_0_40,plain,(
    ! [X32,X33] :
      ( ~ r1_xboole_0(k1_tarski(X32),k1_tarski(X33))
      | X32 != X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).

fof(c_0_41,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k3_xboole_0(X7,X8) = k1_xboole_0 )
      & ( k3_xboole_0(X7,X8) != k1_xboole_0
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_42,plain,
    ( k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk1_0,esk2_0)) != k3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k3_xboole_0(k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5)),X6) = k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6))
    | k3_enumset1(X1,X2,X3,X4,X5) = k1_xboole_0
    | k1_setfam_1(k1_xboole_0) = X6 ),
    inference(spm,[status(thm)],[c_0_34,c_0_38])).

cnf(c_0_45,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[c_0_39,c_0_33])).

cnf(c_0_46,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2)) = k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_28]),c_0_28]),c_0_17]),c_0_17]),c_0_17]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)) != k3_xboole_0(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_17]),c_0_25]),c_0_26])).

cnf(c_0_50,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) = k3_xboole_0(X1,X2)
    | k3_enumset1(X1,X1,X1,X1,X1) = k1_xboole_0
    | k1_setfam_1(k1_xboole_0) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_34]),c_0_45])).

cnf(c_0_51,plain,
    ( X1 != X2
    | ~ r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_28]),c_0_28]),c_0_17]),c_0_17]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_52,plain,
    ( r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2))
    | k3_enumset1(X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0
    | k1_setfam_1(k1_xboole_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( ~ r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k1_setfam_1(k1_xboole_0) = esk2_0
    | r1_xboole_0(k1_xboole_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( k1_setfam_1(k1_xboole_0) = esk2_0
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( k1_setfam_1(k1_xboole_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_53]),c_0_56])).

cnf(c_0_58,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) = k3_xboole_0(X1,X2)
    | k3_enumset1(X1,X1,X1,X1,X1) = k1_xboole_0
    | esk2_0 = X2 ),
    inference(rw,[status(thm)],[c_0_50,c_0_57])).

cnf(c_0_59,plain,
    ( k3_enumset1(X1,X1,X1,X1,X1) = k1_xboole_0
    | k3_xboole_0(X1,X1) = X1
    | esk2_0 = X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_58])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X1) = X1
    | esk2_0 = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_59]),c_0_57])])).

cnf(c_0_61,plain,
    ( k3_xboole_0(k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5)),X6) = k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6))
    | k3_enumset1(X1,X2,X3,X4,X5) = k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_38])).

cnf(c_0_62,plain,
    ( esk2_0 = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_60])])).

cnf(c_0_63,plain,
    ( k3_xboole_0(k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5)),X6) = k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6))
    | k3_enumset1(X1,X2,X3,X4,X5) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_64,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) = k3_xboole_0(X1,X2)
    | k3_enumset1(X1,X1,X1,X1,X1) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_34]),c_0_45])).

cnf(c_0_65,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_65]),c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k1_xboole_0)) != k3_xboole_0(esk1_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_66]),c_0_66])).

cnf(c_0_68,plain,
    ( k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)) = k3_xboole_0(X1,X2)
    | k3_enumset1(X2,X2,X2,X2,X2) = k1_xboole_0
    | k3_enumset1(X1,X1,X1,X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_45])).

cnf(c_0_69,negated_conjecture,
    ( k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0
    | k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_69]),c_0_57]),c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_70]),c_0_72])).

cnf(c_0_74,negated_conjecture,
    ( k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_73]),c_0_73]),c_0_73]),c_0_73]),c_0_73])])).

cnf(c_0_75,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_73]),c_0_73]),c_0_73]),c_0_73]),c_0_34]),c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_74]),c_0_74]),c_0_74]),c_0_75]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.13/0.39  # and selection function SelectCQIArNpEqFirst.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.027 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.13/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.39  fof(t10_setfam_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&k1_setfam_1(k2_xboole_0(X1,X2))!=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 0.13/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.39  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 0.13/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.39  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.13/0.39  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 0.13/0.39  fof(t12_setfam_1, conjecture, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.39  fof(t19_zfmisc_1, axiom, ![X1, X2]:k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 0.13/0.39  fof(t16_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),k1_tarski(X2))&X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 0.13/0.39  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.13/0.39  fof(c_0_13, plain, ![X30, X31]:k3_tarski(k2_tarski(X30,X31))=k2_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.13/0.39  fof(c_0_14, plain, ![X21, X22]:k1_enumset1(X21,X21,X22)=k2_tarski(X21,X22), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.39  fof(c_0_15, plain, ![X36, X37]:(X36=k1_xboole_0|X37=k1_xboole_0|k1_setfam_1(k2_xboole_0(X36,X37))=k3_xboole_0(k1_setfam_1(X36),k1_setfam_1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).
% 0.13/0.39  cnf(c_0_16, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  fof(c_0_18, plain, ![X23, X24, X25]:k2_enumset1(X23,X23,X24,X25)=k1_enumset1(X23,X24,X25), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.39  fof(c_0_19, plain, ![X26, X27, X28, X29]:k3_enumset1(X26,X26,X27,X28,X29)=k2_enumset1(X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.39  fof(c_0_20, plain, ![X14, X15, X16, X17, X18, X19]:k4_enumset1(X14,X15,X16,X17,X18,X19)=k2_xboole_0(k3_enumset1(X14,X15,X16,X17,X18),k1_tarski(X19)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.13/0.39  fof(c_0_21, plain, ![X20]:k2_tarski(X20,X20)=k1_tarski(X20), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.39  fof(c_0_22, plain, ![X38]:k1_setfam_1(k1_tarski(X38))=X38, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 0.13/0.39  cnf(c_0_23, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_24, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.39  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_27, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_29, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  fof(c_0_30, plain, ![X9, X10, X11, X12, X13]:k3_enumset1(X9,X10,X11,X12,X13)=k2_xboole_0(k2_enumset1(X9,X10,X11,X12),k1_tarski(X13)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 0.13/0.39  fof(c_0_31, negated_conjecture, ~(![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t12_setfam_1])).
% 0.13/0.39  cnf(c_0_32, plain, (X2=k1_xboole_0|X1=k1_xboole_0|k1_setfam_1(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])).
% 0.13/0.39  cnf(c_0_33, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k3_tarski(k3_enumset1(k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X1,X2,X3,X4,X5),k3_enumset1(X6,X6,X6,X6,X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_17]), c_0_24]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.13/0.39  cnf(c_0_34, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_28]), c_0_17]), c_0_25]), c_0_26])).
% 0.13/0.39  cnf(c_0_35, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  fof(c_0_36, plain, ![X34, X35]:k3_xboole_0(k1_tarski(X34),k2_tarski(X34,X35))=k1_tarski(X34), inference(variable_rename,[status(thm)],[t19_zfmisc_1])).
% 0.13/0.39  fof(c_0_37, negated_conjecture, k1_setfam_1(k2_tarski(esk1_0,esk2_0))!=k3_xboole_0(esk1_0,esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.13/0.39  cnf(c_0_38, plain, (k3_xboole_0(k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5)),X6)=k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6))|k3_enumset1(X1,X2,X3,X4,X5)=k1_xboole_0|k3_enumset1(X6,X6,X6,X6,X6)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.13/0.39  cnf(c_0_39, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X5,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_28]), c_0_17]), c_0_24]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.13/0.39  fof(c_0_40, plain, ![X32, X33]:(~r1_xboole_0(k1_tarski(X32),k1_tarski(X33))|X32!=X33), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).
% 0.13/0.39  fof(c_0_41, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k3_xboole_0(X7,X8)=k1_xboole_0)&(k3_xboole_0(X7,X8)!=k1_xboole_0|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.13/0.39  cnf(c_0_42, plain, (k3_xboole_0(k1_tarski(X1),k2_tarski(X1,X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (k1_setfam_1(k2_tarski(esk1_0,esk2_0))!=k3_xboole_0(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.39  cnf(c_0_44, plain, (k3_xboole_0(k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5)),X6)=k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6))|k3_enumset1(X1,X2,X3,X4,X5)=k1_xboole_0|k1_setfam_1(k1_xboole_0)=X6), inference(spm,[status(thm)],[c_0_34, c_0_38])).
% 0.13/0.39  cnf(c_0_45, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[c_0_39, c_0_33])).
% 0.13/0.39  cnf(c_0_46, plain, (~r1_xboole_0(k1_tarski(X1),k1_tarski(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.39  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.39  cnf(c_0_48, plain, (k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2))=k3_enumset1(X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_28]), c_0_28]), c_0_17]), c_0_17]), c_0_17]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0))!=k3_xboole_0(esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_17]), c_0_25]), c_0_26])).
% 0.13/0.39  cnf(c_0_50, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))=k3_xboole_0(X1,X2)|k3_enumset1(X1,X1,X1,X1,X1)=k1_xboole_0|k1_setfam_1(k1_xboole_0)=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_34]), c_0_45])).
% 0.13/0.39  cnf(c_0_51, plain, (X1!=X2|~r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_28]), c_0_28]), c_0_17]), c_0_17]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.13/0.39  cnf(c_0_52, plain, (r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2))|k3_enumset1(X1,X1,X1,X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0|k1_setfam_1(k1_xboole_0)=esk2_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.39  cnf(c_0_54, plain, (~r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_51])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (k1_setfam_1(k1_xboole_0)=esk2_0|r1_xboole_0(k1_xboole_0,k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (k1_setfam_1(k1_xboole_0)=esk2_0|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_53])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (k1_setfam_1(k1_xboole_0)=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_53]), c_0_56])).
% 0.13/0.39  cnf(c_0_58, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))=k3_xboole_0(X1,X2)|k3_enumset1(X1,X1,X1,X1,X1)=k1_xboole_0|esk2_0=X2), inference(rw,[status(thm)],[c_0_50, c_0_57])).
% 0.13/0.39  cnf(c_0_59, plain, (k3_enumset1(X1,X1,X1,X1,X1)=k1_xboole_0|k3_xboole_0(X1,X1)=X1|esk2_0=X1), inference(spm,[status(thm)],[c_0_34, c_0_58])).
% 0.13/0.39  cnf(c_0_60, plain, (k3_xboole_0(X1,X1)=X1|esk2_0=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_59]), c_0_57])])).
% 0.13/0.39  cnf(c_0_61, plain, (k3_xboole_0(k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5)),X6)=k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6))|k3_enumset1(X1,X2,X3,X4,X5)=k1_xboole_0|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_38])).
% 0.13/0.39  cnf(c_0_62, plain, (esk2_0=k1_xboole_0|r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_60])])).
% 0.13/0.39  cnf(c_0_63, plain, (k3_xboole_0(k1_setfam_1(k3_enumset1(X1,X2,X3,X4,X5)),X6)=k1_setfam_1(k4_enumset1(X1,X2,X3,X4,X5,X6))|k3_enumset1(X1,X2,X3,X4,X5)=k1_xboole_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.13/0.39  cnf(c_0_64, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))=k3_xboole_0(X1,X2)|k3_enumset1(X1,X1,X1,X1,X1)=k1_xboole_0|esk2_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_34]), c_0_45])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_64])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (esk2_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_65]), c_0_62])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (k1_setfam_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,k1_xboole_0))!=k3_xboole_0(esk1_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_66]), c_0_66])).
% 0.13/0.39  cnf(c_0_68, plain, (k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))=k3_xboole_0(X1,X2)|k3_enumset1(X2,X2,X2,X2,X2)=k1_xboole_0|k3_enumset1(X1,X1,X1,X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_45])).
% 0.13/0.39  cnf(c_0_69, negated_conjecture, (k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0|k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.13/0.39  cnf(c_0_70, negated_conjecture, (k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)=k1_xboole_0|esk1_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_69]), c_0_57]), c_0_66])).
% 0.13/0.39  cnf(c_0_71, negated_conjecture, (esk1_0=k1_xboole_0|r1_xboole_0(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_52, c_0_70])).
% 0.13/0.39  cnf(c_0_72, negated_conjecture, (esk1_0=k1_xboole_0|~r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_70])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (esk1_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_70]), c_0_72])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_73]), c_0_73]), c_0_73]), c_0_73]), c_0_73])])).
% 0.13/0.39  cnf(c_0_75, negated_conjecture, (k3_xboole_0(k1_xboole_0,k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_73]), c_0_73]), c_0_73]), c_0_73]), c_0_34]), c_0_73])).
% 0.13/0.39  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_74]), c_0_74]), c_0_74]), c_0_75]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 77
% 0.13/0.39  # Proof object clause steps            : 50
% 0.13/0.39  # Proof object formula steps           : 27
% 0.13/0.39  # Proof object conjectures             : 20
% 0.13/0.39  # Proof object clause conjectures      : 17
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 13
% 0.13/0.39  # Proof object initial formulas used   : 13
% 0.13/0.39  # Proof object generating inferences   : 23
% 0.13/0.39  # Proof object simplifying inferences  : 79
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 13
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 14
% 0.13/0.39  # Removed in clause preprocessing      : 5
% 0.13/0.39  # Initial clauses in saturation        : 9
% 0.13/0.39  # Processed clauses                    : 157
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 58
% 0.13/0.39  # ...remaining for further processing  : 99
% 0.13/0.39  # Other redundant clauses eliminated   : 3
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 4
% 0.13/0.39  # Backward-rewritten                   : 37
% 0.13/0.39  # Generated clauses                    : 738
% 0.13/0.39  # ...of the previous two non-trivial   : 711
% 0.13/0.39  # Contextual simplify-reflections      : 4
% 0.13/0.39  # Paramodulations                      : 732
% 0.13/0.39  # Factorizations                       : 3
% 0.13/0.39  # Equation resolutions                 : 3
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
% 0.13/0.39  # Current number of processed clauses  : 48
% 0.13/0.39  #    Positive orientable unit clauses  : 8
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 2
% 0.13/0.39  #    Non-unit-clauses                  : 38
% 0.13/0.39  # Current number of unprocessed clauses: 501
% 0.13/0.39  # ...number of literals in the above   : 2411
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 55
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 797
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 286
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 66
% 0.13/0.39  # Unit Clause-clause subsumption calls : 55
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 9
% 0.13/0.39  # BW rewrite match successes           : 5
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 14002
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.047 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.051 s
% 0.13/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
