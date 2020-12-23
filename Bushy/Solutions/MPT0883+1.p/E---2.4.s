%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t43_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:08 EDT 2019

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 265 expanded)
%              Number of clauses        :   35 ( 120 expanded)
%              Number of leaves         :    9 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 ( 305 expanded)
%              Number of equality atoms :   57 ( 304 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t104_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X2,X4) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t43_mcart_1.p',t104_enumset1)).

fof(t45_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t43_mcart_1.p',t45_enumset1)).

fof(t25_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t43_mcart_1.p',t25_mcart_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t43_mcart_1.p',idempotence_k2_xboole_0)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t43_mcart_1.p',t120_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t43_mcart_1.p',t36_zfmisc_1)).

fof(t43_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4),k1_tarski(X5)) = k2_enumset1(k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5),k3_mcart_1(X1,X4,X5),k3_mcart_1(X2,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t43_mcart_1.p',t43_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t43_mcart_1.p',d3_zfmisc_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t43_mcart_1.p',d3_mcart_1)).

fof(c_0_9,plain,(
    ! [X26,X27,X28,X29] : k2_enumset1(X26,X27,X28,X29) = k2_enumset1(X26,X28,X27,X29) ),
    inference(variable_rename,[status(thm)],[t104_enumset1])).

fof(c_0_10,plain,(
    ! [X45,X46,X47,X48] : k2_enumset1(X45,X46,X47,X48) = k2_xboole_0(k2_tarski(X45,X46),k2_tarski(X47,X48)) ),
    inference(variable_rename,[status(thm)],[t45_enumset1])).

fof(c_0_11,plain,(
    ! [X36,X37,X38,X39] : k2_zfmisc_1(k2_tarski(X36,X37),k2_tarski(X38,X39)) = k2_enumset1(k4_tarski(X36,X38),k4_tarski(X36,X39),k4_tarski(X37,X38),k4_tarski(X37,X39)) ),
    inference(variable_rename,[status(thm)],[t25_mcart_1])).

fof(c_0_12,plain,(
    ! [X25] : k2_xboole_0(X25,X25) = X25 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_13,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X1,X3,X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X30,X31,X32] :
      ( k2_zfmisc_1(k2_xboole_0(X30,X31),X32) = k2_xboole_0(k2_zfmisc_1(X30,X32),k2_zfmisc_1(X31,X32))
      & k2_zfmisc_1(X32,k2_xboole_0(X30,X31)) = k2_xboole_0(k2_zfmisc_1(X32,X30),k2_zfmisc_1(X32,X31)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X42,X43,X44] :
      ( k2_zfmisc_1(k1_tarski(X42),k2_tarski(X43,X44)) = k2_tarski(k4_tarski(X42,X43),k4_tarski(X42,X44))
      & k2_zfmisc_1(k2_tarski(X42,X43),k1_tarski(X44)) = k2_tarski(k4_tarski(X42,X44),k4_tarski(X43,X44)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_xboole_0(k2_tarski(X1,X3),k2_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14]),c_0_14])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_xboole_0(k2_tarski(k4_tarski(X1,X3),k4_tarski(X1,X4)),k2_tarski(k4_tarski(X2,X3),k4_tarski(X2,X4))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) = k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4),k1_tarski(X5)) = k2_enumset1(k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5),k3_mcart_1(X1,X4,X5),k3_mcart_1(X2,X4,X5)) ),
    inference(assume_negation,[status(cth)],[t43_mcart_1])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k2_xboole_0(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X2)),k2_zfmisc_1(k2_tarski(X1,X3),X4)) = k2_zfmisc_1(k2_tarski(X1,X3),k2_xboole_0(k1_tarski(X2),X4)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( k2_xboole_0(k2_tarski(X1,k4_tarski(X2,X3)),k2_tarski(X4,k4_tarski(X5,X3))) = k2_xboole_0(k2_tarski(X1,X4),k2_zfmisc_1(k2_tarski(X2,X5),k1_tarski(X3))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_30,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0),k3_mcart_1(esk1_0,esk4_0,esk5_0),k3_mcart_1(esk2_0,esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_31,plain,(
    ! [X20,X21,X22] : k3_zfmisc_1(X20,X21,X22) = k2_zfmisc_1(k2_zfmisc_1(X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_32,plain,(
    ! [X17,X18,X19] : k3_mcart_1(X17,X18,X19) = k4_tarski(k4_tarski(X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_33,plain,
    ( k2_xboole_0(k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)),k2_zfmisc_1(X4,k2_tarski(X2,X3))) = k2_zfmisc_1(k2_xboole_0(k1_tarski(X1),X4),k2_tarski(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) = k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_22])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k2_zfmisc_1(k2_tarski(X1,X2),X3),k2_tarski(k4_tarski(X1,X4),k4_tarski(X2,X4))) = k2_zfmisc_1(k2_tarski(X1,X2),k2_xboole_0(X3,k1_tarski(X4))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_xboole_0(k1_tarski(X3),X4)) = k2_zfmisc_1(k2_tarski(X1,X2),k2_xboole_0(k2_tarski(X3,X3),X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_29]),c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0),k3_mcart_1(esk1_0,esk4_0,esk5_0),k3_mcart_1(esk2_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k2_tarski(X3,X4)) = k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_22])).

cnf(c_0_41,plain,
    ( k2_xboole_0(k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)),k2_zfmisc_1(X5,k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))) = k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X2),X5),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_34])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_xboole_0(X3,k1_tarski(X4))) = k2_zfmisc_1(k2_tarski(X1,X2),k2_xboole_0(X3,k2_tarski(X4,X4))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_29]),c_0_35])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X4))) = k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)),k1_tarski(esk5_0)) != k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)),k2_tarski(k4_tarski(k4_tarski(esk1_0,esk4_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk4_0),esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_14])).

cnf(c_0_45,plain,
    ( k2_xboole_0(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X2)),k2_zfmisc_1(X4,k2_tarski(X2,X2))) = k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X3),X4),k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_29])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,k2_xboole_0(k1_tarski(X2),k1_tarski(X3))),k2_tarski(X4,X5)) = k2_zfmisc_1(k2_xboole_0(X1,k2_tarski(X2,X3)),k2_tarski(X4,X5)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_40]),c_0_25])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))) = k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)),k2_tarski(X5,X6)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_25])).

cnf(c_0_48,negated_conjecture,
    ( k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk4_0),esk5_0)),k2_tarski(k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk4_0),esk5_0))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)),k1_tarski(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_19])).

cnf(c_0_49,plain,
    ( k2_xboole_0(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X2)),k2_tarski(k4_tarski(X4,X2),k4_tarski(X5,X2))) = k2_zfmisc_1(k2_xboole_0(k2_tarski(X1,X3),k2_tarski(X4,X5)),k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_29]),c_0_46])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))) = k2_zfmisc_1(k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)),k2_tarski(X5,X6)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)),k1_tarski(esk5_0)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)),k2_tarski(esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_22])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)),k1_tarski(X5)) = k2_zfmisc_1(k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)),k2_tarski(X5,X5)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_18])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
