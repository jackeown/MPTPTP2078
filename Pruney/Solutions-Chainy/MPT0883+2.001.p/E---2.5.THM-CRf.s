%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:41 EST 2020

% Result     : Theorem 4.40s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 338 expanded)
%              Number of clauses        :   30 ( 137 expanded)
%              Number of leaves         :   12 ( 100 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 ( 358 expanded)
%              Number of equality atoms :   58 ( 357 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_enumset1,axiom,(
    ! [X1,X2,X3] : k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(t44_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(t43_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4),k1_tarski(X5)) = k2_enumset1(k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5),k3_mcart_1(X1,X4,X5),k3_mcart_1(X2,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_mcart_1)).

fof(t146_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(c_0_12,plain,(
    ! [X25,X26] : k3_tarski(k2_tarski(X25,X26)) = k2_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X11,X12,X13] : k1_enumset1(X11,X12,X13) = k2_xboole_0(k2_tarski(X11,X12),k1_tarski(X13)) ),
    inference(variable_rename,[status(thm)],[t43_enumset1])).

fof(c_0_15,plain,(
    ! [X22] : k2_tarski(X22,X22) = k1_tarski(X22) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_16,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X34,X35,X36] :
      ( k2_zfmisc_1(k1_tarski(X34),k2_tarski(X35,X36)) = k2_tarski(k4_tarski(X34,X35),k4_tarski(X34,X36))
      & k2_zfmisc_1(k2_tarski(X34,X35),k1_tarski(X36)) = k2_tarski(k4_tarski(X34,X36),k4_tarski(X35,X36)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X14,X15,X16,X17] : k2_enumset1(X14,X15,X16,X17) = k2_xboole_0(k1_tarski(X14),k1_enumset1(X15,X16,X17)) ),
    inference(variable_rename,[status(thm)],[t44_enumset1])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4),k1_tarski(X5)) = k2_enumset1(k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5),k3_mcart_1(X1,X4,X5),k3_mcart_1(X2,X4,X5)) ),
    inference(assume_negation,[status(cth)],[t43_mcart_1])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X30,X31,X32,X33] : k2_zfmisc_1(k2_tarski(X30,X31),k2_tarski(X32,X33)) = k2_enumset1(k4_tarski(X30,X32),k4_tarski(X30,X33),k4_tarski(X31,X32),k4_tarski(X31,X33)) ),
    inference(variable_rename,[status(thm)],[t146_zfmisc_1])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X6,X7] : k2_tarski(X6,X7) = k2_tarski(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_28,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0),k3_mcart_1(esk1_0,esk4_0,esk5_0),k3_mcart_1(esk2_0,esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_29,plain,(
    ! [X37,X38,X39] : k3_mcart_1(X37,X38,X39) = k4_tarski(k4_tarski(X37,X38),X39) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_30,plain,(
    ! [X40,X41,X42] : k3_zfmisc_1(X40,X41,X42) = k2_zfmisc_1(k2_zfmisc_1(X40,X41),X42) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_31,plain,(
    ! [X27,X28,X29] :
      ( k2_zfmisc_1(k2_xboole_0(X27,X28),X29) = k2_xboole_0(k2_zfmisc_1(X27,X29),k2_zfmisc_1(X28,X29))
      & k2_zfmisc_1(X29,k2_xboole_0(X27,X28)) = k2_xboole_0(k2_zfmisc_1(X29,X27),k2_zfmisc_1(X29,X28)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X2),k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22]),c_0_17]),c_0_17]),c_0_23])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X3)) = k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_22]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_22]),c_0_17]),c_0_23])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0),k3_mcart_1(esk1_0,esk4_0,esk5_0),k3_mcart_1(esk2_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X2),k1_enumset1(X1,X1,X2),k2_zfmisc_1(k1_enumset1(X3,X3,X3),k1_enumset1(X4,X4,X4)))) = k1_enumset1(X1,X2,k4_tarski(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3)) = k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_22]),c_0_17]),c_0_17]),c_0_17])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X4)) = k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3)),k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3)),k1_enumset1(k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_17]),c_0_17]),c_0_36])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_17]),c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk2_0),k1_enumset1(esk3_0,esk3_0,esk4_0)),k1_enumset1(esk5_0,esk5_0,esk5_0)) != k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0)),k1_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0)),k1_enumset1(k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk4_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk4_0),esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_22]),c_0_17]),c_0_17]),c_0_17]),c_0_39]),c_0_39]),c_0_39]),c_0_39]),c_0_40]),c_0_36])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)),X3) = k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_23]),c_0_23])).

cnf(c_0_48,plain,
    ( k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3)),k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3)),k2_zfmisc_1(k1_enumset1(X4,X4,X4),k1_enumset1(X5,X5,X5)))) = k1_enumset1(k4_tarski(X1,X3),k4_tarski(X2,X3),k4_tarski(X4,X5)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k1_enumset1(k4_tarski(X1,X3),k4_tarski(X4,X2),k4_tarski(X4,X3)))) = k2_zfmisc_1(k1_enumset1(X1,X1,X4),k1_enumset1(X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_33]),c_0_33])).

cnf(c_0_50,plain,
    ( k1_enumset1(X1,X2,X3) = k1_enumset1(X2,X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_45]),c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk3_0,esk3_0,esk3_0)),k1_enumset1(esk5_0,esk5_0,esk5_0)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk3_0,esk3_0,esk3_0)),k1_enumset1(esk5_0,esk5_0,esk5_0)),k1_enumset1(k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk4_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk4_0),esk5_0)))) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk2_0),k1_enumset1(esk3_0,esk3_0,esk4_0)),k1_enumset1(esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_43]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_52,plain,
    ( k1_enumset1(k4_tarski(X1,X2),k4_tarski(X3,X2),k4_tarski(X4,X2)) = k2_zfmisc_1(k1_enumset1(X1,X3,X4),k1_enumset1(X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_32])).

cnf(c_0_53,plain,
    ( k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k1_enumset1(k4_tarski(X3,X2),k4_tarski(X1,X4),k4_tarski(X3,X4)))) = k2_zfmisc_1(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X4)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_47]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:19:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 4.40/4.57  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 4.40/4.57  # and selection function SelectNewComplexAHP.
% 4.40/4.57  #
% 4.40/4.57  # Preprocessing time       : 0.027 s
% 4.40/4.57  # Presaturation interreduction done
% 4.40/4.57  
% 4.40/4.57  # Proof found!
% 4.40/4.57  # SZS status Theorem
% 4.40/4.57  # SZS output start CNFRefutation
% 4.40/4.57  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.40/4.57  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.40/4.57  fof(t43_enumset1, axiom, ![X1, X2, X3]:k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 4.40/4.57  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.40/4.57  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 4.40/4.57  fof(t44_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 4.40/4.57  fof(t43_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4),k1_tarski(X5))=k2_enumset1(k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5),k3_mcart_1(X1,X4,X5),k3_mcart_1(X2,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_mcart_1)).
% 4.40/4.57  fof(t146_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 4.40/4.57  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.40/4.57  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 4.40/4.57  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.40/4.57  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 4.40/4.57  fof(c_0_12, plain, ![X25, X26]:k3_tarski(k2_tarski(X25,X26))=k2_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 4.40/4.57  fof(c_0_13, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 4.40/4.57  fof(c_0_14, plain, ![X11, X12, X13]:k1_enumset1(X11,X12,X13)=k2_xboole_0(k2_tarski(X11,X12),k1_tarski(X13)), inference(variable_rename,[status(thm)],[t43_enumset1])).
% 4.40/4.57  fof(c_0_15, plain, ![X22]:k2_tarski(X22,X22)=k1_tarski(X22), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 4.40/4.57  cnf(c_0_16, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.40/4.57  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.40/4.57  fof(c_0_18, plain, ![X34, X35, X36]:(k2_zfmisc_1(k1_tarski(X34),k2_tarski(X35,X36))=k2_tarski(k4_tarski(X34,X35),k4_tarski(X34,X36))&k2_zfmisc_1(k2_tarski(X34,X35),k1_tarski(X36))=k2_tarski(k4_tarski(X34,X36),k4_tarski(X35,X36))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 4.40/4.57  fof(c_0_19, plain, ![X14, X15, X16, X17]:k2_enumset1(X14,X15,X16,X17)=k2_xboole_0(k1_tarski(X14),k1_enumset1(X15,X16,X17)), inference(variable_rename,[status(thm)],[t44_enumset1])).
% 4.40/4.57  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4),k1_tarski(X5))=k2_enumset1(k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5),k3_mcart_1(X1,X4,X5),k3_mcart_1(X2,X4,X5))), inference(assume_negation,[status(cth)],[t43_mcart_1])).
% 4.40/4.57  cnf(c_0_21, plain, (k1_enumset1(X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.40/4.57  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.40/4.57  cnf(c_0_23, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 4.40/4.57  cnf(c_0_24, plain, (k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.40/4.57  fof(c_0_25, plain, ![X30, X31, X32, X33]:k2_zfmisc_1(k2_tarski(X30,X31),k2_tarski(X32,X33))=k2_enumset1(k4_tarski(X30,X32),k4_tarski(X30,X33),k4_tarski(X31,X32),k4_tarski(X31,X33)), inference(variable_rename,[status(thm)],[t146_zfmisc_1])).
% 4.40/4.57  cnf(c_0_26, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.40/4.57  fof(c_0_27, plain, ![X6, X7]:k2_tarski(X6,X7)=k2_tarski(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 4.40/4.57  fof(c_0_28, negated_conjecture, k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0),k3_mcart_1(esk1_0,esk4_0,esk5_0),k3_mcart_1(esk2_0,esk4_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 4.40/4.57  fof(c_0_29, plain, ![X37, X38, X39]:k3_mcart_1(X37,X38,X39)=k4_tarski(k4_tarski(X37,X38),X39), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 4.40/4.57  fof(c_0_30, plain, ![X40, X41, X42]:k3_zfmisc_1(X40,X41,X42)=k2_zfmisc_1(k2_zfmisc_1(X40,X41),X42), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 4.40/4.57  fof(c_0_31, plain, ![X27, X28, X29]:(k2_zfmisc_1(k2_xboole_0(X27,X28),X29)=k2_xboole_0(k2_zfmisc_1(X27,X29),k2_zfmisc_1(X28,X29))&k2_zfmisc_1(X29,k2_xboole_0(X27,X28))=k2_xboole_0(k2_zfmisc_1(X29,X27),k2_zfmisc_1(X29,X28))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 4.40/4.57  cnf(c_0_32, plain, (k1_enumset1(X1,X2,X3)=k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X2),k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22]), c_0_17]), c_0_17]), c_0_23])).
% 4.40/4.57  cnf(c_0_33, plain, (k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X3))=k1_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_22]), c_0_17]), c_0_17]), c_0_17])).
% 4.40/4.57  cnf(c_0_34, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.40/4.57  cnf(c_0_35, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.40/4.57  cnf(c_0_36, plain, (k2_enumset1(X1,X2,X3,X4)=k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_22]), c_0_17]), c_0_23])).
% 4.40/4.57  cnf(c_0_37, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 4.40/4.57  cnf(c_0_38, negated_conjecture, (k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0),k1_tarski(esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0),k3_mcart_1(esk1_0,esk4_0,esk5_0),k3_mcart_1(esk2_0,esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.40/4.57  cnf(c_0_39, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.40/4.57  cnf(c_0_40, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 4.40/4.57  cnf(c_0_41, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 4.40/4.57  cnf(c_0_42, plain, (k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X2),k1_enumset1(X1,X1,X2),k2_zfmisc_1(k1_enumset1(X3,X3,X3),k1_enumset1(X4,X4,X4))))=k1_enumset1(X1,X2,k4_tarski(X3,X4))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 4.40/4.57  cnf(c_0_43, plain, (k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3))=k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_22]), c_0_17]), c_0_17]), c_0_17])).
% 4.40/4.57  cnf(c_0_44, plain, (k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X4))=k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3)),k1_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3)),k1_enumset1(k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_17]), c_0_17]), c_0_36])).
% 4.40/4.57  cnf(c_0_45, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_17]), c_0_17])).
% 4.40/4.57  cnf(c_0_46, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk2_0),k1_enumset1(esk3_0,esk3_0,esk4_0)),k1_enumset1(esk5_0,esk5_0,esk5_0))!=k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0)),k1_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0)),k1_enumset1(k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk4_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk4_0),esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_22]), c_0_17]), c_0_17]), c_0_17]), c_0_39]), c_0_39]), c_0_39]), c_0_39]), c_0_40]), c_0_36])).
% 4.40/4.57  cnf(c_0_47, plain, (k2_zfmisc_1(k3_tarski(k1_enumset1(X1,X1,X2)),X3)=k3_tarski(k1_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_23]), c_0_23])).
% 4.40/4.57  cnf(c_0_48, plain, (k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3)),k2_zfmisc_1(k1_enumset1(X1,X1,X2),k1_enumset1(X3,X3,X3)),k2_zfmisc_1(k1_enumset1(X4,X4,X4),k1_enumset1(X5,X5,X5))))=k1_enumset1(k4_tarski(X1,X3),k4_tarski(X2,X3),k4_tarski(X4,X5))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 4.40/4.57  cnf(c_0_49, plain, (k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k1_enumset1(k4_tarski(X1,X3),k4_tarski(X4,X2),k4_tarski(X4,X3))))=k2_zfmisc_1(k1_enumset1(X1,X1,X4),k1_enumset1(X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_33]), c_0_33])).
% 4.40/4.57  cnf(c_0_50, plain, (k1_enumset1(X1,X2,X3)=k1_enumset1(X2,X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_45]), c_0_32])).
% 4.40/4.57  cnf(c_0_51, negated_conjecture, (k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk3_0,esk3_0,esk3_0)),k1_enumset1(esk5_0,esk5_0,esk5_0)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk1_0),k1_enumset1(esk3_0,esk3_0,esk3_0)),k1_enumset1(esk5_0,esk5_0,esk5_0)),k1_enumset1(k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk1_0,esk4_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk4_0),esk5_0))))!=k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk1_0,esk1_0,esk2_0),k1_enumset1(esk3_0,esk3_0,esk4_0)),k1_enumset1(esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_43]), c_0_43]), c_0_43]), c_0_43])).
% 4.40/4.57  cnf(c_0_52, plain, (k1_enumset1(k4_tarski(X1,X2),k4_tarski(X3,X2),k4_tarski(X4,X2))=k2_zfmisc_1(k1_enumset1(X1,X3,X4),k1_enumset1(X2,X2,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_32])).
% 4.40/4.57  cnf(c_0_53, plain, (k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k2_zfmisc_1(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X2,X2)),k1_enumset1(k4_tarski(X3,X2),k4_tarski(X1,X4),k4_tarski(X3,X4))))=k2_zfmisc_1(k1_enumset1(X1,X1,X3),k1_enumset1(X2,X2,X4))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 4.40/4.57  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_47]), c_0_53])]), ['proof']).
% 4.40/4.57  # SZS output end CNFRefutation
% 4.40/4.57  # Proof object total steps             : 55
% 4.40/4.57  # Proof object clause steps            : 30
% 4.40/4.57  # Proof object formula steps           : 25
% 4.40/4.57  # Proof object conjectures             : 7
% 4.40/4.57  # Proof object clause conjectures      : 4
% 4.40/4.57  # Proof object formula conjectures     : 3
% 4.40/4.57  # Proof object initial clauses used    : 13
% 4.40/4.57  # Proof object initial formulas used   : 12
% 4.40/4.57  # Proof object generating inferences   : 5
% 4.40/4.57  # Proof object simplifying inferences  : 45
% 4.40/4.57  # Training examples: 0 positive, 0 negative
% 4.40/4.57  # Parsed axioms                        : 14
% 4.40/4.57  # Removed by relevancy pruning/SinE    : 0
% 4.40/4.57  # Initial clauses                      : 16
% 4.40/4.57  # Removed in clause preprocessing      : 6
% 4.40/4.57  # Initial clauses in saturation        : 10
% 4.40/4.57  # Processed clauses                    : 28697
% 4.40/4.57  # ...of these trivial                  : 5508
% 4.40/4.57  # ...subsumed                          : 22209
% 4.40/4.57  # ...remaining for further processing  : 980
% 4.40/4.57  # Other redundant clauses eliminated   : 0
% 4.40/4.57  # Clauses deleted for lack of memory   : 0
% 4.40/4.57  # Backward-subsumed                    : 0
% 4.40/4.57  # Backward-rewritten                   : 151
% 4.40/4.57  # Generated clauses                    : 762069
% 4.40/4.57  # ...of the previous two non-trivial   : 277095
% 4.40/4.57  # Contextual simplify-reflections      : 0
% 4.40/4.57  # Paramodulations                      : 762069
% 4.40/4.57  # Factorizations                       : 0
% 4.40/4.57  # Equation resolutions                 : 0
% 4.40/4.57  # Propositional unsat checks           : 0
% 4.40/4.57  #    Propositional check models        : 0
% 4.40/4.57  #    Propositional check unsatisfiable : 0
% 4.40/4.57  #    Propositional clauses             : 0
% 4.40/4.57  #    Propositional clauses after purity: 0
% 4.40/4.57  #    Propositional unsat core size     : 0
% 4.40/4.57  #    Propositional preprocessing time  : 0.000
% 4.40/4.57  #    Propositional encoding time       : 0.000
% 4.40/4.57  #    Propositional solver time         : 0.000
% 4.40/4.57  #    Success case prop preproc time    : 0.000
% 4.40/4.57  #    Success case prop encoding time   : 0.000
% 4.40/4.57  #    Success case prop solver time     : 0.000
% 4.40/4.57  # Current number of processed clauses  : 819
% 4.40/4.57  #    Positive orientable unit clauses  : 543
% 4.40/4.57  #    Positive unorientable unit clauses: 276
% 4.40/4.57  #    Negative unit clauses             : 0
% 4.40/4.57  #    Non-unit-clauses                  : 0
% 4.40/4.57  # Current number of unprocessed clauses: 245394
% 4.40/4.57  # ...number of literals in the above   : 245394
% 4.40/4.57  # Current number of archived formulas  : 0
% 4.40/4.57  # Current number of archived clauses   : 167
% 4.40/4.57  # Clause-clause subsumption calls (NU) : 0
% 4.40/4.57  # Rec. Clause-clause subsumption calls : 0
% 4.40/4.57  # Non-unit clause-clause subsumptions  : 0
% 4.40/4.57  # Unit Clause-clause subsumption calls : 12785
% 4.40/4.57  # Rewrite failures with RHS unbound    : 0
% 4.40/4.57  # BW rewrite match attempts            : 49582
% 4.40/4.57  # BW rewrite match successes           : 5863
% 4.40/4.57  # Condensation attempts                : 0
% 4.40/4.57  # Condensation successes               : 0
% 4.40/4.57  # Termbank termtop insertions          : 19270018
% 4.43/4.59  
% 4.43/4.59  # -------------------------------------------------
% 4.43/4.59  # User time                : 4.116 s
% 4.43/4.59  # System time              : 0.128 s
% 4.43/4.59  # Total time               : 4.244 s
% 4.43/4.59  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
