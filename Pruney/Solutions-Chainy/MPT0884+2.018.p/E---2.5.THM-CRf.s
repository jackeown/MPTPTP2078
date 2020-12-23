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
% DateTime   : Thu Dec  3 10:59:44 EST 2020

% Result     : Theorem 8.49s
% Output     : CNFRefutation 8.49s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 689 expanded)
%              Number of clauses        :   32 ( 262 expanded)
%              Number of leaves         :   14 ( 213 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 ( 691 expanded)
%              Number of equality atoms :   62 ( 690 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t50_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(t48_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(t146_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(t44_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(c_0_14,plain,(
    ! [X32,X33] : k3_tarski(k2_tarski(X32,X33)) = k2_xboole_0(X32,X33) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X25,X26,X27] : k2_enumset1(X25,X25,X26,X27) = k1_enumset1(X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X28,X29,X30,X31] : k3_enumset1(X28,X28,X29,X30,X31) = k2_enumset1(X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X17,X18,X19,X20,X21] : k3_enumset1(X17,X18,X19,X20,X21) = k2_xboole_0(k2_enumset1(X17,X18,X19,X20),k1_tarski(X21)) ),
    inference(variable_rename,[status(thm)],[t50_enumset1])).

fof(c_0_22,plain,(
    ! [X22] : k2_tarski(X22,X22) = k1_tarski(X22) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X8,X9,X10,X11] : k2_enumset1(X8,X9,X10,X11) = k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X10,X11)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_24,plain,(
    ! [X12,X13,X14,X15,X16] : k3_enumset1(X12,X13,X14,X15,X16) = k2_xboole_0(k2_tarski(X12,X13),k1_enumset1(X14,X15,X16)) ),
    inference(variable_rename,[status(thm)],[t48_enumset1])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X5,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_18]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_28])).

fof(c_0_35,plain,(
    ! [X34,X35,X36,X37] : k2_zfmisc_1(k2_tarski(X34,X35),k2_tarski(X36,X37)) = k2_enumset1(k4_tarski(X34,X36),k4_tarski(X34,X37),k4_tarski(X35,X36),k4_tarski(X35,X37)) ),
    inference(variable_rename,[status(thm)],[t146_zfmisc_1])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_18]),c_0_18]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X4,X5))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_18]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_38,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X3,X4,X5))) = k3_enumset1(X2,X3,X4,X5,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5)) = k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)) ),
    inference(assume_negation,[status(cth)],[t44_mcart_1])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( k3_enumset1(X1,X2,X3,X3,X4) = k3_enumset1(X1,X1,X2,X3,X4) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X4,X4,X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_43,negated_conjecture,(
    k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

fof(c_0_44,plain,(
    ! [X41,X42,X43] : k3_mcart_1(X41,X42,X43) = k4_tarski(k4_tarski(X41,X42),X43) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_45,plain,(
    ! [X44,X45,X46] : k3_zfmisc_1(X44,X45,X46) = k2_zfmisc_1(k2_zfmisc_1(X44,X45),X46) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X4)) = k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_18]),c_0_18]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_47,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X1,X2,X2,X3,X4) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_41]),c_0_34])).

cnf(c_0_48,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k3_enumset1(X4,X1,X2,X3,X5) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_42]),c_0_34])).

fof(c_0_49,plain,(
    ! [X38,X39,X40] :
      ( k2_zfmisc_1(k1_tarski(X38),k2_tarski(X39,X40)) = k2_tarski(k4_tarski(X38,X39),k4_tarski(X38,X40))
      & k2_zfmisc_1(k2_tarski(X38,X39),k1_tarski(X40)) = k2_tarski(k4_tarski(X38,X40),k4_tarski(X39,X40)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_50,negated_conjecture,
    ( k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) != k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X4,X2),k4_tarski(X4,X3)) = k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X4),k3_enumset1(X2,X2,X2,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k3_enumset1(X2,X4,X4,X1,X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_48])).

cnf(c_0_55,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0)) != k3_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_30]),c_0_18]),c_0_18]),c_0_18]),c_0_27]),c_0_27]),c_0_27]),c_0_51]),c_0_51]),c_0_51]),c_0_51]),c_0_52]),c_0_28]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_57,plain,
    ( k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X2),k4_tarski(X1,X4),k4_tarski(X3,X4)) = k2_zfmisc_1(k3_enumset1(X3,X3,X3,X3,X1),k3_enumset1(X2,X2,X2,X2,X4)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X3)) = k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_30]),c_0_18]),c_0_18]),c_0_18]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_59,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k3_enumset1(X2,X2,X2,X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_38])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:02:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 8.49/8.67  # AutoSched0-Mode selected heuristic H_____102_B08_00_F1_PI_AE_CS_SP_PS_S2S
% 8.49/8.67  # and selection function SelectNewComplexAHP.
% 8.49/8.67  #
% 8.49/8.67  # Preprocessing time       : 0.026 s
% 8.49/8.67  # Presaturation interreduction done
% 8.49/8.67  
% 8.49/8.67  # Proof found!
% 8.49/8.67  # SZS status Theorem
% 8.49/8.67  # SZS output start CNFRefutation
% 8.49/8.67  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.49/8.67  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 8.49/8.67  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.49/8.67  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 8.49/8.67  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 8.49/8.67  fof(t50_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 8.49/8.67  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 8.49/8.67  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 8.49/8.67  fof(t48_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 8.49/8.67  fof(t146_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 8.49/8.67  fof(t44_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_mcart_1)).
% 8.49/8.67  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 8.49/8.67  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 8.49/8.67  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 8.49/8.67  fof(c_0_14, plain, ![X32, X33]:k3_tarski(k2_tarski(X32,X33))=k2_xboole_0(X32,X33), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 8.49/8.67  fof(c_0_15, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 8.49/8.67  fof(c_0_16, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 8.49/8.67  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 8.49/8.67  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 8.49/8.67  fof(c_0_19, plain, ![X25, X26, X27]:k2_enumset1(X25,X25,X26,X27)=k1_enumset1(X25,X26,X27), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 8.49/8.67  fof(c_0_20, plain, ![X28, X29, X30, X31]:k3_enumset1(X28,X28,X29,X30,X31)=k2_enumset1(X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 8.49/8.67  fof(c_0_21, plain, ![X17, X18, X19, X20, X21]:k3_enumset1(X17,X18,X19,X20,X21)=k2_xboole_0(k2_enumset1(X17,X18,X19,X20),k1_tarski(X21)), inference(variable_rename,[status(thm)],[t50_enumset1])).
% 8.49/8.67  fof(c_0_22, plain, ![X22]:k2_tarski(X22,X22)=k1_tarski(X22), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 8.49/8.67  fof(c_0_23, plain, ![X8, X9, X10, X11]:k2_enumset1(X8,X9,X10,X11)=k2_xboole_0(k2_tarski(X8,X9),k2_tarski(X10,X11)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 8.49/8.67  fof(c_0_24, plain, ![X12, X13, X14, X15, X16]:k3_enumset1(X12,X13,X14,X15,X16)=k2_xboole_0(k2_tarski(X12,X13),k1_enumset1(X14,X15,X16)), inference(variable_rename,[status(thm)],[t48_enumset1])).
% 8.49/8.67  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 8.49/8.67  cnf(c_0_26, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 8.49/8.67  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 8.49/8.67  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 8.49/8.67  cnf(c_0_29, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X5))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 8.49/8.67  cnf(c_0_30, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 8.49/8.67  cnf(c_0_31, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 8.49/8.67  cnf(c_0_32, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k2_tarski(X1,X2),k1_enumset1(X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 8.49/8.67  cnf(c_0_33, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 8.49/8.67  cnf(c_0_34, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X1,X1,X2,X3,X4),k3_enumset1(X5,X5,X5,X5,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_18]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_28])).
% 8.49/8.67  fof(c_0_35, plain, ![X34, X35, X36, X37]:k2_zfmisc_1(k2_tarski(X34,X35),k2_tarski(X36,X37))=k2_enumset1(k4_tarski(X34,X36),k4_tarski(X34,X37),k4_tarski(X35,X36),k4_tarski(X35,X37)), inference(variable_rename,[status(thm)],[t146_zfmisc_1])).
% 8.49/8.67  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_18]), c_0_18]), c_0_26]), c_0_27]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_28])).
% 8.49/8.67  cnf(c_0_37, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X4,X5)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_18]), c_0_26]), c_0_27]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28]), c_0_28])).
% 8.49/8.67  cnf(c_0_38, plain, (k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X3,X4,X5)))=k3_enumset1(X2,X3,X4,X5,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 8.49/8.67  fof(c_0_39, negated_conjecture, ~(![X1, X2, X3, X4, X5]:k3_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3),k2_tarski(X4,X5))=k2_enumset1(k3_mcart_1(X1,X3,X4),k3_mcart_1(X2,X3,X4),k3_mcart_1(X1,X3,X5),k3_mcart_1(X2,X3,X5))), inference(assume_negation,[status(cth)],[t44_mcart_1])).
% 8.49/8.67  cnf(c_0_40, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))=k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 8.49/8.67  cnf(c_0_41, plain, (k3_enumset1(X1,X2,X3,X3,X4)=k3_enumset1(X1,X1,X2,X3,X4)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 8.49/8.67  cnf(c_0_42, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X4,X4,X1,X2,X3)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 8.49/8.67  fof(c_0_43, negated_conjecture, k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 8.49/8.67  fof(c_0_44, plain, ![X41, X42, X43]:k3_mcart_1(X41,X42,X43)=k4_tarski(k4_tarski(X41,X42),X43), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 8.49/8.67  fof(c_0_45, plain, ![X44, X45, X46]:k3_zfmisc_1(X44,X45,X46)=k2_zfmisc_1(k2_zfmisc_1(X44,X45),X46), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 8.49/8.67  cnf(c_0_46, plain, (k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X4))=k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_18]), c_0_18]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28])).
% 8.49/8.67  cnf(c_0_47, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X1,X2,X2,X3,X4)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_41]), c_0_34])).
% 8.49/8.67  cnf(c_0_48, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k3_enumset1(X4,X1,X2,X3,X5)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_42]), c_0_34])).
% 8.49/8.67  fof(c_0_49, plain, ![X38, X39, X40]:(k2_zfmisc_1(k1_tarski(X38),k2_tarski(X39,X40))=k2_tarski(k4_tarski(X38,X39),k4_tarski(X38,X40))&k2_zfmisc_1(k2_tarski(X38,X39),k1_tarski(X40))=k2_tarski(k4_tarski(X38,X40),k4_tarski(X39,X40))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 8.49/8.67  cnf(c_0_50, negated_conjecture, (k3_zfmisc_1(k2_tarski(esk1_0,esk2_0),k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))!=k2_enumset1(k3_mcart_1(esk1_0,esk3_0,esk4_0),k3_mcart_1(esk2_0,esk3_0,esk4_0),k3_mcart_1(esk1_0,esk3_0,esk5_0),k3_mcart_1(esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 8.49/8.67  cnf(c_0_51, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 8.49/8.67  cnf(c_0_52, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 8.49/8.67  cnf(c_0_53, plain, (k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X4,X2),k4_tarski(X4,X3))=k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X4),k3_enumset1(X2,X2,X2,X2,X3))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 8.49/8.67  cnf(c_0_54, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k3_enumset1(X2,X4,X4,X1,X3)), inference(spm,[status(thm)],[c_0_42, c_0_48])).
% 8.49/8.67  cnf(c_0_55, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 8.49/8.67  cnf(c_0_56, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k3_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0))!=k3_enumset1(k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk4_0),k4_tarski(k4_tarski(esk1_0,esk3_0),esk5_0),k4_tarski(k4_tarski(esk2_0,esk3_0),esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_30]), c_0_18]), c_0_18]), c_0_18]), c_0_27]), c_0_27]), c_0_27]), c_0_51]), c_0_51]), c_0_51]), c_0_51]), c_0_52]), c_0_28]), c_0_28]), c_0_28]), c_0_28])).
% 8.49/8.67  cnf(c_0_57, plain, (k3_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X3,X2),k4_tarski(X1,X4),k4_tarski(X3,X4))=k2_zfmisc_1(k3_enumset1(X3,X3,X3,X3,X1),k3_enumset1(X2,X2,X2,X2,X4))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 8.49/8.67  cnf(c_0_58, plain, (k2_zfmisc_1(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X3,X3,X3,X3,X3))=k3_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_30]), c_0_18]), c_0_18]), c_0_18]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28])).
% 8.49/8.67  cnf(c_0_59, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k3_enumset1(X2,X2,X2,X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_38])).
% 8.49/8.67  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_59])]), ['proof']).
% 8.49/8.67  # SZS output end CNFRefutation
% 8.49/8.67  # Proof object total steps             : 61
% 8.49/8.67  # Proof object clause steps            : 32
% 8.49/8.67  # Proof object formula steps           : 29
% 8.49/8.67  # Proof object conjectures             : 6
% 8.49/8.67  # Proof object clause conjectures      : 3
% 8.49/8.67  # Proof object formula conjectures     : 3
% 8.49/8.67  # Proof object initial clauses used    : 14
% 8.49/8.67  # Proof object initial formulas used   : 14
% 8.49/8.67  # Proof object generating inferences   : 8
% 8.49/8.67  # Proof object simplifying inferences  : 81
% 8.49/8.67  # Training examples: 0 positive, 0 negative
% 8.49/8.67  # Parsed axioms                        : 14
% 8.49/8.67  # Removed by relevancy pruning/SinE    : 0
% 8.49/8.67  # Initial clauses                      : 15
% 8.49/8.67  # Removed in clause preprocessing      : 7
% 8.49/8.67  # Initial clauses in saturation        : 8
% 8.49/8.67  # Processed clauses                    : 46849
% 8.49/8.67  # ...of these trivial                  : 510
% 8.49/8.67  # ...subsumed                          : 44916
% 8.49/8.67  # ...remaining for further processing  : 1423
% 8.49/8.67  # Other redundant clauses eliminated   : 0
% 8.49/8.67  # Clauses deleted for lack of memory   : 0
% 8.49/8.67  # Backward-subsumed                    : 253
% 8.49/8.67  # Backward-rewritten                   : 11
% 8.49/8.67  # Generated clauses                    : 3653702
% 8.49/8.67  # ...of the previous two non-trivial   : 3092537
% 8.49/8.67  # Contextual simplify-reflections      : 0
% 8.49/8.67  # Paramodulations                      : 3653702
% 8.49/8.67  # Factorizations                       : 0
% 8.49/8.67  # Equation resolutions                 : 0
% 8.49/8.67  # Propositional unsat checks           : 0
% 8.49/8.67  #    Propositional check models        : 0
% 8.49/8.67  #    Propositional check unsatisfiable : 0
% 8.49/8.67  #    Propositional clauses             : 0
% 8.49/8.67  #    Propositional clauses after purity: 0
% 8.49/8.67  #    Propositional unsat core size     : 0
% 8.49/8.67  #    Propositional preprocessing time  : 0.000
% 8.49/8.67  #    Propositional encoding time       : 0.000
% 8.49/8.67  #    Propositional solver time         : 0.000
% 8.49/8.67  #    Success case prop preproc time    : 0.000
% 8.49/8.67  #    Success case prop encoding time   : 0.000
% 8.49/8.67  #    Success case prop solver time     : 0.000
% 8.49/8.67  # Current number of processed clauses  : 1151
% 8.49/8.67  #    Positive orientable unit clauses  : 105
% 8.49/8.67  #    Positive unorientable unit clauses: 1046
% 8.49/8.67  #    Negative unit clauses             : 0
% 8.49/8.67  #    Non-unit-clauses                  : 0
% 8.49/8.67  # Current number of unprocessed clauses: 3039722
% 8.49/8.67  # ...number of literals in the above   : 3039722
% 8.49/8.67  # Current number of archived formulas  : 0
% 8.49/8.67  # Current number of archived clauses   : 279
% 8.49/8.67  # Clause-clause subsumption calls (NU) : 0
% 8.49/8.67  # Rec. Clause-clause subsumption calls : 0
% 8.49/8.67  # Non-unit clause-clause subsumptions  : 0
% 8.49/8.67  # Unit Clause-clause subsumption calls : 762729
% 8.49/8.67  # Rewrite failures with RHS unbound    : 0
% 8.49/8.67  # BW rewrite match attempts            : 739650
% 8.49/8.67  # BW rewrite match successes           : 147456
% 8.49/8.67  # Condensation attempts                : 0
% 8.49/8.67  # Condensation successes               : 0
% 8.49/8.67  # Termbank termtop insertions          : 15447780
% 8.57/8.75  
% 8.57/8.75  # -------------------------------------------------
% 8.57/8.75  # User time                : 7.764 s
% 8.57/8.75  # System time              : 0.631 s
% 8.57/8.75  # Total time               : 8.395 s
% 8.57/8.75  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
