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
% DateTime   : Thu Dec  3 10:37:59 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 281 expanded)
%              Number of clauses        :   39 ( 125 expanded)
%              Number of leaves         :   12 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 311 expanded)
%              Number of equality atoms :   52 ( 278 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(t90_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(t82_enumset1,axiom,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(t76_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t21_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(t78_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(t17_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(t16_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
        & X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t18_zfmisc_1])).

fof(c_0_13,plain,(
    ! [X22,X23] : r1_xboole_0(k4_xboole_0(X22,k3_xboole_0(X22,X23)),X23) ),
    inference(variable_rename,[status(thm)],[t90_xboole_1])).

fof(c_0_14,plain,(
    ! [X11,X12] : k4_xboole_0(X11,k4_xboole_0(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X9,X10] : k4_xboole_0(X9,k3_xboole_0(X9,X10)) = k4_xboole_0(X9,X10) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_16,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) = k1_tarski(esk1_0)
    & esk1_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_17,plain,(
    ! [X24] : k2_enumset1(X24,X24,X24,X24) = k1_tarski(X24) ),
    inference(variable_rename,[status(thm)],[t82_enumset1])).

fof(c_0_18,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_xboole_0(X16,X17)
      | r1_xboole_0(k3_xboole_0(X18,X16),k3_xboole_0(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_xboole_1])])).

cnf(c_0_19,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X13,X14,X15] : k3_xboole_0(X13,k4_xboole_0(X14,X15)) = k4_xboole_0(k3_xboole_0(X13,X14),X15) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_23,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) = k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

fof(c_0_28,plain,(
    ! [X6,X7,X8] : k4_xboole_0(k4_xboole_0(X6,X7),X8) = k4_xboole_0(X6,k2_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))) = k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24]),c_0_24]),c_0_20])).

fof(c_0_31,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k2_xboole_0(X4,X5)) = X4 ),
    inference(variable_rename,[status(thm)],[t21_xboole_1])).

cnf(c_0_32,plain,
    ( r1_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X1)),k4_xboole_0(X3,k4_xboole_0(X3,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_20]),c_0_20])).

cnf(c_0_33,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_20]),c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) = k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_30])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_xboole_0(X19,X20)
      | k3_xboole_0(X19,k2_xboole_0(X20,X21)) = k3_xboole_0(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).

cnf(c_0_39,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))) = k4_xboole_0(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),X1))) = k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_35]),c_0_27])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_37,c_0_20])).

cnf(c_0_43,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k3_xboole_0(X1,X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X27,X28] :
      ( X27 = X28
      | r1_xboole_0(k1_tarski(X27),k1_tarski(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).

cnf(c_0_45,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),X1)) = k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_41])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X1),X2)) = X1 ),
    inference(rw,[status(thm)],[c_0_42,c_0_34])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3))) = k4_xboole_0(X1,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_20]),c_0_20])).

cnf(c_0_49,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_50,plain,(
    ! [X25,X26] :
      ( ~ r1_xboole_0(k1_tarski(X25),k1_tarski(X26))
      | X25 != X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),X1),k4_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),X2)),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_27])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_47,c_0_47])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)) = k4_xboole_0(X1,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_48,c_0_34])).

cnf(c_0_54,plain,
    ( X1 = X2
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_24]),c_0_24])).

cnf(c_0_55,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X2))
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),X1),k4_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)))),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),X3)) = k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X3))
    | X1 = X2 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_59,plain,
    ( X1 != X2
    | ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_24]),c_0_24])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(X1,k4_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)))))),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_46]),c_0_35])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),X1)) = k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_36]),c_0_47]),c_0_58])).

cnf(c_0_62,plain,
    ( ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_62]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.21/0.40  # and selection function SelectCQIArNpEqFirst.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.026 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t18_zfmisc_1, conjecture, ![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 0.21/0.40  fof(t90_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 0.21/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.40  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.21/0.40  fof(t82_enumset1, axiom, ![X1]:k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 0.21/0.40  fof(t76_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 0.21/0.40  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.21/0.40  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.21/0.40  fof(t21_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 0.21/0.40  fof(t78_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,X2)=>k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 0.21/0.40  fof(t17_zfmisc_1, axiom, ![X1, X2]:(X1!=X2=>r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 0.21/0.40  fof(t16_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),k1_tarski(X2))&X1=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 0.21/0.40  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t18_zfmisc_1])).
% 0.21/0.40  fof(c_0_13, plain, ![X22, X23]:r1_xboole_0(k4_xboole_0(X22,k3_xboole_0(X22,X23)),X23), inference(variable_rename,[status(thm)],[t90_xboole_1])).
% 0.21/0.40  fof(c_0_14, plain, ![X11, X12]:k4_xboole_0(X11,k4_xboole_0(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.40  fof(c_0_15, plain, ![X9, X10]:k4_xboole_0(X9,k3_xboole_0(X9,X10))=k4_xboole_0(X9,X10), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.21/0.40  fof(c_0_16, negated_conjecture, (k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))=k1_tarski(esk1_0)&esk1_0!=esk2_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.21/0.40  fof(c_0_17, plain, ![X24]:k2_enumset1(X24,X24,X24,X24)=k1_tarski(X24), inference(variable_rename,[status(thm)],[t82_enumset1])).
% 0.21/0.40  fof(c_0_18, plain, ![X16, X17, X18]:(~r1_xboole_0(X16,X17)|r1_xboole_0(k3_xboole_0(X18,X16),k3_xboole_0(X18,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t76_xboole_1])])).
% 0.21/0.40  cnf(c_0_19, plain, (r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.40  cnf(c_0_20, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.40  cnf(c_0_21, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  fof(c_0_22, plain, ![X13, X14, X15]:k3_xboole_0(X13,k4_xboole_0(X14,X15))=k4_xboole_0(k3_xboole_0(X13,X14),X15), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.21/0.40  cnf(c_0_23, negated_conjecture, (k3_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))=k1_tarski(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_24, plain, (k2_enumset1(X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  cnf(c_0_25, plain, (r1_xboole_0(k3_xboole_0(X3,X1),k3_xboole_0(X3,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.40  cnf(c_0_26, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.40  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.21/0.40  fof(c_0_28, plain, ![X6, X7, X8]:k4_xboole_0(k4_xboole_0(X6,X7),X8)=k4_xboole_0(X6,k2_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.21/0.40  cnf(c_0_29, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.40  cnf(c_0_30, negated_conjecture, (k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)))=k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24]), c_0_24]), c_0_20])).
% 0.21/0.40  fof(c_0_31, plain, ![X4, X5]:k3_xboole_0(X4,k2_xboole_0(X4,X5))=X4, inference(variable_rename,[status(thm)],[t21_xboole_1])).
% 0.21/0.40  cnf(c_0_32, plain, (r1_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X1)),k4_xboole_0(X3,k4_xboole_0(X3,X2)))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_20]), c_0_20])).
% 0.21/0.40  cnf(c_0_33, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.40  cnf(c_0_34, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.40  cnf(c_0_35, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_20]), c_0_20])).
% 0.21/0.40  cnf(c_0_36, negated_conjecture, (k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))=k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))), inference(spm,[status(thm)],[c_0_27, c_0_30])).
% 0.21/0.40  cnf(c_0_37, plain, (k3_xboole_0(X1,k2_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.40  fof(c_0_38, plain, ![X19, X20, X21]:(~r1_xboole_0(X19,X20)|k3_xboole_0(X19,k2_xboole_0(X20,X21))=k3_xboole_0(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_xboole_1])])).
% 0.21/0.40  cnf(c_0_39, plain, (r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.40  cnf(c_0_40, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)))=k4_xboole_0(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_27, c_0_34])).
% 0.21/0.40  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),X1)))=k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_35]), c_0_27])).
% 0.21/0.40  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_37, c_0_20])).
% 0.21/0.40  cnf(c_0_43, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k3_xboole_0(X1,X3)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.40  fof(c_0_44, plain, ![X27, X28]:(X27=X28|r1_xboole_0(k1_tarski(X27),k1_tarski(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).
% 0.21/0.40  cnf(c_0_45, plain, (r1_xboole_0(k4_xboole_0(k4_xboole_0(X1,X2),X3),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.40  cnf(c_0_46, negated_conjecture, (k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),X1))=k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),X1))), inference(spm,[status(thm)],[c_0_27, c_0_41])).
% 0.21/0.40  cnf(c_0_47, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X1),X2))=X1), inference(rw,[status(thm)],[c_0_42, c_0_34])).
% 0.21/0.40  cnf(c_0_48, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X3)))=k4_xboole_0(X1,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_20]), c_0_20])).
% 0.21/0.40  cnf(c_0_49, plain, (X1=X2|r1_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.40  fof(c_0_50, plain, ![X25, X26]:(~r1_xboole_0(k1_tarski(X25),k1_tarski(X26))|X25!=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_zfmisc_1])])).
% 0.21/0.40  cnf(c_0_51, negated_conjecture, (r1_xboole_0(k4_xboole_0(k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),X1),k4_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),X2)),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_27])).
% 0.21/0.40  cnf(c_0_52, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X1))=X1), inference(spm,[status(thm)],[c_0_47, c_0_47])).
% 0.21/0.40  cnf(c_0_53, plain, (k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3))=k4_xboole_0(X1,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_48, c_0_34])).
% 0.21/0.40  cnf(c_0_54, plain, (X1=X2|r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_24]), c_0_24])).
% 0.21/0.40  cnf(c_0_55, plain, (~r1_xboole_0(k1_tarski(X1),k1_tarski(X2))|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.40  cnf(c_0_56, negated_conjecture, (r1_xboole_0(k4_xboole_0(k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),X1),k4_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)))),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.40  cnf(c_0_57, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),X3))=k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_enumset1(X1,X1,X1,X1),X3))|X1=X2), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.40  cnf(c_0_58, negated_conjecture, (esk1_0!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_59, plain, (X1!=X2|~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_24]), c_0_24])).
% 0.21/0.40  cnf(c_0_60, negated_conjecture, (r1_xboole_0(k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(X1,k4_xboole_0(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)))))),k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_46]), c_0_35])).
% 0.21/0.40  cnf(c_0_61, negated_conjecture, (k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),k4_xboole_0(k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0),X1))=k2_enumset1(esk1_0,esk1_0,esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_36]), c_0_47]), c_0_58])).
% 0.21/0.40  cnf(c_0_62, plain, (~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_59])).
% 0.21/0.40  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_62]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 64
% 0.21/0.40  # Proof object clause steps            : 39
% 0.21/0.40  # Proof object formula steps           : 25
% 0.21/0.40  # Proof object conjectures             : 14
% 0.21/0.40  # Proof object clause conjectures      : 11
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 13
% 0.21/0.40  # Proof object initial formulas used   : 12
% 0.21/0.40  # Proof object generating inferences   : 12
% 0.21/0.40  # Proof object simplifying inferences  : 29
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 12
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 13
% 0.21/0.40  # Removed in clause preprocessing      : 2
% 0.21/0.40  # Initial clauses in saturation        : 11
% 0.21/0.40  # Processed clauses                    : 139
% 0.21/0.40  # ...of these trivial                  : 32
% 0.21/0.40  # ...subsumed                          : 0
% 0.21/0.40  # ...remaining for further processing  : 107
% 0.21/0.40  # Other redundant clauses eliminated   : 1
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 0
% 0.21/0.40  # Backward-rewritten                   : 15
% 0.21/0.40  # Generated clauses                    : 2292
% 0.21/0.40  # ...of the previous two non-trivial   : 1233
% 0.21/0.40  # Contextual simplify-reflections      : 0
% 0.21/0.40  # Paramodulations                      : 2291
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 1
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 80
% 0.21/0.40  #    Positive orientable unit clauses  : 73
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 2
% 0.21/0.40  #    Non-unit-clauses                  : 5
% 0.21/0.40  # Current number of unprocessed clauses: 1093
% 0.21/0.40  # ...number of literals in the above   : 1177
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 28
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 1
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 1
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.40  # Unit Clause-clause subsumption calls : 12
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 280
% 0.21/0.40  # BW rewrite match successes           : 12
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 49245
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.055 s
% 0.21/0.40  # System time              : 0.007 s
% 0.21/0.40  # Total time               : 0.062 s
% 0.21/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
