%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t25_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:05 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   23 (  51 expanded)
%              Number of clauses        :   12 (  24 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  65 expanded)
%              Number of equality atoms :   26 (  64 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t25_mcart_1.p',t25_mcart_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t25_mcart_1.p',idempotence_k2_xboole_0)).

fof(t132_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_tarski(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3))
      & k2_zfmisc_1(X3,k2_tarski(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X3,k1_tarski(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t25_mcart_1.p',t132_zfmisc_1)).

fof(t45_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t25_mcart_1.p',t45_enumset1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t25_mcart_1.p',t36_zfmisc_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(assume_negation,[status(cth)],[t25_mcart_1])).

fof(c_0_6,plain,(
    ! [X17] : k2_xboole_0(X17,X17) = X17 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_7,plain,(
    ! [X18,X19,X20] :
      ( k2_zfmisc_1(k2_tarski(X18,X19),X20) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X18),X20),k2_zfmisc_1(k1_tarski(X19),X20))
      & k2_zfmisc_1(X20,k2_tarski(X18,X19)) = k2_xboole_0(k2_zfmisc_1(X20,k1_tarski(X18)),k2_zfmisc_1(X20,k1_tarski(X19))) ) ),
    inference(variable_rename,[status(thm)],[t132_zfmisc_1])).

fof(c_0_8,negated_conjecture,(
    k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0),k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X29,X30,X31,X32] : k2_enumset1(X29,X30,X31,X32) = k2_xboole_0(k2_tarski(X29,X30),k2_tarski(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t45_enumset1])).

fof(c_0_10,plain,(
    ! [X26,X27,X28] :
      ( k2_zfmisc_1(k1_tarski(X26),k2_tarski(X27,X28)) = k2_tarski(k4_tarski(X26,X27),k4_tarski(X26,X28))
      & k2_zfmisc_1(k2_tarski(X26,X27),k1_tarski(X28)) = k2_tarski(k4_tarski(X26,X28),k4_tarski(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_11,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0),k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X1),X2) = k2_zfmisc_1(k1_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_xboole_0(k2_tarski(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0)),k2_tarski(k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( k2_xboole_0(k2_zfmisc_1(k2_tarski(X1,X1),X2),k2_zfmisc_1(k1_tarski(X3),X2)) = k2_zfmisc_1(k2_tarski(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(k2_tarski(esk1_0,esk1_0),k2_tarski(esk3_0,esk4_0)),k2_zfmisc_1(k2_tarski(esk2_0,esk2_0),k2_tarski(esk3_0,esk4_0))) != k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

cnf(c_0_21,plain,
    ( k2_xboole_0(k2_zfmisc_1(k2_tarski(X1,X1),X2),k2_zfmisc_1(k2_tarski(X3,X3),X2)) = k2_zfmisc_1(k2_tarski(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
