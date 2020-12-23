%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0867+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:19 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   16 (  19 expanded)
%              Number of clauses        :    7 (   8 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  25 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_mcart_1)).

fof(t45_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(t132_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_tarski(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3))
      & k2_zfmisc_1(X3,k2_tarski(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X3,k1_tarski(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X4),k4_tarski(X2,X3),k4_tarski(X2,X4)) ),
    inference(assume_negation,[status(cth)],[t25_mcart_1])).

fof(c_0_5,negated_conjecture,(
    k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0),k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X12,X13,X14,X15] : k2_enumset1(X12,X13,X14,X15) = k2_xboole_0(k2_tarski(X12,X13),k2_tarski(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t45_enumset1])).

cnf(c_0_7,negated_conjecture,
    ( k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_enumset1(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0),k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X9,X10,X11] :
      ( k2_zfmisc_1(k1_tarski(X9),k2_tarski(X10,X11)) = k2_tarski(k4_tarski(X9,X10),k4_tarski(X9,X11))
      & k2_zfmisc_1(k2_tarski(X9,X10),k1_tarski(X11)) = k2_tarski(k4_tarski(X9,X11),k4_tarski(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_10,negated_conjecture,
    ( k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) != k2_xboole_0(k2_tarski(k4_tarski(esk1_0,esk3_0),k4_tarski(esk1_0,esk4_0)),k2_tarski(k4_tarski(esk2_0,esk3_0),k4_tarski(esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X6,X7,X8] :
      ( k2_zfmisc_1(k2_tarski(X6,X7),X8) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X6),X8),k2_zfmisc_1(k1_tarski(X7),X8))
      & k2_zfmisc_1(X8,k2_tarski(X6,X7)) = k2_xboole_0(k2_zfmisc_1(X8,k1_tarski(X6)),k2_zfmisc_1(X8,k1_tarski(X7))) ) ),
    inference(variable_rename,[status(thm)],[t132_zfmisc_1])).

cnf(c_0_13,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),k2_tarski(esk3_0,esk4_0)),k2_zfmisc_1(k1_tarski(esk2_0),k2_tarski(esk3_0,esk4_0))) != k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_11]),c_0_11])).

cnf(c_0_14,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_14])]),
    [proof]).

%------------------------------------------------------------------------------
