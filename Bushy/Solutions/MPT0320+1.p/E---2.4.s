%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t132_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:00 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   14 (  19 expanded)
%              Number of clauses        :    7 (   8 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  28 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t132_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_tarski(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3))
      & k2_zfmisc_1(X3,k2_tarski(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X3,k1_tarski(X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t132_zfmisc_1.p',t132_zfmisc_1)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t132_zfmisc_1.p',t41_enumset1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t132_zfmisc_1.p',t120_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k2_zfmisc_1(k2_tarski(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X3))
        & k2_zfmisc_1(X3,k2_tarski(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X3,k1_tarski(X2))) ) ),
    inference(assume_negation,[status(cth)],[t132_zfmisc_1])).

fof(c_0_4,negated_conjecture,
    ( k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),esk3_0),k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))
    | k2_zfmisc_1(esk3_0,k2_tarski(esk1_0,esk2_0)) != k2_xboole_0(k2_zfmisc_1(esk3_0,k1_tarski(esk1_0)),k2_zfmisc_1(esk3_0,k1_tarski(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X18,X19] : k2_tarski(X18,X19) = k2_xboole_0(k1_tarski(X18),k1_tarski(X19)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

cnf(c_0_6,negated_conjecture,
    ( k2_zfmisc_1(k2_tarski(esk1_0,esk2_0),esk3_0) != k2_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),esk3_0),k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))
    | k2_zfmisc_1(esk3_0,k2_tarski(esk1_0,esk2_0)) != k2_xboole_0(k2_zfmisc_1(esk3_0,k1_tarski(esk1_0)),k2_zfmisc_1(esk3_0,k1_tarski(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X14,X15,X16] :
      ( k2_zfmisc_1(k2_xboole_0(X14,X15),X16) = k2_xboole_0(k2_zfmisc_1(X14,X16),k2_zfmisc_1(X15,X16))
      & k2_zfmisc_1(X16,k2_xboole_0(X14,X15)) = k2_xboole_0(k2_zfmisc_1(X16,X14),k2_zfmisc_1(X16,X15)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_9,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0))) != k2_xboole_0(k2_zfmisc_1(esk3_0,k1_tarski(esk1_0)),k2_zfmisc_1(esk3_0,k1_tarski(esk2_0)))
    | k2_zfmisc_1(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk3_0) != k2_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),esk3_0),k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_6,c_0_7]),c_0_7])).

cnf(c_0_10,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( k2_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),esk3_0),k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)) != k2_zfmisc_1(k2_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10])])).

cnf(c_0_12,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12])]),
    [proof]).
%------------------------------------------------------------------------------
