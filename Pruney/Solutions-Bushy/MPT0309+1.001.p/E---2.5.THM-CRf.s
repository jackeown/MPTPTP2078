%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0309+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:23 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   13 (  18 expanded)
%              Number of clauses        :    6 (   7 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   15 (  24 expanded)
%              Number of equality atoms :   14 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t121_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_xboole_0(X1,X2),k2_xboole_0(X3,X4)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X4)),k2_zfmisc_1(X2,X3)),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_zfmisc_1)).

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t4_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k2_zfmisc_1(k2_xboole_0(X1,X2),k2_xboole_0(X3,X4)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X4)),k2_zfmisc_1(X2,X3)),k2_zfmisc_1(X2,X4)) ),
    inference(assume_negation,[status(cth)],[t121_zfmisc_1])).

fof(c_0_4,negated_conjecture,(
    k2_zfmisc_1(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk3_0,esk4_0)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(esk1_0,esk3_0),k2_zfmisc_1(esk1_0,esk4_0)),k2_zfmisc_1(esk2_0,esk3_0)),k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X5,X6,X7] :
      ( k2_zfmisc_1(k2_xboole_0(X5,X6),X7) = k2_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X7))
      & k2_zfmisc_1(X7,k2_xboole_0(X5,X6)) = k2_xboole_0(k2_zfmisc_1(X7,X5),k2_zfmisc_1(X7,X6)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

cnf(c_0_6,negated_conjecture,
    ( k2_zfmisc_1(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk3_0,esk4_0)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(esk1_0,esk3_0),k2_zfmisc_1(esk1_0,esk4_0)),k2_zfmisc_1(esk2_0,esk3_0)),k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X8,X9,X10] : k2_xboole_0(k2_xboole_0(X8,X9),X10) = k2_xboole_0(X8,k2_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t4_xboole_1])).

cnf(c_0_9,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k2_zfmisc_1(esk1_0,k2_xboole_0(esk3_0,esk4_0)),k2_zfmisc_1(esk2_0,esk3_0)),k2_zfmisc_1(esk2_0,esk4_0)) != k2_zfmisc_1(k2_xboole_0(esk1_0,esk2_0),k2_xboole_0(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_7]),c_0_11])]),
    [proof]).

%------------------------------------------------------------------------------
