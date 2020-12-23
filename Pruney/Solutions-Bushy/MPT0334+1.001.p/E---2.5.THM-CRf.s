%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0334+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:26 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   13 (  16 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    3 (   4 expanded)
%              Depth                    :    4
%              Number of atoms          :   23 (  29 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t147_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( X1 != X2
     => k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).

fof(t87_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,X2)
     => k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(t17_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( X1 != X2
       => k4_xboole_0(k2_xboole_0(X3,k1_tarski(X1)),k1_tarski(X2)) = k2_xboole_0(k4_xboole_0(X3,k1_tarski(X2)),k1_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t147_zfmisc_1])).

fof(c_0_4,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_xboole_0(X6,X7)
      | k2_xboole_0(k4_xboole_0(X8,X6),X7) = k4_xboole_0(k2_xboole_0(X8,X7),X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_xboole_1])])).

fof(c_0_5,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | r1_xboole_0(k1_tarski(X4),k1_tarski(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).

fof(c_0_6,negated_conjecture,
    ( esk1_0 != esk2_0
    & k4_xboole_0(k2_xboole_0(esk3_0,k1_tarski(esk1_0)),k1_tarski(esk2_0)) != k2_xboole_0(k4_xboole_0(esk3_0,k1_tarski(esk2_0)),k1_tarski(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( k2_xboole_0(k4_xboole_0(X3,X1),X2) = k4_xboole_0(k2_xboole_0(X3,X2),X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(esk3_0,k1_tarski(esk1_0)),k1_tarski(esk2_0)) != k2_xboole_0(k4_xboole_0(esk3_0,k1_tarski(esk2_0)),k1_tarski(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X2)),k1_tarski(X3)) = k4_xboole_0(k2_xboole_0(X1,k1_tarski(X3)),k1_tarski(X2))
    | X2 = X3 ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),
    [proof]).

%------------------------------------------------------------------------------
