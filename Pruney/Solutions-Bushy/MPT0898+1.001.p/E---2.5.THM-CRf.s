%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0898+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:22 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   14 (  98 expanded)
%              Number of clauses        :    9 (  39 expanded)
%              Number of leaves         :    2 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 ( 408 expanded)
%              Number of equality atoms :   55 ( 407 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_mcart_1,conjecture,(
    ! [X1,X2] :
      ( k4_zfmisc_1(X1,X1,X1,X1) = k4_zfmisc_1(X2,X2,X2,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_mcart_1)).

fof(t56_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k4_zfmisc_1(X1,X2,X3,X4) = k4_zfmisc_1(X5,X6,X7,X8)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | X4 = k1_xboole_0
        | ( X1 = X5
          & X2 = X6
          & X3 = X7
          & X4 = X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_zfmisc_1(X1,X1,X1,X1) = k4_zfmisc_1(X2,X2,X2,X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t58_mcart_1])).

fof(c_0_3,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( X9 = X13
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) != k4_zfmisc_1(X13,X14,X15,X16) )
      & ( X10 = X14
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) != k4_zfmisc_1(X13,X14,X15,X16) )
      & ( X11 = X15
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) != k4_zfmisc_1(X13,X14,X15,X16) )
      & ( X12 = X16
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0
        | k4_zfmisc_1(X9,X10,X11,X12) != k4_zfmisc_1(X13,X14,X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_mcart_1])])])).

fof(c_0_4,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk1_0,esk1_0,esk1_0) = k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0)
    & esk1_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X1 = k1_xboole_0
    | k4_zfmisc_1(X3,X4,X5,X1) != k4_zfmisc_1(X6,X7,X8,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( k4_zfmisc_1(esk1_0,esk1_0,esk1_0,esk1_0) = k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk1_0 = X1
    | k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0) != k4_zfmisc_1(X2,X3,X4,X1) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_8,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_7]),c_0_8])).

cnf(c_0_10,negated_conjecture,
    ( k4_zfmisc_1(esk2_0,esk2_0,esk2_0,esk2_0) = k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_6,c_0_9]),c_0_9]),c_0_9]),c_0_9])).

cnf(c_0_11,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( esk2_0 = X1
    | k4_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != k4_zfmisc_1(X2,X3,X4,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_10]),c_0_11])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_11]),
    [proof]).

%------------------------------------------------------------------------------
