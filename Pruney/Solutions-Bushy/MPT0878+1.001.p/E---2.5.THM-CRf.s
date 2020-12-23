%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0878+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:20 EST 2020

% Result     : Theorem 0.09s
% Output     : CNFRefutation 0.09s
% Verified   : 
% Statistics : Number of formulae       :   15 (  85 expanded)
%              Number of clauses        :   10 (  34 expanded)
%              Number of leaves         :    2 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 ( 279 expanded)
%              Number of equality atoms :   48 ( 278 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_mcart_1,conjecture,(
    ! [X1,X2] :
      ( k3_zfmisc_1(X1,X1,X1) = k3_zfmisc_1(X2,X2,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).

fof(t36_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( k3_zfmisc_1(X1,X2,X3) = k3_zfmisc_1(X4,X5,X6)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X3 = k1_xboole_0
        | ( X1 = X4
          & X2 = X5
          & X3 = X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k3_zfmisc_1(X1,X1,X1) = k3_zfmisc_1(X2,X2,X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t38_mcart_1])).

fof(c_0_3,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( X7 = X10
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) != k3_zfmisc_1(X10,X11,X12) )
      & ( X8 = X11
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) != k3_zfmisc_1(X10,X11,X12) )
      & ( X9 = X12
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0
        | k3_zfmisc_1(X7,X8,X9) != k3_zfmisc_1(X10,X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_mcart_1])])])).

fof(c_0_4,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk1_0,esk1_0) = k3_zfmisc_1(esk2_0,esk2_0,esk2_0)
    & esk1_0 != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X1 = k1_xboole_0
    | k3_zfmisc_1(X3,X4,X1) != k3_zfmisc_1(X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( k3_zfmisc_1(esk1_0,esk1_0,esk1_0) = k3_zfmisc_1(esk2_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk1_0 = X1
    | k3_zfmisc_1(esk2_0,esk2_0,esk2_0) != k3_zfmisc_1(X2,X3,X1) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_8,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_7]),c_0_8])).

cnf(c_0_10,plain,
    ( X1 = X2
    | X3 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k1_xboole_0
    | k3_zfmisc_1(X3,X1,X4) != k3_zfmisc_1(X5,X2,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,negated_conjecture,
    ( k3_zfmisc_1(esk2_0,esk2_0,esk2_0) = k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_6,c_0_9]),c_0_9]),c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( esk2_0 = X1
    | k3_zfmisc_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k3_zfmisc_1(X2,X1,X3) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_14,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_12]),
    [proof]).

%------------------------------------------------------------------------------
