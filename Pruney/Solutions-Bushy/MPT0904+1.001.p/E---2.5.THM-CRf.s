%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0904+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:23 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   20 (  85 expanded)
%              Number of clauses        :   13 (  36 expanded)
%              Number of leaves         :    3 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 ( 202 expanded)
%              Number of equality atoms :    3 (  24 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ~ r1_xboole_0(k4_zfmisc_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))
     => ( ~ r1_xboole_0(X1,X5)
        & ~ r1_xboole_0(X2,X6)
        & ~ r1_xboole_0(X3,X7)
        & ~ r1_xboole_0(X4,X8) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_mcart_1)).

fof(t53_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( ~ r1_xboole_0(k4_zfmisc_1(X1,X2,X3,X4),k4_zfmisc_1(X5,X6,X7,X8))
       => ( ~ r1_xboole_0(X1,X5)
          & ~ r1_xboole_0(X2,X6)
          & ~ r1_xboole_0(X3,X7)
          & ~ r1_xboole_0(X4,X8) ) ) ),
    inference(assume_negation,[status(cth)],[t64_mcart_1])).

fof(c_0_4,negated_conjecture,
    ( ~ r1_xboole_0(k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0))
    & ( r1_xboole_0(esk1_0,esk5_0)
      | r1_xboole_0(esk2_0,esk6_0)
      | r1_xboole_0(esk3_0,esk7_0)
      | r1_xboole_0(esk4_0,esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

fof(c_0_5,plain,(
    ! [X13,X14,X15,X16] : k4_zfmisc_1(X13,X14,X15,X16) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X13,X14),X15),X16) ),
    inference(variable_rename,[status(thm)],[t53_mcart_1])).

cnf(c_0_6,negated_conjecture,
    ( ~ r1_xboole_0(k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0),k4_zfmisc_1(esk5_0,esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ r1_xboole_0(X9,X10)
        | r1_xboole_0(k2_zfmisc_1(X9,X11),k2_zfmisc_1(X10,X12)) )
      & ( ~ r1_xboole_0(X11,X12)
        | r1_xboole_0(k2_zfmisc_1(X9,X11),k2_zfmisc_1(X10,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_9,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),esk4_0),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_6,c_0_7]),c_0_7])).

cnf(c_0_10,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_12,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk5_0)
    | r1_xboole_0(esk2_0,esk6_0)
    | r1_xboole_0(esk3_0,esk7_0)
    | r1_xboole_0(esk4_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18]),
    [proof]).

%------------------------------------------------------------------------------
