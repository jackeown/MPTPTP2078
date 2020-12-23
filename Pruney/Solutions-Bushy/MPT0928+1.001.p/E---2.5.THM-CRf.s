%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0928+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:25 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   20 (  35 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 ( 110 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4)
        & r1_tarski(X5,X6)
        & r1_tarski(X7,X8) )
     => r1_tarski(k4_zfmisc_1(X1,X3,X5,X7),k4_zfmisc_1(X2,X4,X6,X8)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(t119_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(t77_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4)
        & r1_tarski(X5,X6) )
     => r1_tarski(k3_zfmisc_1(X1,X3,X5),k3_zfmisc_1(X2,X4,X6)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_mcart_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6,X7,X8] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4)
          & r1_tarski(X5,X6)
          & r1_tarski(X7,X8) )
       => r1_tarski(k4_zfmisc_1(X1,X3,X5,X7),k4_zfmisc_1(X2,X4,X6,X8)) ) ),
    inference(assume_negation,[status(cth)],[t88_mcart_1])).

fof(c_0_5,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk5_0,esk6_0)
    & r1_tarski(esk7_0,esk8_0)
    & ~ r1_tarski(k4_zfmisc_1(esk1_0,esk3_0,esk5_0,esk7_0),k4_zfmisc_1(esk2_0,esk4_0,esk6_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X9,X10,X11,X12] : k4_zfmisc_1(X9,X10,X11,X12) = k2_zfmisc_1(k3_zfmisc_1(X9,X10,X11),X12) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

cnf(c_0_7,negated_conjecture,
    ( ~ r1_tarski(k4_zfmisc_1(esk1_0,esk3_0,esk5_0,esk7_0),k4_zfmisc_1(esk2_0,esk4_0,esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X13,X14,X15,X16] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(k2_zfmisc_1(X13,X15),k2_zfmisc_1(X14,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_zfmisc_1])])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(k3_zfmisc_1(esk1_0,esk3_0,esk5_0),esk7_0),k2_zfmisc_1(k3_zfmisc_1(esk2_0,esk4_0,esk6_0),esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_7,c_0_8]),c_0_8])).

cnf(c_0_11,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_13,plain,(
    ! [X17,X18,X19,X20,X21,X22] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X19,X20)
      | ~ r1_tarski(X21,X22)
      | r1_tarski(k3_zfmisc_1(X17,X19,X21),k3_zfmisc_1(X18,X20,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_mcart_1])])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(k3_zfmisc_1(esk1_0,esk3_0,esk5_0),k3_zfmisc_1(esk2_0,esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_15,plain,
    ( r1_tarski(k3_zfmisc_1(X1,X3,X5),k3_zfmisc_1(X2,X4,X6))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r1_tarski(X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18])]),
    [proof]).

%------------------------------------------------------------------------------
