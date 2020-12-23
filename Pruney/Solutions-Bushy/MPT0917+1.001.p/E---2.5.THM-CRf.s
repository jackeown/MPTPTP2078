%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0917+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:24 EST 2020

% Result     : Theorem 0.09s
% Output     : CNFRefutation 0.09s
% Verified   : 
% Statistics : Number of formulae       :   16 (  31 expanded)
%              Number of clauses        :    9 (  11 expanded)
%              Number of leaves         :    3 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  79 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t77_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4)
        & r1_tarski(X5,X6) )
     => r1_tarski(k3_zfmisc_1(X1,X3,X5),k3_zfmisc_1(X2,X4,X6)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t119_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4)
          & r1_tarski(X5,X6) )
       => r1_tarski(k3_zfmisc_1(X1,X3,X5),k3_zfmisc_1(X2,X4,X6)) ) ),
    inference(assume_negation,[status(cth)],[t77_mcart_1])).

fof(c_0_4,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk5_0,esk6_0)
    & ~ r1_tarski(k3_zfmisc_1(esk1_0,esk3_0,esk5_0),k3_zfmisc_1(esk2_0,esk4_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X7,X8,X9] : k3_zfmisc_1(X7,X8,X9) = k2_zfmisc_1(k2_zfmisc_1(X7,X8),X9) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_6,negated_conjecture,
    ( ~ r1_tarski(k3_zfmisc_1(esk1_0,esk3_0,esk5_0),k3_zfmisc_1(esk2_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X10,X11,X12,X13] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X12,X13)
      | r1_tarski(k2_zfmisc_1(X10,X12),k2_zfmisc_1(X11,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_zfmisc_1])])).

cnf(c_0_9,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0),esk5_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_6,c_0_7]),c_0_7])).

cnf(c_0_10,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(esk1_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_10]),c_0_13]),c_0_14])]),
    [proof]).

%------------------------------------------------------------------------------
