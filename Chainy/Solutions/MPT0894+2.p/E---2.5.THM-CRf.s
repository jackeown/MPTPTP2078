%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0894+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:56 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   12 (  15 expanded)
%              Number of clauses        :    5 (   6 expanded)
%              Number of leaves         :    3 (   4 expanded)
%              Depth                    :    4
%              Number of atoms          :   12 (  15 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t54_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] : k3_zfmisc_1(k2_zfmisc_1(X1,X2),X3,X4) = k4_zfmisc_1(X1,X2,X3,X4) ),
    inference(assume_negation,[status(cth)],[t54_mcart_1])).

fof(c_0_4,plain,(
    ! [X17,X18,X19,X20] : k4_zfmisc_1(X17,X18,X19,X20) = k2_zfmisc_1(k3_zfmisc_1(X17,X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X25,X26,X27] : k3_zfmisc_1(X25,X26,X27) = k2_zfmisc_1(k2_zfmisc_1(X25,X26),X27) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_6,negated_conjecture,(
    k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0) != k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( k3_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0,esk4_0) != k4_zfmisc_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_8]),c_0_10])]),
    [proof]).
%------------------------------------------------------------------------------
