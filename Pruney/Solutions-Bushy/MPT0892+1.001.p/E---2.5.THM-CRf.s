%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0892+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:21 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  59 expanded)
%              Number of clauses        :   12 (  25 expanded)
%              Number of leaves         :    3 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 ( 128 expanded)
%              Number of equality atoms :    3 (  18 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ~ r1_xboole_0(k3_zfmisc_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
     => ( ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X3,X6) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ~ r1_xboole_0(k3_zfmisc_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
       => ( ~ r1_xboole_0(X1,X4)
          & ~ r1_xboole_0(X2,X5)
          & ~ r1_xboole_0(X3,X6) ) ) ),
    inference(assume_negation,[status(cth)],[t52_mcart_1])).

fof(c_0_4,negated_conjecture,
    ( ~ r1_xboole_0(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
    & ( r1_xboole_0(esk1_0,esk4_0)
      | r1_xboole_0(esk2_0,esk5_0)
      | r1_xboole_0(esk3_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

fof(c_0_5,plain,(
    ! [X7,X8,X9] : k3_zfmisc_1(X7,X8,X9) = k2_zfmisc_1(k2_zfmisc_1(X7,X8),X9) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_6,negated_conjecture,
    ( ~ r1_xboole_0(k3_zfmisc_1(esk1_0,esk2_0,esk3_0),k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ r1_xboole_0(X12,X13)
        | r1_xboole_0(k2_zfmisc_1(X12,X14),k2_zfmisc_1(X13,X15)) )
      & ( ~ r1_xboole_0(X14,X15)
        | r1_xboole_0(k2_zfmisc_1(X12,X14),k2_zfmisc_1(X13,X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_9,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0),esk3_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_6,c_0_7]),c_0_7])).

cnf(c_0_10,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r1_xboole_0(esk1_0,esk4_0)
    | r1_xboole_0(esk2_0,esk5_0)
    | r1_xboole_0(esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(esk1_0,esk2_0),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk5_0)
    | r1_xboole_0(esk1_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_xboole_0(esk1_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_15,c_0_16]),c_0_17]),
    [proof]).

%------------------------------------------------------------------------------
