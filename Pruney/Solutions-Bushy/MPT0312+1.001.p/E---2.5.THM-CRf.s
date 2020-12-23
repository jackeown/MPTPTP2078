%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0312+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:24 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   19 (  28 expanded)
%              Number of clauses        :   10 (  11 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  52 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t124_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X3)) = k2_zfmisc_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4) )
       => k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X3)) = k2_zfmisc_1(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t124_zfmisc_1])).

fof(c_0_5,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r1_tarski(esk3_0,esk4_0)
    & k3_xboole_0(k2_zfmisc_1(esk1_0,esk4_0),k2_zfmisc_1(esk2_0,esk3_0)) != k2_zfmisc_1(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10] : k2_zfmisc_1(k3_xboole_0(X7,X8),k3_xboole_0(X9,X10)) = k3_xboole_0(k2_zfmisc_1(X7,X9),k2_zfmisc_1(X8,X10)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_8,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k3_xboole_0(X11,X12) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_9,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk1_0,esk4_0),k2_zfmisc_1(esk2_0,esk3_0)) != k2_zfmisc_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk1_0,esk2_0),k3_xboole_0(esk3_0,esk4_0)) != k2_zfmisc_1(esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k3_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),
    [proof]).

%------------------------------------------------------------------------------
