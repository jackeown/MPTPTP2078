%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0319+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:24 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   14 (  19 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  47 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t131_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( X1 != X2
     => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X4))
        & r1_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X4,k1_tarski(X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_zfmisc_1)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(t17_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( X1 != X2
       => ( r1_xboole_0(k2_zfmisc_1(k1_tarski(X1),X3),k2_zfmisc_1(k1_tarski(X2),X4))
          & r1_xboole_0(k2_zfmisc_1(X3,k1_tarski(X1)),k2_zfmisc_1(X4,k1_tarski(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t131_zfmisc_1])).

fof(c_0_4,negated_conjecture,
    ( esk1_0 != esk2_0
    & ( ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),esk3_0),k2_zfmisc_1(k1_tarski(esk2_0),esk4_0))
      | ~ r1_xboole_0(k2_zfmisc_1(esk3_0,k1_tarski(esk1_0)),k2_zfmisc_1(esk4_0,k1_tarski(esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ r1_xboole_0(X5,X6)
        | r1_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X8)) )
      & ( ~ r1_xboole_0(X7,X8)
        | r1_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

cnf(c_0_6,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(k1_tarski(esk1_0),esk3_0),k2_zfmisc_1(k1_tarski(esk2_0),esk4_0))
    | ~ r1_xboole_0(k2_zfmisc_1(esk3_0,k1_tarski(esk1_0)),k2_zfmisc_1(esk4_0,k1_tarski(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( X9 = X10
      | r1_xboole_0(k1_tarski(X9),k1_tarski(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_zfmisc_1])])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk1_0),k1_tarski(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8])).

cnf(c_0_11,plain,
    ( X1 = X2
    | r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),
    [proof]).

%------------------------------------------------------------------------------
