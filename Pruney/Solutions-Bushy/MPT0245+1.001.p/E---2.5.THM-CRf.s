%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0245+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:17 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   10 (  16 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    2 (   4 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  40 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t40_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r2_hidden(X3,X1)
        | r1_tarski(X1,k4_xboole_0(X2,k1_tarski(X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_zfmisc_1)).

fof(l2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r2_hidden(X3,X1)
        | r1_tarski(X1,k4_xboole_0(X2,k1_tarski(X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_zfmisc_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,X2)
       => ( r2_hidden(X3,X1)
          | r1_tarski(X1,k4_xboole_0(X2,k1_tarski(X3))) ) ) ),
    inference(assume_negation,[status(cth)],[t40_zfmisc_1])).

fof(c_0_3,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & ~ r2_hidden(esk3_0,esk1_0)
    & ~ r1_tarski(esk1_0,k4_xboole_0(esk2_0,k1_tarski(esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

fof(c_0_4,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | r2_hidden(X6,X4)
      | r1_tarski(X4,k4_xboole_0(X5,k1_tarski(X6))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_zfmisc_1])])).

cnf(c_0_5,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k4_xboole_0(esk2_0,k1_tarski(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( r2_hidden(X3,X1)
    | r1_tarski(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_9,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7])]),c_0_8]),
    [proof]).

%------------------------------------------------------------------------------
