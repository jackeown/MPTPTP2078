%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0066+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:58 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   11 (  17 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    2 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  42 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_xboole_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X3) )
     => r2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

fof(l58_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X3) )
     => r2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l58_xboole_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X2,X3) )
       => r2_xboole_0(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t59_xboole_1])).

fof(c_0_3,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ r2_xboole_0(X5,X6)
      | r2_xboole_0(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l58_xboole_1])])).

fof(c_0_4,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r2_xboole_0(esk2_0,esk3_0)
    & ~ r2_xboole_0(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( r2_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( ~ r2_xboole_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r2_xboole_0(esk1_0,X1)
    | ~ r2_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( r2_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])]),
    [proof]).

%------------------------------------------------------------------------------
