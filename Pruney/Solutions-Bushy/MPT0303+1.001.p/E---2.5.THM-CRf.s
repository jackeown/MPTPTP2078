%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0303+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:23 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   24 ( 109 expanded)
%              Number of clauses        :   17 (  46 expanded)
%              Number of leaves         :    3 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 ( 309 expanded)
%              Number of equality atoms :   14 ( 108 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X1) = k2_zfmisc_1(X2,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X1) = k2_zfmisc_1(X2,X2)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t115_zfmisc_1])).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8] :
      ( ( r2_hidden(X5,X7)
        | ~ r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) )
      & ( r2_hidden(X6,X8)
        | ~ r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) )
      & ( ~ r2_hidden(X5,X7)
        | ~ r2_hidden(X6,X8)
        | r2_hidden(k4_tarski(X5,X6),k2_zfmisc_1(X7,X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_5,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk2_0) = k2_zfmisc_1(esk3_0,esk3_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk2_0) = k2_zfmisc_1(esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk3_0,esk3_0))
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

fof(c_0_10,plain,(
    ! [X9,X10] :
      ( ( ~ r2_hidden(esk1_2(X9,X10),X9)
        | ~ r2_hidden(esk1_2(X9,X10),X10)
        | X9 = X10 )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r2_hidden(esk1_2(X9,X10),X10)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( esk2_0 = X1
    | r2_hidden(esk1_2(esk2_0,X1),X1)
    | r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_0,esk3_0),esk3_0)
    | ~ r2_hidden(esk1_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_14]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_12]),c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_0,esk3_0),esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_21,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk1_2(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_19])]),c_0_15]),
    [proof]).

%------------------------------------------------------------------------------
