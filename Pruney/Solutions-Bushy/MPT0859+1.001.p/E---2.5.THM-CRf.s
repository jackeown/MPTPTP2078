%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0859+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:18 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   19 (  39 expanded)
%              Number of clauses        :   12 (  16 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   65 ( 136 expanded)
%              Number of equality atoms :   32 (  56 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t15_mcart_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))
     => ( ( k1_mcart_1(X1) = X2
          | k1_mcart_1(X1) = X3 )
        & r2_hidden(k2_mcart_1(X1),X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_tarski(X2,X3),X4))
       => ( ( k1_mcart_1(X1) = X2
            | k1_mcart_1(X1) = X3 )
          & r2_hidden(k2_mcart_1(X1),X4) ) ) ),
    inference(assume_negation,[status(cth)],[t15_mcart_1])).

fof(c_0_4,plain,(
    ! [X14,X15,X16] :
      ( ( r2_hidden(k1_mcart_1(X14),X15)
        | ~ r2_hidden(X14,k2_zfmisc_1(X15,X16)) )
      & ( r2_hidden(k2_mcart_1(X14),X16)
        | ~ r2_hidden(X14,k2_zfmisc_1(X15,X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

fof(c_0_5,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),esk5_0))
    & ( k1_mcart_1(esk2_0) != esk3_0
      | ~ r2_hidden(k2_mcart_1(esk2_0),esk5_0) )
    & ( k1_mcart_1(esk2_0) != esk4_0
      | ~ r2_hidden(k2_mcart_1(esk2_0),esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X5
        | X8 = X6
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X5
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( esk1_3(X10,X11,X12) != X10
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( esk1_3(X10,X11,X12) != X11
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | esk1_3(X10,X11,X12) = X10
        | esk1_3(X10,X11,X12) = X11
        | X12 = k2_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(k2_tarski(esk3_0,esk4_0),esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk4_0
    | ~ r2_hidden(k2_mcart_1(esk2_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk2_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0
    | ~ r2_hidden(k2_mcart_1(esk2_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk2_0),k2_tarski(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12])])).

cnf(c_0_17,negated_conjecture,
    ( k1_mcart_1(esk2_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_12])])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),
    [proof]).

%------------------------------------------------------------------------------
