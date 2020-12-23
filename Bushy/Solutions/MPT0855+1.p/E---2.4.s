%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t11_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:04 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   20 (  29 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 112 expanded)
%              Number of equality atoms :   32 (  41 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t11_mcart_1.p',t8_mcart_1)).

fof(t11_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) )
     => ( ! [X4,X5] : X1 != k4_tarski(X4,X5)
        | r2_hidden(X1,k2_zfmisc_1(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t11_mcart_1.p',t11_mcart_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t11_mcart_1.p',d2_zfmisc_1)).

fof(c_0_3,plain,(
    ! [X42,X43,X44] :
      ( X42 != k4_tarski(X43,X44)
      | k4_tarski(k1_mcart_1(X42),k2_mcart_1(X42)) = X42 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_mcart_1])])])).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_hidden(k1_mcart_1(X1),X2)
          & r2_hidden(k2_mcart_1(X1),X3) )
       => ( ! [X4,X5] : X1 != k4_tarski(X4,X5)
          | r2_hidden(X1,k2_zfmisc_1(X2,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t11_mcart_1])).

fof(c_0_5,plain,(
    ! [X14,X15,X16,X17,X20,X21,X22,X23,X24,X25,X27,X28] :
      ( ( r2_hidden(esk6_4(X14,X15,X16,X17),X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k2_zfmisc_1(X14,X15) )
      & ( r2_hidden(esk7_4(X14,X15,X16,X17),X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k2_zfmisc_1(X14,X15) )
      & ( X17 = k4_tarski(esk6_4(X14,X15,X16,X17),esk7_4(X14,X15,X16,X17))
        | ~ r2_hidden(X17,X16)
        | X16 != k2_zfmisc_1(X14,X15) )
      & ( ~ r2_hidden(X21,X14)
        | ~ r2_hidden(X22,X15)
        | X20 != k4_tarski(X21,X22)
        | r2_hidden(X20,X16)
        | X16 != k2_zfmisc_1(X14,X15) )
      & ( ~ r2_hidden(esk8_3(X23,X24,X25),X25)
        | ~ r2_hidden(X27,X23)
        | ~ r2_hidden(X28,X24)
        | esk8_3(X23,X24,X25) != k4_tarski(X27,X28)
        | X25 = k2_zfmisc_1(X23,X24) )
      & ( r2_hidden(esk9_3(X23,X24,X25),X23)
        | r2_hidden(esk8_3(X23,X24,X25),X25)
        | X25 = k2_zfmisc_1(X23,X24) )
      & ( r2_hidden(esk10_3(X23,X24,X25),X24)
        | r2_hidden(esk8_3(X23,X24,X25),X25)
        | X25 = k2_zfmisc_1(X23,X24) )
      & ( esk8_3(X23,X24,X25) = k4_tarski(esk9_3(X23,X24,X25),esk10_3(X23,X24,X25))
        | r2_hidden(esk8_3(X23,X24,X25),X25)
        | X25 = k2_zfmisc_1(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_6,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_7,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk1_0),esk2_0)
    & r2_hidden(k2_mcart_1(esk1_0),esk3_0)
    & esk1_0 = k4_tarski(esk4_0,esk5_0)
    & ~ r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k4_tarski(k1_mcart_1(k4_tarski(X1,X2)),k2_mcart_1(k4_tarski(X1,X2))) = k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( esk1_0 = k4_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | X1 != k4_tarski(X4,X5)
    | ~ r2_hidden(X5,X3)
    | ~ r2_hidden(X4,X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk1_0),k2_mcart_1(esk1_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | X1 != esk1_0
    | ~ r2_hidden(k2_mcart_1(esk1_0),X3)
    | ~ r2_hidden(k1_mcart_1(esk1_0),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk1_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(X2,esk3_0))
    | X1 != esk1_0
    | ~ r2_hidden(k1_mcart_1(esk1_0),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk2_0,esk3_0))
    | X1 != esk1_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_17,c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
