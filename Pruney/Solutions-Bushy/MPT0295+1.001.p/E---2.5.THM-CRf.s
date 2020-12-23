%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0295+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:22 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   23 (  59 expanded)
%              Number of clauses        :   16 (  26 expanded)
%              Number of leaves         :    3 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   88 ( 280 expanded)
%              Number of equality atoms :   24 (  70 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t103_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X4,X1)
        & ! [X5,X6] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & X4 = k4_tarski(X5,X6) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
          & r2_hidden(X4,X1)
          & ! [X5,X6] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X6,X3)
                & X4 = k4_tarski(X5,X6) ) ) ),
    inference(assume_negation,[status(cth)],[t103_zfmisc_1])).

fof(c_0_4,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( ~ r1_tarski(X24,X25)
        | ~ r2_hidden(X26,X24)
        | r2_hidden(X26,X25) )
      & ( r2_hidden(esk6_2(X27,X28),X27)
        | r1_tarski(X27,X28) )
      & ( ~ r2_hidden(esk6_2(X27,X28),X28)
        | r1_tarski(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X34,X35] :
      ( r1_tarski(esk7_0,k2_zfmisc_1(esk8_0,esk9_0))
      & r2_hidden(esk10_0,esk7_0)
      & ( ~ r2_hidden(X34,esk8_0)
        | ~ r2_hidden(X35,esk9_0)
        | esk10_0 != k4_tarski(X34,X35) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X13,X14,X15,X16,X17,X18,X20,X21] :
      ( ( r2_hidden(esk1_4(X7,X8,X9,X10),X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( r2_hidden(esk2_4(X7,X8,X9,X10),X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( X10 = k4_tarski(esk1_4(X7,X8,X9,X10),esk2_4(X7,X8,X9,X10))
        | ~ r2_hidden(X10,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( ~ r2_hidden(X14,X7)
        | ~ r2_hidden(X15,X8)
        | X13 != k4_tarski(X14,X15)
        | r2_hidden(X13,X9)
        | X9 != k2_zfmisc_1(X7,X8) )
      & ( ~ r2_hidden(esk3_3(X16,X17,X18),X18)
        | ~ r2_hidden(X20,X16)
        | ~ r2_hidden(X21,X17)
        | esk3_3(X16,X17,X18) != k4_tarski(X20,X21)
        | X18 = k2_zfmisc_1(X16,X17) )
      & ( r2_hidden(esk4_3(X16,X17,X18),X16)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k2_zfmisc_1(X16,X17) )
      & ( r2_hidden(esk5_3(X16,X17,X18),X17)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k2_zfmisc_1(X16,X17) )
      & ( esk3_3(X16,X17,X18) = k4_tarski(esk4_3(X16,X17,X18),esk5_3(X16,X17,X18))
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k2_zfmisc_1(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r1_tarski(esk7_0,k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk8_0,esk9_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk10_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk10_0,k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X2,esk9_0)
    | esk10_0 != k4_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( k4_tarski(esk1_4(esk8_0,esk9_0,k2_zfmisc_1(esk8_0,esk9_0),esk10_0),esk2_4(esk8_0,esk9_0,k2_zfmisc_1(esk8_0,esk9_0),esk10_0)) = esk10_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_4(esk8_0,esk9_0,k2_zfmisc_1(esk8_0,esk9_0),esk10_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_4(esk8_0,esk9_0,k2_zfmisc_1(esk8_0,esk9_0),esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])]),
    [proof]).

%------------------------------------------------------------------------------
