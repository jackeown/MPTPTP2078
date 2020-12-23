%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:20 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   67 (4666 expanded)
%              Number of clauses        :   56 (2267 expanded)
%              Number of leaves         :    5 (1103 expanded)
%              Depth                    :   22
%              Number of atoms          :  168 (22574 expanded)
%              Number of equality atoms :   51 (8892 expanded)
%              Maximal formula depth    :   23 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
    <=> ( r2_hidden(X1,X4)
        & r2_hidden(X2,X5)
        & r2_hidden(X3,X6) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_mcart_1)).

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

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
      <=> ( r2_hidden(X1,X4)
          & r2_hidden(X2,X5)
          & r2_hidden(X3,X6) ) ) ),
    inference(assume_negation,[status(cth)],[t73_mcart_1])).

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

fof(c_0_7,negated_conjecture,
    ( ( ~ r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0))
      | ~ r2_hidden(esk6_0,esk9_0)
      | ~ r2_hidden(esk7_0,esk10_0)
      | ~ r2_hidden(esk8_0,esk11_0) )
    & ( r2_hidden(esk6_0,esk9_0)
      | r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0)) )
    & ( r2_hidden(esk7_0,esk10_0)
      | r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0)) )
    & ( r2_hidden(esk8_0,esk11_0)
      | r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X24,X25,X26] : k3_mcart_1(X24,X25,X26) = k4_tarski(k4_tarski(X24,X25),X26) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_9,plain,(
    ! [X27,X28,X29] : k3_zfmisc_1(X27,X28,X29) = k2_zfmisc_1(k2_zfmisc_1(X27,X28),X29) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_10,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk7_0,esk10_0)
    | r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk8_0,esk11_0)
    | r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk7_0,esk10_0)
    | r2_hidden(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk6_0,esk9_0)
    | r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk8_0,esk11_0)
    | r2_hidden(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_12]),c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_15])])).

cnf(c_0_21,negated_conjecture,
    ( k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))) = k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)
    | r2_hidden(esk7_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk6_0,esk9_0)
    | r2_hidden(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_12]),c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))) = k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)
    | r2_hidden(esk8_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))) = k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)
    | r2_hidden(k4_tarski(X1,esk7_0),k2_zfmisc_1(X2,esk10_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))) = k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)
    | r2_hidden(esk6_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_22])).

fof(c_0_26,plain,(
    ! [X30,X31] :
      ( k1_mcart_1(k4_tarski(X30,X31)) = X30
      & k2_mcart_1(k4_tarski(X30,X31)) = X31 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_27,negated_conjecture,
    ( k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))) = k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)
    | r2_hidden(k4_tarski(X1,esk8_0),k2_zfmisc_1(X2,esk11_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))) = k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)
    | r2_hidden(k4_tarski(esk6_0,esk7_0),k2_zfmisc_1(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))) = k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_16])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_32,negated_conjecture,
    ( esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)) = esk8_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_34,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk8_0) = k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),k2_zfmisc_1(esk9_0,esk10_0))
    | r2_hidden(esk7_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)) = k4_tarski(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),k2_zfmisc_1(esk9_0,esk10_0))
    | r2_hidden(esk7_0,esk10_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),k2_zfmisc_1(esk9_0,esk10_0))
    | r2_hidden(esk6_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( k4_tarski(esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)),esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0))) = k4_tarski(esk6_0,esk7_0)
    | r2_hidden(esk7_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( k4_tarski(esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))),esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))) = esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))
    | r2_hidden(esk6_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( k4_tarski(esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)),esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0))) = k4_tarski(esk6_0,esk7_0)
    | r2_hidden(k4_tarski(X1,esk7_0),k2_zfmisc_1(X2,esk10_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k4_tarski(esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)),esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0))) = k4_tarski(esk6_0,esk7_0)
    | r2_hidden(esk6_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_37]),c_0_37]),c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_45,negated_conjecture,
    ( k4_tarski(esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)),esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0))) = k4_tarski(esk6_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_16])).

cnf(c_0_46,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_45]),c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))),esk10_0)
    | r2_hidden(esk7_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( k4_tarski(esk6_0,esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0))) = k4_tarski(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0))
    | ~ r2_hidden(esk6_0,esk9_0)
    | ~ r2_hidden(esk7_0,esk10_0)
    | ~ r2_hidden(esk8_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk11_0)
    | r2_hidden(esk8_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))),esk9_0)
    | r2_hidden(esk6_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)),esk10_0)
    | r2_hidden(esk7_0,esk10_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_49]),c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(esk6_0,esk9_0)
    | ~ r2_hidden(esk7_0,esk10_0)
    | ~ r2_hidden(esk8_0,esk11_0)
    | ~ r2_hidden(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_12]),c_0_13])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk8_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_32])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)),esk9_0)
    | r2_hidden(esk6_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_37])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk7_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))
    | ~ r2_hidden(esk6_0,esk9_0)
    | ~ r2_hidden(esk7_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk6_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_47])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_0),k2_zfmisc_1(X2,esk10_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))
    | ~ r2_hidden(esk7_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk8_0),k2_zfmisc_1(X2,esk11_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk7_0),k2_zfmisc_1(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_58])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:33:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 2.36/2.53  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 2.36/2.53  # and selection function SelectCQArNTNpEqFirst.
% 2.36/2.53  #
% 2.36/2.53  # Preprocessing time       : 0.026 s
% 2.36/2.53  # Presaturation interreduction done
% 2.36/2.53  
% 2.36/2.53  # Proof found!
% 2.36/2.53  # SZS status Theorem
% 2.36/2.53  # SZS output start CNFRefutation
% 2.36/2.53  fof(t73_mcart_1, conjecture, ![X1, X2, X3, X4, X5, X6]:(r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))<=>((r2_hidden(X1,X4)&r2_hidden(X2,X5))&r2_hidden(X3,X6))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_mcart_1)).
% 2.36/2.53  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.36/2.53  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.36/2.53  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.36/2.53  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.36/2.53  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4, X5, X6]:(r2_hidden(k3_mcart_1(X1,X2,X3),k3_zfmisc_1(X4,X5,X6))<=>((r2_hidden(X1,X4)&r2_hidden(X2,X5))&r2_hidden(X3,X6)))), inference(assume_negation,[status(cth)],[t73_mcart_1])).
% 2.36/2.53  fof(c_0_6, plain, ![X7, X8, X9, X10, X13, X14, X15, X16, X17, X18, X20, X21]:(((((r2_hidden(esk1_4(X7,X8,X9,X10),X7)|~r2_hidden(X10,X9)|X9!=k2_zfmisc_1(X7,X8))&(r2_hidden(esk2_4(X7,X8,X9,X10),X8)|~r2_hidden(X10,X9)|X9!=k2_zfmisc_1(X7,X8)))&(X10=k4_tarski(esk1_4(X7,X8,X9,X10),esk2_4(X7,X8,X9,X10))|~r2_hidden(X10,X9)|X9!=k2_zfmisc_1(X7,X8)))&(~r2_hidden(X14,X7)|~r2_hidden(X15,X8)|X13!=k4_tarski(X14,X15)|r2_hidden(X13,X9)|X9!=k2_zfmisc_1(X7,X8)))&((~r2_hidden(esk3_3(X16,X17,X18),X18)|(~r2_hidden(X20,X16)|~r2_hidden(X21,X17)|esk3_3(X16,X17,X18)!=k4_tarski(X20,X21))|X18=k2_zfmisc_1(X16,X17))&(((r2_hidden(esk4_3(X16,X17,X18),X16)|r2_hidden(esk3_3(X16,X17,X18),X18)|X18=k2_zfmisc_1(X16,X17))&(r2_hidden(esk5_3(X16,X17,X18),X17)|r2_hidden(esk3_3(X16,X17,X18),X18)|X18=k2_zfmisc_1(X16,X17)))&(esk3_3(X16,X17,X18)=k4_tarski(esk4_3(X16,X17,X18),esk5_3(X16,X17,X18))|r2_hidden(esk3_3(X16,X17,X18),X18)|X18=k2_zfmisc_1(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 2.36/2.53  fof(c_0_7, negated_conjecture, ((~r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0))|(~r2_hidden(esk6_0,esk9_0)|~r2_hidden(esk7_0,esk10_0)|~r2_hidden(esk8_0,esk11_0)))&(((r2_hidden(esk6_0,esk9_0)|r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0)))&(r2_hidden(esk7_0,esk10_0)|r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0))))&(r2_hidden(esk8_0,esk11_0)|r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 2.36/2.53  fof(c_0_8, plain, ![X24, X25, X26]:k3_mcart_1(X24,X25,X26)=k4_tarski(k4_tarski(X24,X25),X26), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 2.36/2.53  fof(c_0_9, plain, ![X27, X28, X29]:k3_zfmisc_1(X27,X28,X29)=k2_zfmisc_1(k2_zfmisc_1(X27,X28),X29), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 2.36/2.53  cnf(c_0_10, plain, (X1=k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 2.36/2.53  cnf(c_0_11, negated_conjecture, (r2_hidden(esk7_0,esk10_0)|r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.36/2.53  cnf(c_0_12, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 2.36/2.53  cnf(c_0_13, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.36/2.53  cnf(c_0_14, negated_conjecture, (r2_hidden(esk8_0,esk11_0)|r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.36/2.53  cnf(c_0_15, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 2.36/2.53  cnf(c_0_16, plain, (k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_10])).
% 2.36/2.53  cnf(c_0_17, negated_conjecture, (r2_hidden(esk7_0,esk10_0)|r2_hidden(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_13])).
% 2.36/2.53  cnf(c_0_18, negated_conjecture, (r2_hidden(esk6_0,esk9_0)|r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.36/2.53  cnf(c_0_19, negated_conjecture, (r2_hidden(esk8_0,esk11_0)|r2_hidden(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_12]), c_0_13])).
% 2.36/2.53  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_15])])).
% 2.36/2.53  cnf(c_0_21, negated_conjecture, (k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))=k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)|r2_hidden(esk7_0,esk10_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 2.36/2.53  cnf(c_0_22, negated_conjecture, (r2_hidden(esk6_0,esk9_0)|r2_hidden(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_12]), c_0_13])).
% 2.36/2.53  cnf(c_0_23, negated_conjecture, (k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))=k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)|r2_hidden(esk8_0,esk11_0)), inference(spm,[status(thm)],[c_0_16, c_0_19])).
% 2.36/2.53  cnf(c_0_24, negated_conjecture, (k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))=k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)|r2_hidden(k4_tarski(X1,esk7_0),k2_zfmisc_1(X2,esk10_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 2.36/2.53  cnf(c_0_25, negated_conjecture, (k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))=k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)|r2_hidden(esk6_0,esk9_0)), inference(spm,[status(thm)],[c_0_16, c_0_22])).
% 2.36/2.53  fof(c_0_26, plain, ![X30, X31]:(k1_mcart_1(k4_tarski(X30,X31))=X30&k2_mcart_1(k4_tarski(X30,X31))=X31), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 2.36/2.53  cnf(c_0_27, negated_conjecture, (k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))=k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)|r2_hidden(k4_tarski(X1,esk8_0),k2_zfmisc_1(X2,esk11_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_23])).
% 2.36/2.53  cnf(c_0_28, negated_conjecture, (k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))=k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)|r2_hidden(k4_tarski(esk6_0,esk7_0),k2_zfmisc_1(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 2.36/2.53  cnf(c_0_29, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.36/2.53  cnf(c_0_30, negated_conjecture, (k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)))=k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_16])).
% 2.36/2.53  cnf(c_0_31, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 2.36/2.53  cnf(c_0_32, negated_conjecture, (esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))=esk8_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_29])).
% 2.36/2.53  cnf(c_0_33, plain, (r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_31])).
% 2.36/2.53  cnf(c_0_34, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.36/2.53  cnf(c_0_35, negated_conjecture, (k4_tarski(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk8_0)=k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)), inference(rw,[status(thm)],[c_0_30, c_0_32])).
% 2.36/2.53  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),k2_zfmisc_1(esk9_0,esk10_0))|r2_hidden(esk7_0,esk10_0)), inference(spm,[status(thm)],[c_0_33, c_0_17])).
% 2.36/2.53  cnf(c_0_37, negated_conjecture, (esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))=k4_tarski(esk6_0,esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_34])).
% 2.36/2.53  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),k2_zfmisc_1(esk9_0,esk10_0))|r2_hidden(esk7_0,esk10_0)), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 2.36/2.53  cnf(c_0_39, negated_conjecture, (r2_hidden(esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),k2_zfmisc_1(esk9_0,esk10_0))|r2_hidden(esk6_0,esk9_0)), inference(spm,[status(thm)],[c_0_33, c_0_22])).
% 2.36/2.53  cnf(c_0_40, negated_conjecture, (k4_tarski(esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)),esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)))=k4_tarski(esk6_0,esk7_0)|r2_hidden(esk7_0,esk10_0)), inference(spm,[status(thm)],[c_0_16, c_0_38])).
% 2.36/2.53  cnf(c_0_41, negated_conjecture, (k4_tarski(esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))),esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))))=esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))|r2_hidden(esk6_0,esk9_0)), inference(spm,[status(thm)],[c_0_16, c_0_39])).
% 2.36/2.53  cnf(c_0_42, negated_conjecture, (k4_tarski(esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)),esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)))=k4_tarski(esk6_0,esk7_0)|r2_hidden(k4_tarski(X1,esk7_0),k2_zfmisc_1(X2,esk10_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_40])).
% 2.36/2.53  cnf(c_0_43, negated_conjecture, (k4_tarski(esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)),esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)))=k4_tarski(esk6_0,esk7_0)|r2_hidden(esk6_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_37]), c_0_37]), c_0_37])).
% 2.36/2.53  cnf(c_0_44, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 2.36/2.53  cnf(c_0_45, negated_conjecture, (k4_tarski(esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)),esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)))=k4_tarski(esk6_0,esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_16])).
% 2.36/2.53  cnf(c_0_46, plain, (r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_44])).
% 2.36/2.53  cnf(c_0_47, negated_conjecture, (esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0))=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_45]), c_0_34])).
% 2.36/2.53  cnf(c_0_48, negated_conjecture, (r2_hidden(esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))),esk10_0)|r2_hidden(esk7_0,esk10_0)), inference(spm,[status(thm)],[c_0_46, c_0_36])).
% 2.36/2.53  cnf(c_0_49, negated_conjecture, (k4_tarski(esk6_0,esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)))=k4_tarski(esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_45, c_0_47])).
% 2.36/2.53  cnf(c_0_50, negated_conjecture, (~r2_hidden(k3_mcart_1(esk6_0,esk7_0,esk8_0),k3_zfmisc_1(esk9_0,esk10_0,esk11_0))|~r2_hidden(esk6_0,esk9_0)|~r2_hidden(esk7_0,esk10_0)|~r2_hidden(esk8_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.36/2.53  cnf(c_0_51, negated_conjecture, (r2_hidden(esk2_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0)),esk11_0)|r2_hidden(esk8_0,esk11_0)), inference(spm,[status(thm)],[c_0_46, c_0_19])).
% 2.36/2.53  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),esk1_4(k2_zfmisc_1(esk9_0,esk10_0),esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0),k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0))),esk9_0)|r2_hidden(esk6_0,esk9_0)), inference(spm,[status(thm)],[c_0_33, c_0_39])).
% 2.36/2.53  cnf(c_0_53, negated_conjecture, (r2_hidden(esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)),esk10_0)|r2_hidden(esk7_0,esk10_0)), inference(rw,[status(thm)],[c_0_48, c_0_37])).
% 2.36/2.53  cnf(c_0_54, negated_conjecture, (esk2_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0))=esk7_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_49]), c_0_29])).
% 2.36/2.53  cnf(c_0_55, negated_conjecture, (~r2_hidden(esk6_0,esk9_0)|~r2_hidden(esk7_0,esk10_0)|~r2_hidden(esk8_0,esk11_0)|~r2_hidden(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_12]), c_0_13])).
% 2.36/2.53  cnf(c_0_56, negated_conjecture, (r2_hidden(esk8_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_32])])).
% 2.36/2.53  cnf(c_0_57, negated_conjecture, (r2_hidden(esk1_4(esk9_0,esk10_0,k2_zfmisc_1(esk9_0,esk10_0),k4_tarski(esk6_0,esk7_0)),esk9_0)|r2_hidden(esk6_0,esk9_0)), inference(rw,[status(thm)],[c_0_52, c_0_37])).
% 2.36/2.53  cnf(c_0_58, negated_conjecture, (r2_hidden(esk7_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54])])).
% 2.36/2.53  cnf(c_0_59, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))|~r2_hidden(esk6_0,esk9_0)|~r2_hidden(esk7_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])])).
% 2.36/2.53  cnf(c_0_60, negated_conjecture, (r2_hidden(esk6_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_47])])).
% 2.36/2.53  cnf(c_0_61, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_0),k2_zfmisc_1(X2,esk10_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_58])).
% 2.36/2.53  cnf(c_0_62, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))|~r2_hidden(esk7_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 2.36/2.53  cnf(c_0_63, negated_conjecture, (r2_hidden(k4_tarski(X1,esk8_0),k2_zfmisc_1(X2,esk11_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_56])).
% 2.36/2.53  cnf(c_0_64, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk7_0),k2_zfmisc_1(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_61, c_0_60])).
% 2.36/2.53  cnf(c_0_65, negated_conjecture, (~r2_hidden(k4_tarski(k4_tarski(esk6_0,esk7_0),esk8_0),k2_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0),esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_58])])).
% 2.36/2.53  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), ['proof']).
% 2.36/2.53  # SZS output end CNFRefutation
% 2.36/2.53  # Proof object total steps             : 67
% 2.36/2.53  # Proof object clause steps            : 56
% 2.36/2.53  # Proof object formula steps           : 11
% 2.36/2.53  # Proof object conjectures             : 47
% 2.36/2.53  # Proof object clause conjectures      : 44
% 2.36/2.53  # Proof object formula conjectures     : 3
% 2.36/2.53  # Proof object initial clauses used    : 12
% 2.36/2.53  # Proof object initial formulas used   : 5
% 2.36/2.53  # Proof object generating inferences   : 24
% 2.36/2.53  # Proof object simplifying inferences  : 40
% 2.36/2.53  # Training examples: 0 positive, 0 negative
% 2.36/2.53  # Parsed axioms                        : 5
% 2.36/2.53  # Removed by relevancy pruning/SinE    : 0
% 2.36/2.53  # Initial clauses                      : 16
% 2.36/2.53  # Removed in clause preprocessing      : 2
% 2.36/2.53  # Initial clauses in saturation        : 14
% 2.36/2.53  # Processed clauses                    : 1302
% 2.36/2.53  # ...of these trivial                  : 13
% 2.36/2.53  # ...subsumed                          : 136
% 2.36/2.53  # ...remaining for further processing  : 1153
% 2.36/2.53  # Other redundant clauses eliminated   : 5
% 2.36/2.53  # Clauses deleted for lack of memory   : 0
% 2.36/2.53  # Backward-subsumed                    : 8
% 2.36/2.53  # Backward-rewritten                   : 733
% 2.36/2.53  # Generated clauses                    : 270905
% 2.36/2.53  # ...of the previous two non-trivial   : 270877
% 2.36/2.53  # Contextual simplify-reflections      : 2
% 2.36/2.53  # Paramodulations                      : 270901
% 2.36/2.53  # Factorizations                       : 0
% 2.36/2.53  # Equation resolutions                 : 5
% 2.36/2.53  # Propositional unsat checks           : 0
% 2.36/2.53  #    Propositional check models        : 0
% 2.36/2.53  #    Propositional check unsatisfiable : 0
% 2.36/2.53  #    Propositional clauses             : 0
% 2.36/2.53  #    Propositional clauses after purity: 0
% 2.36/2.53  #    Propositional unsat core size     : 0
% 2.36/2.53  #    Propositional preprocessing time  : 0.000
% 2.36/2.53  #    Propositional encoding time       : 0.000
% 2.36/2.53  #    Propositional solver time         : 0.000
% 2.36/2.53  #    Success case prop preproc time    : 0.000
% 2.36/2.53  #    Success case prop encoding time   : 0.000
% 2.36/2.53  #    Success case prop solver time     : 0.000
% 2.36/2.53  # Current number of processed clauses  : 394
% 2.36/2.53  #    Positive orientable unit clauses  : 132
% 2.36/2.53  #    Positive unorientable unit clauses: 0
% 2.36/2.53  #    Negative unit clauses             : 1
% 2.36/2.53  #    Non-unit-clauses                  : 261
% 2.36/2.53  # Current number of unprocessed clauses: 269372
% 2.36/2.53  # ...number of literals in the above   : 942435
% 2.36/2.53  # Current number of archived formulas  : 0
% 2.36/2.53  # Current number of archived clauses   : 757
% 2.36/2.53  # Clause-clause subsumption calls (NU) : 73413
% 2.36/2.53  # Rec. Clause-clause subsumption calls : 39857
% 2.36/2.53  # Non-unit clause-clause subsumptions  : 141
% 2.36/2.53  # Unit Clause-clause subsumption calls : 3028
% 2.36/2.53  # Rewrite failures with RHS unbound    : 0
% 2.36/2.53  # BW rewrite match attempts            : 3568
% 2.36/2.53  # BW rewrite match successes           : 13
% 2.36/2.53  # Condensation attempts                : 0
% 2.36/2.53  # Condensation successes               : 0
% 2.36/2.53  # Termbank termtop insertions          : 11309427
% 2.36/2.54  
% 2.36/2.54  # -------------------------------------------------
% 2.36/2.54  # User time                : 2.067 s
% 2.36/2.54  # System time              : 0.129 s
% 2.36/2.54  # Total time               : 2.197 s
% 2.36/2.54  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
