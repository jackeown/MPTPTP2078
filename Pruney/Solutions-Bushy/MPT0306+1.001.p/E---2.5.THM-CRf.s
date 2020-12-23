%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0306+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   36 (  96 expanded)
%              Number of clauses        :   29 (  51 expanded)
%              Number of leaves         :    3 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 517 expanded)
%              Number of equality atoms :   24 ( 132 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t118_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(c_0_3,plain,(
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

cnf(c_0_4,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_5,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( ~ r1_tarski(X24,X25)
        | ~ r2_hidden(X26,X24)
        | r2_hidden(X26,X25) )
      & ( r2_hidden(esk6_2(X27,X28),X27)
        | r1_tarski(X27,X28) )
      & ( ~ r2_hidden(esk6_2(X27,X28),X28)
        | r1_tarski(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( r1_tarski(X1,X2)
       => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
          & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t118_zfmisc_1])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | X1 != k4_tarski(X4,X5)
    | ~ r2_hidden(X5,X3)
    | ~ r2_hidden(X4,X2) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k4_tarski(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_2(k2_zfmisc_1(X1,X2),X3)),esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_2(k2_zfmisc_1(X1,X2),X3))) = esk6_2(k2_zfmisc_1(X1,X2),X3)
    | r1_tarski(k2_zfmisc_1(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

fof(c_0_13,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0)
    & ( ~ r1_tarski(k2_zfmisc_1(esk7_0,esk9_0),k2_zfmisc_1(esk8_0,esk9_0))
      | ~ r1_tarski(k2_zfmisc_1(esk9_0,esk7_0),k2_zfmisc_1(esk9_0,esk8_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_15,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | r2_hidden(X4,k2_zfmisc_1(X5,X6))
    | X4 != esk6_2(k2_zfmisc_1(X1,X2),X3)
    | ~ r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_2(k2_zfmisc_1(X1,X2),X3)),X6)
    | ~ r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_2(k2_zfmisc_1(X1,X2),X3)),X5) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | r2_hidden(esk6_2(k2_zfmisc_1(X1,X2),X3),k2_zfmisc_1(X4,X5))
    | ~ r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_2(k2_zfmisc_1(X1,X2),X3)),X5)
    | ~ r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_2(k2_zfmisc_1(X1,X2),X3)),X4) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | r2_hidden(esk2_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_2(k2_zfmisc_1(X1,X2),X3)),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_2(k2_zfmisc_1(X1,X2),X3)),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_8])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | r2_hidden(esk6_2(k2_zfmisc_1(X1,X2),X3),k2_zfmisc_1(X4,X2))
    | ~ r2_hidden(esk1_4(X1,X2,k2_zfmisc_1(X1,X2),esk6_2(k2_zfmisc_1(X1,X2),X3)),X4) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk7_0,X1),X2)
    | r2_hidden(esk1_4(esk7_0,X1,k2_zfmisc_1(esk7_0,X1),esk6_2(k2_zfmisc_1(esk7_0,X1),X2)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,esk7_0),X2)
    | r2_hidden(esk2_4(X1,esk7_0,k2_zfmisc_1(X1,esk7_0),esk6_2(k2_zfmisc_1(X1,esk7_0),X2)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk6_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk7_0,X1),X2)
    | r2_hidden(esk6_2(k2_zfmisc_1(esk7_0,X1),X2),k2_zfmisc_1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,esk7_0),X2)
    | r2_hidden(esk6_2(k2_zfmisc_1(X1,esk7_0),X2),k2_zfmisc_1(X3,esk8_0))
    | ~ r2_hidden(esk1_4(X1,esk7_0,k2_zfmisc_1(X1,esk7_0),esk6_2(k2_zfmisc_1(X1,esk7_0),X2)),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(esk7_0,esk9_0),k2_zfmisc_1(esk8_0,esk9_0))
    | ~ r1_tarski(k2_zfmisc_1(esk9_0,esk7_0),k2_zfmisc_1(esk9_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk7_0,X1),k2_zfmisc_1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,esk7_0),X2)
    | r2_hidden(esk6_2(k2_zfmisc_1(X1,esk7_0),X2),k2_zfmisc_1(X1,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(esk9_0,esk7_0),k2_zfmisc_1(esk9_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,esk7_0),k2_zfmisc_1(X1,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])]),
    [proof]).

%------------------------------------------------------------------------------
