%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0396+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:33 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   30 (  55 expanded)
%              Number of clauses        :   21 (  25 expanded)
%              Number of leaves         :    4 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 226 expanded)
%              Number of equality atoms :   11 (  25 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t18_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

fof(c_0_4,plain,(
    ! [X19,X20,X21,X23,X24,X25,X26,X28] :
      ( ( r2_hidden(X21,esk4_3(X19,X20,X21))
        | ~ r2_hidden(X21,X20)
        | X20 != k3_tarski(X19) )
      & ( r2_hidden(esk4_3(X19,X20,X21),X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k3_tarski(X19) )
      & ( ~ r2_hidden(X23,X24)
        | ~ r2_hidden(X24,X19)
        | r2_hidden(X23,X20)
        | X20 != k3_tarski(X19) )
      & ( ~ r2_hidden(esk5_2(X25,X26),X26)
        | ~ r2_hidden(esk5_2(X25,X26),X28)
        | ~ r2_hidden(X28,X25)
        | X26 = k3_tarski(X25) )
      & ( r2_hidden(esk5_2(X25,X26),esk6_2(X25,X26))
        | r2_hidden(esk5_2(X25,X26),X26)
        | X26 = k3_tarski(X25) )
      & ( r2_hidden(esk6_2(X25,X26),X25)
        | r2_hidden(esk5_2(X25,X26),X26)
        | X26 = k3_tarski(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_5,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X9,X10,X12] :
      ( ( r2_hidden(esk1_3(X5,X6,X7),X6)
        | ~ r2_hidden(X7,X5)
        | ~ r1_setfam_1(X5,X6) )
      & ( r1_tarski(X7,esk1_3(X5,X6,X7))
        | ~ r2_hidden(X7,X5)
        | ~ r1_setfam_1(X5,X6) )
      & ( r2_hidden(esk2_2(X9,X10),X9)
        | r1_setfam_1(X9,X10) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r1_tarski(esk2_2(X9,X10),X12)
        | r1_setfam_1(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( ~ r1_tarski(X13,X14)
        | ~ r2_hidden(X15,X13)
        | r2_hidden(X15,X14) )
      & ( r2_hidden(esk3_2(X16,X17),X16)
        | r1_tarski(X16,X17) )
      & ( ~ r2_hidden(esk3_2(X16,X17),X17)
        | r1_tarski(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,esk1_3(X2,X3,X1))
    | ~ r2_hidden(X1,X2)
    | ~ r1_setfam_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_setfam_1(X1,X2)
       => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    inference(assume_negation,[status(cth)],[t18_setfam_1])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,esk1_3(X3,X2,X4))
    | ~ r2_hidden(X4,X3)
    | ~ r1_setfam_1(X3,X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X4))
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X4,X2)
    | ~ r1_setfam_1(X2,X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_15,negated_conjecture,
    ( r1_setfam_1(esk7_0,esk8_0)
    & ~ r1_tarski(k3_tarski(esk7_0),k3_tarski(esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X1,X3)
    | ~ r1_setfam_1(X4,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( r1_setfam_1(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk8_0))
    | ~ r2_hidden(X2,esk7_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_19,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk8_0))
    | X2 != k3_tarski(esk7_0)
    | ~ r2_hidden(X1,esk4_3(esk7_0,X2,X3))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(esk7_0),k3_tarski(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk8_0))
    | ~ r2_hidden(X1,esk4_3(esk7_0,k3_tarski(esk7_0),X2))
    | ~ r2_hidden(X2,k3_tarski(esk7_0)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_2(k3_tarski(esk7_0),k3_tarski(esk8_0)),k3_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(esk8_0))
    | ~ r2_hidden(X1,esk4_3(esk7_0,k3_tarski(esk7_0),esk3_2(k3_tarski(esk7_0),k3_tarski(esk8_0)))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,esk4_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(esk3_2(k3_tarski(esk7_0),k3_tarski(esk8_0)),k3_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_24])]),c_0_28]),
    [proof]).

%------------------------------------------------------------------------------
